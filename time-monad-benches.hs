{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances #-}

import Data.Time
import Control.Applicative
import Control.Concurrent
import Data.Monoid

import Debug.Trace

-- Some aliases to simplify code
type Time = UTCTime
type VTime = NominalDiffTime
diffTime = diffUTCTime

-- Core data type and monad definition
data Temporal a = T ((Time, Time) -> (VTime -> IO (a, VTime)))

instance Monad Temporal where
    return a     = T (\_ -> \vt -> return (a, vt))

    (T p) >>= q  = T (\(startT, nowT) -> \vt -> 
                             do (x, vt')    <- p (startT, nowT) vt
                                let (T q')  = q x
                                thenT       <- getCurrentTime
                                q' (startT, thenT) vt')

runTime :: Temporal a -> IO a
runTime (T c) = do startT <- getCurrentTime
                   (y, _) <- c (startT, startT) 0
                   return y

time, start :: Temporal Time
time  = T (\(_, nowT) -> \vT -> return (nowT, vT))
start = T (\(startT, _) -> \vT -> return (startT, vT))

getVirtualTime :: Temporal VTime
getVirtualTime = T (\(_, _) -> \vT -> return (vT, vT))

setVirtualTime :: VTime -> Temporal ()
setVirtualTime vT = T (\_ -> \_ -> return ((), vT))

sleep :: VTime -> Temporal ()
sleep delayT = do vT        <- getVirtualTime
                  let vT'   = vT + delayT
                  setVirtualTime vT'
                  startT    <- start
                  nowT      <- time
                  let diffT = diffTime nowT startT
                  if (vT' < diffT) then return () 
                                   else kernelSleep (vT' - diffT)

sleep' :: VTime -> Temporal ()
sleep' delayT = do vT        <- getVirtualTime
                   let vT'   = vT + delayT
                   setVirtualTime vT'
                   startT    <- start
                   nowT      <- time
                   let diffT = diffTime nowT startT
                   kernelSleep (vT' - diffT)

sleep'' :: VTime -> Temporal ()
sleep'' delayT = do nowT      <- time
                    vT        <- getVirtualTime
                    let vT'   = vT + delayT
                    setVirtualTime vT'
                    startT    <- start
                    let diffT = diffTime nowT startT
                    if (vT' < diffT) then return () 
                                     else kernelSleep (vT' - diffT)

sleept :: VTime -> Temporal ()
sleept delayT = do vT        <- getVirtualTime
                   startT    <- start
                   nowT      <- time
                   let vT'   = vT + delayT
                   let diffT = diffTime nowT startT
                   if (vT' < diffT) then return () 
                                   else kernelSleep (vT' - diffT)
                   setVirtualTime vT'

sleep3 :: VTime -> Temporal ()
sleep3 delayT = do nowT      <- time
                   vT        <- getVirtualTime
                   let vT'   = vT + delayT
                   setVirtualTime vT'
                   startT    <- start
                   let diffT = diffTime nowT startT
                   kernelSleep (vT' - diffT)
  
liftT :: IO a -> Temporal a
liftT k = T (\_ -> \vt -> do {x <- k; return (x, vt)})


{-# INLINE kernelSleep #-}
kernelSleep :: RealFrac a => a -> Temporal ()
kernelSleep x = T (\(_, _) -> \vT -> do { threadDelay (round (x * 1000000)); return ((), vT) })

duration k = do x <- k
                startT <- start
                endT <- time
                return $ (x, diffTime endT startT)

{- Alternate computation structures, derived from the monad -}

instance Functor Temporal where
    fmap f x = do { x' <- x; return (f x') }

instance Applicative Temporal where
    pure a          = return a
    f <*> x         = do { f' <- f; x' <- x; return (f' x') }

instance Monoid (Temporal ()) where
    mempty        = return ()
    a `mappend` b = do { a; b; return () }

{- Paper examples -}

fig2a = (sleep 1) <> (sleep 2)
fig2b = (kernelSleep 1) <> (sleep 1) <> (sleep 2)
fig2c = (kernelSleep 2) <> (sleep 1) <> (sleep 2)
fig2d = (kernelSleep 2) <> (sleep 1) <> (kernelSleep 2) <> (sleep 2) 

fig2aA = (sleep 1) *> (sleep 2)
fig2bA = (kernelSleep 1) *> (sleep 1) *> (sleep 2)
fig2cA = (kernelSleep 2) *> (sleep 1) *> (sleep 2)
fig2dA = (kernelSleep 2) *> (sleep 1) *> (kernelSleep 2) *> (sleep 2) 

fig2aM = do sleep 1
            sleep 2

fig2bM = do kernelSleep 1
            sleep 1
            sleep 2

fig2cM = do kernelSleep 2
            sleep 1
            sleep 2

fig2dM = do kernelSleep 2
            sleep 1
            kernelSleep 2
            sleep 2

{- Other examples -}

main = do putStrLn "sleep"
          testQ sleep
          putStrLn "sleep'"
          testQ sleep'
          putStrLn "sleep''"
          testQ sleep''
          putStrLn "sleep trad"
          testQ sleept
          putStrLn "sleep3"
          testQ sleep3

testQ slp = do (_, r1) <- getMean 5 (test1 slp)
               putStrLn $ show $ r1
               (_, r2) <- getMean 5 (test2 slp)
               putStrLn $ show $ r2
               (_, r3) <- getMean 5 (test3A slp)
               putStrLn $ show $ r3
               (_, r4) <- getMean 5 (test3 slp)
               putStrLn $ show $ r4
               (_, r5) <- getMean 5 (test3' slp)
               putStrLn $ show $ r5
               (_, r6) <- getMean 5 (test3'' slp)
               putStrLn $ show $ r6
               (_, r7) <- getMean 5 (test4A slp)
               putStrLn $ show $ r7
               (_, r8) <- getMean 5 (test4B slp)
               putStrLn $ show $ r8

tests slp = do putStrLn "test 1, expected = 2s, (2s, 1s, 3s)" 
               r1 <- getMean 5 (test1 slp)
               putStrLn $ show $ r1

               putStrLn "test 2, expected = 3s, (1s, 2s, 3s)"
               r2 <- getMean 5 (test2 slp)
               putStrLn $ show $ r2

               putStrLn "test 3A, expected = 6s"
               r3 <- getMean 5 (test3A slp)
               putStrLn $ show $ r3

               putStrLn "test 3, expected = 6s"
               r4 <- getMean 5 (test3 slp)
               putStrLn $ show $ r4

               putStrLn "test 3', expected = 7s"
               r5 <- getMean 5 (test3' slp)
               putStrLn $ show $ r5

               putStrLn "test 3'', expected = 5s"
               r6 <- getMean 5 (test3'' slp)
               putStrLn $ show $ r6

               putStrLn "test 4A, expected = 5s"
               r7 <- getMean 5 (test4A slp)
               putStrLn $ show $ r7

               putStrLn "test 4B, expected = 5s"
               r8 <- getMean 5 (test4B slp)
               putStrLn $ show $ r8

-- [test1]_t = 2
test1 slp = 
     do a <- time
        kernelSleep 2
        slp 2
        b <- time
        slp 1
        c <- time
        return $ (diffUTCTime b a, -- 2s
                  diffUTCTime c b, -- 1s
                  diffUTCTime c a) -- 3s

-- [test2]_t = 3
test2 slp =
      do a <- time
         slp 1
         b <- time
         slp 2
         c <- time
         return $ (diffUTCTime b a, -- 1s
                   diffUTCTime c b, -- 2s
                   diffUTCTime c a) -- 3s

-- [test3A]_t = 6
test3A slp = (kernelSleep 2) *> (slp 1) *> (slp 2) *> (kernelSleep 3)

-- [test3]_t = 6
test3 slp = do kernelSleep 2
               slp 1
               (test4A slp)

-- [test3']_t = 7
test3' slp = do kernelSleep 2
                slp 1
                (test4B slp)

-- [test3'']_t = 5
test3'' slp = do kernelSleep 2
                 slp 1
                 kernelSleep 3
                 slp 2

-- [test4A]_t = 5
test4A slp = do slp 2
                kernelSleep 3
                s <- start
                e <- time
                r <- getVirtualTime
                return $ (diffUTCTime e s, r)

-- [test4B]_t = 5
test4B slp = do kernelSleep 5
                slp 2
                s <- start
                e <- time
                r <- getVirtualTime
                return $ (diffUTCTime e s, r)

getMean :: (Fractional b) => Integer -> Temporal b -> IO (b, NominalDiffTime)
getMean n k = do (r, d) <- getMean' n
                 return (r / (fromInteger n), d / (fromInteger n))
               where getMean' 0 = return (0, 0)
                     getMean' c = do (r, d)  <- runTime $ duration k
                                     (r', d') <- getMean' (c - 1)
                                     return (r + r', d + d')
instance Num () where
    () + () = ()
    fromInteger _ = ()
instance Fractional () where
    () / () = ()

instance (Num a, Num b, Num c) => Num (a, b, c) where
    (a, b, c) + (x, y, z) = (a + x, b + y, c + z)
    fromInteger i = (fromInteger i, fromInteger i, fromInteger i)
instance (Fractional a, Fractional b, Fractional c) => Fractional (a, b, c) where
    (a, b, c) / (x, y, z) = (a / x, b / y, c / z)

instance (Num a, Num b) => Num (a, b) where
    (a, b) + (x, y) = (a + x, b + y)
    fromInteger i = (fromInteger i, fromInteger i)
instance (Fractional a, Fractional b) => Fractional (a, b) where
    (a, b) / (x, y) = (a / x, b / y)


{- Monad laws experimentation -}

unitLaw f x = do left  <- runTime $ do { y <- return x; f y }
                 right <- runTime $ do { f x }
                 putStrLn $ show left
                 putStrLn $ show right

unitLaw2 m = do left  <- runTime $ do { x <- m;  return x }
                right <- runTime $ do { m }
                putStrLn $ show left
                putStrLn $ show right


assocLaw f g m = do left  <- runTime $ do { y <- do { x <- m; f x; }; g y } 
                    right <- runTime $ do { x <- m; do { y <- f x; g y }; }
                    putStrLn $ show left
                    putStrLn $ show right


law1Foo = unitLaw (\t -> do { sleep t; time; }) 1.0
law2Foo = unitLaw2 (T (\(t, t') _ -> return $ (diffUTCTime t' t, 0)))

law3Foo = assocLaw sleep' sleep2 (T (\(t, t') _ -> return $ (diffUTCTime t' t, 0)))
                where sleep' x = do { sleep x; return (x * 0.5); }
                      sleep2 x = do { sleep x; sleep x; time }
