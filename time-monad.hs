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
sleep delayT = do vT     <- getVirtualTime
                  startT <- start
                  nowT   <- time
                  let diffT = diffTime nowT startT
                  let vT'   = vT + delayT
                  if (vT' < diffT) then return () 
                                   else kernelSleep (vT' - diffT)
                  setVirtualTime vT'

kernelSleep :: RealFrac a => a -> Temporal ()
kernelSleep x = T (\(_, _) -> \vT -> do { threadDelay (round (x * 1000000)); return ((), vT) })

duration k = do k
                startT <- start
                endT <- time
                return $ (diffTime endT startT)

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

foo = do a <- time
         kernelSleep 2
         sleep 2
         b <- time
         sleep 1
         c <- time
         return $ (diffUTCTime b a, -- 2
                   diffUTCTime c b, -- 1
                   diffUTCTime c a) -- 3

foo2 = do a <- time
          sleep 1
          b <- time
          sleep 2
          c <- time
          return $ (diffUTCTime b a, -- 1
                    diffUTCTime c b, -- 2
                    diffUTCTime c a) -- 3

-- [foo4A]_t = 6
foo4A = (kernelSleep 2) *> (sleep 1) *> (sleep 2) *> (kernelSleep 3)

-- [foo4]_t = 6
foo4 = do kernelSleep 2
          sleep 1
          foo5A

-- [foo4']_t = 7
foo4' = do kernelSleep 2
           sleep 1
           foo5B

-- [foo4'']_t = 5
foo4'' = do kernelSleep 2
            sleep 1
            kernelSleep 3
            sleep 2

-- [foo5A]_t = 5
foo5A = do sleep 2
           kernelSleep 3
           s <- start
           e <- time
           r <- getVirtualTime
           return $ (diffUTCTime e s, r)

-- [foo5B]_t = 5
foo5B = do kernelSleep 5
           sleep 2
           s <- start
           e <- time
           r <- getVirtualTime
           return $ (diffUTCTime e s, r)


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
