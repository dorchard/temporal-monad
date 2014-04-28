{-# LANGUAGE NoMonomorphismRestriction #-}

import Data.Time
import Control.Applicative
import Control.Concurrent

import Debug.Trace

type Time = UTCTime
type VTime = NominalDiffTime
diffTime = diffUTCTime

data Temporal a = T ((Time, Time) -> (VTime -> IO (a, VTime)))

instance Functor Temporal where
    fmap f (T x) = T (\(startT, nowT) -> \vT -> do (a, vT') <- x (startT, nowT) vT
                                                   return (f a, vT'))

instance Applicative Temporal where
    pure a          = T (\(_, _) -> \vt -> return (a, vt))
    (T f) <*> (T x) = T (\(startT, nowT) -> \vT -> 
                             do thenT      <- getCurrentTime
                                (f', vT')  <- f (startT, thenT) vT
                                (x', vT'') <- x (startT, nowT) vT'
                                return (f' x', vT''))

instance Monad Temporal where
    return a     = T $ \(_, _) -> \vt -> return (a, vt)
    (T c1) >>= f = T $ \(startT, nowT) -> \vT -> do thenT <- getCurrentTime
                                                    (x, vT') <- c1 (startT, thenT) vT
                                                    let (T c2) = f x in c2 (startT, nowT) vT'
                                           

runTime :: Temporal a -> IO a
runTime (T c) = do t <- getCurrentTime
                   (y, _) <- c (t, t) 0
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
kernelSleep x = T $ \(_, _) -> \vT -> do { threadDelay (round (x * 1000000)); return ((), vT) } 

{- Testing -}

timeTaken k = do k
                 startT <- start
                 endT <- time
                 return $ (diffTime endT startT)


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
          return $ (diffUTCTime b a, 
                    diffUTCTime c b,
                    diffUTCTime c a)

foo3 = do sleep 1
          sleep 2
          s <- start
          e <- time
          return $ (diffUTCTime e s)

foo4app = (kernelSleep 2) *> (sleep 1) *> (sleep 2) *> (kernelSleep 3)


foo4 = do kernelSleep 2
          sleep 1
          -- ;
          foo4A
          s <- start
          e <- time
          return $ (diffUTCTime e s)

foo4' = do kernelSleep 2
           sleep 1
           -- ;
           --kernelSleep 5
           --sleep 2
           foo4B
           s <- start
           e <- time
           return $ (diffUTCTime e s)

foo4'' = do kernelSleep 2
            sleep 1
            -- ;
            kernelSleep 3
            sleep 2
            s <- start
            e <- time
            return $ (diffUTCTime e s)



foo4A = do sleep 2
           kernelSleep 3
           s <- start
           e <- time
           r <- getVirtualTime
           return $ (diffUTCTime e s, r)

foo4B = do kernelSleep 5
           sleep 2
           s <- start
           e <- time
           r <- getVirtualTime
           return $ (diffUTCTime e s, r)


foo5 = do sleep 1
          sleep 2
          s <- start
          e <- time
          return $ (diffUTCTime e s)
          

{- Monad laws -}

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

{- law1Foo2 = unitLaw (\t -> (sleep t) >> (T $ (\_ -> putStrLn "hello"))) 1.0 -}
