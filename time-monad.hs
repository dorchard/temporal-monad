{-# LANGUAGE NoMonomorphismRestriction #-}

import Data.Time
import Control.Concurrent

import Debug.Trace

data TimeMonad a = TM { unTM :: (UTCTime, UTCTime, NominalDiffTime) -> IO (a, NominalDiffTime) }

instance Monad TimeMonad where
    return a      = TM $ \(_, _, vt)  -> return (a, vt)
    (TM c1) >>= f = TM $ \(startT, nowT, vT) -> do thenT <- getCurrentTime
                                                   (x, vT') <- c1 (startT, thenT, vT)
                                                   (unTM $ f x) (startT, nowT, vT')
                                           

runTime :: TimeMonad a -> IO a
runTime (TM c) = do t <- getCurrentTime
                    (y, _) <- c (t, t, 0)
                    return y

time :: TimeMonad UTCTime
time = TM $ \(_, nowT, vT) -> return (nowT, vT)

startTime :: TimeMonad UTCTime
startTime = TM $ \(startT, _, vT) -> return (startT, vT)

virtualTime :: TimeMonad NominalDiffTime
virtualTime = TM $ \(_, _, vT) -> return (vT, vT)

setVirtualTime :: NominalDiffTime -> TimeMonad ()
setVirtualTime vT = TM $ \_ -> return ((), vT)

sleep :: NominalDiffTime -> TimeMonad ()
sleep delayT = do vT    <- virtualTime
                  thenT <- startTime
                  nowT  <- time
                  let diffT = diffUTCTime nowT thenT
                  let vT'   = vT + delayT
                  if (vT' < diffT) then return () else kernelSleep (vT' - diffT)
                  setVirtualTime vT'

kernelSleep :: RealFrac a => a -> TimeMonad ()
kernelSleep x = TM $ \(_, _, vT) -> do { threadDelay (round (x * 1000000)); return ((), vT) } 

{- Testing -}

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
          s <- startTime
          e <- time
          return $ (diffUTCTime e s)

foo4 = do kernelSleep 2
          sleep 1
          -- ;
          --sleep 2
          --kernelSleep 3
          foo4A
          s <- startTime
          e <- time
          return $ (diffUTCTime e s)

foo4' = do kernelSleep 2
           sleep 1
           -- ;
           --kernelSleep 5
           --sleep 2
           foo4B
           s <- startTime
           e <- time
           return $ (diffUTCTime e s)

foo4'' = do kernelSleep 2
            sleep 1
            -- ;
            kernelSleep 3
            sleep 2
            s <- startTime
            e <- time
            return $ (diffUTCTime e s)



foo4A = do sleep 2
           kernelSleep 3
           s <- startTime
           e <- time
           r <- virtualTime
           return $ (diffUTCTime e s, r)

foo4B = do kernelSleep 5
           sleep 2
           s <- startTime
           e <- time
           r <- virtualTime
           return $ (diffUTCTime e s, r)


foo5 = do sleep 1
          sleep 2
          s <- startTime
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
law2Foo = unitLaw2 (TM (\(t, t', _) -> return $ (diffUTCTime t' t, 0)))

law3Foo = assocLaw sleep' sleep2 (TM (\(t, t', _) -> return $ (diffUTCTime t' t, 0)))
                where sleep' x = do { sleep x; return (x * 0.5); }
                      sleep2 x = do { sleep x; sleep x; time }

{- law1Foo2 = unitLaw (\t -> (sleep t) >> (TM $ (\_ -> putStrLn "hello"))) 1.0 -}
