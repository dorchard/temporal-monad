{-# LANGUAGE NoMonomorphismRestriction #-}

import Data.Time
import Control.Concurrent
import System.IO.Unsafe

import Debug.Trace

data TimeMonad a = TM { unTM :: (UTCTime, UTCTime, NominalDiffTime) -> (a, NominalDiffTime) }

instance Monad TimeMonad where
    return a      = TM $ \(_, _, vt)  -> return (a, vt)
    (TM c1) >>= f = TM $ \(startT, nowT, vT) -> let thenT = unsafePerformIO getCurrentTime
                                                   (x, vT') = c1 (startT, thenT, vT)
                                                in (unTM $ f x) (startT, nowT, vT')
                                           

runTime :: TimeMonad a -> IO a
runTime (TM c) = do t <- getCurrentTime
                    (y, _) <- c (t, t, 0)
                    return y

getTime :: TimeMonad UTCTime
getTime = TM $ \(_, nowT, vT) -> return (nowT, vT)

startTime :: TimeMonad UTCTime
startTime = TM $ \(startT, _, vT) -> return (startT, vT)

getVirtualTime :: TimeMonad NominalDiffTime
getVirtualTime = TM $ \(_, _, vT) -> return (vT, vT)

setVirtualTime :: NominalDiffTime -> TimeMonad ()
setVirtualTime vT = TM $ \_ -> return ((), vT)

sleep :: NominalDiffTime -> TimeMonad ()
sleep delayT = do vT    <- getVirtualTime
                  thenT <- startTime
                  nowT  <- getTime
                  let diffT = diffUTCTime nowT thenT
                  let vT'   = vT + delayT
                  if (vT' < diffT) then return () else kernelSleep (vT' - diffT)
                  setVirtualTime vT'

kernelSleep :: RealFrac a => a -> TimeMonad ()
kernelSleep x = TM $ \(_, _, vT) -> do { threadDelay (round (x * 1000000)); return ((), vT) } 

{- Testing -}

foo = do a <- getTime
         kernelSleep 2
         sleep 2
         b <- getTime
         sleep 1
         c <- getTime
         return $ (diffUTCTime b a, -- 2
                   diffUTCTime c b, -- 1
                   diffUTCTime c a) -- 3

foo2 = do a <- getTime
          sleep 1
          b <- getTime
          sleep 2
          c <- getTime
          return $ (diffUTCTime b a, 
                    diffUTCTime c b,
                    diffUTCTime c a)

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


law1Foo = unitLaw (\t -> do { sleep t; getTime; }) 1.0
law2Foo = unitLaw2 (TM (\(t, t', _) -> return $ (diffUTCTime t' t, 0)))

law3Foo = assocLaw sleep' sleep2 (TM (\(t, t', _) -> return $ (diffUTCTime t' t, 0)))
                where sleep' x = do { sleep x; return (x * 0.5); }
                      sleep2 x = do { sleep x; sleep x; getTime }

{- law1Foo2 = unitLaw (\t -> (sleep t) >> (TM $ (\_ -> putStrLn "hello"))) 1.0 -}
