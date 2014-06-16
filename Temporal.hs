{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances #-}

module Temporal where

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

-- Evaluate a temporal computation
runTime :: Temporal a -> IO a
runTime (T c) = do startT <- getCurrentTime
                   (y, _) <- c (startT, startT) 0
                   return y

runTime' :: Temporal () -> IO ()
runTime' (T c) = do startT <- getCurrentTime
                    c (startT, startT) 0
                    return ()
                   

-- Effectful computations in Temporal monad

-- Accessors
time, start :: Temporal Time
time  = T (\(_, nowT) -> \vT -> return (nowT, vT))
start = T (\(startT, _) -> \vT -> return (startT, vT))

-- State operations
getVirtualTime :: Temporal VTime
getVirtualTime = T (\(_, _) -> \vT -> return (vT, vT))

setVirtualTime :: VTime -> Temporal ()
setVirtualTime vT = T (\_ -> \_ -> return ((), vT))

-- Sleep
sleep :: VTime -> Temporal ()
sleep delayT = do nowT      <- time
                  vT        <- getVirtualTime
                  let vT'   = vT + delayT
                  setVirtualTime vT'
                  startT    <- start
                  let diffT = diffTime nowT startT
                  if (vT' < diffT) then return () 
                                   else kernelSleep (vT' - diffT)

sleep_alt :: VTime -> Temporal ()
sleep_alt delayT = do vT        <- getVirtualTime
                      let vT'   = vT + delayT
                      setVirtualTime vT'
                      startT    <- start
                      nowT      <- time
                      let diffT = diffTime nowT startT
                      if (vT' < diffT) then return () 
                                       else kernelSleep (vT' - diffT)

-- Lift an IO computation to a temporal computation
liftIO :: IO a -> Temporal a
liftIO k = T (\_ -> \vt -> do {x <- k; return (x, vt)})


{-# INLINE kernelSleep #-}
kernelSleep :: RealFrac a => a -> Temporal ()
kernelSleep x = T (\(_, _) -> \vT -> do { threadDelay (round (x * 1000000)); return ((), vT) })

duration :: Temporal b -> Temporal (b, VTime)
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

fig7a = (sleep 1) <> (sleep 2)
fig7b = (kernelSleep 1) <> (sleep 1) <> (sleep 2)
fig7c = (kernelSleep 2) <> (sleep 1) <> (sleep 2)
fig7d = (kernelSleep 2) <> (sleep 1) <> (kernelSleep 2) <> (sleep 2) 

fig7aA = (sleep 1) *> (sleep 2)
fig7bA = (kernelSleep 1) *> (sleep 1) *> (sleep 2)
fig7cA = (kernelSleep 2) *> (sleep 1) *> (sleep 2)
fig7dA = (kernelSleep 2) *> (sleep 1) *> (kernelSleep 2) *> (sleep 2) 

fig7aM = do sleep 1
            sleep 2

fig7bM = do kernelSleep 1
            sleep 1
            sleep 2

fig7cM = do kernelSleep 2
            sleep 1
            sleep 2

fig7dM = do kernelSleep 2
            sleep 1
            kernelSleep 2
            sleep 2

