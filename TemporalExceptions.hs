{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances #-}

module TemporalExceptions where

import Data.Time
import Control.Applicative
import Control.Concurrent
import Data.Monoid
import Debug.Trace

import Temporal (Temporal(..), Time, VTime, diffTime)
import qualified Temporal as Temporal

data Warning = StrongOverrun VTime | WeakOverrun VTime deriving Show

data TemporalE a = TE (VTime -> Temporal (a, [Warning]))

instance Monad TemporalE where 
    return a = TE (\_ -> return (a, []))
    (TE p) >>= q = TE (\eps -> do (a, es) <- p eps
                                  let (TE q') = q a
                                  (b, es') <- q' eps
                                  return (b, es++es'))

-- Evaluate a temporal computation
runTime :: VTime -> TemporalE a -> IO (a, [Warning])
runTime eps (TE c) = do startT <- getCurrentTime
                        let (T c') = c eps
                        (y, _) <- c' (startT, startT) 0
                        return y


lift :: Temporal a -> TemporalE a
lift t = TE (\_ -> fmap (\a -> (a, [])) t)

-- Accessors
epsilonTime :: TemporalE VTime
epsilonTime = TE (\eps -> return (eps, []))

time  = lift (Temporal.time)
start = lift (Temporal.start)
getVirtualTime = lift (Temporal.getVirtualTime)
setVirtualTime vT = lift (Temporal.setVirtualTime vT)

-- Lift an IO computation to a temporal computation
liftIO :: IO a -> TemporalE a
liftIO k = lift (Temporal.liftIO k)

{-# INLINE kernelSleep #-}
kernelSleep :: RealFrac a => a -> TemporalE ()
kernelSleep x = lift (Temporal.kernelSleep x)


weakException t = TE (\_ -> return ((), [WeakOverrun t])) >>
                    (liftIO . putStrLn $ "warning: overran by " ++ (show t))
strongException t = TE (\_ -> return ((), [StrongOverrun t])) >>
                    (liftIO . putStrLn $ "WARNING: overran by " ++ (show t))

sleep :: VTime -> TemporalE ()
sleep delayT = do nowT      <- time
                  vT        <- getVirtualTime
                  let vT'   = vT + delayT
                  setVirtualTime vT'
                  startT    <- start
                  eps       <- epsilonTime
                  let diffT = diffTime nowT startT
                  if (vT' < diffT) then if ((vT' + eps) < diffT) 
                                        then strongException (diffT - vT')
                                        else weakException (diffT - vT')
                                   else kernelSleep (vT' - diffT)

duration :: TemporalE b -> TemporalE (b, VTime)
duration k = do x <- k
                startT <- start
                endT <- time
                return $ (x, diffTime endT startT)

{- Alternate computation structures, derived from the monad -}

instance Functor TemporalE where
    fmap f x = do { x' <- x; return (f x') }

instance Applicative TemporalE where
    pure a          = return a
    f <*> x         = do { f' <- f; x' <- x; return (f' x') }

instance Monoid (TemporalE ()) where
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
