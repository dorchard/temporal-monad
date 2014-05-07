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
sleep' delayT = do nowT      <- time
                   vT        <- getVirtualTime
                   let vT'   = vT + delayT
                   setVirtualTime vT'
                   startT    <- start
                   let diffT = diffTime nowT startT
                   if (vT' < diffT) then return () 
                                    else kernelSleep (vT' - diffT)

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

testQ slp = do (r1, r1p, r1m) <- getMean 5 (test1 slp)
               putStrLn $ (show $ r1) ++ "\t" ++ (show r1p) ++ "\t" ++ (show r1m)
               (r2, r2p, r2m) <- getMean 5 (test2 slp)
               putStrLn $ (show $ r2) ++ "\t" ++ (show r2p) ++ "\t" ++ (show r2m)
               (r3, r3p, r3m) <- getMean 5 (test3A slp)
               putStrLn $ (show $ r3) ++ "\t" ++ (show r3p) ++ "\t" ++ (show r3m)
               (r4, r4p, r4m) <- getMean 5 (test3 slp)
               putStrLn $ (show $ r4) ++ "\t" ++ (show r4p) ++ "\t" ++ (show r4m)
               (r5, r5p, r5m) <- getMean 5 (test3' slp)
               putStrLn $ (show $ r5) ++ "\t" ++ (show r5p) ++ "\t" ++ (show r5m)
               (r6, r6p, r6m) <- getMean 5 (test3'' slp)
               putStrLn $ (show $ r6) ++ "\t" ++ (show r6p) ++ "\t" ++ (show r6m)
               (r7, r7p, r7m) <- getMean 5 (test4A slp)
               putStrLn $ (show $ r7) ++ "\t" ++ (show r7p) ++ "\t" ++ (show r7m)
               (r8, r8p, r8m) <- getMean 5 (test4B slp)
               putStrLn $ (show $ r8) ++ "\t" ++ (show r8p) ++ "\t" ++ (show r8m)
               (r9, r9p, r9m) <- getMean 5 (test5 slp)
               putStrLn $ (show $ r9) ++ "\t" ++ (show r9p) ++ "\t" ++ (show r9m)
               (r10, r10p, r10m) <- getMean 5 (test6 slp)
               putStrLn $ (show $ r10) ++ "\t" ++ (show r10p) ++ "\t" ++ (show r10m)
               (r11, r11p, r11m) <- getMean 5 (test7 slp)
               putStrLn $ (show $ r11) ++ "\t" ++ (show r11p) ++ "\t" ++ (show r11m)

-- [test1]_t = 2
test1 slp = 
     do kernelSleep 2
        slp 2
        slp 1

-- [test2]_t = 3
test2 slp =
      do slp 1
         slp 2

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

-- [test4B]_t = 5
test4B slp = do kernelSleep 5
                slp 2

test5 slp = do kernelSleep 2
               sleep 3
               kernelSleep 1
               sleep 1
               kernelSleep 1
               sleep 2

test6 slp = do kernelSleep (2.9999::Float)
               sleep 1
               sleep 2
test7 slp = do kernelSleep (2.98::Float)
               sleep 3
               

getMean :: Integer -> Temporal b -> IO (VTime, VTime, VTime)
getMean n k = do (d, dmax, dmin) <- getMean' n
                 let dmean = d / (fromInteger n)
                 return (dmean, dmax - dmean, dmin - dmean)
               where getMean' 0 = return (0, 0, 1000000)
                     getMean' c = do (_, d)  <- runTime $ duration k
                                     (d', dmax, dmin) <- getMean' (c - 1)
                                     return (d + d', d `max` dmax, d `min` dmin)

