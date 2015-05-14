{-# LANGUAGE FlexibleInstances #-}

import Data.Maybe
import Data.List
import Debug.Trace

-- Set-up some type aliases
type State = Int
type Time = Float
type Machine = Int
type Channel = String
type Info = String 

data Action = Send Channel | Recv Channel | Sleep Time | None Info deriving (Eq, Show)

-- Broadcasting communicating timed-automata 
data BCTA = BCTA { current     :: State,   -- current state 
                   clock       :: Time,    -- current clock
                   transitions :: [(State, (State, Action))] -- transition function 
                 } deriving (Eq, Show)

-- System is a number of automata
data System = Sys [BCTA] 

-- Pretty printer for 
instance Show System where
    show (Sys []) = ""
    show (Sys ((BCTA q t ts):as)) = show q ++ " @ " ++ 
                                    "t = " ++ show t ++ "\n" ++ show (Sys as)

------------------------------------------

{- Example 1 
   
   Two process, each with three states in a loop. 
     1) sleeps 2, sends on 'c' then recurses
     2) sleeps 1, receives on 'c' then recurses

    Therefore, the second process has to wait for 1 second to sync with
    the first.

Provides the model for:

live_loop :A do
  sleep 2
  cue :c
end

live_loop :B do
  sleep 1
  sync :c
end

 -}

ex1 = Sys [BCTA 0 0 [(0, (1, Sleep 2)), (1, (2, Send "c")), (2, (0, None ""))], 
           BCTA 0 0 [(0, (1, Sleep 1)), (1, (2, Recv "c")), (2, (0, None ""))]]

{- Example 2
   
   Similar to the above but now the first process (which sends) sleeps only 1, and
   the second sleeps 2. This leads to the processes going 'in phase' after every two
   iterations of the first process

Provides the model for:

live_loop :A do
  sleep 1
  cue :c
end

live_loop :B do
  sleep 2
  sync :c
end

 -}

ex2 = Sys [BCTA 0 0 [(0, (1, Sleep 1)), (1, (2, Send "c")), (2, (0, None ""))], 
           BCTA 0 0 [(0, (1, Sleep 2)), (1, (2, Recv "c")), (2, (0, None ""))]]

{- Exmaple 3 - classic deadlock

Provides the model for:

live_loop :A do
  sync :c
  cue :d
end

live_loop :B do
  sync :d
  cue :c
end

 -}

ex3 = Sys [BCTA 0 0 [(0, (1, Recv "c")), (1, (2, Send "d")), (2, (3, None ""))], 
           BCTA 0 0 [(0, (1, Recv "d")), (1, (2, Send "c")), (2, (3, None ""))]]

{- Example 4 

live_loop :A do
  sleep 0.5
  cue :c
end

in_thread do
  sync :c
  puts "ok"
end

-}

ex4 = Sys [BCTA 0 0 [(0, (1, Sleep 0.5)), (1, (2, Send "c")), (2, (0, None ""))], 
           BCTA 0 0 [(0, (1, Recv "c"))]]

--------------------------------

-- Find a process which has a send on channel at this time
hasSendTo :: Channel -> Time -> System -> Maybe Time
hasSendTo chan atT (Sys []) = Nothing
hasSendTo chan atT (Sys ((BCTA c t ts):as)) = 
                 case lookup c ts of
                   Just (q, Send chan') -> if chan == chan' && t >= atT 
                                           then Just t
                                           else hasSendTo chan atT (Sys as)
                   _                    -> hasSendTo chan atT (Sys as)

-- Causes (at most) one transition step for every automata in a system
step sys@(Sys xs) = 
     Sys $ map (\(me, a) -> runLocal me a) (zip [0..] xs)
          where
           runLocal me a@(BCTA q t ts) = 
               case lookup q ts of 
                   Nothing -> a 
                   Just (q1, None i)   -> a { current = q1 }
                   Just (q1, Sleep dt) -> a { current = q1, clock = t + dt }
                   Just (q1, Send ch)  -> a { current = q1 }
                   Just (q1, Recv ch)  -> case (hasSendTo ch t sys) of
                                                   Nothing   -> a
                                                   Just nt -> a { current = q1, clock = nt }
      
-- run the example - Press any key to move on, press 'q' or 'x' to terminate
run ex = do putStrLn $ show ex
            x <- getChar
            if (x=='q' || x =='x') then return ()
            else run (step ex)
                   
---------------------------------------------------------------------------------

-- Timed automata (just the transition functions, assuming natural nubmer states,
--   parameterised on the alphabet
data TA alphabet = TA [(State, (State, alphabet))] -- transition function 

-- Convert a network of BCTAs into a single timed auomata
toTimedAut :: System -> TA [Action]
toTimedAut (Sys xs) = TA $ step xs [] 0 where

    minSleep :: [Action] -> Time
    minSleep = minimum . mapMaybe (\x -> case x of Sleep t -> Just t
                                                   _       -> Nothing) 

    updateTrans :: [(State, (State, Action))] -> State -> Action -> [(State, (State, Action))]
    updateTrans [] _ _ = []
    updateTrans ((q1, (q2, a)):ts) q b | q == q1   = (q1, (q2, b)) : ts
                                       | otherwise = (q1, (q2, a)) : (updateTrans ts q b) 

    advance sys minSleep me a@(BCTA q t ts) = 
         case lookup q ts of 
              Nothing -> (a { current = -1 }, None "finished")
              Just (q1, None i)   -> (a { current = q1, clock = t }, None i)
              Just (q1, Sleep dt) -> 
                     if dt == minSleep
                     then (a { current = q1, clock = t + dt }, Sleep dt)
                     else (a { transitions = splitSleep ts q minSleep, 
                               current     = q1, 
                               clock       = t + minSleep }, Sleep minSleep)

              Just (q1, Send ch)  -> (a { current = q1, clock = t }, Send ch)
              Just (q1, Recv ch)  -> case (hasSendTo ch t (Sys sys)) of
                                           Nothing -> (a, None $ "blocked on recv " ++ ch)
                                           Just nt -> (a { current = q1, clock = nt }, Recv ch)

    step as ass q = 
          let ms = minSleep $ map (\(BCTA q _ ts) -> maybe (None "") snd (lookup q ts)) as
              (as', acs) = unzip $ map (\(me, a) -> advance as ms me a) (zip [0..] as) 

          in   if ((CT as') `elem` ass)
               then [(q, (fromJust $ elemIndex (CT as') ass, [None ""]))]
               else (q, (q+1, acs)) : (step as' (ass ++ [CT as']) (q+1))

-- Show the transition function
instance Show (TA [Action]) where
    show (TA [])     = ""
    show (TA (x:xs)) = show x ++ "\n" ++ show (TA xs)

-- Special wrapper for performing equality where consecutive sleeps are coalesced
data CT = CT [BCTA] 
instance Eq CT where
    (CT sys) == (CT sys') = coalesceSleeps sys `equ` coalesceSleeps sys'
                             where -- ignore the clock when checking equality
                                   equ as1 as2 = (map current as1) == (map current as2) 
                                              && (map transitions as1) == (map transitions as2)

-- split a sleep state into two 
splitSleep :: [(State, (State, Action))] -> State -> Time -> [(State, (State, Action))]
splitSleep [] _ _ = []
splitSleep ((q1, (q2, Sleep t)):ts) q dT | q == q1 
      = (q1, (q2, Sleep dT)) : (q2, (q2+1, Sleep (t-dT))) : (map (incStatesAfter q1) ts)
           where incStatesAfter q (q1, (q2, a)) =
                    (if q1 > q then q1 + 1 else q1, (if q2 > q then q2 + 1 else q2, a))
splitSleep (t:ts) q dT = t : (splitSleep ts q dT)

-- coalesce two consecutive sleeps into once (roughly the inverse to splitSleeps). 
coalesceSleeps :: [BCTA] -> [BCTA]
coalesceSleeps = map (\(BCTA q t ts) -> BCTA q t (coalesceSleepsT ts)) 
coalesceSleepsT :: [(State, (State, Action))] -> [(State, (State, Action))]
coalesceSleepsT [] = []
coalesceSleepsT (a@(q1, (q2, Sleep t1)):(b@(q2', (q3, Sleep t2)):ts)) = 
        if (q2 == q2') then coalesceSleepsT ((q1, (q3, Sleep $ t1+t2)) : ts)
                       else a:(coalesceSleepsT (b:ts))
coalesceSleepsT (a:ts) = a:(coalesceSleepsT ts)
