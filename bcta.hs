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

data Tree a = Node [Tree a] | Leaf a deriving Eq

instance Show a => Show (Tree a) where
    show (Leaf x) = show x
    show (Node ls) = show ls

instance Functor Tree where
    fmap f (Node ns) = Node (map (fmap f) ns) 
    fmap f (Leaf x)  = Leaf (f x)

instance Monad Tree where
    return x = Leaf x
    (Leaf x) >>= f  = f x
    (Node ns) >>= f = Node (map (\x -> x >>= f) ns)

-- Broadcasting communicating timed-automata 
data BCTA = BCTA { current     :: Tree (State, Time), -- current states/times
                                                      --  [ tree for simulating branching ]
                   transitions :: [(State, (State, Action))] -- transition function 
                 } deriving (Eq, Show)

-- System is a number of automata
data System = Sys [BCTA] 

-- Pretty printer for 
instance Show System where
    show (Sys []) = ""
    show (Sys ((BCTA qs ts):as)) = show (fmap fst qs) ++ " @ " ++ 
                                    "t = " ++ show (fmap snd qs) ++ "\n" ++ show (Sys as)

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

ex1 = Sys [BCTA (Leaf (0, 0)) [(0, (1, Sleep 2)), (1, (2, Send "c")), (2, (0, None ""))], 
           BCTA (Leaf (0, 0)) [(0, (1, Sleep 1)), (1, (2, Recv "c")), (2, (0, None ""))]]

-- 
-- [BCTA {current = (0,6.0), transitions = [(0,(1,Sleep 1.0)),(1,(2,Sleep 1.0)),(2,(3,Send "c")),(3,(0,None ""))]},BCTA {current = (0,6.0), transitions = [(0,(1,Sleep 1.0)),(1,(2,Recv "c")),(2,(0,None ""))]}] 


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

ex2 = Sys [BCTA (Leaf (0, 0)) [(0, (1, Sleep 1)), (1, (2, Send "c")), (2, (0, None ""))], 
           BCTA (Leaf (0, 0)) [(0, (1, Sleep 2)), (1, (2, Recv "c")), (2, (0, None ""))]]

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

ex3 = Sys [BCTA (Leaf (0, 0)) [(0, (1, Recv "c")), (1, (2, Send "d")), (2, (3, None ""))], 
           BCTA (Leaf (0, 0)) [(0, (1, Recv "d")), (1, (2, Send "c")), (2, (3, None ""))]]

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

ex4 = Sys [BCTA (Leaf (0, 0)) [(0, (1, Sleep 0.5)), (1, (2, Send "c")), (2, (0, None ""))], 
           BCTA (Leaf (0, 0)) [(0, (1, Recv "c"))]]

{- Example 5 

live_loop :A do
  if p then 
      sleep 2
  else
      sleep 1
  end
end

-}

ex5 = Sys [BCTA (Leaf (0, 0)) [(0, (1, Sleep 1)), (0, (1, Sleep 2)), (1, (0, None ""))]]


--------------------------------

-- Find a process which has a send on channel at this time
hasSendTo :: Channel -> Time -> System -> Maybe Time
hasSendTo chan atT (Sys []) = Nothing
hasSendTo chan atT (Sys ((BCTA qs trs):as)) = 
  let hasSendTo' (Node []) = Nothing
      hasSendTo' (Node (n:ns)) = case (hasSendTo' n) of
                                   Nothing -> hasSendTo' (Node ns)
                                   Just t  -> Just t 
      hasSendTo' (Leaf (c, t)) =
          case lookup c trs of
            Just (q, Send chan') -> if chan == chan' && t >= atT 
                                    then Just t
                                    else Nothing
            _                    -> Nothing
  in case (hasSendTo' qs) of
       Nothing -> hasSendTo chan atT (Sys as)
       Just t  -> Just t

-- Causes transitions (to at most a depth one) for every automata in a system
step sys@(Sys xs) = 
     Sys $ map (\(me, a) -> runLocal me a) (zip [0..] xs)
          where
           runLocal me a@(BCTA qs trs) = a { current = qs >>= (runLocal' trs) }

           trans :: (State, Time) -> (State, Action) -> (State, Time)
           trans (q, t) (q1, None i)   = (q1, t) -- a { current = q1 }
           trans (q, t) (q1, Sleep dt) = (q1, t + dt) -- a { current = q1, clock = t + dt }
           trans (q, t) (q1, Send ch)  = (q1, t) -- a { current = q1 }
           trans (q, t) (q1, Recv ch)  = case (hasSendTo ch t sys) of
                                           Nothing -> (q, t) -- a
                                           Just nt -> (q1, nt) -- a { current = q1, clock = nt }

           runLocal' :: [(State, (State, Action))] -> (State, Time) -> Tree (State, Time)
           runLocal' trs (q, t) =  
              case lookups q trs of
                []  -> Leaf (q, t)
                [s] -> Leaf (trans (q, t) s)
                ss  -> Node $ map (Leaf . trans (q, t)) ss
      
-- run the example - Press any key to move on, press 'q' or 'x' to terminate
run ex = do putStrLn $ show ex
            x <- getChar
            if (x=='q' || x =='x') then return ()
            else run (step ex)

lookups :: Eq a => a -> [(a, b)] -> [b]
lookups _ [] = []
lookups x ((y, b):f) | x == y = b : (lookups x f)
                     | otherwise = lookups x f
          
         
---------------------------------------------------------------------------------

-- Timed automata (just the transition functions, assuming natural nubmer states,
--   parameterised on the alphabet
data TA alphabet = TA [(State, (State, alphabet))] -- transition function 

-- Convert a network of BCTAs into a single timed auomata
toTimedAut :: System -> TA ([Tree Action])
toTimedAut (Sys xs) = TA $ step xs [] 0 where


    -- What is the smallest sleep time from any of the current automata states?
    minSleepS :: [BCTA] -> Time
    minSleepS = minimum . (map (\(BCTA q trs) -> minSleepT q trs))

    minSleepT :: Tree (State, Time) -> [(State, (State, Action))] -> Time
    minSleepT t trs = minSleepT' t trs 10000000
    minSleepT' (Node ns) trs mt = min mt (minimum (map (\n -> minSleepT' n trs 1000000) ns))
    minSleepT' (Leaf (q, _)) trs mt = case lookup q trs of 
                                         Just (_, Sleep t) -> min t mt
                                         _                 -> mt

    -- Advance a particular automata (in the context of a system), giving an update automata,
    -- and a tree of actions which occured 
    advance :: Time -> [BCTA] -> BCTA -> (BCTA, Tree Action)
    advance minSleep sys a@(BCTA q trs) = 
      let
        advance' :: Tree (State, Time) -> [(State, (State, Action))] -> (Tree (State, Time), [(State, (State, Action))], Tree Action)
        advance' (Node ns) trs = 
              let (qs, trs', as) = foldl (\(qss, trs', ass) n -> let (q, trs'', as) = advance' n trs'
                                                                 in (q : qss, trs'', as : ass)) ([], trs, []) ns
              in (Node qs, trs', Node as)
                               
        advance' (Leaf (q, t)) trs = 
            case lookups q trs of
              [] -> (Leaf (-1, t), trs, Leaf (None "finished"))
              ns -> let (qs, trs', as) = 
                            foldl (\(qss, trs', ass) a -> let (q', trs'', a') = trans (q, t) trs' a
                                                          in ((Leaf q') : qss, trs'', (Leaf a') : ass)) ([], trs, []) ns
                    in  if ((length qs) == 1) then 
                          (head qs, trs', head as)
                        else
                          (Node qs, trs', Node as)

        trans (q, t) trs (q1, None i)   = ((q1, t), trs, None i)
        trans (q, t) trs (q1, Sleep dt) = 
                     if dt == minSleep
                     then ((q1, t + dt), trs, Sleep dt)
                     else ((q1, t + minSleep), splitSleep trs q minSleep, Sleep minSleep)
        trans (q, t) trs (q1, Send ch) = ((q1, t), trs, Send ch)
        trans (q, t) trs (q1, Recv ch) =
                     case (hasSendTo ch t (Sys sys)) of
                         Nothing -> ((q, t), trs, None $ "blocked on recv " ++ ch)
                         Just nt -> ((q1, nt), trs, Recv ch)

        (q', trs', as) = advance' q trs
      in (BCTA (nubT q') trs', nubT as)

    step sys sysHist q = 
          let minSleep = minSleepS sys
              (sys', acs) = unzip $ map (advance minSleep sys) sys

          in   if ((CT sys') `elem` sysHist)
               then -- At a state we have been in before, therefore insert a loop, and finish
                    [(q, (fromJust $ elemIndex (CT sys') sysHist, [Leaf $ None ""]))]
               else -- Otherwise, progress 
                    (q, (q+1, acs)) : (step sys' (sysHist ++ [CT sys']) (q+1))

nubT :: Eq a => Tree a -> Tree a
nubT t = case (nub . flatten $ t) of 
           [x] -> Leaf x
           xs  -> Node (map Leaf xs)

flatten :: Tree a -> [a]
flatten (Leaf x) = [x]
flatten (Node xs) = concatMap flatten xs
                                             
-- Show the transition function
instance Show (TA [Tree Action]) where
    show (TA [])     = ""
    show (TA (x:xs)) = show x ++ "\n" ++ show (TA xs)

-- Special wrapper for performing equality where consecutive sleeps are coalesced
data CT = CT [BCTA] deriving Show
instance Eq CT where
    (CT sys) == (CT sys') = coalesceSleeps sys `equ` coalesceSleeps sys'
                             where -- ignore the clock when checking equality
                                   equ as1 as2 = (map ((fmap fst) . current) as1) 
                                                 == (map ((fmap fst) . current) as2) 
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
coalesceSleeps = map (\(BCTA q ts) -> BCTA q (coalesceSleepsT ts)) 
coalesceSleepsT :: [(State, (State, Action))] -> [(State, (State, Action))]
coalesceSleepsT [] = []
coalesceSleepsT (a@(q1, (q2, Sleep t1)):(b@(q2', (q3, Sleep t2)):ts)) = 
        if (q2 == q2') then coalesceSleepsT ((q1, (q3, Sleep $ t1+t2)) : ts)
                       else a:(coalesceSleepsT (b:ts))
coalesceSleepsT (a:ts) = a:(coalesceSleepsT ts)
