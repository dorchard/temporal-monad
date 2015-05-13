-- Set-up some type aliases
type State = Int
type Time = Float
type Machine = Int
type Channel = String

data Action = Send Channel | Recv Channel | Sleep Time | None 

-- Broadcasting communicating timed-automata 
data BCTA = BCTA { current     :: (State, Time),       -- current config 
                   transitions :: [(State, (State, Action))] -- transition function 
                 }

-- System is a number of automata
data System = Sys [BCTA] 

-- Pretty printer for 
instance Show System where
    show (Sys []) = ""
    show (Sys ((BCTA (q, t) ts):as)) = show q ++ " @ " ++ 
                                       "t = " ++ show t ++ "\n" ++ show (Sys as)

------------------------------------------

{- Example 1 
   
   Two process, each with three states in a loop. 
     1) sleeps 2, sends on 'c' then recurses
     2) sleeps 1, receives on 'c' then recurses
   Since they are 'out of phases' the second is constantly blocked on the first receive.

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

ex1 = Sys [BCTA (0,0) [(0, (1, Sleep 2)), (1, (2, Send "c")), (2, (0, None))], 
           BCTA (0,0) [(0, (1, Sleep 1)), (1, (2, Recv "c")), (2, (0, None))]]

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

ex2 = Sys [BCTA (0,0) [(0, (1, Sleep 1)), (1, (2, Send "c")), (2, (0, None))], 
           BCTA (0,0) [(0, (1, Sleep 2)), (1, (2, Recv "c")), (2, (0, None))]]

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

ex3 = Sys [BCTA (0,0) [(0, (1, Recv "c")), (1, (2, Send "d")), (2, (3, None))], 
           BCTA (0,0) [(0, (1, Recv "d")), (1, (2, Send "c")), (2, (3, None))]]

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

ex4 = Sys [BCTA (0,0) [(0, (1, Sleep 0.5)), (1, (2, Send "c")), (2, (0, None))], 
           BCTA (0,0) [(0, (1, Recv "c"))]]

--------------------------------

-- Find a process which has a send on channel at this time
hasSendTo :: Channel -> Time -> System -> Maybe Time
hasSendTo chan atT (Sys []) = Nothing
hasSendTo chan atT (Sys ((BCTA (c,t) ts):as)) = 
                 case lookup c ts of
                   Just (q, Send chan') -> if chan == chan' && t >= atT 
                                           then Just t
                                           else hasSendTo chan atT (Sys as)
                   _                    -> hasSendTo chan atT (Sys as)

-- Causes (at most) one transition step for every automata in a system
step sys@(Sys xs) = 
     Sys $ map (\(me, a) -> runLocal me a) (zip [0..] xs)
          where
           runLocal me a@(BCTA (q,t) ts) = 
               case lookup q ts of 
                   Nothing -> a
                   Just (q1, None)     -> a { current = (q1, t) }
                   Just (q1, Sleep dt) -> a { current = (q1, t + dt) }
                   Just (q1, Send ch)  -> a { current = (q1, t) }
                   Just (q1, Recv ch)  -> case (hasSendTo ch t sys) of
                                                   Nothing   -> a
                                                   Just nt -> a { current = (q1, nt) }
      
-- run the example - Press any key to move on, press 'q' or 'x' to terminate
run ex = do putStrLn $ show ex
            x <- getChar
            if (x=='q' || x =='x') then return ()
            else run (step ex)
                   