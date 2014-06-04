import Temporal


data Prog = Seq Prog Stmt | Empty                                 deriving Show 
data Stmt = NoBind Expr | Bind String Expr | Print Expr           deriving Show
data Expr = Sleep VTime | KSleep VTime | Const Value | Var String deriving Show

data Value = NoValue | IntVal Int                                 deriving Show

type Env = String -> Value

ext :: Env -> (String, Value) -> Env
ext env (var, val) = \var' -> if var==var' then val else env var'

interpExpr :: Expr -> Env -> Temporal Value
interpExpr (Sleep t)  _ = (sleep t) >> (return NoValue)
interpExpr (KSleep t) _ = (kernelSleep t) >> (return NoValue)
interpExpr (Const v)  _ = return v
interpExpr (Var v)  env = return (env v)

interpProg :: Prog -> (Env -> Temporal ()) -> Temporal ()
interpProg Empty     k = k emptyEnv
interpProg (Seq p s) k = interpProg p ((interpStmt s) >=> k)
--interpProg (Seq p s) k = interpProg p (\env -> (interpStmt s env) >>= (\env' -> k env'))

f >=> g = \x -> (f x) >>= g

interpStmt :: Stmt -> Env -> Temporal Env
interpStmt (NoBind e)   env = (interpExpr e env) >>= (\_ -> return env)
interpStmt (Bind var e) env = (interpExpr e env) >>= (\x -> return (env `ext` (var, x)))
interpStmt (Print e)    env = (interpExpr e env) >>= (\x -> liftIO $ putStrLn $ show x) >>= (\_ -> return env)

interp p = interpProg p (\_ -> return ())

emptyEnv = \var -> NoValue

{- Examples from the paper -}

fig7aS = Seq (Seq Empty (NoBind $ Sleep 1)) (NoBind $ Sleep 2)
fig7bS = Seq (Seq (Seq Empty (NoBind $ KSleep 1)) (NoBind $ Sleep 1)) (NoBind $ Sleep 2)
fig7cS = Seq (Seq (Seq Empty (NoBind $ KSleep 2)) (NoBind $ Sleep 1)) (NoBind $ Sleep 2)
fig7dS = Seq (Seq (Seq (Seq Empty (NoBind $ KSleep 2)) (NoBind $ Sleep 1)) (NoBind $ KSleep 2)) (NoBind $ Sleep 2)

-- Example showing a variable binding
fig7aS' = Seq (Seq (Seq (Seq Empty (Bind "x" (Const $ IntVal 42))) (NoBind $ Sleep 1)) (NoBind $ Sleep 2)) 
            (Print (Var "x"))

{-

    interpProg (Seq p (NoBind $ Sleep t)) (\_ -> return ())

 => interpProg p (interpStmt (NoBind $ Sleep t) (\_ -> return ()))

 => interpProg p (\env -> (interExpr (Sleep t) env) >>= (\_ -> (\_ -> return ()) env))

 => interpProg p (\env -> (interExpr (Sleep t) env) >>= (\_ -> return ()))

 => interpProg p (\env -> ((sleep t) >> (return NoValue)) >>= (\_ -> return ()))

 => interpProg p (\env -> ((sleep t) >> (return NoValue)))


runTime (interpProg p (\env -> ((sleep t) >> (return NoValue))))

 => 

do startT <- getCurrentTime
   (y, _) <- (runT (interpProg p (\env -> ((sleep t) >> (return NoValue))))) (startT, startT) 0
   return y

 => 

do startT <- getCurrentTime
   (y, _) <- (runT (interpProg p (\_ -> 
                 do nowT      <- time
                    vT        <- getVirtualTime
                    let vT'   = vT + t
                    setVirtualTime vT'
                    startT'    <- start
                    let diffT = diffTime nowT startT'
                    if (vT' < diffT) then return () 
                                     else kernelSleep (vT' - diffT)
                    return NoValue))) (startT, startT) 0
   return y

 => (can probably do this reasoning- startT is constant)

do startT <- getCurrentTime
   (y, _) <- (runT (interpProg p (\_ -> 
                 do nowT      <- time
                    vT        <- getVirtualTime
                    let vT'   = vT + t
                    setVirtualTime vT'
                    let diffT = diffTime nowT startT
                    if (vT' < diffT) then return () 
                                     else kernelSleep (vT' - diffT)
                    return NoValue))) (startT, startT) 0
   return y

 => 

if p = Empty then 

 interpProg Empty (\_ -> k')  = k'

if p = Seq p' s

 interpProg (Seq p' s) (\_ -> k') = k'


By induction... since trees are finite

(interpStmt sn >=> (interpStmt sn-1 >=>  .. (interpStmt s1 >=> k))) emptyEnv

If monad is associative then (i.e., really a monad) 

((((interpStmt sn >=> interpStmt sn-1) >=>  .. ) >=> interpStmt s1 >=>)  k) emptyEnv


 => 

do startT <- getCurrentTime
   (y, _) <- (runT (interpProg p (\_ -> return NoValue))) (startT, startT) 0
   nowT      <- time
   vT        <- getVirtualTime
   let vT'   = vT + t
   setVirtualTime vT'
   let diffT = diffTime nowT startT
   if (vT' < diffT) then return () 
                    else kernelSleep (vT' - diffT)
   return y

-}