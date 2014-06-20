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
interpProg (Seq p s) k = interpProg p (\env -> (interpStmt s env) >>= k)

{-
   Alternatively, can be written in terms of Kleisli composition

   interpProg (Seq p s) k = interpProg p ((interpStmt s) >=> k) 
                                where f >=> g = \x -> (f x) >>= g
-}

interpStmt :: Stmt -> Env -> Temporal Env
interpStmt (NoBind e)   env = (interpExpr e env) >>= (\_ -> return env)
interpStmt (Bind var e) env = (interpExpr e env) >>= (\x -> return (env `ext` (var, x)))
interpStmt (Print e)    env = (interpExpr e env) >>= (\x -> liftIO $ putStrLn $ show x) >>= (\_ -> return env)

{- Top level -}

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
interpProg (Seq (Seq (Seq Empty s1) s2) s3) k = 

interpProg (Seq (Seq Empty s1) s2) ((interpStmt s3) >=> k)

interpProg (Seq Empty s1) ((interpStmt s2) >=> ((interpStmt s3) >=> k))

interpProg Empty ((interpStmt s1) >=> ((interpStmt s2) >=> ((interpStmt s3) >=> k)))

((interpStmt s1) >=> ((interpStmt s2) >=> ((interpStmt s3) >=> k))) emptyEnv

((\env -> interpStmt s1 env) >>= ((\env -> interpStmt s2 env) >>= k)

do env <- interpStmt s1 env
   env <- interpStmt s2 env 
   k

(p;(q;r))
(p;q);r
 ; 
/ \
p  ;
  / \
 q   r
-}


{-  interpProg (Seq p (NoBind $ Sleep t)) (\_ -> return ())
 => interpProg p (\env -> (interpStmt (NoBind $ Sleep t) env) >>= (\_ -> return ())
m=> interpProg p (\env -> (interpStmt (NoBind $ Sleep t) env))
 => interpProg p (\env -> (interpExpr (Sleep t) env) >>= (_ -> return env))
m=> interpProg p (\env -> (interpExpr (Sleep t) env))
m=> interpProg p (\env -> ((sleep t) >> (return NoValue)))
---
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

 => (can probably do this reasoning- startT is constant)[yep]

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
By induction... since trees are finite

(interpStmt sn >=> (interpStmt sn-1 >=>  .. (interpStmt s1 >=> k))) emptyEnv
therefore

do startT <- getCurrentTime
   (y, _) <- (runT (do env_1 <- interpStmt s1 env_1
                       env_2 <- interpStmt s2 env_2
                       ...
                       env_n <- interpStmt sn env_n
                       nowT      <- time
                       vT        <- getVirtualTime
                       let vT'   = vT + t
                       setVirtualTime vT'
                       let diffT = diffTime nowT startT
                       if (vT' < diffT) then return () 
                                        else kernelSleep (vT' - diffT)
                       return NoValue))) (startT, startT) 0
   return y

=>

do startT <- getCurrentTime
   (runT (do env_1 <- interpStmt s1 env_1
             env_2 <- interpStmt s2 env_2
              ...
             env_n <- interpStmt sn env_n
             nowT      <- time
             vT        <- getVirtualTime
             let vT'   = vT + t
             setVirtualTime vT'
             let diffT = diffTime nowT startT
             if (vT' < diffT) then return () 
                              else kernelSleep (vT' - diffT)
             return NoValue))) (startT, startT) 0

do startT <- getCurrentTime
   (_, vT) <- (runT (do env_1 <- interpStmt s1 env_1
                        env_2 <- interpStmt s2 env_2
                        ... 
                        env_n <- interpStmt sn env_n) (startT, startT) 0
    nowT  <- getCurrentTime
    vT    <- getVirtualTime
    let vT'   = vT + t
    let diffT = diffTime nowT startT
    if (vT' < diffT) then return () 
                     else kernelSleep' (vT' - diffT)
-}