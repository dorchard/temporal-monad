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
interpProg (Seq p s) k = interpProg p (interpStmt s k)

interpStmt :: Stmt -> (Env -> Temporal ()) -> (Env -> Temporal ())
interpStmt (NoBind e)   k env = (interpExpr e env) >>= (\_ -> k env)
interpStmt (Bind var e) k env = (interpExpr e env) >>= (\x -> k (env `ext` (var, x)))
interpStmt (Print e)    k env = (interpExpr e env) >>= (\x -> liftIO $ putStrLn $ show x) >>= (\_ -> k env)


interp p = interpProg p (\_ -> return ())

emptyEnv = \var -> NoValue

{- Examples from the paper -}

fig7aS = Seq (Seq Empty (NoBind $ Sleep 1)) (NoBind $ Sleep 2)
fig7bS = Seq (Seq (Seq Empty (NoBind $ KSleep 1)) (NoBind $ Sleep 1)) (NoBind $ Sleep 2)
fig7cS = Seq (Seq (Seq Empty (NoBind $ KSleep 2)) (NoBind $ Sleep 1)) (NoBind $ Sleep 2)
fig7dS = Seq (Seq (Seq (Seq Empty (NoBind $ KSleep 2)) (NoBind $ Sleep 1)) (NoBind $ KSleep 2)) (NoBind $ Sleep 2)

fig7aS' = Seq (Seq (Seq (Seq Empty (Bind "x" (Const $ IntVal 42))) (NoBind $ Sleep 1)) (NoBind $ Sleep 2)) 
            (Print (Var "x"))

