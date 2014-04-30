import Temporal

tests slp = do putStrLn "test 1, expected = 2s, (2s, 1s, 3s)" 
               r1 <- getMean 5 (test1 slp)
               putStrLn $ show $ r1

               putStrLn "test 2, expected = 3s, (1s, 2s, 3s)"
               r2 <- getMean 5 (test2 slp)
               putStrLn $ show $ r2

               putStrLn "test 3A, expected = 6s"
               r3 <- getMean 5 (test3A slp)
               putStrLn $ show $ r3

               putStrLn "test 3, expected = 6s"
               r4 <- getMean 5 (test3 slp)
               putStrLn $ show $ r4

               putStrLn "test 3', expected = 7s"
               r5 <- getMean 5 (test3' slp)
               putStrLn $ show $ r5

               putStrLn "test 3'', expected = 5s"
               r6 <- getMean 5 (test3'' slp)
               putStrLn $ show $ r6

               putStrLn "test 4A, expected = 5s"
               r7 <- getMean 5 (test4A slp)
               putStrLn $ show $ r7

               putStrLn "test 4B, expected = 5s"
               r8 <- getMean 5 (test4B slp)
               putStrLn $ show $ r8

-- [test1]_t = 2
test1 slp = 
     do a <- time
        kernelSleep 2
        slp 2
        b <- time
        slp 1
        c <- time
        return $ (diffUTCTime b a, -- 2s
                  diffUTCTime c b, -- 1s
                  diffUTCTime c a) -- 3s

-- [test2]_t = 3
test2 slp =
      do a <- time
         slp 1
         b <- time
         slp 2
         c <- time
         return $ (diffUTCTime b a, -- 1s
                   diffUTCTime c b, -- 2s
                   diffUTCTime c a) -- 3s

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
                s <- start
                e <- time
                r <- getVirtualTime
                return $ (diffUTCTime e s, r)

-- [test4B]_t = 5
test4B slp = do kernelSleep 5
                slp 2
                s <- start
                e <- time
                r <- getVirtualTime
                return $ (diffUTCTime e s, r)

getMean :: (Fractional b) => Integer -> Temporal b -> IO (b, NominalDiffTime)
getMean n k = do (r, d) <- getMean' n
                 return (r / (fromInteger n), d / (fromInteger n))
               where getMean' 0 = return (0, 0)
                     getMean' c = do (r, d)  <- runTime $ duration k
                                     (r', d') <- getMean' (c - 1)
                                     return (r + r', d + d')
instance Num () where
    () + () = ()
    fromInteger _ = ()
instance Fractional () where
    () / () = ()

instance (Num a, Num b, Num c) => Num (a, b, c) where
    (a, b, c) + (x, y, z) = (a + x, b + y, c + z)
    fromInteger i = (fromInteger i, fromInteger i, fromInteger i)
instance (Fractional a, Fractional b, Fractional c) => Fractional (a, b, c) where
    (a, b, c) / (x, y, z) = (a / x, b / y, c / z)

instance (Num a, Num b) => Num (a, b) where
    (a, b) + (x, y) = (a + x, b + y)
    fromInteger i = (fromInteger i, fromInteger i)
instance (Fractional a, Fractional b) => Fractional (a, b) where
    (a, b) / (x, y) = (a / x, b / y)


{- Monad laws experimentation -}

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


law1Foo = unitLaw (\t -> do { sleep t; time; }) 1.0
law2Foo = unitLaw2 (T (\(t, t') _ -> return $ (diffUTCTime t' t, 0)))

law3Foo = assocLaw sleep' sleep2 (T (\(t, t') _ -> return $ (diffUTCTime t' t, 0)))
                where sleep' x = do { sleep x; return (x * 0.5); }
                      sleep2 x = do { sleep x; sleep x; time }
