{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Subst1 where

import Control.Monad (when)
import Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators ((?))

data Exp
  = Var Int
  | App Exp Exp
  | Lam Int Exp
  deriving (Show, Eq)

{-@ measure freeVars @-}
freeVars :: Exp -> Set Int
freeVars = \case
    Var i -> singleton i
    App e0 e1 -> union (freeVars e0) (freeVars e1)
    Lam i e -> difference (freeVars e) (singleton i)

{-@ assume freshVar :: s:Set Int -> {v:Int | not (member v s)} @-}
freshVar :: Set Int -> Int
freshVar s = case lookupMax s of
    Nothing -> 0
    Just i -> i + 1

{-@ type ScopedExp S = {e:Exp | isSubsetOf (freeVars e) S} @-}

--------------------------------------------
-- A replaceable type for substitutions
--------------------------------------------

newtype Subst e = Subst [(Int, e)]

{-@ measure domain :: Subst e -> Set Int @-}

{-@
assume extendSubst
  :: s:Subst a
  -> i:Int
  -> a
  -> {v:_ | union (domain s) (singleton i) = domain v }
@-}
extendSubst :: Subst a -> Int -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

{-@
assume lookupSubst
  :: forall <p :: Exp -> Bool>.
     s:Subst Exp<p> -> {i:Int | member i (domain s)} -> Exp<p>
@-}
lookupSubst :: Subst Exp -> Int -> Exp
lookupSubst (Subst s) i = case lookup i s of
    Nothing -> Var i
    Just e -> e

-------------------------------------------
-- applying substitutions to expressions
-------------------------------------------

{-@
substitute
  :: scope:Set Int
  -> s:Subst (ScopedExp scope)
  -> ScopedExp (domain s)
  -> ScopedExp scope
@-}
substitute :: Set Int -> Subst Exp -> Exp -> Exp
substitute scope s = \case
  Var i -> lookupSubst s i
  App e0 e1 -> App (substitute scope s e0) (substitute scope s e1)
  Lam i e
    | member i scope,
      let j = freshVar scope ->
        Lam j $ substitute (insert j scope) (extendSubst s i (Var j)) e
    | otherwise ->
        Lam i $ substitute (insert i scope) (extendSubst s i (Var i)) e


-------------------------------------------
-- tests
-------------------------------------------

{-@ assume idSubst :: scope:Set Int -> {v:Subst (ScopedExp scope) | domain v = scope} @-}
idSubst :: Set Int -> Subst Exp
idSubst scope = Subst []

{-@ reflect scope01 @-}
scope01 :: Set Int
scope01 = Set.fromList [0, 1]

{-@ testSubst :: _ -> ss:Subst (ScopedExp scope01) -> e:ScopedExp (domain ss) -> _ @-}
testSubst :: String -> Subst Exp -> Exp -> Exp -> IO ()
testSubst label ss e expected =
    if se == expected then
      putStrLn $ "Test " ++ label ++ " passed"
    else do
      putStrLn $ "Test: " ++ label
      putStrLn "substitute result does not match expected"
      putStrLn $ "Expected: " ++ show expected
      putStrLn $ "Got:      " ++ show se
  where
    se = substitute scope01 ss e

test1 :: IO ()
test1 =
    testSubst "test1" ss
      (Lam 0 (App (Var 0) (Var 1)))
      (Lam 2 (App (Var 2) (Var 1)))
  where
    ss = extendSubst (idSubst (singleton 1)) 0 (Var 0)

test2 :: IO ()
test2 =
    testSubst "test2" ss
      (Lam 0 (App (Var 0) (Var 0)))
      (Lam 2 (App (Var 2) (Var 2)))
  where
    ss = extendSubst (idSubst (singleton 1)) 0 (Var 1)

test3 :: IO ()
test3 =
    testSubst "test3" ss
      (Lam 0 (App (Var 0) (Var 1)))
      (Lam 2 (App (Var 2) (Var 0)))
  where
    ss = extendSubst (idSubst (singleton 1)) 1 (Var 0)

test4 :: IO ()
test4 =
    testSubst "test4" ss
      (Lam 2 (App (Var 2) (Var 1)))
      (Lam 2 (App (Var 2) (Var 0)))
  where
    ss = extendSubst (idSubst (singleton 1)) 1 (Var 0)

test :: IO ()
test = sequence_ [test1, test2, test3, test4]

