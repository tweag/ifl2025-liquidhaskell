{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Subst2 where

import Data.Set hiding (member, union, singleton)
import qualified Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators ((?))

data Exp
  = Var Int
  | App Exp Exp
  | Lam Int Exp
  deriving (Show, Eq)

{-@ measure freeVars @-}
freeVars :: Exp -> Set Int
freeVars = \case
    Var i -> Set.singleton i
    App e0 e1 -> Set.union (freeVars e0) (freeVars e1)
    Lam i e -> difference (freeVars e) (Set.singleton i)

--------------------------------------------------
-- A type of scope sets with controlled insertion
--------------------------------------------------

-- BUG: should be a newtype, but Liquid Haskell is confused by newtypes at the
-- moment.

-- unsafeUnScope is not intended to be used directly by the user
data Scope = UnsafeScope { unsafeUnScope :: Set Int }
{-@ data Scope = UnsafeScope { unsafeUnScope :: Set Int } @-}

{-@ predicate Member E S = Set.member E (unsafeUnScope S) @-}
{-@ predicate IsSubsetOfScope S SS = Set.isSubsetOf S (unsafeUnScope SS) @-}

{-@ inline union @-}
union :: Scope -> Scope -> Scope
union s1 s2 = UnsafeScope (Set.union (unsafeUnScope s1) (unsafeUnScope s2))

{-@ inline singleton @-}
singleton :: Int -> Scope
singleton i = UnsafeScope (Set.singleton i)

{-@
withRefreshed
  :: s:Scope
  -> i:Int
  -> {p:(Scope, Int)
     |  not (Member (snd p) s)
     && fst p == union s (singleton (snd p))
     }
@-}
-- | This is the only way to insert a variable into a scope.
withRefreshed :: Scope -> Int -> (Scope, Int)
withRefreshed (UnsafeScope s) i
    | Set.member i s = let j = freshVar s in (UnsafeScope (insert j s), j)
    | otherwise = (UnsafeScope (insert i s), i)

{-@ assume freshVar :: s:Set Int -> {v:Int | not (Set.member v s)} @-}
freshVar :: Set Int -> Int
freshVar s = case lookupMax s of
    Nothing -> 0
    Just i -> i + 1

{-@ type ScopedExp S = {e:Exp | IsSubsetOfScope (freeVars e) S} @-}


--------------------------------------------
-- A replaceable type for substitutions
--------------------------------------------

newtype Subst e = Subst [(Int, e)]

{-@ measure domain :: Subst e -> Scope @-}

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
     s:Subst Exp<p> -> {i:Int | Member i (domain s)} -> Exp<p>
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
  :: scope:Scope
  -> s:Subst (ScopedExp scope)
  -> ScopedExp (domain s)
  -> ScopedExp scope
@-}
substitute :: Scope -> Subst Exp -> Exp -> Exp
substitute scope s e0 = case e0 of
  Var i -> lookupSubst s i
  App e0 e1 -> App (substitute scope s e0) (substitute scope s e1)
  Lam i e ->
    let (scope', j) = withRefreshed scope i
     in Lam j $ substitute scope' (extendSubst s i (Var j)) e


-------------------------------------------
-- tests
-------------------------------------------

{-@ idSubst :: scope:Scope -> {v:Subst a | domain v = scope} @-}
idSubst :: Scope -> Subst a
idSubst _ = Subst []

{-@ reflect scope01 @-}
scope01 :: Scope
scope01 = UnsafeScope (Set.fromList [0, 1])

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
