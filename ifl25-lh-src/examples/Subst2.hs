{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--reflection" @-}
module Subst2 where

import Data.Maybe
import Data.Set hiding (member, union, singleton)
import qualified Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators ((?))

data Exp
  = Var Int
  | App Exp Exp
  | Lam Int Exp

{-@ measure freeVars @-}
freeVars :: Exp -> Set Int
freeVars = \case
    Var i -> Set.singleton i
    App e0 e1 -> Set.union (freeVars e0) (freeVars e1)
    Lam i e -> difference (freeVars e) (Set.singleton i)

--------------------------------------------------
-- A type of scope sets with controlled insertion
--------------------------------------------------

data Scope = UnsafeScope (Set Int)
{-@ data Scope = UnsafeScope (Set Int) @-}

{-@ inline member @-}
member :: Int -> Scope -> Bool
member i (UnsafeScope s) = Set.member i s

{-@ inline isSubsetOfScope @-}
isSubsetOfScope :: Set Int -> Scope -> Bool
isSubsetOfScope s (UnsafeScope s') = isSubsetOf s s'

{-@ inline union @-}
union :: Scope -> Scope -> Scope
union (UnsafeScope s1) (UnsafeScope s2) = UnsafeScope (Set.union s1 s2)

{-@ inline singleton @-}
singleton :: Int -> Scope
singleton i = UnsafeScope (Set.singleton i)

{-@
withRefreshed
  :: s:Scope
  -> i:Int
  -> {p:(Scope, Int)
     |  not (member (snd p) s)
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

{-@ type ScopedExp S = {e:Exp | isSubsetOfScope (freeVars e) S} @-}


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
  :: i:Int
  -> xs:Subst e
  -> {m:Maybe e | isJust m == member i (domain xs) }
@-}
lookupSubst :: Int -> Subst e -> Maybe e
lookupSubst i (Subst s) = lookup i s

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
  Var i -> case lookupSubst i s of Nothing -> e0; Just e -> e
  App e0 e1 -> App (substitute scope s e0) (substitute scope s e1)
  Lam i e ->
    let (scope', j) = withRefreshed scope i
     in Lam j $ substitute scope' (extendSubst s i (Var j)) e
