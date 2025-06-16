{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--reflection" @-}
module Subst1 where

import Data.Maybe
import Data.Set
import Language.Haskell.Liquid.ProofCombinators ((?))

data Exp
  = Var Int
  | App Exp Exp
  | Lam Int Exp

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
  :: scope:Set Int
  -> s:Subst (ScopedExp scope)
  -> ScopedExp (domain s)
  -> ScopedExp scope
@-}
substitute :: Set Int -> Subst Exp -> Exp -> Exp
substitute scope s e0 = case e0 of
  Var i -> case lookupSubst i s of Nothing -> e0; Just e -> e
  App e0 e1 -> App (substitute scope s e0) (substitute scope s e1)
  Lam i e
    | member i scope,
      let j = freshVar scope ->
        Lam j $ substitute (insert j scope) (extendSubst s i (Var j)) e
    | otherwise ->
        Lam i $ substitute (insert i scope) (extendSubst s i (Var i)) e

