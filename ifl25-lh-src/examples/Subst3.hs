{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Subst3 where

import Data.Maybe
import Data.Set
import Language.Haskell.Liquid.ProofCombinators ((?), (===), (==.), (==!), (***), QED(QED, Admit))

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

{-@ reflect freeVarsMaybe @-}
freeVarsMaybe :: Maybe Exp -> Set Int
freeVarsMaybe Nothing = empty
freeVarsMaybe (Just e) = freeVars e

{-@
type ScopedExp S = {e:Exp | isSubsetOf (freeVars e) S}
@-}

--------------------------------------------
-- A replaceable type for substitutions
--------------------------------------------

newtype Subst e = Subst [(Int, e)]

-- | A type with an assumed concrete representation
--
-- In contrast, we consider @Subst e@ as abstract/opaque.
type Assoc e = [(Int, e)]

-- | In the logic, we will reason with substitutions as if they were
-- association lists. @asAssoc s@ provides the association list of @s@.
--
-- We leave the function undefined to signal that it is only intended
-- to be used in the logic.
--
{-@ opaque-reflect asAssoc @-}
asAssoc :: Subst e -> Assoc e
asAssoc = undefined


{-@ reflect domain @-}
domain :: Assoc e -> Set Int
domain [] = empty
domain ((i, _) : s) = union (singleton i) (domain s)

-- | @freeVarsSubst used s@ computes the set of free variables in the range of
-- the substitution @s@ that will be used according to the set @used@.
--
-- Thus, @freeVars e0[x:=e1]@ include @freeVarsSubst (freeVars e0) [(x, e1)]@.
--
{-@ reflect freeVarsSubst @-}
freeVarsSubst :: Set Int -> Assoc Exp -> Set Int
freeVarsSubst used [] = empty
freeVarsSubst used ((i, e) : s) =
    if member i used then
      union
        (freeVars e)
        -- only add the free vars of the first occurrence of i
        (freeVarsSubst (difference used (singleton i)) s)
    else
      freeVarsSubst used s

{-@ inline extendAssoc @-}
extendAssoc :: Assoc e -> Int -> e -> Assoc e
extendAssoc s i e = (i, e) : s

{-@
assume extendSubst
  :: s:Subst a
  -> i:Int
  -> e:a
  -> { v:_
     |  union (domain (asAssoc s)) (singleton i) = domain (asAssoc v)
     && asAssoc v == extendAssoc (asAssoc s) i e
     }
@-}
extendSubst :: Subst a -> Int -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

{-@
assume lookupSubst
  :: i:Int
  -> s:Subst e
  -> { m:Maybe e
     | isJust m == member i (domain (asAssoc s))
     && m == lookupAssoc i (asAssoc s)
     }
@-}
lookupSubst :: Int -> Subst e -> Maybe e
lookupSubst i (Subst xs) = lookup i xs

{-@
reflect lookupAssoc
lookupAssoc
  :: i:Int
  -> s:Assoc e
  -> {m:Maybe e | isJust m == member i (domain s) }
@-}
lookupAssoc :: Int -> Assoc b -> Maybe b
lookupAssoc _ [] = Nothing
lookupAssoc x ((y, b) : xs)
    | x == y = Just b
    | otherwise = lookupAssoc x xs


-------------------------------------------
-- applying substitutions to expressions
-------------------------------------------

{-@
substitute
  :: scope:Set Int
  -> s:Subst (ScopedExp scope)
  -> ei:ScopedExp (domain (asAssoc s))
  -> {v:Exp | freeVars v == freeVarsSubst (freeVars ei) (asAssoc s)}
@-}
substitute :: Set Int -> Subst Exp -> Exp -> Exp
substitute scope s = \case
    Var i -> case lookupSubst i s of
      Nothing -> Var i
      Just e -> e ? lemmaFreeVarsSubstSing i (asAssoc s)
    App e0 e1 ->
      App
        (substitute scope s e0)
        (substitute scope s e1)
      ? lemmaFreeVarsSubstUnion (freeVars e0) (freeVars e1) (asAssoc s)
    Lam i e
      | member i scope ->
          let j = freshVar scope
           in Lam j $
                substitute
                  (insert j scope)
                  (extendSubst s i (Var j))
                  e
                ? lemmaFreeVarsSubstExtend scope (freeVars e) i (Var j) (asAssoc s)
      | otherwise ->
          Lam i $
            substitute
              (insert i scope)
              -- This has the effect of canceling the substitution of i
              -- whatever it was in f
              (extendSubst s i (Var i))
              e
            ? lemmaFreeVarsSubstExtend scope (freeVars e) i (Var i) (asAssoc s)

----------
-- Lemmas
----------

{-@
lemmaFreeVarsSubstEmpty
  :: used:_
  -> {s:_ | Data.Set.null (intersection used (domain s))}
  -> { freeVarsSubst used s == empty }
@-}
lemmaFreeVarsSubstEmpty :: Set Int -> Assoc Exp -> ()
lemmaFreeVarsSubstEmpty used [] = ()
lemmaFreeVarsSubstEmpty used (_ : s) = lemmaFreeVarsSubstEmpty used s

{-@
lemmaFreeVarsSubstSing
  :: i:_
  -> s:_
  -> { freeVarsSubst (singleton i) s == freeVarsMaybe (lookupAssoc i s) }
@-}
lemmaFreeVarsSubstSing :: Int -> Assoc Exp -> ()
lemmaFreeVarsSubstSing _ [] = ()
lemmaFreeVarsSubstSing i ((j, _) : s)
    | i == j =
      lemmaFreeVarsSubstEmpty empty s
    | otherwise =
      lemmaFreeVarsSubstSing i s ? lemmaFreeVarsSubstEmpty empty s

{-@
lemmaFreeVarsSubstUnion
  :: s1:_
  -> s2:_
  -> s:_
  -> { freeVarsSubst (union s1 s2) s
       == union (freeVarsSubst s1 s) (freeVarsSubst s2 s) }
@-}
lemmaFreeVarsSubstUnion :: Set Int -> Set Int -> Assoc Exp -> ()
lemmaFreeVarsSubstUnion _ _ [] = ()
lemmaFreeVarsSubstUnion s1 s2 ((i, _) : s) =
    lemmaFreeVarsSubstUnion
      (difference s1 (singleton i))
      (difference s2 (singleton i))
      s

{-@
lemmaFreeVarsSubstScoped
  :: scope:_
  -> used:_
  -> s:Assoc (ScopedExp scope)
  -> { isSubsetOf (freeVarsSubst used s) scope }
@-}
lemmaFreeVarsSubstScoped :: Set Int -> Set Int -> Assoc Exp -> ()
lemmaFreeVarsSubstScoped _ _ [] = ()
lemmaFreeVarsSubstScoped scope used ((i, _) : s) =
    lemmaFreeVarsSubstScoped scope (difference used (singleton i)) s

{-@
lemmaFreeVarsSubstExtend
  :: scope:_
  -> used:_
  -> i:_
  -> {e:_ | Data.Set.null (intersection (freeVars e) scope)}
  -> s:Assoc (ScopedExp scope)
  -> { freeVarsSubst (difference used (singleton i)) s ==
       difference (freeVarsSubst used (extendAssoc s i e)) (freeVars e)
     }
@-}
lemmaFreeVarsSubstExtend :: Set Int -> Set Int -> Int -> Exp -> Assoc Exp -> ()
lemmaFreeVarsSubstExtend scope used i _ s =
    lemmaFreeVarsSubstScoped scope (difference used (singleton i)) s

