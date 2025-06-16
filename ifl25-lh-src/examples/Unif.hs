{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Unif where

import Control.Monad
import Control.Monad.State
import Data.Foldable qualified as Foldable
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace qualified
import qualified Data.Maybe as GHC.Internal.Maybe
import Language.Haskell.Liquid.ProofCombinators

-- We start with a preamble of definitions to introduce the interpretation of
-- the IntMap type as an array. Any @IntMap a b@ in this file is interpreted as
-- an array mapping integers to values of type @Set Int@, so we are careful to
-- not use @IntMap@ instantiated with other types.

{-@

// Syntax to express that any IntMap a b shoud be interpreted as an
// IntMapSetInt_t, which is Array Int (Option (Set Int))
embed IntMap * as IntMapSetInt_t

// Operations on IntMap's are declared to correspond in meaning to operations
// that have been defined in a patch to the liquid-fixpoint package prepared
// for this test.
define IntMap.empty     = (IntMapSetInt_default None)
define IntMap.insert x y m = (IntMapSetInt_store m x (Some y))
define IntMap.lookup x m = if (isSome (IntMapSetInt_select m x)) then (GHC.Internal.Maybe.Just (someVal (IntMapSetInt_select m x))) else GHC.Internal.Maybe.Nothing
define IntMap.delete x m = (Map_store m x None)

define IntMap.union x y = IntMapSetInt_union x y
define IntMap.difference x y = IntMapSetInt_difference x y
define intMapIsSubsetOf x y = IntMapSetInt_isSubsetOf x y
@-}

-- Only provided here for use in specifications
intMapIsSubsetOf :: IntMap (Set Int) -> IntMap (Set Int) -> Bool
intMapIsSubsetOf _ _ = undefined

-- BUG: It shouldn't be necessary to define intMapUnion. Without it, we get
-- that IntMap.union is not correctly expanded to what the preamble defines.
{-@ assume intMapUnion
     :: s0:IntMap (Set Int) -> s1:IntMap (Set Int) -> {v:_ | IntMap.union s0 s1 = v }
@-}
intMapUnion :: IntMap (Set Int) -> IntMap (Set Int) -> IntMap (Set Int)
intMapUnion = IntMap.union

{-@ infixr ++ @-}

-- | We have plain variables
type Var = Int
-- | And we have applications of skolem functions for existential variables that
-- might have a pending substitution.
--
-- The applications are only allowed to be instantiated by unification
-- with terms whose free variables are in the domain of the substitution.
--
-- All occurrences of a skolem function must have pending substitutions
-- with exactly the same domain since the domain of the substitution gives
-- the arity of the skolem function.
type SkolemApp = (Var, Subst Term)

--------------------------------------
-- Substitutions and their operations
--------------------------------------

data Subst t = Subst [(Var,t)]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

lookupSubst :: Var -> Subst e -> Maybe e
lookupSubst i (Subst s) = lookup i s

emptySubst :: Subst e
emptySubst = Subst []

extendSubst :: Subst a -> Var -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

fromListSubst :: [(Var, t)] -> Subst t
fromListSubst = Subst

{-@
assume lemmaScopeSubstSubset
  :: m0:_
  -> s:Subst {t:Term | intMapIsSubsetOf (scopesTerm t) m0}
  -> { intMapIsSubsetOf (scopesSubst s) m0 } @-}
lemmaScopeSubstSubset :: IntMap (Set Int) -> Subst Term -> ()
lemmaScopeSubstSubset _ _ = ()

{-@
assume lemmaComposeSubstDomain
  :: s0:Subst Term
  -> s1:Subst {t:_ | isVar t}
  -> {   domain s0 == domain (composeSubst s0 s1)
      && scopesSubst s0 == scopesSubst (composeSubst s0 s1)
     }
@-}
lemmaComposeSubstDomain :: Subst Term -> Subst Term -> ()
lemmaComposeSubstDomain _ _ = ()

-- For each skolem, indicate what are the variables that
-- are allowed in its solutions.
{-@ reflect scopes @-}
scopes :: Formula -> IntMap (Set Int)
scopes (Forall _ f) = scopes f
scopes (Exists _ f) = scopes f
scopes (Conj f1 f2) = IntMap.union (scopes f1) (scopes f2)
scopes (Then (t0, t1) f2) =
    IntMap.union (scopesTerm t0) (IntMap.union (scopesTerm t1) (scopes f2))
scopes (Eq t0 t1) = IntMap.union (scopesTerm t0) (scopesTerm t1)

{-@ reflect scopesTerm @-}
scopesTerm :: Term -> IntMap (Set Int)
scopesTerm (V i) = IntMap.empty
scopesTerm (SA (i, s)) = IntMap.insert i (domain s) (scopesSubst s)
scopesTerm U = IntMap.empty
scopesTerm (L t) = scopesTerm t
scopesTerm (P t0 t1) = IntMap.union (scopesTerm t0) (scopesTerm t1)

{-@ opaque-reflect domain @-}
{-@ ignore domain @-}
domain :: Subst e -> Set Int
domain (Subst xs) = Set.fromList $ map fst xs


-----------------------
-- The logic language
-----------------------

-- | A language of terms with variables, functions, and constants.
data Term
  = V Var
  | SA SkolemApp
  -- Data constructors of the language (i.e. they are injective)
  | U
  | L Term
  | P Term Term
  deriving (Eq, Ord, Show)

-- | A language of first order formulas with equality, conjunction, implication
-- and quantifiers.
data Formula
  = Eq Term Term
  | Conj Formula Formula
    -- | The implication form is constrained to allow only one
    -- equality in the antecedent.
  | Then (Term, Term) Formula
  | Exists Var Formula
  | Forall Var Formula
  deriving Show

{-@ measure freeVars @-}
freeVars :: Term -> Set Int
freeVars = \case
    V i -> Set.singleton i
    SA (_, s) -> freeVarsSubst s
    U -> Set.empty
    L t -> freeVars t
    P t0 t1 -> Set.union (freeVars t0) (freeVars t1)

{-@ opaque-reflect skolemSet @-}
skolemSet :: Term -> Set Var
skolemSet = \case
    V _ -> Set.empty
    SA (i, s) -> Set.insert i (skolemAppsSubst s)
    U -> Set.empty
    L t -> skolemSet t
    P t0 t1 -> Set.union (skolemSet t0) (skolemSet t1)

{-@ opaque-reflect freeVarsSubst @-}
{-@ ignore freeVarsSubst @-}
freeVarsSubst :: Subst Term -> Set Int
freeVarsSubst (Subst s) = Set.unions $ map (freeVars . snd) s

{-@ ignore skolemAppsSubst @-}
skolemAppsSubst :: Subst Term -> Set Int
skolemAppsSubst (Subst s) = Set.unions $ map (skolemSet . snd) s

{-@ assume freshVar :: s:Set Int -> {v:Int | not (member v s)} @-}
freshVar :: Set Int -> Int
freshVar s = case Set.lookupMax s of
    Nothing -> 0
    Just i -> i + 1

{-@
type ScopedTerm S = {t:Term | isSubsetOf (freeVars t) S}
@-}

-- | The size of a formula is the number of its subformulas.
{-@ measure formulaSize @-}
{-@ formulaSize :: Formula -> Nat @-}
formulaSize :: Formula -> Int
formulaSize (Forall _ f) = 1 + formulaSize f
formulaSize (Exists _ f) = 1 + formulaSize f
formulaSize (Conj f1 f2) = 1 + formulaSize f1 + formulaSize f2
formulaSize (Then _ f2) = 1 + formulaSize f2
formulaSize (Eq t0 t1) = 1


------------------
-- Normalization
------------------

-- The goal of this normalization is to put a formula in prenex normal form,
-- eliminating existential quantification via skolemization and removing
-- implications via substitution and injectivity of term constructors.

-- | Rename universal and existential variables when they are bound more than
-- once.
--
{-@ ignore rename @-}
rename
  :: Set Int -- the set of variables that can appear free in the input formula
  -> Formula
  -> Formula
rename scope0 ff0 = evalState (go ff0) Set.empty
  where
    go f0 = get >>= \bs -> case f0 of
      Forall v f
        | Set.member v bs -> do
          -- if v is already in the bound set, we rename it
          let u = freshVar bs
              bs' = Set.insert u bs
              f' = substituteFormula bs' (fromListSubst [(v, V u)]) f
          put bs'
          Forall u <$> go f'
        | otherwise -> do
           put (Set.insert v bs)
           Forall v <$> go f

      Exists v f
        | Set.member v bs -> do
          -- if v is already in the bound set, we rename it
          let u = freshVar bs
              bs' = Set.insert u bs
              f' = substituteFormula bs' (fromListSubst [(v, V u)]) f
          put bs'
          Exists u <$> go f'
        | otherwise -> do
           modify (Set.insert v)
           Exists v <$> go f

      Conj f1 f2 -> Conj <$> go f1 <*> go f2
      Then eq1 f2 -> Then eq1 <$> go f2
      Eq t0 t1 -> pure $ Eq t0 t1

-- | Replaces existential variables with skolem functions
--
-- Every time that `SA (i,s)` occurs, the domain of `s` is exactly the set of
-- bound variables in scope.
{-@ ignore skolemize @-}
skolemize :: Formula -> Formula
skolemize = go Map.empty []
  where
    -- eenv tells for every existential variable the skolem function to replace
    -- it with
    --
    -- uvs are the universally quantified variables in scope
    go :: Map Var Term -> [Var] -> Formula -> Formula
    go eenv uvs f0 = case f0 of
      Forall v f ->
        Forall v $ go eenv (v : uvs) f

      Exists v f ->
        let eenv' = Map.insert v (mkSkolemApp v uvs) eenv
         in go eenv' uvs f

      Conj f1 f2 -> Conj (go eenv uvs f1) (go eenv uvs f2)
      Then (t0, t1) f2 ->
        let s = fromListSubst (Map.toList eenv)
            -- substitute variables with the skolem functions
         in Then (substitute s t0, substitute s t1) (go eenv uvs f2)
      Eq t0 t1 -> do
        let s = fromListSubst (Map.toList eenv)
            -- substitute variables with the skolem functions
         in Eq (substitute s t0) (substitute s t1)

-- | @mkSkolemApp v uvs@ makes a term with a skolem application for the
-- existential variable @v@ and the universally quantified variables in
-- scope @uvs@.
mkSkolemApp :: Var -> [Var] -> Term
mkSkolemApp v uvs = SA (v, idSubst uvs)
  where
    idSubst :: [Var] -> Subst Term
    idSubst vs = fromListSubst [(v, V v) | v <- vs]

{-@ reflect substitute @-}
substitute :: Subst Term -> Term -> Term
substitute s t = case t of
    V v -> case lookupSubst v s of
      Nothing -> V v
      Just t1 -> t1
    SA (v, s1) -> SA (v, composeSubst s1 s)
    U -> U
    L t1 -> L (substitute s t1)
    P t1 t2 -> P (substitute s t1) (substitute s t2)

{-@ lazy composeSubst @-}
{-@ opaque-reflect composeSubst @-}
composeSubst :: Subst Term -> Subst Term -> Subst Term
composeSubst (Subst xs) s = Subst (map (fmap (substitute s)) xs)

{-@
substituteFormula
  :: Set Int
  -> Subst Term
  -> f:Formula
  -> {v:Formula | formulaSize f == formulaSize v}
@-}
substituteFormula :: Set Int -> Subst Term -> Formula -> Formula
substituteFormula scope s = \case
    Forall v f
      | Set.member v scope ->
        let u = freshVar scope
            scope' = Set.insert u scope
            s' = extendSubst s v (V u)
            f' = substituteFormula scope' s' f
         in
            Forall u f'
      | otherwise ->
        let scope' = Set.insert v scope
            -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteFormula scope' s' f
         in
            Forall v f'
    Exists v f
      | Set.member v scope ->
        let u = freshVar scope
            scope' = Set.insert u scope
            s' = extendSubst s v (V u)
            f' = substituteFormula scope' s' f
         in
            Exists u f'
      | otherwise ->
        let scope' = Set.insert v scope
            -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteFormula scope' s' f
         in
            Exists v f'
    Conj f1 f2 -> Conj (substituteFormula scope s f1) (substituteFormula scope s f2)
    Then (t0, t1) f2 ->
      Then (substitute s t0, substitute s t1) (substituteFormula scope s f2)
    Eq t0 t1 -> Eq (substitute s t0) (substitute s t1)


{-@
lazy substituteSkolemsTerm
assume substituteSkolemsTerm
  :: Subst Term
  -> t:Term
  -> {v:Term | intMapIsSubsetOf (scopesTerm v) (scopesTerm t) }
@-}
substituteSkolemsTerm :: Subst Term -> Term -> Term
substituteSkolemsTerm s t = case t of
    V v -> V v
    SA (v, s1) -> case lookupSubst v s of
      Just t1 -> substituteSkolemsTerm s1 t1
      Nothing -> SA (v, composeSubst s1 s)
    U -> U
    L t1 -> L (substituteSkolemsTerm s t1)
    P t1 t2 -> P (substituteSkolemsTerm s t1) (substituteSkolemsTerm s t2)
  where
    {-@ ignore composeSubst @-}
    composeSubst :: Subst Term -> Subst Term -> Subst Term
    composeSubst (Subst xs) s = Subst (map (fmap (substituteSkolemsTerm s)) xs)


-- BUG: Appartently Liquid Haskell cannot prove termination of recursive
-- functions on mutually recursive types, so we disable the termination checker
-- for this function.
{-@ lazy scopesSubst @-}
{-@ opaque-reflect scopesSubst @-}
scopesSubst :: Subst Term -> IntMap (Set Int)
scopesSubst (Subst xs) = foldr IntMap.union IntMap.empty $ map (scopesTerm . snd) xs

-- LH can show that substituteSkolems preserves formulaSize, but we need reacher
-- specifications for auxiliary functions if we want to verify the relationship
-- between scopes.
--
-- BUG: when trying to check this function, the facts comming from
-- consistentSkolemScopes seem to be missing after pattern matching
-- on the input.
{-@
assume substituteSkolems
  :: s:Subst Term
  -> {f:Formula | consistentSkolemScopes f}
  -> {v:Formula |
          formulaSize f == formulaSize v
       && intMapIsSubsetOf (scopes v) (IntMap.union (scopes f) (scopesSubst s))
       && consistentSkolemScopes v
     }
ignore substituteSkolems
@-}
substituteSkolems :: Subst Term -> Formula -> Formula
substituteSkolems s = \case
    Forall v f ->
        let -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteSkolems s' f
         in
            Forall v f'
    Exists v f ->
        let -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteSkolems s' f
         in
            Exists v f'
    Conj f1 f2 -> Conj (substituteSkolems s f1) (substituteSkolems s f2)
    Then (t0, t1) f2 ->
      Then (substituteSkolemsTerm s t0, substituteSkolemsTerm s t1) (substituteSkolems s f2)
    Eq t0 t1 -> Eq (substituteSkolemsTerm s t0) (substituteSkolemsTerm s t1)

-- | @toPrenex f@ transforms a formula into prenex normal form by moving all
-- the universal quantifiers to the front.
{-@ ignore toPrenex @-}
toPrenex :: Formula -> Formula
toPrenex f0 =
    let (vs, f') = go f0
     in foldr Forall f' vs
  where
    go (Forall v f) =
      let (vs, f') = go f
       in (v : vs, f')
    go (Exists v f) = error "toPrenex: unexpected"
    go (Conj f1 f2) =
      let (vs1, f1') = go f1
          (vs2, f2') = go f2
       in (vs1 ++ vs2, Conj f1' f2')
    go (Then eq1 f2) = Then eq1 <$> go f2
    go f@(Eq {}) = ([], f)


-- | Removes implications from the formula by substituting in the consequent
--
-- @x == t -> f@ becomes @f[x:=t]@
{-@ ignore removeImplications @-}
removeImplications :: Formula -> Formula
removeImplications = go
  where
    go (Forall v f) = Forall v (go f)
    go (Exists v f) = Exists v (go f)
    go (Conj f1 f2) = Conj (go f1) (go f2)
    go (Then eq1 f2) =
      case eq1 of
        -- The scope of the substitution is empty since we don't expect
        -- quantifiers in f or f2. This is a hack, but a hack that acomplishes
        -- the same as computing the appropriate scope.
        (V v, t) -> go $ substituteFormula mempty (fromListSubst [(v, t)]) f2
        (t, V v) -> go $ substituteFormula mempty (fromListSubst [(v, t)]) f2
        (U, U) -> go f2
        (L t1, L t2) -> go $ Then (t1, t2) f2
        (P ta1 ta2, P tb1 tb2) -> go $ Then (ta1, tb1) $ Then (ta2, tb2) f2
        (SA{}, _) -> Then eq1 $ go f2
        (_, SA{}) -> Then eq1 $ go f2
        _ -> Eq U U
    go f@(Eq {}) = f

-- | Removes constructors from equalities
--
-- @P a b == P c d -> e@ becomes @a == c -> b == d -> e@
{-@ ignore removeConstructors @-}
removeConstructors :: Formula -> Formula
removeConstructors = go
  where
    go (Forall v f) = Forall v (go f)
    go (Exists v f) = Exists v (go f)
    go (Conj f1 f2) = Conj (go f1) (go f2)
    go (Then (t0, t1) f2) =
      foldr Then (go f2) $ goEq t0 t1
    go (Eq t0 t1) = case goEq t0 t1 of
      [] -> Eq U U
      xs -> foldr1 Conj $ map (uncurry Eq) xs

    goEq :: Term -> Term -> [(Term, Term)]
    goEq (L t1) (L t2) = goEq t1 t2
    goEq (P ta1 ta2) (P tb1 tb2) = goEq ta1 ta2 ++ goEq tb1 tb2
    goEq t0 t1 = [(t0, t1)]

-- | Assign terms to skolem functions.
--
-- When @unify@ returns pairs @(i, t) :: (Var, Term)@, @t@'s free variables are
-- in the scope of @i@ (the domain of the accompanying substitution).
--
-- Example:
--
-- > unify (t == SA (i, s))@ is @[(i, substitute (inverseSubst s) t)
--
{-@
unify
  :: {f:Formula | consistentSkolemScopes f}
  -> [{p:_ |
           isSubsetOfJust (freeVars (snd p)) (IntMap.lookup (fst p) (scopes f))
        && not (Set.member (fst p) (skolemSet (snd p)))
      }] / [formulaSize f]
@-}
unify :: Formula -> [(Var, Term)]
unify (Forall v f) = unify f
unify (Exists v f) = unify f
unify (Conj f1 f2) = unify f1 ++ unify f2
unify f@(Then (t0, t1) f2) =
    let unifsT1 = unifyEq t0 t1
        unifsT1Subst = fromListSubst unifsT1
     in unifsT1 ++ unify (substituteSkolems unifsT1Subst f2)
          ? lemmaScopeSubstSubset (scopes f) unifsT1Subst
unify (Eq t0 t1) = unifyEq t0 t1

{-@
unifyEq
  :: t0:Term
  -> {t1:Term | UnionCommutes (scopesTerm t0) (scopesTerm t1)}
  -> [{p:( Var
         , {t:Term |
              intMapIsSubsetOf
                (scopesTerm t)
                (IntMap.union (scopesTerm t0) (scopesTerm t1))
           }
         ) |
           isSubsetOfJust (freeVars (snd p)) (IntMap.lookup (fst p) (IntMap.union (scopesTerm t0) (scopesTerm t1)))
        && not (Set.member (fst p) (skolemSet (snd p)))
      }]
@-}
unifyEq :: Term -> Term -> [(Var, Term)]
unifyEq t0 t1@(SA (i, s))
      | Just s' <- inverseSubst $ narrowForInvertibility (freeVars t0) s
      , let t' = substitute s' t0
      , not (Set.member i (skolemSet t'))
      , Set.isSubsetOf (freeVars t') (domain s)
      =
        [(i, t')]
          ? lemmaSubstituteScopesTerm s' t0
unifyEq t0@(SA (i, s)) t1
      | Just s' <- inverseSubst $ narrowForInvertibility (freeVars t1) s
      , let t' = substitute s' t1
      , not (Set.member i (skolemSet t'))
      , Set.isSubsetOf (freeVars t') (domain s)
      =
        [(i, t')]
          ? lemmaSubstituteScopesTerm s' t1
unifyEq _ _ = []

{-@ predicate UnionCommutes S0 S1 = IntMap.union S0 S1 == IntMap.union S1 S0 @-}
-- BUG: unionCommutes is not unfolded in proofs for some reason, so we resort
-- instead to using the predicate alias UnionCommutes.
{-@ reflect unionCommutes @-}
unionCommutes :: IntMap (Set Int) -> IntMap (Set Int) -> Bool
unionCommutes s0 s1 = IntMap.union s0 s1 == IntMap.union s1 s0

{-@ measure consistentSkolemScopes @-}
consistentSkolemScopes :: Formula -> Bool
consistentSkolemScopes (Forall _ f) = consistentSkolemScopes f
consistentSkolemScopes (Exists _ f) = consistentSkolemScopes f
consistentSkolemScopes (Conj f1 f2) =
      consistentSkolemScopes f1 && consistentSkolemScopes f2
  &&  unionCommutes (scopes f1) (scopes f2)
consistentSkolemScopes (Then (t0, t1) f2) =
     consistentSkolemScopes f2
  && unionCommutes (scopesTerm t0) (scopesTerm t1)
  && unionCommutes (IntMap.union (scopesTerm t0) (scopesTerm t1)) (scopes f2)
consistentSkolemScopes (Eq t0 t1) =
  unionCommutes (scopesTerm t0) (scopesTerm t1)

{-@
lemmaSubstituteScopesTerm
  :: s:Subst {t:_ | isVar t}
  -> t:Term
  -> { scopesTerm t = scopesTerm (substitute s t) }
@-}
lemmaSubstituteScopesTerm :: Subst Term -> Term -> ()
lemmaSubstituteScopesTerm s (SA (_, s1)) = lemmaComposeSubstDomain s1 s
lemmaSubstituteScopesTerm s U = ()
lemmaSubstituteScopesTerm s (L t) = lemmaSubstituteScopesTerm s t
lemmaSubstituteScopesTerm s (P t0 t1) =
    lemmaSubstituteScopesTerm s t0 `seq` lemmaSubstituteScopesTerm s t1
lemmaSubstituteScopesTerm s (V v) = case lookupSubst v s of
    Nothing -> ()
    Just (V _) -> ()
    Just _ -> ()

{-@ inline isSubsetOfJust @-}
isSubsetOfJust :: Ord a => Set a -> Maybe (Set a) -> Bool
isSubsetOfJust xs (Just ys) = Set.isSubsetOf xs ys
isSubsetOfJust xs Nothing = False

-- TODO: consider what to do when unification introduces equalities of
-- constructors that might need to be eliminated

-- | @narrowForInvertibility vs s@ removes pairs from @s@ if the range
-- is not a variable, or if the range is not a member of @vs@.
narrowForInvertibility :: Set Var -> Subst Term -> Subst Term
narrowForInvertibility vs (Subst xs) = Subst [(i, V j) | (i, V j) <- xs, Set.member j vs]

-- TODO: consider what to do with non-invertible substitutions like ?v[x\z,y\z] ?= z
--
-- At the moment we just pick the first of the variables with a duplicated
-- range.
{-@ inverseSubst :: _ -> Maybe (Subst {t:_ | isVar t}) @-}
inverseSubst :: Subst Term -> Maybe (Subst Term)
inverseSubst (Subst xs) = Subst <$> go xs
  where
    {-@ go :: _ -> Maybe [(Var, {t:_ | isVar t})] @-}
    go :: [(Var, Term)] -> Maybe [(Var, Term)]
    go [] = Just []
    go ((i, V j) : xs) = ((j, V i) :) <$> go xs
    go _ = Nothing

-- BUG: isVar should work regardles of whether it is inline or reflect'ed
-- but for some reason it is only unfolded in proofs if declared as inline.
{-@ inline isVar @-}
isVar :: Term -> Bool
isVar V{} = True
isVar _ = False

--- | Assign terms to existential variables in an attempt to make a formula
-- true.
{-@ ignore unifyFormula @-}
unifyFormula :: Formula -> [(Var, Term)]
unifyFormula = unifyFormula' False

{-@ ignore unifyFormulaTrace @-}
unifyFormulaTrace :: Formula -> [(Var, Term)]
unifyFormulaTrace = unifyFormula' True

{-@ ignore unifyFormula' @-}
unifyFormula' :: Bool -> Formula -> [(Var, Term)]
unifyFormula' mustTrace =
    traceUnify
          "                     unify" .
    unify .
    trace "        removeConstructors" .
    removeConstructors .
    trace "        removeImplications" .
    removeImplications .
    trace "                  toPrenex" .
    toPrenex .
    trace "                 skolemize" .
    skolemize .
    trace "                    rename" .
    rename Set.empty .
    trace "                   initial"
  where
    trace :: String -> Formula -> Formula
    trace label f
      | mustTrace = Debug.Trace.trace (label ++ ": " ++ ppFormula prettyName f) f
      | otherwise = f
    traceUnify :: String -> [(Var, Term)] -> [(Var, Term)]
    traceUnify label xs
      | mustTrace = Debug.Trace.trace (label ++ ": " ++ showUnification xs) xs
      | otherwise = xs
    showUnification :: [(Var, Term)] -> String
    showUnification xs =
      let xs' = map (\(i, t) -> (prettyName i, ppTerm prettyName t)) xs
       in "[" ++ List.intercalate ", " (map (\(i, t) -> i ++ ":=" ++ t) xs') ++ "]"

-- pretty printing

-- | Pretty print a variable name
{-@ ignore prettyName @-}
prettyName :: Int -> String
prettyName = ((["x", "y", "z", "u", "v", "w", "r", "s", "t"] ++ [ "v" ++ show i | i <- [1..] ]) !!)
-- prettyName = ((["a", "b", "c", "t_f", "x_f", "l", "r" ] ++ ["x", "y", "z", "u", "v", "w", "r", "s", "t"] ++ [ "v" ++ show i | i <- [1..] ]) !!)

-- | Pretty print a formula
{-@ ignore ppFormula @-}
ppFormula :: (Int -> String) -> Formula -> String
ppFormula vnames = go
  where
    go (Forall v f) = "∀" ++ (vnames v) ++ ". " ++ go f
    go (Exists v f) = "∃" ++ (vnames v) ++ ". " ++ go f
    go (Conj f1 f2) = "(" ++ go f1 ++ ") ∧ (" ++ go f2 ++ ")"
    go (Then (t0, t1) f2) = go (Eq t0 t1) ++ " → " ++ go f2
    go (Eq t0 t1) = ppTerm vnames t0 ++ " == " ++ ppTerm vnames t1

{-@ ignore ppTerm @-}
ppTerm :: (Int -> String) -> Term -> String
ppTerm vnames t =
  case t of
    V i -> vnames i
    SA (i, s) -> vnames i ++ ppSubst vnames s
    U -> "U"
    L t1 -> "L(" ++ ppTerm vnames t1 ++ ")"
    P t1 t2 -> "P(" ++ ppTerm vnames t1 ++ ", " ++ ppTerm vnames t2 ++ ")"

{-@ ignore ppSubst @-}
ppSubst :: (Int -> String) -> Subst Term -> String
ppSubst vnames (Subst xs) =
  "[" ++ List.intercalate ", " (map (\(i, t) -> vnames i ++ ":=" ++ ppTerm vnames t) xs) ++ "]"


-- Test formulas

tf0 :: Formula
tf0 = Forall 0 $ Exists 1 $ V 1 `Eq` V 0

tf1 :: Formula
tf1 =
  Forall 0 $ Exists 1 $ Forall 2 $
    (V 1 `Eq` V 0) `Conj` (Exists 1 $ V 1 `Eq` V 2)

tf2 :: Formula
tf2 =
  Forall 0 $ Exists 1 $
    (V 1 `Eq` V 0) `Conj` (Forall 2 $ Exists 1 $ V 1 `Eq` V 2)

tf3 :: Formula
tf3 =
  Conj
    (Forall 1 $ Exists 0 $ V 0 `Eq` V 1)
    (Forall 2 $ Exists 0 $ V 0 `Eq` V 2)

tf4 :: Formula
tf4 = Forall 0 $ Forall 1 $
  (V 0, L (V 1)) `Then` Exists 2 (Eq (V 0) (L (V 2)))

tf5 :: Formula
tf5 = Forall 0 $ Forall 1 $
  (V 0, L (V 1)) `Then` Forall 1 ((V 1, V 0) `Then` Exists 2 (Eq (V 1) (L (V 2))))

tf6 :: Formula
tf6 = Forall 0 $ Forall 0 $ Exists 1 (Eq (V 1) (V 0))

tf7 :: Formula
tf7 = Forall 0 $ Exists 1 $ Exists 2 $ (V 0, V 1) `Then` Eq (V 0) (V 2)

infixr 7 `Then`
infixr 8 `Conj`

-- | forall a b c. exists t_f x_f. a = (b, c) -> a = (Int -> Int, Int) -> t_f = b -> x_f = c -> exists l r. t_f = l -> r /\ l = x_f /\ x_f = Int -> r = c
tf8 :: Formula
tf8 = Forall 0 $ Forall 1 $ Forall 2 $
  Exists 3 (Exists 4 $
    (V 0, P (V 1) (V 2))
      `Then` (V 0, P (P U U) U)
      `Then` (V 3, V 1)
      `Then` (V 4, V 2)
      `Then`
    Exists 5 (Exists 6 $
             Eq (V 3) (P (V 5) (V 6))
      `Conj` Eq (V 5) (V 4)
      `Conj` ((V 4, U) `Then` Eq (V 6) (V 2))
    )
  )

{-@ ignore test @-}
test :: IO ()
test = do
  let tests =
        [ ("tf0", (tf0, [(1,V 0)]))
        , ("tf1", (tf1, [(1,V 0), (3,V 2)]))
        , ("tf2", (tf2, [(1,V 0), (3,V 2)]))
        , ("tf3", (tf3, [(0,V 1), (3,V 2)]))
        , ("tf4", (tf4, [(2,V 1)]))
        , ("tf5", (tf5, [(3,V 1)]))
        , ("tf6", (tf6, [(2,V 1)]))
        , ("tf7", (tf7, [(1,SA (2,Subst [(0,SA (1,Subst [(0,V 0)]))]))]))
        , ("tf8", (tf8, [(3,P U U),(4,U),(5,U),(6,U)]))
        ]
  mapM_ runUnificationTest tests
  where
    runUnificationTest (name, (f, expected)) = do
      let result = unifyFormula f
      if result == expected
        then putStrLn $ concat ["Test ", name, ": Passed"]
        else putStrLn $
               concat ["Test ", name, ": Failed\n", show expected, " but got ", show result, "\n"]
