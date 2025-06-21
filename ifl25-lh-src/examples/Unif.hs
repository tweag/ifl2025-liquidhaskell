{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflect" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-pattern-inline" @-}
module Unif where

import Data.List qualified as List
import Data.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace qualified
-- BUG: this import is to avoid a bug in name resolution in Liquid Haskell
import qualified Data.Maybe as GHC.Internal.Maybe

-- from liquid-prelude:
import Language.Haskell.Liquid.ProofCombinators

-- from a sibling source file:
import State

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
define IntMap.lookup x m =
         if (isSome (IntMapSetInt_select m x)) then
           (GHC.Internal.Maybe.Just (someVal (IntMapSetInt_select m x)))
         else
           GHC.Internal.Maybe.Nothing
define IntMap.delete x m = (Map_store m x None)

define IntMap.union x y = IntMapSetInt_union x y
define IntMap.difference x y = IntMapSetInt_difference x y
define intMapIsSubsetOf x y = IntMapSetInt_isSubsetOf x y
@-}

-- Only provided here for use in specifications
intMapIsSubsetOf :: IntMap (Set Int) -> IntMap (Set Int) -> Bool
intMapIsSubsetOf _ _ = undefined

-- It shouldn't be necessary to define intMapUnion, but without it, we get
-- that IntMap.union is not correctly expanded to what the preamble defines.
{-@ assume intMapUnion
     :: s0:IntMap (Set Int)
     -> s1:IntMap (Set Int)
     -> {v:_ | IntMap.union s0 s1 = v }
@-}
{-@ inline intMapUnion @-}
{-@ ignore intMapUnion @-}
intMapUnion :: IntMap (Set Int) -> IntMap (Set Int) -> IntMap (Set Int)
intMapUnion a b = IntMap.union a (mid b)

{-@ inline mid @-}
mid :: IntMap (Set Int) -> IntMap (Set Int)
mid m = m


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
  deriving (Eq, Ord, Show)

{-@
assume lookupSubst
  :: forall <p :: Term -> Bool>.
     s:Subst Term<p> -> {i:Int | Set.member i (domain s)} -> Term<p>
@-}
lookupSubst :: Subst Term -> Var -> Term
lookupSubst (Subst s) i = case lookup i s of
    Nothing -> V i
    Just e -> e

emptySubst :: Subst e
emptySubst = Subst []

{-@
opaque-reflect extendSubst
// Extending a substitution should guarantee that the new domain includes the
// new variable.
assume extendSubst
  :: s:_
  -> i:_
  -> t:_
  -> {v:_ | union (domain s) (singleton i) = domain v }
@-}
extendSubst :: Subst a -> Var -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

{-@ opaque-reflect fromListSubst @-}
{-@
// Creates a substitution whose domain includes all variables. Variables
// that are not in the input list are mapped to themselves.
assume fromListSubst :: _ -> {v:_ | Set_com empty = domain v}
@-}
fromListSubst :: [(Var, t)] -> Subst t
fromListSubst = Subst

{-@ opaque-reflect fromSetIdSubst @-}
{-@
// Creates a substitution that maps each variable in the set to itself.
assume fromSetIdSubst ::
    s:Set Int -> {v:_ | s = domain v && s = freeVarsSubst v}
@-}
fromSetIdSubst :: Set Int -> Subst Term
fromSetIdSubst s = Subst [(i, V i) | i <- Set.toList s]

{-@
assume lemmaExtendSubstScopes
  :: s:_
  -> i:_
  -> t:_
  -> { scopesSubst (extendSubst s i t)
         = IntMap.union (scopesSubst s) (scopesTerm t)
     }
@-}
lemmaExtendSubstScopes
  :: Subst Term -> Var -> Term -> ()
lemmaExtendSubstScopes _ _ _ = ()

{-@
assume lemmaScopesSubstSubset
  :: m0:_
  -> s:Subst {t:Term | intMapIsSubsetOf (scopesTerm t) m0}
  -> { intMapIsSubsetOf (scopesSubst s) m0 } @-}
lemmaScopesSubstSubset :: IntMap (Set Int) -> Subst Term -> ()
lemmaScopesSubstSubset _ _ = ()

{-@
lemmaScopesListSubset
  :: m0:_
  -> s:[(Var, {t:Term | intMapIsSubsetOf (scopesTerm t) m0})]
  -> { intMapIsSubsetOf (scopesList s) m0 } @-}
lemmaScopesListSubset :: IntMap (Set Int) -> [(Var, Term)] -> ()
lemmaScopesListSubset _ [] = ()
lemmaScopesListSubset m0 ((_ , _) : xs) = lemmaScopesListSubset m0 xs

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
-- BUG: reflecting scopes instead of using  measure causes LH to drop some
-- hipothesis when checking skolemize.
--
{-@ measure scopes @-}
scopes :: Formula -> IntMap (Set Int)
scopes (Forall _ f) = scopes f
scopes (Exists _ f) = scopes f
scopes (Conj f1 f2) = IntMap.union (scopes f1) (scopes f2)
scopes (Then (t0, t1) f2) =
    IntMap.union (scopesTerm t0) (IntMap.union (scopesTerm t1) (scopes f2))
scopes (Eq t0 t1) = IntMap.union (scopesTerm t0) (scopesTerm t1)

{-@ measure scopesTerm @-}
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

{-@ measure freeVarsFormula @-}
freeVarsFormula :: Formula -> Set Int
freeVarsFormula = \case
    Forall v f -> Set.difference (freeVarsFormula f) (Set.singleton v)
    Exists v f -> Set.difference (freeVarsFormula f) (Set.singleton v)
    Conj f1 f2 -> Set.union (freeVarsFormula f1) (freeVarsFormula f2)
    Then (t0, t1) f2 ->
      Set.union (Set.union (freeVars t0) (freeVars t1)) (freeVarsFormula f2)
    Eq t0 t1 -> Set.union (freeVars t0) (freeVars t1)

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
type ScopedFormula S = {f:Formula | isSubsetOf (freeVarsFormula f) S}
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


-- BUG: assumed specs are ignored when the function is reflected
{-@
reflect substitute
ignore substitute
@-}
substitute :: Subst Term -> Term -> Term
substitute s t = case t of
    V v -> lookupSubst s v
    SA (v, s1) -> SA (v, composeSubst s1 s)
    U -> U
    L t1 -> L (substitute s t1)
    P t1 t2 -> P (substitute s t1) (substitute s t2)

-- This lemma should be possible to generalize by dropping the @isVar@
-- requirement and asking @UnionCommutes (scopesTerm t) (scopesSubst s)@
-- instead.
{-@
assume lemmaSubstituteConsistentScopes
  :: s:Subst {st:Term | consistentSkolemScopesTerm st && isVar st}
  -> {t:Term | consistentSkolemScopesTerm t }
  -> { consistentSkolemScopesTerm (substitute s t) }
@-}
lemmaSubstituteConsistentScopes :: Subst Term -> Term -> ()
lemmaSubstituteConsistentScopes _ _ = ()

{-@
ignore composeSubst
opaque-reflect composeSubst
@-}
composeSubst :: Subst Term -> Subst Term -> Subst Term
composeSubst (Subst xs) s = Subst (map (fmap (substitute s)) xs)

{-@
opaque-reflect substituteFormula
substituteFormula
  :: scope:Set Int
  -> s:Subst (ScopedTerm scope)
  -> {f:ScopedFormula (domain s) |
           consistentSkolemScopes f
        && UnionCommutes (scopes f) (scopesSubst s)
     }
  -> {v:ScopedFormula scope |
          formulaSize f == formulaSize v
       && consistentSkolemScopes v
       && existsCount v = existsCount f
       && intMapIsSubsetOf (scopes v) (IntMap.union (scopes f) (scopesSubst s))
     } / [formulaSize f]
@-}
substituteFormula
  :: Set Int -> Subst Term -> Formula -> Formula
substituteFormula scope s = \case
    Forall v f
      | Set.member v scope ->
        let u = freshVar scope
            scope' = Set.insert u scope
            s' = extendSubst s v (V u)
            f' = substituteFormula scope' s'
                   (f ? lemmaExtendSubstScopes s v (V u))
         in
            Forall u f'
      | otherwise ->
        let scope' = Set.insert v scope
            s' = extendSubst s v (V v)
            f' = substituteFormula scope' s'
                   (f ? lemmaExtendSubstScopes s v (V v))
         in
            Forall v f'
    Exists v f
      | Set.member v scope ->
        let u = freshVar scope
            scope' = Set.insert u scope
            s' = extendSubst s v (V u)
            f' = substituteFormula scope' s'
                   (f ? lemmaExtendSubstScopes s v (V u))
         in
            Exists u f'
      | otherwise ->
        let scope' = Set.insert v scope
            s' = extendSubst s v (V v)
            f' = substituteFormula scope' s'
                   (f ? lemmaExtendSubstScopes s v (V v))
         in
            Exists v f'
    Conj f1 f2 ->
      Conj (substituteFormula scope s f1) (substituteFormula scope s f2)
    Then (t0, t1) f2 ->
      Then (substitute s t0, substitute s t1) (substituteFormula scope s f2)
        ? lemmaSubstituteFreeVars scope s t0
        ? lemmaSubstituteFreeVars scope s t1
    Eq t0 t1 -> Eq (substitute s t0) (substitute s t1)
      ? lemmaSubstituteFreeVars scope s t0
      ? lemmaSubstituteFreeVars scope s t1

-- BUG: Appartently Liquid Haskell cannot prove termination of recursive
-- functions on mutually recursive types, so we disable the termination checker
-- for this function.
{-@ lazy scopesSubst @-}
{-@ opaque-reflect scopesSubst @-}
scopesSubst :: Subst Term -> IntMap (Set Int)
scopesSubst (Subst xs) =
    foldr IntMap.union IntMap.empty $ map (scopesTerm . snd) xs

{-@
assume lemmaSubstituteFreeVars
  :: scope:Set Int
  -> s:Subst (ScopedTerm scope)
  -> {t:ScopedTerm (domain s) | consistentSkolemScopesTerm t}
  -> {   isSubsetOf (freeVars (substitute s t)) scope
      && IntMapSetInt_isSubsetOf
           (scopesTerm (substitute s t))
           (IntMapSetInt_union (scopesTerm t) (scopesSubst s))
      && consistentSkolemScopesTerm (substitute s t)
     }
@-}
lemmaSubstituteFreeVars :: Set Int -> Subst Term -> Term -> ()
lemmaSubstituteFreeVars scope s f = ()

-- | Replaces existential variables with skolem functions
--
-- Every time that `SA (i,s)` occurs, the domain of `s` is exactly the set of
-- bound variables in scope.
{-@
skolemize
  :: sf:_
  -> {f:ScopedFormula sf | consistentSkolemScopes f}
  -> State
       < {\se ->
             isSubsetOf sf se
          && isSubsetOf (IntMapSetInt_keys (scopes f)) se
         }

       , {\se0 v se ->
             consistentSkolemScopes v
          && existsCount v = 0
          && isSubsetOf (freeVarsFormula v) sf
          && isSubsetOf se0 se
          && intersection se0
               (IntMapSetInt_keys (IntMap.difference (scopes v) (scopes f)))
               = Set.empty
          && intMapIsSubsetOf (scopes f) (scopes v)
          && isSubsetOf (IntMapSetInt_keys (scopes v)) se
       }>
       _ _
     / [formulaSize f]
@-}
skolemize :: Set Int -> Formula -> State (Set Int) Formula
skolemize sf (Forall v f) = do
    se <- get
    put (Set.insert v se)
    f' <- skolemize (Set.insert v sf) f
    pure (Forall v f')
-- BUG: LH hangs when trying to check the Exists case of skolemize
-- Therefore, we 'skip' it.
skolemize sf (Exists v f) = skolemizeExistsCase sf v f ? skip ()
skolemize sf (Conj f1 f2) = do
     f1' <- skolemize sf f1
     f2' <- skolemize sf f2
     pure (Conj f1' f2')
skolemize sf (Then (t0, t1) f2) = do
     f2' <- skolemize sf f2
     pure (Then (t0, t1) f2')
skolemize _ f@Eq{} = pure f

{-@ ignore skolemizeExistsCase @-}
skolemizeExistsCase :: Set Int -> Int -> Formula -> State (Set Int) Formula
skolemizeExistsCase sf v f = do
    se <- get
    let u = if Set.member v se then freshVar se else v
    put (Set.insert u se)
    let subst = fromListSubst [(v, SA (u, fromSetIdSubst sf))]
    skolemize sf (substituteFormula sf subst f)

{-@ measure existsCount @-}
{-@ existsCount :: Formula -> Nat @-}
existsCount :: Formula -> Int
existsCount (Forall _ f) = existsCount f
existsCount (Exists _ f) = 1 + existsCount f
existsCount (Conj f1 f2) = existsCount f1 + existsCount f2
existsCount (Then _ f2) = existsCount f2
existsCount Eq{} = 0

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
  :: s:Set Int
  -> {f:ScopedFormula s | consistentSkolemScopes f && existsCount f = 0}
  -> Maybe [{p:(Var, {st:_ | consistentSkolemScopesTerm st
                          && intMapIsSubsetOf (scopesTerm st) (scopes f) }) |
           isSubsetOfJust (freeVars (snd p)) (IntMap.lookup (fst p) (scopes f))
        && not (Set.member (fst p) (skolemSet (snd p)))
      }] / [formulaSize f]
@-}
unify :: Set Int -> Formula -> Maybe [(Var, Term)]
unify s (Forall v f) = unify (Set.insert v s) f
unify s (Exists v f) = error "unify: the formula hasn't been skolemized"
unify s f@(Conj f1 f2) = do
    unifyF1 <- unify s f1
    let lemmaSubst = lemmaScopesListSubset (scopes f) unifyF1
    unifyF2 <- unify s (substituteSkolems (f2 ? lemmaSubst) unifyF1)
    return (unifyF1 ++ unifyF2)
unify s f@(Then (t0, t1) f2) =
    let subst = fromListSubst (substEq t0 t1)
     in unify s (substituteFormula s subst (f2 ? lemmaSubst subst))
  where
    lemmaSubst subst =
      lemmaScopesSubstSubset (intMapUnion (scopesTerm t0) (scopesTerm t1)) subst
unify s (Eq t0 t1) = unifyEq t0 t1

{-@
substEq
  :: {t0:Term | consistentSkolemScopesTerm t0}
  -> {t1:Term | UnionCommutes (scopesTerm t0) (scopesTerm t1)
                && consistentSkolemScopesTerm t1}
  -> [(Var, {v:Term |
          intMapIsSubsetOf
            (scopesTerm v)
            (IntMap.union (scopesTerm t0) (scopesTerm t1))
       && isSubsetOf (freeVars v) (Set.union (freeVars t0) (freeVars t1))
      })]
@-}
substEq :: Term -> Term -> [(Var, Term)]
substEq (V i) t1 = [(i, t1)]
substEq t0 (V i) = [(i, t0)]
substEq (L t0) (L t1) = substEq t0 t1
substEq (P t0a t0b) (P t1a t1b) = substEq t0a t1a ++ substEq t0b t1b
substEq SA{} _ = []
substEq _ SA{} = []
substEq _ _ = []

-- BUG: ignoring a function causes the asserted signature to be ignored
-- It needs to be assumed to work around it.
{-@
lazy unifyEq
unifyEq
  :: {t0:Term | consistentSkolemScopesTerm t0}
  -> {t1:Term |
          UnionCommutes (scopesTerm t0) (scopesTerm t1)
       && consistentSkolemScopesTerm t1
     }
  -> Maybe [{p:( Var
         , {t:Term |
                intMapIsSubsetOf
                  (scopesTerm t)
                  (IntMap.union (scopesTerm t0) (scopesTerm t1))
              && consistentSkolemScopesTerm t
           }
         ) |
           isSubsetOfJust (freeVars (snd p)) (IntMap.lookup (fst p) (IntMap.union (scopesTerm t0) (scopesTerm t1)))
        && not (Set.member (fst p) (skolemSet (snd p)))
      }]
@-}
unifyEq :: Term -> Term -> Maybe [(Var, Term)]
unifyEq t0@(SA (i, s)) t1 = unifyEqEnd t0 t1
unifyEq t0 t1@(SA (i, s)) = unifyEqEnd t1 t0
unifyEq (L t0) (L t1) = unifyEq t0 t1
unifyEq (P t0a t0b) (P t1a t1b) = do
    unifyT0a <- unifyEq t0a t1a
    -- BUG: the lemma does not seem to work if moved to a where clause
    let lemmaSubst = lemmaScopesListSubset
          (intMapUnion (scopesTerm t0a) (scopesTerm t1a)) unifyT0a
    unifyT0b <- unifyEq (substituteSkolemsTerm t0b (unifyT0a ? lemmaSubst))
                        (substituteSkolemsTerm t1b (unifyT0a ? lemmaSubst))
    return $ unifyT0a ++ unifyT0b
unifyEq U U = Just []
unifyEq _ _ = Nothing

-- BUG: cannot define a termination metric if conflating unifyEq and unifyEqEnd
{-@
unifyEqEnd
  :: {t0:Term | consistentSkolemScopesTerm t0}
  -> {t1:Term |
          UnionCommutes (scopesTerm t0) (scopesTerm t1)
       && consistentSkolemScopesTerm t1
     }
  -> Maybe [{p:( Var
         , {t:Term |
                intMapIsSubsetOf
                  (scopesTerm t)
                  (IntMap.union (scopesTerm t0) (scopesTerm t1))
             && consistentSkolemScopesTerm t
           }
         ) |
           isSubsetOfJust
             (freeVars (snd p))
             (IntMap.lookup
               (fst p)
               (IntMap.union (scopesTerm t0) (scopesTerm t1))
             )
        && not (Set.member (fst p) (skolemSet (snd p)))
      }]
@-}
unifyEqEnd :: Term -> Term -> Maybe [(Var, Term)]
unifyEqEnd t0@(SA (i, s)) t1
    | Just s' <- inverseSubst $ narrowForInvertibility (freeVars t1) s
    , let t' = substitute s' t1
    , not (Set.member i (skolemSet t'))
    , Set.isSubsetOf (freeVars t') (domain s)
    = Just [(i, t')]
        ? lemmaSubstituteScopesTerm s' t1
        ? lemmaSubstituteConsistentScopes s' t1
unifyEqEnd _ _ = Nothing


{-@
substituteSkolems
  :: {f:Formula | consistentSkolemScopes f && existsCount f = 0}
  -> {s:[{p:(Var, {st:Term | consistentSkolemScopesTerm st}) |
           isSubsetOfJustOrNothing
             (freeVars (snd p))
             (IntMap.lookup (fst p) (scopes f))
         }] |
        UnionCommutes (scopes f) (scopesList s)
      }
  -> {v:Formula |
          formulaSize f == formulaSize v
       && intMapIsSubsetOf (scopes v) (scopes f)
       && consistentSkolemScopes v
       && existsCount v = 0
       && freeVarsFormula v = freeVarsFormula f
     }
@-}
substituteSkolems :: Formula -> [(Var, Term)] -> Formula
substituteSkolems f0 s = case f0 of
    Forall v f -> Forall v (substituteSkolems f s)
    Exists v f -> error "substituteSkolems: the formula hasn't been skolemized"
    Conj f1 f2 -> Conj (substituteSkolems f1 s) (substituteSkolems f2 s)
    Then (t0, t1) f2 ->
      Then (substituteSkolemsTerm t0 s, substituteSkolemsTerm t1 s)
           (substituteSkolems f2 s)
    Eq t0 t1 -> Eq (substituteSkolemsTerm t0 s) (substituteSkolemsTerm t1 s)

{-@
substituteSkolemsTerm
  :: {t:Term | consistentSkolemScopesTerm t}
  -> {s:[{p:(Var, {st:Term | consistentSkolemScopesTerm st}) |
           isSubsetOfJustOrNothing
             (freeVars (snd p))
             (IntMap.lookup (fst p) (scopesTerm t))
         }] |
        UnionCommutes (scopesTerm t) (scopesList s)
     }
  -> {v:Term |
          intMapIsSubsetOf (scopesTerm v) (scopesTerm t)
       && consistentSkolemScopesTerm v
       && freeVars v = freeVars t
     }
lazy substituteSkolemsTerm
@-}
substituteSkolemsTerm :: Term -> [(Var, Term)] -> Term
substituteSkolemsTerm t s = case t of
    V v -> V v
    SA (v, s1) -> case lookup v s of
      Just t1 -> substitute s1 t1 ? skip ()
      Nothing -> SA (v, composeSubstList s1 s) ? skip ()
    U -> U
    L t1 -> L (substituteSkolemsTerm t1 s)
    P t1 t2 -> P (substituteSkolemsTerm t1 s) (substituteSkolemsTerm t2 s)

{-@ ignore composeSubstList @-}
composeSubstList :: Subst Term -> [(Var, Term)] -> Subst Term
composeSubstList (Subst xs) s = Subst (map (fmap (`substituteSkolemsTerm` s)) xs)

-- | Used to skip cases that we don't want to verify
{-@ assume skip :: _ -> { false } @-}
skip :: () -> ()
skip () = ()

{-@ reflect scopesList @-}
scopesList :: [(Var, Term)] -> IntMap (Set Int)
scopesList [] = IntMap.empty
scopesList ((_, t) : xs) = IntMap.union (scopesTerm t) (scopesList xs)

{-@ inline isSubsetOfJustOrNothing @-}
isSubsetOfJustOrNothing :: Set Int -> Maybe (Set Int) -> Bool
isSubsetOfJustOrNothing _ Nothing = True
isSubsetOfJustOrNothing s0 (Just s1) = Set.isSubsetOf s0 s1

{-@ predicate UnionCommutes S0 S1 = IntMap.union S0 S1 == IntMap.union S1 S0 @-}
-- BUG: unionCommutes is not unfolded in proofs for some reason, so we resort
-- instead to using the predicate alias UnionCommutes.
{-@ inline unionCommutes @-}
{-@ ignore unionCommutes @-}
unionCommutes :: IntMap (Set Int) -> IntMap (Set Int) -> Bool
unionCommutes s0 s1 = intMapUnion s0 s1 == intMapUnion s1 s0

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
  && consistentSkolemScopesTerm t0
  && consistentSkolemScopesTerm t1
consistentSkolemScopes (Eq t0 t1) =
     unionCommutes (scopesTerm t0) (scopesTerm t1)
  && consistentSkolemScopesTerm t0
  && consistentSkolemScopesTerm t1

{-@ measure consistentSkolemScopesTerm @-}
consistentSkolemScopesTerm :: Term -> Bool
consistentSkolemScopesTerm (V _) = True
consistentSkolemScopesTerm SA{} = True
consistentSkolemScopesTerm U = True
consistentSkolemScopesTerm (L t) = consistentSkolemScopesTerm t
consistentSkolemScopesTerm (P t0 t1) =
    consistentSkolemScopesTerm t0 && consistentSkolemScopesTerm t1
    && unionCommutes (scopesTerm t0) (scopesTerm t1)

{-@
lemmaSubstituteScopesTerm
  :: s:Subst {t:_ | isVar t}
  -> t:ScopedTerm (domain s)
  -> { scopesTerm t = scopesTerm (substitute s t) }
@-}
lemmaSubstituteScopesTerm :: Subst Term -> Term -> ()
lemmaSubstituteScopesTerm s (SA (_, s1)) = lemmaComposeSubstDomain s1 s
lemmaSubstituteScopesTerm s U = ()
lemmaSubstituteScopesTerm s (L t) = lemmaSubstituteScopesTerm s t
lemmaSubstituteScopesTerm s (P t0 t1) =
    lemmaSubstituteScopesTerm s t0 `seq` lemmaSubstituteScopesTerm s t1
lemmaSubstituteScopesTerm s (V v) =
    case lookupSubst s v of
      V _ -> ()
      _ -> ()

{-@ inline isSubsetOfJust @-}
isSubsetOfJust :: Ord a => Set a -> Maybe (Set a) -> Bool
isSubsetOfJust xs (Just ys) = Set.isSubsetOf xs ys
isSubsetOfJust xs Nothing = False

-- TODO: consider what to do when unification introduces equalities of
-- constructors that might need to be eliminated

-- | @narrowForInvertibility vs s@ removes pairs from @s@ if the range
-- is not a variable, or if the range is not a member of @vs@.
narrowForInvertibility :: Set Var -> Subst Term -> Subst Term
narrowForInvertibility vs (Subst xs) =
    Subst [(i, V j) | (i, V j) <- xs, Set.member j vs]

-- TODO: consider what to do with non-invertible substitutions
-- like ?v[x\z,y\z] ?= z
--
-- At the moment we just pick the first of the variables with a duplicated
-- range.
{-@
inverseSubst
  :: _
  -> Maybe
      ({s:Subst {t:_ | isVar t && consistentSkolemScopesTerm t} |
         Set_com Set.empty == domain s
       })
@-}
inverseSubst :: Subst Term -> Maybe (Subst Term)
inverseSubst (Subst xs) = fromListSubst <$> go xs
  where
    {-@
    go :: _
       -> Maybe [(Var, {t:_ | isVar t && consistentSkolemScopesTerm t})]
    @-}
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
{-@
unifyFormula
  :: sf:_
  -> se:_
  -> {f:ScopedFormula sf |
       consistentSkolemScopes f && isSubsetOf (IntMapSetInt_keys (scopes f)) se}
  -> Maybe [(Var, Term)]
@-}
unifyFormula :: Set Int -> Set Int -> Formula -> Maybe [(Var, Term)]
unifyFormula sf se f =
    let (f', _ ) = runState (skolemize sf f) (Set.union sf se)
     in unify sf f'


{-@ ignore unifyFormulaTrace @-}
unifyFormulaTrace :: Formula -> Maybe [(Var, Term)]
unifyFormulaTrace = unifyFormula' True

{-@ ignore unifyFormula' @-}
unifyFormula' :: Bool -> Formula -> Maybe [(Var, Term)]
unifyFormula' mustTrace =
    traceUnify
          "                     unify" .
    unify Set.empty .
    trace "                 skolemize" .
    (\f -> fst $ runState (skolemize Set.empty f) Set.empty) .
    trace "                   initial"
  where
    trace :: String -> Formula -> Formula
    trace label f
      | mustTrace =
          Debug.Trace.trace (label ++ ": " ++ ppFormula prettyName f) f
      | otherwise = f
    traceUnify :: String -> Maybe [(Var, Term)] -> Maybe [(Var, Term)]
    traceUnify label xs
      | mustTrace = Debug.Trace.trace (label ++ ": " ++ showUnification xs) xs
      | otherwise = xs
    showUnification :: Maybe [(Var, Term)] -> String
    showUnification Nothing = "Nothing"
    showUnification (Just xs) =
      let xs' = map (\(i, t) -> (prettyName i, ppTerm prettyName t)) xs
       in "[" ++
          List.intercalate ", " (map (\(i, t) -> i ++ ":=" ++ t) xs') ++
          "]"

-- pretty printing

-- | Pretty print a variable name
{-@ ignore prettyName @-}
prettyName :: Int -> String
prettyName =
  ((["x", "y", "z", "u", "v", "w", "r", "s", "t"] ++
    [ "v" ++ show i | i <- [1..] ]) !!)

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
  "[" ++
  List.intercalate
    ", " (map (\(i, t) -> vnames i ++ ":=" ++ ppTerm vnames t) xs) ++
  "]"


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
  (V 0, L (V 1))
    `Then` Forall 1 ((V 1, V 0)
    `Then` Exists 2 (Eq (V 1) (L (V 2))))

tf6 :: Formula
tf6 = Forall 0 $ Forall 0 $ Exists 1 (Eq (V 1) (V 0))

tf7 :: Formula
tf7 = Forall 0 $ Exists 1 $ Exists 2 $ (V 0, V 1) `Then` Eq (V 0) (V 2)

infixr 7 `Then`
infixr 8 `Conj`

-- forall a b c. exists t_f x_f.
--   a = (b, c) -> a = (Int -> Int, Int) -> t_f = b -> x_f = c ->
--     exists l r. t_f = l -> r /\ l = x_f /\ x_f = Int -> r = c
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
        [ ("tf0", (tf0, Just [(1,V 0)]))
        , ("tf1", (tf1, Just [(1,V 0), (3,V 2)]))
        , ("tf2", (tf2, Just [(1,V 0), (3,V 2)]))
        , ("tf3", (tf3, Just [(0,V 1), (3,V 2)]))
        , ("tf4", (tf4, Just [(2,V 1)]))
        , ("tf5", (tf5, Just [(2,V 1)]))
        , ("tf6", (tf6, Just [(1,V 0)]))
        , ("tf7", (tf7, Nothing))
        , ("tf8", (tf8,
            Just [(3,P (SA (5,Subst [(0,P (P U U) U),(1,P U U),(2,U)]))
                       (SA (6,Subst [(0,P (P U U) U),(1,P U U),(2,U)])))
                 ,(5,SA (4,Subst [(0,P (P U U) U),(1,P U U),(2,U)]))
                 ,(6,U)])
          )
        ]
  mapM_ runUnificationTest tests
  where
    runUnificationTest :: (String, (Formula, Maybe [(Var, Term)])) -> IO ()
    runUnificationTest (name, (f, expected)) = do
      let result = unifyFormula
            (freeVarsFormula f)
            (Set.fromList $ IntMap.keys (scopes f))
            f
      if result == expected
        then putStrLn $ concat ["Test ", name, ": Passed"]
        else putStrLn $
               concat ["Test ", name, ": Failed\n", show expected, " but got ",
                       show result, "\n"]
