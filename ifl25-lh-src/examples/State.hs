{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-@ LIQUID "--no-pattern-inline" @-}

-- | This module defines a state monad with refined types. It is used in
-- the Unif.hs example.
-- The code has been copied and adapted from the Liquid Haskell repository:
--
-- https://github.com/ucsd-progsys/liquidhaskell/blob/a826d422730eee153a2818e68f392f770fbc5cab/tests/benchmarks/icfp15/pos/RIO2.hs
--
module State where

import Data.Set as Set

{-@ data State s a <p :: s -> Bool, q :: s -> a -> s -> Bool>
      = State (x:s<p> -> (a, s)<\w -> {v:s<q x w> | true}>)
  @-}
data State s a  = State {runState :: s -> (a, s)}

{-@ runState :: forall <p :: s -> Bool, q :: s -> a -> s -> Bool>.
                State <p, q> s a -> x:s<p> -> (a, s)<\w -> {v:s<q x w> | true}> @-}

instance Functor (State s) where
{-@
instance Functor (State s) where
  fmap :: forall < p  :: s -> Bool
                 , q :: s -> a -> s -> Bool
                 , q2 :: s -> a -> s -> Bool
                 , pa :: a -> Bool
                 , pb :: b -> Bool
                 >.
            {x::a<pa>, s0::s<p>, y::b<pb> |- s<q s0 x> <: s<q2 s0 y>}
            (a<pa> -> b<pb>)
         -> State <p, q> s a<pa>
         -> State <p, q2> s b<pb>
@-}
  fmap f x = State $ \s -> let (y, s') = runState x s in (f y, s')

instance Applicative (State s) where
{-@
instance Applicative (State s) where
  pure :: forall <p :: s -> Bool>.
                x:a -> State <p, \w0 y -> {w1:s<p> | w0 == w1 && y == x}> s a
//  pure
//    :: forall <p :: s -> Bool, q :: s -> a -> s -> Bool>.
//       { x::a, s0::s<p> |- {v:s<p> | v = s0} <: {v:s<q s0 x> | true} }
//       x:a -> State <p, q> s a
@-}
  pure x = State $ \s -> (x, s)
  mf <*> mx = State $ \s ->
    let (f, s1) = runState mf s
        (x, s2) = runState mx s1
    in (f x, s2)

instance Monad (State s) where
{-@
instance Monad (State s) where
  >>= :: forall < p  :: s -> Bool
                    , p2 :: a -> s -> Bool
                    , r  :: a -> Bool
                    , q1 :: s -> a -> s -> Bool
                    , q2 :: a -> s -> b -> s -> Bool
                    , q  :: s -> b -> s -> Bool>.
            {x::a<r>, w::s<p>|- s<q1 w x> <: s<p2 x>}
            {w::s<p>, x::a, w1::s<q1 w x>, y::b |- s<q2 x w1 y> <: s<q w y>}
            {x::a, w::s, w2::s<q1 w x>|- {v:a | v = x} <: a<r>}
            State <p, q1> s a
         -> (x:a<r> -> State <{v:s<p2 x> | true}, \w1 y -> {v:s<q2 x w1 y> | true}> s b)
         -> State <p, q> s b ;
  >>  :: forall < p   :: s -> Bool
                    , p2  :: s -> Bool
                    , q1 :: s -> a -> s -> Bool
                    , q2 :: s -> b -> s -> Bool
                    , q :: s -> b -> s -> Bool>.
            {x::a, w::s<p>|- s<q1 w x> <: s<p2>}
            {w::s<p>, w2::s<p2>, x::b, y::a |- s<q2 w2 x> <: s<q w x>}
            State <p, q1> s a
         -> State <p2, q2> s b
         -> State <p, q> s b  ;
  return :: forall <p :: s -> Bool>.
                x:a -> State <p, \w0 y -> {w1:s<p> | w0 == w1 && y == x}> s a
@-}
  (State g) >>= f = State $ \x -> case g x of {(y, s) -> (runState (f y)) s}

  (State g) >>  f = State $ \x -> case g x of {(y, s) -> (runState f    ) s}

  return w      = pureS w

{-@ qualif Papp4(v:a, x:b, y:c, z:d, p:Pred a b c d) : papp4(p, v, x, y, z) @-}

{-@
get :: forall <p :: s -> Bool>.
   State <p, {\s0 v s -> v = s && s = s0}> s s<p>
@-}
get :: State s s
get = State $ \s -> (s, s)

{-@
put :: forall <p :: s -> Bool>.
   s0:s -> State <p, {\_ v s -> s = s0}> s ()
@-}
put :: s -> State s ()
put s = State $ \_ -> ((), s)

{-@
pureS
  :: forall <p :: s -> Bool, q :: s -> a -> s -> Bool>.
     { x::a, s0::s<p> |- {v:s<p> | v = s0} <: {v:s<q s0 x> | true} }
     x:a -> State <p, q> s a
@-}
pureS :: a -> State s a
pureS x = State $ \s -> (x, s)

{-@
modify :: forall <p :: s -> Bool, q :: s -> Bool, q2 :: s -> a -> s -> Bool>.
    { s0::s<p>, x::() |- s<q> <: s<q2 s0 x>   }
    f:(s<p> -> s<q>) -> State <p, q2> s ()
@-}
modify :: (s -> s) -> State s ()
modify f = State $ \s -> ((), f s)
