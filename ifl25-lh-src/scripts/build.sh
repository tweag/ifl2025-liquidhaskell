#!/usr/bin/env bash
set -eux

scripts/clean.sh

# clone the liquidhaskell repository at a known commit in the develop branch
git clone https://github.com/ucsd-progsys/liquidhaskell.git
cd liquidhaskell
git checkout eb585061ffad22ea4ba232cc3f08fd7a2dfb3dfc
# apply patch to liquidhaskell
git apply ../patches/ifl25-liquidhaskell.patch
cd ..

# clone the liquid-fixpoint repository at a known commit in the develop branch
git clone https://github.com/ucsd-progsys/liquid-fixpoint.git
cd liquid-fixpoint
git checkout 556104ba5508891c357b0bdf819ce706e93d9349
# apply patch to liquid-fixpoint
git apply ../patches/ifl25-liquid-fixpoint.patch
cd ..

# build liquidhaskell and liquid-prelude
cabal update
cabal build liquid-prelude

# run liquidhaskell on the example files
time cabal exec -- ghc -fforce-recomp -fplugin=LiquidHaskell examples/Subst1.hs
time cabal exec -- ghc -fforce-recomp -fplugin=LiquidHaskell examples/Subst2.hs
time cabal exec -- ghc -fforce-recomp -fplugin=LiquidHaskell examples/Unif.hs examples/State.hs
