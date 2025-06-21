These files contain the source code for the paper
"Refinement-Types Driven Development"

The example code is written in Haskell and can be found in the
`examples` directory.

The code is built using Nix, a package manager to install the required
version of the GHC compiler and z3 SMT solver. The build script will
clone liquidhaskell and liquid-fixpoint from their official repositories,
it will apply patches prepared for IFL 2025, then it will build them,
and then it will check the examples.

To patch and build liquidhaskell and to verify the examples run

```bash
nix-shell --run scripts/build.sh
```

To clean up the generated artifacts run

```bash
scripts/clean.sh
```
