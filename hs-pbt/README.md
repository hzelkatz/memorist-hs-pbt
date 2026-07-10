# QuickChecking the Cost of Laziness over Infinite Structures (Artifact)

This artifact, accompanying the paper "QuickChecking the Cost of Laziness over Infinite Structures",
contains a QuickCheck-based property-based testing framework implemented in Haskell for testing specifications about lazy evaluation cost of functions and programs.
It also contains several case studies, such as some common first- and higher-order list functions (including the `replicate` function that works on potentially infinite lists), the insertion sort and merge sort algorithms, the batched queue and Okasaki's banker's queue.


## Getting Started

### Haskell and GHC

The framework is implemented in the functional language Haskell, specifically with the GHC 2021 language set, and requires [GHC, the Glasgow Haskell Compiler](https://www.haskell.org/ghc/), for compilation.

We have used GHC version 9.10.3, which can be installed using [`ghcup`](https://www.haskell.org/ghcup/) or [Stack](https://docs.haskellstack.org/en/stable/).
The implementation might work with newer versions of GHC, although we have not tested yet.

<!-- TODO: step-by-step instruction on how to install this version of GHC. -->

This version of GHC also requires `cabal-install` version 3.10.2.0 or later.

More information about GHC 9.10.3 can be found [here](https://www.haskell.org/ghc/download_ghc_9_10_3.html).


### Compiling Source Code

Run
```
stack build
```

Alternatively, if `cabal` is preferred:
```
cabal build
```

##  Formalization Dependencies

This implementation is based on a lazy variant of the Memorist Semantics we developed.
The Memorist Semantics is originally introduced by [Li et al. (2026)](https://doi.org/10.1007/978-3-032-22720-1_17).


## Directory Structure

<!-- TODO: update accordingly -->

The directory is structured as follows:
* `Memorist/`
  * `Base/`
    * `ANT.hs` - the Memorist monad based on our variant of the Memorist Semantics that uses ancestral thunk naming (our main contribution)
    * `Core.hs` - core monadic structures underlying the Memorist monad
    * `Extension.hs` - some useful monadic combinators
    * `Strict.hs` - a version of Memorist monad based directly on the original version of the Semantics for comparison
    * `Thunk.hs` - thunk representations and related components
  * `Data/`
    * `Interface/`
      * `Data.hs` - interface for Memorist representation types
      * `Demand.hs` - interface for demand representation types
    * `Interface.hs`
    * `List.hs` - Memorist representation and demand for lists
  * `Example/` - case studies
    * `Queue/`
      * `Bankers.hs` - Okasaki's banker's queue
      * `Base.hs` - queue interface and traces
      * `Batched.hs` - the batched queue
      * `BatchedLazy.hs` - the batched queue with lazy lists
    * `List.hs` - functions on lists
    * `ListSort.hs` - sorting algorithms on lists, including insertion sort and merge sort
    * `Util.hs`
  * `Infer/`
    * `Infer.hs` - lazy cost derivation and testing interface
  * `Memorist.hs` - re-exporting the Memorist monad
