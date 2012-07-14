{-
  This summary is based on lots of messy and exploratory sketching in:
  https://github.com/larrytheliquid/type-isomorphisms
-}

module FiniteIsomorphicTypes where

{-
  The main development including ⊤, ⊥, ⊎, and ×.
  This contains a definition of the coerce function as well as 
  a proof of one direction of the bijection of the functions 
  it is composed of.
-}
import FiniteIsomorphicTypes.Basic

{-
  This contains some rudimentary work on extending the basic universe
  with dependent pairs (Σ).
-}
import FiniteIsomorphicTypes.DependentPair

{-
  This contains some rudimentary work on extending the basic universe
  with functions (→).
-}
import FiniteIsomorphicTypes.Function

{-
  A woefully incomplete look at how ⊤, ⊥, ⊎, ×, →, Σ, Π, and W
  might look together.
-}
import FiniteIsomorphicTypes.Incomplete

