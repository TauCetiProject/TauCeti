/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.Binary
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# Hilbert symbols of isometric binary forms

Isometric regular binary diagonal forms have the same norm-equation Hilbert symbol. This is the
binary-step input for descending the pairwise product of Hilbert symbols along a diagonal chain,
and hence for defining the local Hasse invariant on isometry classes.

The assertion holds over any field in which two is invertible.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, Proposition 3.18.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1.
-/

public section

open QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- Isometric regular binary diagonal forms have the same norm-equation Hilbert symbol. -/
theorem hilbertSymbol_eq_of_equivalent_binary {a b c d : Kˣ}
    (h : (weightedSumSquares K ![(a : K), b]).Equivalent
      (weightedSumSquares K ![(c : K), d])) :
    hilbertSymbol a b = hilbertSymbol c d :=
  hilbertSymbol_eq_of_nonempty_algEquiv
    (QuaternionAlgebra.nonempty_algEquiv_of_equivalent_binary (a : K) b c d h)

end TauCeti
