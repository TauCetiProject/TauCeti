/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DoubleChain
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Double-chain bounds for the pinned datum

Outside type `G₂`, the Cartan integers of the pinned integral datum lie in
`{-2, -1, 0, 1, 2}`. This transports Mathlib's `RootPairing.IsNotG2` bound from the
rational root system, and supplies the hypothesis of the general double-chain API in
`TauCeti.LinearAlgebra.RootSystem.DoubleChain`. The root-string coefficients, pairings,
and non-root exclusions themselves are proved there for arbitrary finite reduced
crystallographic root pairings, without requiring irreducibility.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

/-- Outside type `G₂`, the pinned datum has Cartan integers bounded by two, as required
by the general double-chain lemmas. -/
theorem pairingIn_mem_zero_one_two_of_ne_G2 {t : DynkinType} {ht : t.Valid}
    (h : t ≠ .G2) (α β : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).pairingIn ℤ α β ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
  let := t.isNotG2_rationalRootSystem ht h
  simpa using RootPairing.IsNotG2.pairingIn_mem_zero_one_two
    (P := t.rationalRootSystem ht) α β

end TauCeti.DynkinType
