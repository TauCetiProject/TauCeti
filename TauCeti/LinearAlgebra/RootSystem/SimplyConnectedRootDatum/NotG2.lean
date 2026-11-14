/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import TauCeti.LinearAlgebra.RootSystem.RankTwo

/-!
# Pinned root systems outside G₂

The pinned rational root system is not G₂ when its Dynkin type is not G₂, and its Cartan
integers then have absolute value at most two. In types B and C, instances make these
root-string bounds available in arbitrary valid rank, in particular for collecting their
positive root subgroups.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plates II and III.
-/

public section

namespace TauCeti.DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- The rational root system has no triple bond unless its Dynkin type is `G₂`. -/
theorem isNotG2_rationalRootSystem (h : t ≠ .G2) :
    (t.rationalRootSystem ht).IsNotG2 := by
  rw [← RootPairing.not_isG2_iff_isNotG2]
  intro hG2
  exact h ((t.hasCartanType_rationalRootSystem ht).eq_of_valid
    (hasCartanType_G2_of_isG2 hG2 (t.rationalBase ht)) ht (by simp))

variable {t} in
/-- Outside type `G₂`, the pinned datum has Cartan integers bounded by two, as required
by the general double-chain lemmas. -/
theorem pairingIn_simplyConnectedRootDatum_mem_zero_one_two_of_ne_G2
    (h : t ≠ .G2) (α β : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).pairingIn ℤ α β ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
  let := t.isNotG2_rationalRootSystem ht h
  simpa using RootPairing.IsNotG2.pairingIn_mem_zero_one_two
    (P := t.rationalRootSystem ht) α β

/-- The Cartan integers of the rational type-B system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemB (n : ℕ) (hn : (B n).Valid) :
    ((B n).rationalRootSystem hn).IsNotG2 :=
  (B n).isNotG2_rationalRootSystem hn (by simp)

/-- The Cartan integers of the rational type-C system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemC (n : ℕ) (hn : (C n).Valid) :
    ((C n).rationalRootSystem hn).IsNotG2 :=
  (C n).isNotG2_rationalRootSystem hn (by simp)

end TauCeti.DynkinType
