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
# Pinned rational root systems outside G₂

A valid pinned rational system whose Dynkin type is not G₂ has no triple root strings.
Instances make these root-string bounds available for types B and C in arbitrary valid rank
and for F₄, in particular for collecting their positive root subgroups.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plates II, III and VIII.
-/

public section

namespace TauCeti.DynkinType

/-- A valid pinned rational root system outside type G₂ has no triple root strings. -/
theorem isNotG2_rationalRootSystem (t : DynkinType) (ht : t.Valid) (hG2 : t ≠ G2) :
    (t.rationalRootSystem ht).IsNotG2 := by
  apply (RootPairing.not_isG2_iff_isNotG2 _).mp
  intro h
  exact hG2 ((hasCartanType_rationalRootSystem t ht).eq_of_valid
    (hasCartanType_G2_of_isG2 h (t.rationalBase ht)) ht (by decide))

/-- The rational F₄ system has no triple root strings. -/
instance instIsNotG2RationalRootSystemF4 (ht : F4.Valid) :
    (F4.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem F4 ht (by intro h; cases h)

private theorem isNotG2_rationalRootSystem_of_abs_pairing_le_two
    {t : DynkinType} {ht : t.Valid}
    (hbound : ∀ i j, |(t.simplyConnectedRootDatum ht).pairing i j| ≤ 2) :
    (t.rationalRootSystem ht).IsNotG2 where
  pairingIn_mem_zero_one_two i j := by
    have heq : (t.rationalRootSystem ht).pairingIn ℤ i j =
        (t.simplyConnectedRootDatum ht).pairing i j := by
      rw [pairingIn_rationalRootSystem]
      exact (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ i j
    have h := abs_le.mp (hbound i j)
    rw [heq]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

/-- The Cartan integers of the rational type-B system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemB (n : ℕ) (hn : (B n).Valid) :
    ((B n).rationalRootSystem hn).IsNotG2 :=
  isNotG2_rationalRootSystem_of_abs_pairing_le_two (by
    rw [simplyConnectedRootDatum_B]
    exact abs_pairing_typeBSimplyConnectedRootDatum_le_two)

/-- The Cartan integers of the rational type-C system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemC (n : ℕ) (hn : (C n).Valid) :
    ((C n).rationalRootSystem hn).IsNotG2 :=
  isNotG2_rationalRootSystem_of_abs_pairing_le_two (by
    rw [simplyConnectedRootDatum_C]
    exact abs_pairing_typeCSimplyConnectedRootDatum_le_two)

end TauCeti.DynkinType
