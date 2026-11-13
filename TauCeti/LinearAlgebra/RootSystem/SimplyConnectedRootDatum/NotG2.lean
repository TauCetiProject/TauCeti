/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SimplyLaced
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2

/-!
# Simply-laced and doubly-laced root systems are not G₂

Simply-laced types satisfy the hypothesis by symmetry of their Cartan pairing.
The Cartan integers of the pinned rational systems of types B, C and F₄ have absolute value at
most two. These instances make the root-string bounds outside G₂ available for the classical
families in arbitrary valid rank and for F₄, in particular for collecting their positive root
subgroups.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plates II, III and VIII.
-/

public section

namespace TauCeti.DynkinType

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

/-- A simply-laced pinned rational root system is not G₂. -/
theorem isNotG2_rationalRootSystem_of_isSimplyLaced
    {t : DynkinType} {ht : t.Valid} (hs : t.IsSimplyLaced) :
    (t.rationalRootSystem ht).IsNotG2 := by
  apply isNotG2_rationalRootSystem_of_abs_pairing_le_two
  intro i j
  have hred := t.isReduced_simplyConnectedRootDatum ht
  have h := (t.simplyConnectedRootDatum ht).pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have heq (a b : Fin t.numRoots) :
      (t.simplyConnectedRootDatum ht).pairingIn ℤ a b =
        (t.simplyConnectedRootDatum ht).pairing a b :=
    (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ a b
  simp only [heq, t.pairing_simplyConnectedRootDatum_comm ht hs j i,
    Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rw [abs_le]
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

/-- The Cartan integers of the rational type-F₄ system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemF4 (ht : F4.Valid) :
    (F4.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_abs_pairing_le_two (by
    rw [simplyConnectedRootDatum_F4]
    exact abs_pairing_f4SimplyConnectedRootDatum_le_two)

end TauCeti.DynkinType
