/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SimplyLaced

/-!
# The pinned root systems outside G₂

The Cartan integers of the pinned rational systems of simply-laced types and types B, C,
and F₄ have absolute value at most two. These instances make the root-string bounds outside
G₂ available for collecting positive root subgroups and for punctured-positive normalization.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plates I–VIII.
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

/-- The Cartan integers of the rational F₄ system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemF4 (ht : F4.Valid) :
    (F4.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_abs_pairing_le_two (by
    rw [simplyConnectedRootDatum_F4]
    exact abs_pairing_f4SimplyConnectedRootDatum_le_two)

private theorem isNotG2_rationalRootSystem_of_isSimplyLaced {t : DynkinType} {ht : t.Valid}
    (hs : t.IsSimplyLaced) : (t.rationalRootSystem ht).IsNotG2 := by
  apply isNotG2_rationalRootSystem_of_abs_pairing_le_two
  intro i j
  have h := (t.simplyConnectedRootDatum ht).pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have heq (a b : Fin t.numRoots) :
      (t.simplyConnectedRootDatum ht).pairingIn ℤ a b =
        (t.simplyConnectedRootDatum ht).pairing a b :=
    (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ a b
  simp only [heq, t.pairing_simplyConnectedRootDatum_comm ht hs j i,
    Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rw [abs_le]
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

/-- The rational type-A root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemA (n : ℕ) (ht : (A n).Valid) :
    ((A n).rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced (isSimplyLaced_A n)

/-- The rational type-D root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemD (n : ℕ) (ht : (D n).Valid) :
    ((D n).rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced (isSimplyLaced_D n)

/-- The rational E₆ root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemE6 (ht : E6.Valid) :
    (E6.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced isSimplyLaced_E6

/-- The rational E₇ root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemE7 (ht : E7.Valid) :
    (E7.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced isSimplyLaced_E7

/-- The rational E₈ root system has no triple root strings. -/
instance instIsNotG2RationalRootSystemE8 (ht : E8.Valid) :
    (E8.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced isSimplyLaced_E8

/-- The pinned rational root system of every Dynkin type other than G₂ has no triple
root strings. -/
theorem isNotG2_rationalRootSystem_of_ne_G2 {t : DynkinType} {ht : t.Valid}
    (h : t ≠ G2) : (t.rationalRootSystem ht).IsNotG2 := by
  cases t <;> first | exact (h rfl).elim | infer_instance

end TauCeti.DynkinType
