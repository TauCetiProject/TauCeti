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
# Rational root systems of Dynkin types other than G₂

Every valid Dynkin type other than `G₂` has Cartan integers between `-2` and `2`, so its pinned
rational root system satisfies `RootPairing.IsNotG2`. For types `B`, `C`, and `F₄` this uses the
root-datum pairing bounds; for simply laced types symmetry of the Cartan pairing excludes unequal
off-diagonal Cartan integers.

## Main declarations

* `TauCeti.DynkinType.isNotG2_rationalRootSystem_of_isSimplyLaced`: simply laced types satisfy
  `IsNotG2`.
* `TauCeti.DynkinType.isNotG2_rationalRootSystem_of_ne_G2`: every valid Dynkin type `t ≠ G2`
  satisfies `(t.rationalRootSystem ht).IsNotG2`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1.3 and Plates I–VIII.
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

/-- The rational root system of any valid simply laced Dynkin type satisfies `IsNotG2`. -/
theorem isNotG2_rationalRootSystem_of_isSimplyLaced {t : DynkinType} (ht : t.Valid)
    (hs : t.IsSimplyLaced) : (t.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_abs_pairing_le_two fun i j => by
    have hmem := (t.simplyConnectedRootDatum ht).pairingIn_pairingIn_mem_set_of_isCrystallographic
      i j
    have hi : (t.simplyConnectedRootDatum ht).pairingIn ℤ i j =
        (t.simplyConnectedRootDatum ht).pairing i j := by
      simpa using (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ i j
    have hj : (t.simplyConnectedRootDatum ht).pairingIn ℤ j i =
        (t.simplyConnectedRootDatum ht).pairing j i := by
      simpa using (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ j i
    rw [hi, hj, ← t.pairing_simplyConnectedRootDatum_comm ht hs i j] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rw [abs_le]
    rcases hmem with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
      ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
      ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- The Cartan integers of the rational type-A system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemA (n : ℕ) (hn : (A n).Valid) :
    ((A n).rationalRootSystem hn).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced hn (isSimplyLaced_A n)

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

/-- The Cartan integers of the rational type-D system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemD (n : ℕ) (hn : (D n).Valid) :
    ((D n).rationalRootSystem hn).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced hn (isSimplyLaced_D n)

/-- The Cartan integers of the rational type-E₆ system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemE6 (ht : E6.Valid) :
    (E6.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced ht isSimplyLaced_E6

/-- The Cartan integers of the rational type-E₇ system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemE7 (ht : E7.Valid) :
    (E7.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced ht isSimplyLaced_E7

/-- The Cartan integers of the rational type-E₈ system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemE8 (ht : E8.Valid) :
    (E8.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_isSimplyLaced ht isSimplyLaced_E8

/-- The Cartan integers of the rational type-F₄ system lie between `-2` and `2`. -/
instance instIsNotG2RationalRootSystemF4 (ht : F4.Valid) :
    (F4.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_abs_pairing_le_two (by
    rw [simplyConnectedRootDatum_F4]
    exact abs_pairing_f4SimplyConnectedRootDatum_le_two)

/-- Every valid Dynkin type other than `G₂` has rational root system satisfying `IsNotG2`. -/
theorem isNotG2_rationalRootSystem_of_ne_G2 {t : DynkinType} (ht : t.Valid) (hne : t ≠ G2) :
    (t.rationalRootSystem ht).IsNotG2 := by
  cases t with
  | A n => infer_instance
  | B n => infer_instance
  | C n => infer_instance
  | D n => infer_instance
  | E6 => infer_instance
  | E7 => infer_instance
  | E8 => infer_instance
  | F4 => infer_instance
  | G2 => exact (hne rfl).elim

end TauCeti.DynkinType
