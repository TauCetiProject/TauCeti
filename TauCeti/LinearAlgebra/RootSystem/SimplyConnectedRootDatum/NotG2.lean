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
# Every valid pinned rational root system except G₂ is not G₂

Among the valid irreducible crystallographic Dynkin types, only `G₂` has a Cartan integer of
absolute value three. For types `B`, `C`, and `F₄`, the explicit coordinate models bound every
Cartan integer in absolute value by two; for the simply-laced types `A`, `D`, `E₆`, `E₇`, and `E₈`,
the Cartan pairing is symmetric (`TauCeti.DynkinType.pairing_simplyConnectedRootDatum_comm`), which
rules out the asymmetric `(-1, -3)` and `(1, 3)` pairings of `G₂`.

Consequently `(t.rationalRootSystem ht).IsNotG2` holds for every valid Dynkin type `t ≠ G2`
(`TauCeti.DynkinType.isNotG2_rationalRootSystem_of_ne_G2`), making the root-string bounds outside
`G₂` available across all non-`G₂` families.

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

/-- The rational root system of any valid simply-laced Dynkin type is not `G₂`, since its Cartan
pairing is symmetric. -/
theorem isNotG2_rationalRootSystem_of_isSimplyLaced {t : DynkinType} (ht : t.Valid)
    (hs : t.IsSimplyLaced) : (t.rationalRootSystem ht).IsNotG2 :=
  isNotG2_rationalRootSystem_of_abs_pairing_le_two fun i j => by
    have heq (a b : Fin t.numRoots) :
        (t.rationalRootSystem ht).pairingIn ℤ a b =
          (t.simplyConnectedRootDatum ht).pairing a b := by
      rw [pairingIn_rationalRootSystem]
      exact (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ a b
    have hcomm :
        (t.rationalRootSystem ht).pairingIn ℤ i j =
          (t.rationalRootSystem ht).pairingIn ℤ j i := by
      rw [heq, heq, t.pairing_simplyConnectedRootDatum_comm ht hs]
    have hmem := (t.rationalRootSystem ht).pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
    rw [← hcomm, heq] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_eq_zero,
      Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at hmem
    rw [abs_le]
    omega

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

/-- Every valid Dynkin type other than `G2` has a rational root system satisfying `IsNotG2`. -/
theorem isNotG2_rationalRootSystem_of_ne_G2 {t : DynkinType} (ht : t.Valid) (h : t ≠ G2) :
    (t.rationalRootSystem ht).IsNotG2 := by
  cases t with
  | G2 => exact absurd rfl h
  | _ => infer_instance

end TauCeti.DynkinType
