/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.DoubleCoset

/-!
# Changing the compatible compact-open tuple

Let `U` and `U'` be compatible compact-open tuples for a rational quadratic form whose
orthogonal and Spin reference families agree at almost every prime; for instance `U'` may be the
shrinking `U.infOpenSubgroup W hW` of `U` at finitely many primes. The finite adelic groups
`O(V)(𝔸_f)`, `SO(V)(𝔸_f)` and `Spin(V)(𝔸_f)` built from the two tuples are then identified by
`TauCeti.restrictedProductCongr`, which is the identity on coordinates. This file shows that these
identifications carry the rational diagonal of one tuple to the rational diagonal of the other;
these are the orthogonal instances of `TauCeti.rationalDiagonal_change_family`.

They need not identify the everywhere-integral subgroups: by
`TauCeti.map_integralSubgroup_restrictedProductCongr_eq_iff` they do so only when the reference
families agree at every prime. So for two tuples differing at a single prime, transport along the
identification matches the class set `G(ℚ) \ G(𝔸_f) / ∏_p U_p` with the quotient by the image of
`∏_p U_p`, which is not `∏_p U'_p`. What there is, when one tuple is contained in the other at every
prime, is the comparison map of class sets obtained by transporting along the identification and
then enlarging the right compact-open subgroup with `DoubleCoset.quotientMapOfLERight`. That map
sends the class of an adele to the class of the same adele, and it is surjective.

## Main results

* `OrthogonalCompactOpens.restrictedProductCongr_finiteAdelicOrthogonalDiagonal`, and its special
  orthogonal and Spin versions: the identifications commute with the rational diagonals.
* `OrthogonalCompactOpens.map_integralSubgroup_infOpenSubgroup_orthogonal_eq_iff`: shrinking a
  tuple at some prime changes the everywhere-integral subgroup, even after the identification.
* `OrthogonalCompactOpens.finiteAdelicOrthogonalDoubleCosetMapOfTupleLE`, and its special
  orthogonal and Spin versions: the comparison of class sets for nested tuples, with its value on
  representatives and its surjectivity.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101–102.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open Filter
open _root_.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (U U' : OrthogonalCompactOpens Q)

/-! ### The rational diagonals -/

/-- Changing to an eventually equal orthogonal reference family preserves the rational
diagonal. -/
@[simp]
theorem restrictedProductCongr_finiteAdelicOrthogonalDiagonal
    (h : ∀ᶠ p in cofinite, U.orthogonal p = U'.orthogonal p) (g : orthogonalGroup Q) :
    restrictedProductCongr U.orthogonal U'.orthogonal h (U.finiteAdelicOrthogonalDiagonal g) =
      U'.finiteAdelicOrthogonalDiagonal g := by
  ext p
  simp

/-- Changing to an eventually equal orthogonal reference family carries the rational orthogonal
points onto the rational orthogonal points. -/
theorem map_range_finiteAdelicOrthogonalDiagonal
    (h : ∀ᶠ p in cofinite, U.orthogonal p = U'.orthogonal p) :
    U.finiteAdelicOrthogonalDiagonal.range.map
        (restrictedProductCongr U.orthogonal U'.orthogonal h :
          U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal) =
      U'.finiteAdelicOrthogonalDiagonal.range := by
  rw [MonoidHom.map_range]
  congr 1
  ext g : 1
  simp

/-- Changing to an eventually equal Spin reference family preserves the rational diagonal. -/
@[simp]
theorem restrictedProductCongr_finiteAdelicSpinDiagonal
    (h : ∀ᶠ p in cofinite, U.spin p = U'.spin p) (x : spinGroup Q) :
    restrictedProductCongr U.spin U'.spin h (U.finiteAdelicSpinDiagonal x) =
      U'.finiteAdelicSpinDiagonal x := by
  ext p
  simp

/-- Changing to an eventually equal Spin reference family carries the rational Spin points onto
the rational Spin points. -/
theorem map_range_finiteAdelicSpinDiagonal (h : ∀ᶠ p in cofinite, U.spin p = U'.spin p) :
    U.finiteAdelicSpinDiagonal.range.map
        (restrictedProductCongr U.spin U'.spin h :
          U.finiteAdelicSpin →* U'.finiteAdelicSpin) =
      U'.finiteAdelicSpinDiagonal.range := by
  rw [MonoidHom.map_range]
  congr 1
  ext x : 1
  simp

section SpecialOrthogonal

variable [FiniteDimensional ℚ V]

/-- Changing to an eventually equal special orthogonal reference family preserves the rational
diagonal. -/
@[simp]
theorem restrictedProductCongr_finiteAdelicSpecialOrthogonalDiagonal
    (h : ∀ᶠ p in cofinite, U.specialOrthogonal p = U'.specialOrthogonal p)
    (g : specialOrthogonalGroup Q) :
    restrictedProductCongr U.specialOrthogonal U'.specialOrthogonal h
        (U.finiteAdelicSpecialOrthogonalDiagonal g) =
      U'.finiteAdelicSpecialOrthogonalDiagonal g := by
  ext p
  simp

/-- Changing to an eventually equal special orthogonal reference family carries the rational
special orthogonal points onto the rational special orthogonal points. -/
theorem map_range_finiteAdelicSpecialOrthogonalDiagonal
    (h : ∀ᶠ p in cofinite, U.specialOrthogonal p = U'.specialOrthogonal p) :
    U.finiteAdelicSpecialOrthogonalDiagonal.range.map
        (restrictedProductCongr U.specialOrthogonal U'.specialOrthogonal h :
          U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) =
      U'.finiteAdelicSpecialOrthogonalDiagonal.range := by
  rw [MonoidHom.map_range]
  congr 1
  ext g : 1
  simp

end SpecialOrthogonal

/-! ### Integral subgroups of a shrunken tuple -/

/-- Shrinking a tuple by open subgroups `W` leaves the ambient finite adelic orthogonal group
unchanged up to `restrictedProductCongr`, but that identification carries `∏_p (U_p^O ⊓ W_p)`
onto `∏_p U_p^O` only when the shrinking is trivial at every prime. -/
theorem map_integralSubgroup_infOpenSubgroup_orthogonal_eq_iff [FiniteDimensional ℚ V]
    (W : ∀ p : Nat.Primes, OpenSubgroup (orthogonalGroup (Q.baseChange ℚ_[p])))
    (hW : ∀ᶠ p in cofinite, U.orthogonal p ≤ W p) :
    (integralSubgroup (U.infOpenSubgroup W hW).orthogonal).map
        (restrictedProductCongr (U.infOpenSubgroup W hW).orthogonal U.orthogonal
            (U.eventually_infOpenSubgroup_orthogonal_eq W hW) :
          (U.infOpenSubgroup W hW).finiteAdelicOrthogonal →* U.finiteAdelicOrthogonal) =
      integralSubgroup U.orthogonal ↔ ∀ p, U.orthogonal p ≤ W p := by
  rw [map_integralSubgroup_restrictedProductCongr_eq_iff, funext_iff]
  simp

/-! ### Comparison of class sets for nested tuples -/

/-- The comparison of finite adelic orthogonal class sets for tuples `U ≤ U'` agreeing at almost
every prime: transport along `restrictedProductCongr`, then enlarge the right subgroup from the
image of `∏_p U_p^O` to `∏_p U'_p^O`. -/
def finiteAdelicOrthogonalDoubleCosetMapOfTupleLE
    (hle : ∀ p, U.orthogonal p ≤ U'.orthogonal p)
    (h : ∀ᶠ p in cofinite, U.orthogonal p = U'.orthogonal p) :
    U.finiteAdelicOrthogonalDoubleCoset → U'.finiteAdelicOrthogonalDoubleCoset :=
  DoubleCoset.quotientMapOfLERight U'.finiteAdelicOrthogonalDiagonal.range
      ((integralSubgroupOf_le_integralSubgroup_iff _ _).mpr hle) ∘
    DoubleCoset.quotientCongr U.finiteAdelicOrthogonalDiagonal.range
      (integralSubgroup U.orthogonal) (restrictedProductCongr U.orthogonal U'.orthogonal h)
      (U.map_range_finiteAdelicOrthogonalDiagonal U' h)
      (map_integralSubgroup_restrictedProductCongr _ _ h)

/-- The orthogonal comparison of class sets sends the class of an adele to the class of the same
adele. -/
@[simp]
theorem finiteAdelicOrthogonalDoubleCosetMapOfTupleLE_apply_mk
    (hle : ∀ p, U.orthogonal p ≤ U'.orthogonal p)
    (h : ∀ᶠ p in cofinite, U.orthogonal p = U'.orthogonal p) (x : U.finiteAdelicOrthogonal) :
    U.finiteAdelicOrthogonalDoubleCosetMapOfTupleLE U' hle h
        (DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
          (integralSubgroup U.orthogonal) x) =
      DoubleCoset.mk U'.finiteAdelicOrthogonalDiagonal.range (integralSubgroup U'.orthogonal)
        (restrictedProductCongr U.orthogonal U'.orthogonal h x) := by
  rw [finiteAdelicOrthogonalDoubleCosetMapOfTupleLE, Function.comp_apply,
    DoubleCoset.quotientCongr_apply_mk, DoubleCoset.quotientMapOfLERight_apply_mk]

/-- The orthogonal comparison of class sets is surjective. -/
theorem finiteAdelicOrthogonalDoubleCosetMapOfTupleLE_surjective
    (hle : ∀ p, U.orthogonal p ≤ U'.orthogonal p)
    (h : ∀ᶠ p in cofinite, U.orthogonal p = U'.orthogonal p) :
    Function.Surjective (U.finiteAdelicOrthogonalDoubleCosetMapOfTupleLE U' hle h) := by
  unfold finiteAdelicOrthogonalDoubleCosetMapOfTupleLE
  exact (DoubleCoset.quotientMapOfLERight_surjective _ _).comp (Equiv.surjective _)

/-- The comparison of finite adelic Spin class sets for tuples `U ≤ U'` agreeing at almost every
prime: transport along `restrictedProductCongr`, then enlarge the right subgroup from the image
of `∏_p U_p^{Spin}` to `∏_p U'_p^{Spin}`. -/
def finiteAdelicSpinDoubleCosetMapOfTupleLE
    (hle : ∀ p, U.spin p ≤ U'.spin p) (h : ∀ᶠ p in cofinite, U.spin p = U'.spin p) :
    U.finiteAdelicSpinDoubleCoset → U'.finiteAdelicSpinDoubleCoset :=
  DoubleCoset.quotientMapOfLERight U'.finiteAdelicSpinDiagonal.range
      ((integralSubgroupOf_le_integralSubgroup_iff _ _).mpr hle) ∘
    DoubleCoset.quotientCongr U.finiteAdelicSpinDiagonal.range
      (integralSubgroup U.spin) (restrictedProductCongr U.spin U'.spin h)
      (U.map_range_finiteAdelicSpinDiagonal U' h)
      (map_integralSubgroup_restrictedProductCongr _ _ h)

/-- The Spin comparison of class sets sends the class of an adele to the class of the same
adele. -/
@[simp]
theorem finiteAdelicSpinDoubleCosetMapOfTupleLE_apply_mk
    (hle : ∀ p, U.spin p ≤ U'.spin p) (h : ∀ᶠ p in cofinite, U.spin p = U'.spin p)
    (x : U.finiteAdelicSpin) :
    U.finiteAdelicSpinDoubleCosetMapOfTupleLE U' hle h
        (DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin) x) =
      DoubleCoset.mk U'.finiteAdelicSpinDiagonal.range (integralSubgroup U'.spin)
        (restrictedProductCongr U.spin U'.spin h x) := by
  rw [finiteAdelicSpinDoubleCosetMapOfTupleLE, Function.comp_apply,
    DoubleCoset.quotientCongr_apply_mk, DoubleCoset.quotientMapOfLERight_apply_mk]

/-- The Spin comparison of class sets is surjective. -/
theorem finiteAdelicSpinDoubleCosetMapOfTupleLE_surjective
    (hle : ∀ p, U.spin p ≤ U'.spin p) (h : ∀ᶠ p in cofinite, U.spin p = U'.spin p) :
    Function.Surjective (U.finiteAdelicSpinDoubleCosetMapOfTupleLE U' hle h) := by
  unfold finiteAdelicSpinDoubleCosetMapOfTupleLE
  exact (DoubleCoset.quotientMapOfLERight_surjective _ _).comp (Equiv.surjective _)

section SpecialOrthogonal

variable [FiniteDimensional ℚ V]

/-- The comparison of finite adelic special orthogonal class sets for tuples whose special
orthogonal reference families satisfy `U ≤ U'` and agree at almost every prime: transport along
`restrictedProductCongr`, then enlarge the right subgroup from the image of `∏_p U_p^{SO}` to
`∏_p U'_p^{SO}`. The hypotheses follow from the corresponding ones on the orthogonal families by
`specialOrthogonal_mono` and `eventually_specialOrthogonal_eq`. -/
def finiteAdelicSpecialOrthogonalDoubleCosetMapOfTupleLE
    (hle : ∀ p, U.specialOrthogonal p ≤ U'.specialOrthogonal p)
    (h : ∀ᶠ p in cofinite, U.specialOrthogonal p = U'.specialOrthogonal p) :
    U.finiteAdelicSpecialOrthogonalDoubleCoset → U'.finiteAdelicSpecialOrthogonalDoubleCoset :=
  DoubleCoset.quotientMapOfLERight U'.finiteAdelicSpecialOrthogonalDiagonal.range
      ((integralSubgroupOf_le_integralSubgroup_iff _ _).mpr hle) ∘
    DoubleCoset.quotientCongr U.finiteAdelicSpecialOrthogonalDiagonal.range
      (integralSubgroup U.specialOrthogonal)
      (restrictedProductCongr U.specialOrthogonal U'.specialOrthogonal h)
      (U.map_range_finiteAdelicSpecialOrthogonalDiagonal U' h)
      (map_integralSubgroup_restrictedProductCongr _ _ h)

/-- The special orthogonal comparison of class sets sends the class of an adele to the class of
the same adele. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalDoubleCosetMapOfTupleLE_apply_mk
    (hle : ∀ p, U.specialOrthogonal p ≤ U'.specialOrthogonal p)
    (h : ∀ᶠ p in cofinite, U.specialOrthogonal p = U'.specialOrthogonal p)
    (x : U.finiteAdelicSpecialOrthogonal) :
    U.finiteAdelicSpecialOrthogonalDoubleCosetMapOfTupleLE U' hle h
        (DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U.specialOrthogonal) x) =
      DoubleCoset.mk U'.finiteAdelicSpecialOrthogonalDiagonal.range
        (integralSubgroup U'.specialOrthogonal)
        (restrictedProductCongr U.specialOrthogonal U'.specialOrthogonal h x) := by
  rw [finiteAdelicSpecialOrthogonalDoubleCosetMapOfTupleLE, Function.comp_apply,
    DoubleCoset.quotientCongr_apply_mk, DoubleCoset.quotientMapOfLERight_apply_mk]

/-- The special orthogonal comparison of class sets is surjective. -/
theorem finiteAdelicSpecialOrthogonalDoubleCosetMapOfTupleLE_surjective
    (hle : ∀ p, U.specialOrthogonal p ≤ U'.specialOrthogonal p)
    (h : ∀ᶠ p in cofinite, U.specialOrthogonal p = U'.specialOrthogonal p) :
    Function.Surjective (U.finiteAdelicSpecialOrthogonalDoubleCosetMapOfTupleLE U' hle h) := by
  unfold finiteAdelicSpecialOrthogonalDoubleCosetMapOfTupleLE
  exact (DoubleCoset.quotientMapOfLERight_surjective _ _).comp (Equiv.surjective _)

end SpecialOrthogonal

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
