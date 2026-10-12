/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.SeventhCyclotomic.Basic
import TauCeti.FieldTheory.IntermediateField.Quadratic

/-!
# The Gaussian-period presentation of the seventh cyclotomic quadratic subfield

The Gaussian period `1 + 2(ζ₇ + ζ₇² + ζ₇⁴)` squares to `-7` and generates the field fixed
by the square of the automorphism with exponent three. This identifies the intrinsic quadratic
fixed field with `ℚ(√-7)`. The exponent-three automorphism negates the generator, so its
restriction is the nontrivial quadratic automorphism.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section
noncomputable section

open IsCyclotomicExtension IntermediateField

namespace TauCeti.NumberField

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

private instance : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The quadratic subfield is Galois over `ℚ`, so absolute automorphisms restrict to it. -/
instance : IsGalois ℚ (seventhCyclotomicQuadraticSubfield (L := L)) := by
  have : IsMulCommutative (L ≃ₐ[ℚ] L) :=
    (Rat.galEquivZMod 7 L).symm.surjective.isMulCommutative
      inferInstance
  rw [seventhCyclotomicQuadraticSubfield_def]
  infer_instance

/-- The Gaussian period giving a square root of `-7` in the seventh cyclotomic field. -/
def seventhCyclotomicSqrtNegSeven : L :=
  1 + 2 * (zeta 7 ℚ L + zeta 7 ℚ L ^ 2 + zeta 7 ℚ L ^ 4)

/-- The square-root generator in terms of the chosen primitive seventh root of unity. -/
theorem seventhCyclotomicSqrtNegSeven_def :
    seventhCyclotomicSqrtNegSeven (L := L) =
      1 + 2 * (zeta 7 ℚ L + zeta 7 ℚ L ^ 2 + zeta 7 ℚ L ^ 4) := (rfl)

private theorem seventhCyclotomic_geom_sum :
    1 + zeta 7 ℚ L + zeta 7 ℚ L ^ 2 + zeta 7 ℚ L ^ 3 +
      zeta 7 ℚ L ^ 4 + zeta 7 ℚ L ^ 5 + zeta 7 ℚ L ^ 6 = 0 := by
  simpa [Finset.sum_range_succ] using (zeta_spec 7 ℚ L).geom_sum_eq_zero (by decide)

/-- The Gaussian period is a square root of `-7`. -/
@[simp] theorem seventhCyclotomicSqrtNegSeven_sq :
    seventhCyclotomicSqrtNegSeven (L := L) ^ 2 = -7 := by
  rw [seventhCyclotomicSqrtNegSeven_def]
  linear_combination
    (4 * zeta 7 ℚ L ^ 2 - 4 * zeta 7 ℚ L + 8) * seventhCyclotomic_geom_sum (L := L)

private theorem frobeniusThreeSeven_apply_zeta :
    frobeniusThreeSeven (L := L) (zeta 7 ℚ L) = zeta 7 ℚ L ^ 3 := by
  have h := (zeta_spec 7 ℚ L).autToPow_spec ℚ (frobeniusThreeSeven (L := L))
  rw [autToPow_frobeniusThreeSeven] at h
  exact h.symm

/-- The Frobenius with exponent three acts nontrivially on the square root of `-7`. -/
@[simp] theorem frobeniusThreeSeven_apply_sqrtNegSeven :
    frobeniusThreeSeven (L := L) (seventhCyclotomicSqrtNegSeven (L := L)) =
      -seventhCyclotomicSqrtNegSeven (L := L) := by
  rw [seventhCyclotomicSqrtNegSeven_def]
  simp only [map_add, map_mul, map_ofNat, map_one, map_pow,
    frobeniusThreeSeven_apply_zeta, ← pow_mul]
  rw [pow_eq_pow_mod 12 (zeta_spec 7 ℚ L).pow_eq_one]
  norm_num
  linear_combination 2 * seventhCyclotomic_geom_sum (L := L)

/-- The square root of `-7` belongs to the quadratic fixed field. -/
-- Apply before the general fixed-field membership expansion.
@[simp high] theorem sqrtNegSeven_mem_seventhCyclotomicQuadraticSubfield :
    seventhCyclotomicSqrtNegSeven (L := L) ∈ seventhCyclotomicQuadraticSubfield (L := L) := by
  simp [pow_two, AlgEquiv.mul_apply]

/-- The quadratic subfield of the seventh cyclotomic field is `ℚ(√-7)`, with the explicit
Gaussian-period square root as generator. -/
theorem seventhCyclotomicQuadraticSubfield_eq_adjoin_sqrtNegSeven :
    seventhCyclotomicQuadraticSubfield (L := L) =
      IntermediateField.adjoin ℚ {seventhCyclotomicSqrtNegSeven (L := L)} := by
  symm
  apply IntermediateField.eq_of_le_of_finrank_eq
    (IntermediateField.adjoin_simple_le_iff.mpr sqrtNegSeven_mem_seventhCyclotomicQuadraticSubfield)
  rw [finrank_seventhCyclotomicQuadraticSubfield]
  exact TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare (a := (-7 : ℚ))
    (by simpa only [map_neg, map_ofNat] using seventhCyclotomicSqrtNegSeven_sq (L := L))
    (fun h ↦ by have := h.nonneg; norm_num at this)

/-- Restriction to `ℚ(√-7)` negates its Gaussian-period generator. -/
@[simp] theorem restrictNormal_frobeniusThreeSeven_apply_sqrtNegSeven :
    (frobeniusThreeSeven (L := L)).restrictNormal
        (seventhCyclotomicQuadraticSubfield (L := L))
        ⟨seventhCyclotomicSqrtNegSeven, sqrtNegSeven_mem_seventhCyclotomicQuadraticSubfield⟩ =
      -⟨seventhCyclotomicSqrtNegSeven, sqrtNegSeven_mem_seventhCyclotomicQuadraticSubfield⟩ := by
  apply Subtype.ext
  simp [AlgEquiv.restrictNormal_apply]

/-- The exponent-three automorphism restricts to a nonidentity automorphism of `ℚ(√-7)`. -/
theorem restrictNormal_frobeniusThreeSeven_ne_one :
    (frobeniusThreeSeven (L := L)).restrictNormal
      (seventhCyclotomicQuadraticSubfield (L := L)) ≠ 1 := by
  intro h
  have ha := restrictNormal_frobeniusThreeSeven_apply_sqrtNegSeven (L := L)
  rw [h, AlgEquiv.one_apply] at ha
  have ha' := congrArg (fun x : seventhCyclotomicQuadraticSubfield (L := L) ↦ (x : L)) ha
  simp only [IntermediateField.coe_neg] at ha'
  have hzero : (2 : L) * seventhCyclotomicSqrtNegSeven (L := L) = 0 := by
    linear_combination ha'
  have hr : seventhCyclotomicSqrtNegSeven (L := L) ≠ 0 := by
    intro hz
    have hs := seventhCyclotomicSqrtNegSeven_sq (L := L)
    rw [hz] at hs
    norm_num at hs
  exact mul_ne_zero (by norm_num) hr hzero

end TauCeti.NumberField

end
