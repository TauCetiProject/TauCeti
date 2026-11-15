/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# The Dedekind-sum formula for the eta multiplier

This file evaluates the Dedekind eta multiplier `TauCeti.ModularForm.etaMultiplier` across all of
`SL(2, ℤ)` in terms of the Dedekind sum `TauCeti.dedekindSum`.

For `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`,
`ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`, where the `-1/4` converts Apostol's
square root `√(-i(c τ + d))` to the principal square root `√(c τ + d)` used in `eta_smul`.
The proof applies the Euclidean uniqueness theorem `eq_etaMultiplier_of_c_pos` from
`TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation`: checking the `T`-step uses the
periodicity `s(c + d, c) = s(d, c)`, while checking the `S`-step uses Dedekind's reciprocity law
`dedekindSum_add_dedekindSum` together with `a d - b c = 1`.

Combining the `c > 0` formula with the negation and upper-triangular formulas in `Transformation`
yields explicit Dedekind-sum formulas for `c < 0`, for `ε(γ⁻¹)`, and for lower-triangular
transvections `(1 0; c 1)`.

## Main results

* `TauCeti.ModularForm.etaMultiplier_of_c_pos`, `TauCeti.ModularForm.eta_smul_of_c_pos`,
  `TauCeti.ModularForm.etaTransformation`: Dedekind's functional equation with the Dedekind sum.
* `TauCeti.ModularForm.etaMultiplier_of_c_neg`: explicit Dedekind-sum formula for `c < 0`.
* `TauCeti.ModularForm.etaMultiplier_inv_of_c_ne_zero`, `TauCeti.ModularForm.etaMultiplier_inv`:
  behavior of `ε` under matrix inversion.
* `TauCeti.ModularForm.etaMultiplier_of_a_eq_one_of_b_eq_zero`: `ε(1 0; c 1) = e^{-π i c / 12}`
  for every integer `c`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4.
-/

public section

open Complex ModularGroup
open scoped UpperHalfPlane Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### The Dedekind-sum formula -/

/-- **Dedekind's formula for the eta multiplier** (Apostol, Theorem 3.4): for `γ = (a b; c d)` in
`SL(2, ℤ)` with `c > 0`, `ε(γ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))`. -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  symm
  refine eq_etaMultiplier_of_c_pos
    (f := fun δ ↦ cexp (π * I *
      (((δ 0 0 + δ 1 1 : ℤ) : ℂ) / (12 * δ 1 0) - dedekindSum (δ 1 1) (δ 1 0) - 1 / 4)))
    (fun δ hδ ↦ ?_) (fun δ hδ ↦ ?_) (fun δ hδ0 hδ1 ↦ ?_) γ hc
  · rw [etaMultiplier_of_c_eq_one δ hδ, hδ, dedekindSum_one_right]
    push_cast
    congr 1
    ring
  · have hc' : (δ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ.ne'
    simp only [Matrix.SpecialLinearGroup.mul_T_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [dedekindSum_self_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  · have hc' : (δ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ0.ne'
    have hd' : (δ 1 1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ1.ne'
    have hcop : IsCoprime (δ 1 1) (δ 1 0) := (δ.isCoprime_row 1).symm
    have hrec := congrArg (Rat.cast : ℚ → ℂ) (dedekindSum_add_dedekindSum hδ1 hδ0 hcop)
    push_cast at hrec
    have hdet : (δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := δ.intCast_fin_two_mul_sub_mul_eq_one
    simp only [Matrix.SpecialLinearGroup.mul_S_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [dedekindSum_neg, ← Complex.exp_add]
    congr 1
    push_cast
    have hexp : (((δ 0 1 : ℂ) + -δ 1 0) / (12 * δ 1 1) - -(dedekindSum (δ 1 0) (δ 1 1) : ℂ) -
        1 / 4) -
        (-1 / 4 + (((δ 0 0 : ℂ) + δ 1 1) / (12 * δ 1 0) - dedekindSum (δ 1 1) (δ 1 0) - 1 / 4)) =
        (dedekindSum (δ 1 1) (δ 1 0) + dedekindSum (δ 1 0) (δ 1 1) -
          (((δ 1 1 : ℂ) ^ 2 + (δ 1 0 : ℂ) ^ 2 + 1) / (12 * δ 1 1 * δ 1 0) - 1 / 4)) -
        ((δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 - 1) / (12 * δ 1 1 * δ 1 0) := by
      field_simp
      ring
    have hzero : (((δ 0 1 : ℂ) + -δ 1 0) / (12 * δ 1 1) - -(dedekindSum (δ 1 0) (δ 1 1) : ℂ) -
        1 / 4) -
        (-1 / 4 + (((δ 0 0 : ℂ) + δ 1 1) / (12 * δ 1 0) - dedekindSum (δ 1 1) (δ 1 0) - 1 / 4)) =
        0 := by
      rw [hexp, hrec, hdet]
      simp
    linear_combination π * I * hzero

/-- **The transformation law of `η` for positive lower-left entry** (Apostol, Theorem 3.4). -/
theorem eta_smul_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    η (γ • τ : ℍ) = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) *
      Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [eta_smul, etaMultiplier_of_c_pos γ hc]

/-- **Dedekind's functional equation**: under each element `γ ∈ SL(2, ℤ)`, `η` transforms by a
24th root of unity times the principal square root of `c τ + d`, and when `c = γ 1 0 > 0` that root
of unity is given explicitly by the finite `Int.fract` Dedekind sum (Apostol, Theorem 3.4). -/
theorem etaTransformation (γ : SL(2, ℤ)) :
    ∃ ε : ℂ, ε ^ 24 = 1 ∧
      (∀ τ : ℍ, η (γ • τ : ℍ) =
        ε * Complex.sqrt ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * η τ) ∧
      (0 < γ 1 0 → ε = cexp (π * I *
        (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * (γ 1 0 : ℂ)) -
          ∑ r ∈ Finset.Ioo (0 : ℤ) (γ 1 0), ((r : ℂ) / (γ 1 0 : ℂ)) *
            (((Int.fract (((γ 1 1 * r : ℤ) : ℝ) / (γ 1 0 : ℝ)) : ℝ) : ℂ) - 1 / 2) -
          1 / 4))) := by
  refine ⟨etaMultiplier γ, etaMultiplier_pow_twentyFour γ, eta_smul γ, fun hc ↦ ?_⟩
  rw [etaMultiplier_of_c_pos γ hc]
  have hcast : (dedekindSum (γ 1 1) (γ 1 0) : ℂ) = ((dedekindSum (γ 1 1) (γ 1 0) : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, (γ.isCoprime_row 1).symm.ratCast_dedekindSum]
  push_cast
  rfl

/-! ### Negative `c`, inversion, and lower-triangular transvections -/

/-- Explicit Dedekind-sum formula for negative lower-left entry `c = γ 1 0 < 0`:
`ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`. -/
theorem etaMultiplier_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier γ = cexp (π * I *
      (((γ 0 0 + γ 1 1 : ℤ) : ℂ) / (12 * γ 1 0) + dedekindSum (γ 1 1) (-γ 1 0) + 1 / 4)) := by
  have hc' : 0 < (-γ) 1 0 := by simpa using hc
  have hneg := etaMultiplier_neg_of_c_pos hc'
  rw [neg_neg] at hneg
  have hpi : π * I / 2 = π / 2 * I := by ring
  have hmulI : ∀ z : ℂ, I * cexp z = cexp (π * I / 2 + z) := fun z ↦ by
    rw [Complex.exp_add, hpi, Complex.exp_pi_div_two_mul_I]
  rw [hneg, etaMultiplier_of_c_pos (-γ) hc', hmulI]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, dedekindSum_neg]
  have hc0 : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
  congr 1
  push_cast
  field_simp
  ring

/-- Whenever `γ 1 0 ≠ 0`, the eta multiplier of `γ⁻¹` is `(ε(γ))⁻¹`. -/
theorem etaMultiplier_inv_of_c_ne_zero {γ : SL(2, ℤ)} (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ⁻¹ = (etaMultiplier γ)⁻¹ := by
  have hpos : ∀ δ : SL(2, ℤ), 0 < δ 1 0 → etaMultiplier δ⁻¹ = (etaMultiplier δ)⁻¹ := by
    intro δ hδ
    have hinv_c : (δ⁻¹ : SL(2, ℤ)) 1 0 < 0 := by simpa using hδ
    have hmod : δ 0 0 * δ 1 1 ≡ 1 [ZMOD δ 1 0] :=
      Int.modEq_iff_dvd.mpr ⟨-δ 0 1, by linear_combination -δ.fin_two_mul_sub_mul_eq_one⟩
    rw [etaMultiplier_of_c_neg δ⁻¹ hinv_c, etaMultiplier_of_c_pos δ hδ, ← Complex.exp_neg]
    simp only [Matrix.SpecialLinearGroup.inv_apply_zero_zero,
      Matrix.SpecialLinearGroup.inv_apply_one_zero, Matrix.SpecialLinearGroup.inv_apply_one_one,
      neg_neg]
    rw [dedekindSum_eq_of_mul_modEq_one hmod]
    have hc' : (δ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hδ.ne'
    congr 1
    push_cast
    field_simp
    ring
  rcases hc.lt_or_gt with hc_neg | hc_pos
  · have hc_inv : 0 < (γ⁻¹ : SL(2, ℤ)) 1 0 := by simpa using hc_neg
    have h := hpos γ⁻¹ hc_inv
    rw [inv_inv] at h
    rw [h, inv_inv]
  · exact hpos γ hc_pos

/-- Explicit inversion law for `etaMultiplier` across all of `SL(2, ℤ)`: `ε(γ⁻¹) = ε(γ)⁻¹` except
on the negative upper-triangular coset `γ = -T⁻ᵇ` (`γ 1 0 = 0` and `γ 1 1 < 0`), where the
automorphy factor `-1` sits on the negative real branch cut and `ε(γ⁻¹) = -ε(γ)⁻¹`. -/
theorem etaMultiplier_inv (γ : SL(2, ℤ)) :
    etaMultiplier γ⁻¹ =
      if γ 1 0 = 0 ∧ γ 1 1 < 0 then -(etaMultiplier γ)⁻¹ else (etaMultiplier γ)⁻¹ := by
  by_cases hc : γ 1 0 = 0
  · have hinv10 : (γ⁻¹ : SL(2, ℤ)) 1 0 = 0 := by simp [hc]
    have hdet := γ.fin_two_mul_sub_mul_eq_one
    rw [hc, mul_zero, sub_zero] at hdet
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · rw [ite_eq_right (by omega), etaMultiplier_of_c_eq_zero_of_d_pos hinv10 (by simp [ha]),
        etaMultiplier_of_c_eq_zero_of_d_pos hc (by omega),
        Matrix.SpecialLinearGroup.inv_apply_zero_one, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    · rw [ite_eq_left (by omega), etaMultiplier_of_c_eq_zero_of_d_neg hinv10 (by simp [ha]),
        etaMultiplier_of_c_eq_zero_of_d_neg hc (by omega),
        Matrix.SpecialLinearGroup.inv_apply_zero_one, mul_inv, inv_neg, Complex.inv_I,
        ← Complex.exp_neg, neg_neg, neg_mul, Int.cast_neg]
      congr 3
      ring
  · rw [ite_eq_right (fun h ↦ hc h.1)]
    exact etaMultiplier_inv_of_c_ne_zero hc

/-- For a lower-triangular transvection `γ = (1 0; c 1) ∈ SL(2, ℤ)`, `ε(γ) = e^{-π i c / 12}` for
every integer `c` (positive, zero, or negative). -/
theorem etaMultiplier_of_a_eq_one_of_b_eq_zero {γ : SL(2, ℤ)} (ha : γ 0 0 = 1) (hb : γ 0 1 = 0) :
    etaMultiplier γ = cexp (-(π * I * γ 1 0 / 12)) := by
  have hd : γ 1 1 = 1 := by
    have hdet := γ.fin_two_mul_sub_mul_eq_one
    rw [ha, hb, one_mul, zero_mul, sub_zero] at hdet
    exact hdet
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · rw [etaMultiplier_of_c_neg γ hc, ha, hd, dedekindSum_one_left (by omega)]
    have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
    congr 1
    push_cast
    field_simp
    ring
  · rw [etaMultiplier_of_c_eq_zero_of_d_pos hc (by omega), hb, hc]
    simp
  · rw [etaMultiplier_of_c_pos γ hc, ha, hd, dedekindSum_one_left hc.le]
    have hc' : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
    congr 1
    push_cast
    field_simp
    ring

end TauCeti.ModularForm
