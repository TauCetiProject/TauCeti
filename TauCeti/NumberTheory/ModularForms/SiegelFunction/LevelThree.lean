/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The Siegel functions of level three

Modulo `ℤ²` and sign, the vectors `r ∈ (⅓ ℤ)² \ ℤ²` are represented by `(0, 1/3)`, `(1/3, 0)`,
`(1/3, 1/3)` and `(1/3, 2/3)`, one for each point of the projective line over `𝔽₃`. This file
expresses the four Siegel functions `g_r` attached to them as quotients of values of Mathlib's
Dedekind eta function `η = ModularForm.eta`, with exact constants:
`g_{(0, 1/3)}(τ) = √3 i η(3τ) / η(τ)` and, for every integer `k`,
`g_{(1/3, k/3)}(τ) = -e^{-π i k / 4} η((τ + k)/3) / η(τ)`.
The first comes from the factorization `(1 - x)(1 - ζ₃ x)(1 - ζ₃² x) = 1 - x³`, the second from
sorting the factors of `∏_{m ≥ 1} (1 - tᵐ)` by the residue of `m` modulo `3`, with
`t = e^{2π i (τ + k)/3}`.

The transformation of `η` under `S : τ ↦ -1/τ`, compared at `τ` and at `3τ`, then gives
`g_{(0, 1/3)}(-1/τ) = -i g_{(1/3, 0)}(τ)` and `g_{(1/3, 0)}(-1/τ) = i g_{(0, 1/3)}(τ)`. Writing
`S T S` as `T⁻¹ S T⁻¹`, these and the translations `τ ↦ τ + 1` give the transformation of the other
two functions under `S`, again with exact roots of unity:
`g_{(1/3, 1/3)}(-1/τ) = e^{π i / 6} g_{(1/3, 2/3)}(τ)`. Under `τ ↦ τ + 1` the function
`g_{(0, 1/3)}` is multiplied by `e^{π i / 6}`, while `g_{(1/3, 0)}`, `g_{(1/3, 1/3)}` and
`g_{(1/3, 2/3)}` are permuted cyclically up to roots of unity. All these roots of unity are twelfth
roots of unity, so `SL₂(ℤ)` permutes the twelfth powers of the four functions: the monic quartic
with these roots is invariant under `SL₂(ℤ)`. The quartic is the input for computing the
conjugates of the value of `g_{(0, 1/3)}¹²` at a CM point, products of which are estimated in
`TauCeti.NumberTheory.ModularForms.SiegelFunction.ClassNumberOne`. In the product of the four
functions the roots of unity cancel exactly, so the product itself is invariant under `SL₂(ℤ)`;
this pins down the multiplier of the Siegel functions on `Γ(3)`.

## Main results

* `TauCeti.ModularForm.siegelFunction_zero_third_eq_eta`,
  `TauCeti.ModularForm.siegelFunction_third_eq_eta`,
  `TauCeti.ModularForm.siegelFunction_third_zero_eq_eta`: the level-three Siegel functions as eta
  quotients.
* `TauCeti.ModularForm.siegelFunction_zero_third_apply_add_one` and its three companions: the
  transformation under `τ ↦ τ + 1`.
* `TauCeti.ModularForm.siegelFunction_zero_third_apply_neg_one_div` and its three companions: the
  transformation under `τ ↦ -1/τ`.
* `TauCeti.ModularForm.prod_X_sub_C_siegelFunction_third_pow_twelve_smul`: the quartic whose roots
  are the twelfth powers of the four functions is invariant under `SL₂(ℤ)`.
* `siegelFunction_zero_third_mul_third_zero_mul_third_third_mul_third_two_thirds_smul`:
  the product of the four functions is invariant under `SL₂(ℤ)`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 (Siegel functions and their transformation under `SL₂(ℤ)`).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 5 (the
  level-three Siegel functions in the class number one problem).
-/

public section

open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Eta quotients -/

/-- `g_{(0, 1/3)}(τ) = √3 i η(3τ) / η(τ)` on the upper half-plane. -/
theorem siegelFunction_zero_third_eq_eta {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 3] τ = √3 * I * (η (3 * τ) / η τ) := by
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hq := norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  -- `w = e^{2π i / 3} = -1/2 + (√3/2) i` and the phase `e^{-π i / 3} = 1/2 - (√3/2) i`.
  have hw : cexp (2 * π * I * (((0 : ℝ) : ℂ) * τ + ((1 / 3 : ℝ) : ℂ))) = -1 / 2 + √3 / 2 * I := by
    have harg : 2 * π * I * (((0 : ℝ) : ℂ) * τ + ((1 / 3 : ℝ) : ℂ)) =
        ((π - π / 3 : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    ring
  have hph : cexp (π * I * ((1 / 3 : ℝ) : ℂ) * (((0 : ℝ) : ℂ) - 1)) = 1 / 2 - √3 / 2 * I := by
    have harg : π * I * ((1 / 3 : ℝ) : ℂ) * (((0 : ℝ) : ℂ) - 1) = ((-(π / 3) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    ring
  have hB : cexp (π * I * bernoulliFun 2 0 * τ) = cexp (π * I * τ / 6) := by
    rw [bernoulliFun_two]
    congr 1
    push_cast
    ring
  have hω : (-1 / 2 + √3 / 2 * I : ℂ) ^ 2 + (-1 / 2 + √3 / 2 * I) + 1 = 0 := by
    linear_combination (-1 / 4 : ℂ) * h3 + ((√3 : ℂ) ^ 2 / 4) * I_sq
  have hθ := qTheta_mul_tprod_of_sq_add_add_one_eq_zero hq hω
  have he : cexp (2 * π * I * (3 * τ) / 24) = cexp (π * I * τ / 6) * cexp (2 * π * I * τ / 24) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hq₃ : cexp (2 * π * I * (3 * τ)) = cexp (2 * π * I * τ) ^ 3 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [siegelFunction_eq_qTheta]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hw, hB, hph, ← mul_div_assoc, eq_div_iff hη, eta_eq_exp_mul_tprod, eta_eq_exp_mul_tprod, he,
    hq₃]
  linear_combination (-cexp (π * I * τ / 6) * (1 / 2 - √3 / 2 * I) * cexp (2 * π * I * τ / 24)) *
      hθ + (cexp (π * I * τ / 6) * cexp (2 * π * I * τ / 24) *
      ∏' n : ℕ, (1 - (cexp (2 * π * I * τ) ^ 3) ^ (n + 1))) *
      ((1 / 4 : ℂ) * h3 - ((√3 : ℂ) ^ 2 / 4) * I_sq)

/-- `g_{(1/3, k/3)}(τ) = -e^{-π i k / 4} η((τ + k)/3) / η(τ)` on the upper half-plane, for every
integer `k`. -/
theorem siegelFunction_third_eq_eta (k : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 3, k / 3] τ = -cexp (-(π * I * k / 4)) * (η ((τ + k) / 3) / η τ) := by
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hz : 0 < ((τ + k) / 3).im := by
    simpa using div_pos hτ three_pos
  set t := cexp (2 * π * I * ((τ + k) / 3)) with ht_def
  have ht : ‖t‖ < 1 := norm_exp_two_pi_I_lt_one ⟨_, hz⟩
  -- With `t = e^{2π i (τ + k)/3}` the nome is `q = t³`, and `w = t`.
  have hq : cexp (2 * π * I * τ) = t ^ 3 := by
    rw [ht_def, ← Complex.exp_nat_mul,
      show ((3 : ℕ) : ℂ) * (2 * π * I * ((τ + k) / 3)) = 2 * π * I * τ + k * (2 * π * I) by
        push_cast
        ring,
      Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  have hw : cexp (2 * π * I * (((1 / 3 : ℝ) : ℂ) * τ + ((k / 3 : ℝ) : ℂ))) = t := by
    rw [ht_def]
    congr 1
    push_cast
    ring
  have hB : cexp (π * I * bernoulliFun 2 (1 / 3) * τ) = cexp (-(π * I * τ / 18)) := by
    rw [bernoulliFun_two]
    congr 1
    push_cast
    ring
  have he : cexp (-(π * I * τ / 18)) * cexp (π * I * ((k / 3 : ℝ) : ℂ) * (((1 / 3 : ℝ) : ℂ) - 1)) *
      cexp (2 * π * I * τ / 24) =
      cexp (-(π * I * k / 4)) * cexp (2 * π * I * ((τ + k) / 3) / 24) := by
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hθ := qTheta_pow_three_self_mul ht
  rw [siegelFunction_eq_qTheta]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hw, hB, ← mul_div_assoc, eq_div_iff hη, eta_eq_exp_mul_tprod, eta_eq_exp_mul_tprod, ← ht_def,
    hq]
  linear_combination (-(cexp (-(π * I * τ / 18)) *
      cexp (π * I * ((k / 3 : ℝ) : ℂ) * (((1 / 3 : ℝ) : ℂ) - 1)) *
        cexp (2 * π * I * τ / 24))) * hθ - (∏' n : ℕ, (1 - t ^ (n + 1))) * he

/-- `g_{(1/3, 0)}(τ) = -η(τ/3) / η(τ)` on the upper half-plane. -/
theorem siegelFunction_third_zero_eq_eta {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 3, 0] τ = -(η (τ / 3) / η τ) := by
  simpa using siegelFunction_third_eq_eta 0 hτ

/-! ### The translation `τ ↦ τ + 1` -/

/-- `g_{(0, 1/3)}(τ + 1) = e^{π i / 6} g_{(0, 1/3)}(τ)`. -/
theorem siegelFunction_zero_third_apply_add_one (τ : ℂ) :
    siegelFunction ![0, 1 / 3] (τ + 1) = cexp (π * I / 6) * siegelFunction ![0, 1 / 3] τ := by
  rw [siegelFunction_apply_add_one]
  simp

/-- `g_{(1/3, 0)}(τ + 1) = e^{π i / 6} g_{(1/3, 1/3)}(τ)`. -/
theorem siegelFunction_third_zero_apply_add_one (τ : ℂ) :
    siegelFunction ![1 / 3, 0] (τ + 1) = cexp (π * I / 6) * siegelFunction ![1 / 3, 1 / 3] τ := by
  rw [siegelFunction_apply_add_one]
  simp

/-- `g_{(1/3, 1/3)}(τ + 1) = e^{π i / 6} g_{(1/3, 2/3)}(τ)`. -/
theorem siegelFunction_third_third_apply_add_one (τ : ℂ) :
    siegelFunction ![1 / 3, 1 / 3] (τ + 1) =
      cexp (π * I / 6) * siegelFunction ![1 / 3, 2 / 3] τ := by
  rw [siegelFunction_apply_add_one]
  norm_num

/-- `g_{(1/3, 2/3)}(τ + 1) = -i g_{(1/3, 0)}(τ)` on the upper half-plane. -/
theorem siegelFunction_third_two_thirds_apply_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 3, 2 / 3] (τ + 1) = -I * siegelFunction ![1 / 3, 0] τ := by
  -- `(1/3, 2/3) T = (1/3, 1)`, the translate of `(1/3, 0)` by `(0, 1)`.
  have h := siegelFunction_add_intCast ![1 / 3, 0] ![0, 1] hτ
  have hr : (![1 / 3, 0] + fun i ↦ ((![0, 1] : Fin 2 → ℤ) i : ℝ)) = ![1 / 3, 1 / 3 + 2 / 3] := by
    ext i
    fin_cases i <;> norm_num
  have he : cexp (π * I / 6) * cexp (π * I * (1 / 3)) = I := by
    rw [← Complex.exp_add, show π * I / 6 + π * I * (1 / 3) = π / 2 * I by ring,
      exp_pi_div_two_mul_I]
  rw [hr] at h
  -- `h` now reads `g_{(1/3, 1)} = -e^{π i / 3} g_{(1/3, 0)}`.
  norm_num at h
  rw [siegelFunction_apply_add_one]
  norm_num
  rw [h]
  linear_combination (-siegelFunction ![1 / 3, 0] τ) * he

/-! ### The transformation `τ ↦ -1/τ` -/

/-- `g_{(0, 1/3)}(-1/τ) = -i g_{(1/3, 0)}(τ)` on the upper half-plane. -/
theorem siegelFunction_zero_third_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 3] (-1 / τ) = -I * siegelFunction ![1 / 3, 0] τ := by
  have hτ₀ : τ ≠ 0 := UpperHalfPlane.ne_zero ⟨τ, hτ⟩
  have him : 0 < (-1 / τ).im := im_neg_one_div_pos hτ
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hη' : η (-1 / τ) ≠ 0 := _root_.ModularForm.eta_ne_zero him
  have h := eta_neg_one_div_ofReal_mul_mul (c := 1 / 3) (by norm_num) hτ
  rw [show ((1 / 3 : ℝ) : ℂ) * τ = τ / 3 by push_cast; ring,
    show -1 / (τ / 3) = 3 * (-1 / τ) by field_simp] at h
  have hs : ((√3 : ℝ) : ℂ) * ((√(1 / 3) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by norm_num)]
    norm_num
  rw [siegelFunction_zero_third_eq_eta him, siegelFunction_third_zero_eq_eta hτ, neg_mul_neg]
  generalize η (3 * (-1 / τ)) = A at h ⊢
  generalize η (τ / 3) = C at h ⊢
  generalize η (-1 / τ) = B at h hη' ⊢
  generalize η τ = D at h hη ⊢
  field_simp
  linear_combination √3 * h + (C * B) * hs

/-- `g_{(1/3, 0)}(-1/τ) = i g_{(0, 1/3)}(τ)` on the upper half-plane. -/
theorem siegelFunction_third_zero_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 3, 0] (-1 / τ) = I * siegelFunction ![0, 1 / 3] τ := by
  have him : 0 < (-1 / τ).im := im_neg_one_div_pos hτ
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hη' : η (-1 / τ) ≠ 0 := _root_.ModularForm.eta_ne_zero him
  have h := eta_neg_one_div_ofReal_mul_mul (c := 3) three_pos hτ
  rw [show ((3 : ℝ) : ℂ) * τ = 3 * τ by push_cast; ring,
    show -1 / (3 * τ) = -1 / τ / 3 by ring] at h
  rw [siegelFunction_third_zero_eq_eta him, siegelFunction_zero_third_eq_eta hτ, ← mul_assoc,
    mul_div_assoc', neg_div', div_eq_div_iff hη' hη]
  linear_combination (-1 : ℂ) * h - (√3 * η (3 * τ) * η (-1 / τ)) * I_sq

/-- `g_{(1/3, 1/3)}(-1/τ) = e^{π i / 6} g_{(1/3, 2/3)}(τ)` on the upper half-plane. -/
theorem siegelFunction_third_third_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 3, 1 / 3] (-1 / τ) =
      cexp (π * I / 6) * siegelFunction ![1 / 3, 2 / 3] τ := by
  -- Follow `S T S = T⁻¹ S T⁻¹` through the points `x = -1/τ`, `x + 1 = -1/σ`, `σ + 1 = -1/(τ - 1)`.
  set x := -1 / τ
  have hx : 0 < x.im := im_neg_one_div_pos hτ
  have hx₁ : 0 < (x + 1).im := by simpa using hx
  set σ := -1 / (x + 1)
  have hσ : 0 < σ.im := im_neg_one_div_pos hx₁
  have hτ₁ : 0 < (τ - 1).im := by simpa using hτ
  have hσx : -1 / σ = x + 1 := by
    simp only [σ]
    field_simp [UpperHalfPlane.ne_zero ⟨_, hx₁⟩]
  have hστ : σ + 1 = -1 / (τ - 1) := by
    have hτ₀ := UpperHalfPlane.ne_zero ⟨τ, hτ⟩
    have hτ₁₀ := UpperHalfPlane.ne_zero ⟨τ - 1, hτ₁⟩
    have h₁ : x + 1 = (τ - 1) / τ := by
      simp only [x]
      field_simp
      ring
    simp only [σ]
    rw [h₁]
    field_simp
    ring
  have ha := siegelFunction_third_zero_apply_add_one x
  have hb := siegelFunction_third_zero_apply_neg_one_div hσ
  rw [hσx] at hb
  have hc := siegelFunction_zero_third_apply_add_one σ
  rw [hστ, siegelFunction_zero_third_apply_neg_one_div hτ₁] at hc
  have hd := siegelFunction_third_two_thirds_apply_add_one hτ₁
  rw [sub_add_cancel] at hd
  have he₆ : cexp (π * I / 6) ≠ 0 := exp_ne_zero _
  have hI : cexp (π * I / 6) ^ 3 = I := by
    rw [← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (π * I / 6) = π / 2 * I by push_cast; ring,
      exp_pi_div_two_mul_I]
  refine mul_left_cancel₀ (pow_ne_zero 2 he₆) ?_
  linear_combination (-cexp (π * I / 6)) * ha + cexp (π * I / 6) * hb - I * hc -
    siegelFunction ![1 / 3, 2 / 3] τ * hI - I * hd

/-- `g_{(1/3, 2/3)}(-1/τ) = e^{-π i / 6} g_{(1/3, 1/3)}(τ)` on the upper half-plane. -/
theorem siegelFunction_third_two_thirds_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 3, 2 / 3] (-1 / τ) =
      cexp (-(π * I / 6)) * siegelFunction ![1 / 3, 1 / 3] τ := by
  have hτ₀ : τ ≠ 0 := UpperHalfPlane.ne_zero ⟨τ, hτ⟩
  have him : 0 < (-1 / τ).im := im_neg_one_div_pos hτ
  have h := siegelFunction_third_third_apply_neg_one_div him
  rw [show -1 / (-1 / τ) = τ by field_simp] at h
  rw [h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-! ### The action of `SL₂(ℤ)` on the twelfth powers -/

/-- The factor `-i` in `siegelFunction_third_two_thirds_apply_add_one` and
`siegelFunction_zero_third_apply_neg_one_div` is a twelfth root of unity. -/
private theorem neg_I_pow_twelve : (-I) ^ 12 = 1 := by norm_num

/-- The quartic with roots the twelfth powers of the level-three Siegel functions is fixed by
`S`. -/
private theorem prod_X_sub_C_siegelFunction_third_pow_twelve_S_smul (τ : ℍ) :
    (X - C (siegelFunction ![0, 1 / 3] ↑(ModularGroup.S • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 0] ↑(ModularGroup.S • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 1 / 3] ↑(ModularGroup.S • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 2 / 3] ↑(ModularGroup.S • τ) ^ 12)) =
      (X - C (siegelFunction ![0, 1 / 3] τ ^ 12)) * (X - C (siegelFunction ![1 / 3, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 1 / 3] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 2 / 3] τ ^ 12)) := by
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
    rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
  have hI : I ^ 12 = 1 := by norm_num
  have h₆' : cexp (-(π * I / 6)) ^ 12 = 1 := by
    rw [Complex.exp_neg, inv_pow, exp_pi_mul_I_div_six_pow_twelve, inv_one]
  rw [hS, siegelFunction_zero_third_apply_neg_one_div τ.im_pos,
    siegelFunction_third_zero_apply_neg_one_div τ.im_pos,
    siegelFunction_third_third_apply_neg_one_div τ.im_pos,
    siegelFunction_third_two_thirds_apply_neg_one_div τ.im_pos, mul_pow, mul_pow, mul_pow, mul_pow,
    hI, neg_I_pow_twelve, exp_pi_mul_I_div_six_pow_twelve, h₆']
  simp only [one_mul]
  ring

/-- The quartic with roots the twelfth powers of the level-three Siegel functions is fixed by
`T`. -/
private theorem prod_X_sub_C_siegelFunction_third_pow_twelve_T_smul (τ : ℍ) :
    (X - C (siegelFunction ![0, 1 / 3] ↑(ModularGroup.T • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 0] ↑(ModularGroup.T • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 1 / 3] ↑(ModularGroup.T • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 2 / 3] ↑(ModularGroup.T • τ) ^ 12)) =
      (X - C (siegelFunction ![0, 1 / 3] τ ^ 12)) * (X - C (siegelFunction ![1 / 3, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 1 / 3] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 2 / 3] τ ^ 12)) := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd, add_comm, ofReal_one]
  rw [hT, siegelFunction_zero_third_apply_add_one, siegelFunction_third_zero_apply_add_one,
    siegelFunction_third_third_apply_add_one,
    siegelFunction_third_two_thirds_apply_add_one τ.im_pos,
    mul_pow, mul_pow, mul_pow, mul_pow, exp_pi_mul_I_div_six_pow_twelve, neg_I_pow_twelve]
  simp only [one_mul]
  ring

/-- **`SL₂(ℤ)` permutes the twelfth powers of the level-three Siegel functions**: for every
`γ ∈ SL₂(ℤ)` and `τ` in the upper half-plane, the monic quartic whose roots are the twelfth powers
of `g_{(0, 1/3)}`, `g_{(1/3, 0)}`, `g_{(1/3, 1/3)}` and `g_{(1/3, 2/3)}` takes the same value at
`γ τ` as at `τ`. -/
theorem prod_X_sub_C_siegelFunction_third_pow_twelve_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (X - C (siegelFunction ![0, 1 / 3] ↑(γ • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 0] ↑(γ • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 1 / 3] ↑(γ • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 2 / 3] ↑(γ • τ) ^ 12)) =
      (X - C (siegelFunction ![0, 1 / 3] τ ^ 12)) * (X - C (siegelFunction ![1 / 3, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 1 / 3] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 3, 2 / 3] τ ^ 12)) := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing τ with
  | one => rw [one_smul]
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact prod_X_sub_C_siegelFunction_third_pow_twelve_S_smul τ
    · exact prod_X_sub_C_siegelFunction_third_pow_twelve_T_smul τ
  | mul g h _ _ hg hh => rw [mul_smul, hg, hh]
  | inv g _ hg => rw [← hg, smul_inv_smul]

/-! ### The product of the four functions -/

/-- **`SL₂(ℤ)` fixes the product of the level-three Siegel functions**: for every `γ ∈ SL₂(ℤ)`,
the product `g_{(0, 1/3)} g_{(1/3, 0)} g_{(1/3, 1/3)} g_{(1/3, 2/3)}` takes the same value at
`γ τ` as at `τ`. The roots of unity in the transformations under `S` and `T` cancel exactly in
the product, so no power needs to be taken. -/
theorem siegelFunction_zero_third_mul_third_zero_mul_third_third_mul_third_two_thirds_smul
    (γ : SL(2, ℤ)) (τ : ℍ) :
    siegelFunction ![0, 1 / 3] ↑(γ • τ) * siegelFunction ![1 / 3, 0] ↑(γ • τ) *
        siegelFunction ![1 / 3, 1 / 3] ↑(γ • τ) * siegelFunction ![1 / 3, 2 / 3] ↑(γ • τ) =
      siegelFunction ![0, 1 / 3] τ * siegelFunction ![1 / 3, 0] τ *
        siegelFunction ![1 / 3, 1 / 3] τ * siegelFunction ![1 / 3, 2 / 3] τ := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing τ with
  | one => rw [one_smul]
  | mem g hg =>
    rcases hg with rfl | rfl
    · -- Under `S` the factors pick up `-i`, `i`, `e^{π i / 6}` and `e^{-π i / 6}`.
      have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
        rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
      have he : cexp (π * I / 6) * cexp (-(π * I / 6)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      rw [hS, siegelFunction_zero_third_apply_neg_one_div τ.im_pos,
        siegelFunction_third_zero_apply_neg_one_div τ.im_pos,
        siegelFunction_third_third_apply_neg_one_div τ.im_pos,
        siegelFunction_third_two_thirds_apply_neg_one_div τ.im_pos]
      linear_combination (-I ^ 2 * (siegelFunction ![0, 1 / 3] τ * siegelFunction ![1 / 3, 0] τ *
          siegelFunction ![1 / 3, 1 / 3] τ * siegelFunction ![1 / 3, 2 / 3] τ)) * he -
        (siegelFunction ![0, 1 / 3] τ * siegelFunction ![1 / 3, 0] τ *
          siegelFunction ![1 / 3, 1 / 3] τ * siegelFunction ![1 / 3, 2 / 3] τ) * I_sq
    · -- Under `T` the factors pick up `e^{π i / 6}` three times and `-i` once.
      have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
        rw [modular_T_smul, coe_vadd, add_comm, ofReal_one]
      have he : cexp (π * I / 6) ^ 3 = I := by
        rw [← Complex.exp_nat_mul,
          show ((3 : ℕ) : ℂ) * (π * I / 6) = π / 2 * I by push_cast; ring, exp_pi_div_two_mul_I]
      rw [hT, siegelFunction_zero_third_apply_add_one, siegelFunction_third_zero_apply_add_one,
        siegelFunction_third_third_apply_add_one,
        siegelFunction_third_two_thirds_apply_add_one τ.im_pos]
      linear_combination (-I * (siegelFunction ![0, 1 / 3] τ * siegelFunction ![1 / 3, 0] τ *
          siegelFunction ![1 / 3, 1 / 3] τ * siegelFunction ![1 / 3, 2 / 3] τ)) * he -
        (siegelFunction ![0, 1 / 3] τ * siegelFunction ![1 / 3, 0] τ *
          siegelFunction ![1 / 3, 1 / 3] τ * siegelFunction ![1 / 3, 2 / 3] τ) * I_sq
  | mul g h _ _ hg hh => rw [mul_smul, hg, hh]
  | inv g _ hg => rw [← hg, smul_inv_smul]

end TauCeti.ModularForm
