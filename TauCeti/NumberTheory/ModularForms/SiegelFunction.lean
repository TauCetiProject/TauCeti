/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ZetaValues

/-!
# Siegel functions

For `r = (r₁, r₂) ∈ ℝ²` the **Siegel function** `g_r` is the holomorphic function on the upper
half-plane given by the product
`g_r(τ) = -e^{π i B₂(r₁) τ} e^{π i r₂ (r₁ - 1)} (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`,
where `q = e^{2π i τ}`, `w = e^{2π i (r₁ τ + r₂)}` and `B₂(x) = x² - x + 1/6` is the second
Bernoulli polynomial. For rational `r` these functions are the basic building blocks of modular
units of level `N`: suitable powers and products of them are modular functions whose values at
imaginary quadratic points generate ray class fields, and they control the small-power class field
inclusions in the proof of the class number one theorem.

This file constructs `g_r` and develops its elementary analytic and algebraic properties:
the defining product converges locally uniformly on the upper half-plane, so `g_r` is
holomorphic there; `g_r` vanishes nowhere on the upper half-plane when `r ∉ ℤ²`; and `g_r`
transforms by an explicit root of unity under integral translations of `r` and under `τ ↦ τ + 1`.
The phases are exact: no root of unity is lost to a choice of branch.

## Main definitions and results

* `TauCeti.ModularForm.siegelFunction r τ`: the Siegel function `g_r(τ)`.
* `TauCeti.ModularForm.differentiableOn_siegelFunction`: `g_r` is holomorphic on the upper
  half-plane.
* `TauCeti.ModularForm.siegelFunction_ne_zero`: for `r ∉ ℤ²`, `g_r` has no zero on the upper
  half-plane.
* `TauCeti.ModularForm.siegelFunction_add_intCast`: for `s ∈ ℤ²`,
  `g_{r + s} = (-1)^{s₁ s₂ + s₁ + s₂} e^{-π i (s₁ r₂ - s₂ r₁)} g_r`.
* `TauCeti.ModularForm.siegelFunction_apply_add_one`:
  `g_r(τ + 1) = e^{π i / 6} g_{(r₁, r₁ + r₂)}(τ)`, the transformation under the translation
  `T = [[1, 1], [0, 1]]` acting on the row vector `r` on the right.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 (the Klein forms and Siegel functions and their transformation properties).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.ModularForm

/-- **The Siegel function** `g_r(τ)` attached to `r = (r₁, r₂) ∈ ℝ²`:
`g_r(τ) = -e^{π i B₂(r₁) τ} e^{π i r₂ (r₁ - 1)} (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`
with `q = e^{2π i τ}`, `w = e^{2π i (r₁ τ + r₂)}` and `B₂ = bernoulliFun 2` the second Bernoulli
polynomial `x² - x + 1/6`. The product converges for `τ` in the upper half-plane, where `g_r` is
holomorphic; elsewhere the value is a junk value. -/
noncomputable def siegelFunction (r : Fin 2 → ℝ) (τ : ℂ) : ℂ :=
  -cexp (π * I * bernoulliFun 2 (r 0) * τ) * cexp (π * I * r 1 * (r 0 - 1)) *
    (1 - cexp (2 * π * I * (r 0 * τ + r 1))) *
    ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (2 * π * I * (r 0 * τ + r 1))) *
      (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (-(2 * π * I * (r 0 * τ + r 1))))

/-- The defining product of the Siegel function. -/
theorem siegelFunction_def (r : Fin 2 → ℝ) (τ : ℂ) :
    siegelFunction r τ =
      -cexp (π * I * bernoulliFun 2 (r 0) * τ) * cexp (π * I * r 1 * (r 0 - 1)) *
        (1 - cexp (2 * π * I * (r 0 * τ + r 1))) *
        ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (2 * π * I * (r 0 * τ + r 1))) *
          (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (-(2 * π * I * (r 0 * τ + r 1)))) :=
  (rfl)

section Product

/-! ### The half products `∏_{n ≥ 1} (1 - qⁿ w)` -/

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)` converges. -/
private theorem multipliable_one_sub_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) * w := by
  apply multipliable_one_sub_of_summable
  simpa [norm_pow, pow_succ, mul_assoc] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖ * ‖w‖)

/-- Shifting the half product: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`. -/
private theorem tprod_one_sub_pow_mul_eq {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * w) = (1 - q * w) * ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)) := by
  rw [tprod_eq_zero_mul' (by simpa [pow_succ, mul_assoc] using
    multipliable_one_sub_pow_mul hq (q * w))]
  simp [pow_succ, mul_assoc]

/-- The other half product, shifted:
`∏_{n ≥ 1} (1 - qⁿ (q w)⁻¹) = (1 - w⁻¹) ∏_{n ≥ 1} (1 - qⁿ w⁻¹)` for `q ≠ 0`. -/
private theorem tprod_one_sub_pow_mul_inv_eq {q : ℂ} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (w : ℂ) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)⁻¹) = (1 - w⁻¹) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) := by
  have h : ∀ n : ℕ, q ^ (n + 1) * (q * w)⁻¹ = q ^ n * w⁻¹ := fun n ↦ by
    rw [mul_inv, pow_succ]
    field_simp
  simp_rw [h]
  rw [tprod_eq_zero_mul' (multipliable_one_sub_pow_mul hq w⁻¹)]
  simp

/-- The product `P_q(w) = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` in the Siegel function. -/
private noncomputable def siegelProd (q w : ℂ) : ℂ :=
  (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹)

/-- The product `P_q` is quasi-periodic: `P_q(q w) = -w⁻¹ P_q(w)`. -/
private theorem siegelProd_mul_left {q : ℂ} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    siegelProd q (q * w) = -w⁻¹ * siegelProd q w := by
  rw [siegelProd, siegelProd,
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    tprod_one_sub_pow_mul_inv_eq hq hq₀, tprod_one_sub_pow_mul_eq hq w]
  field_simp
  ring

end Product

/-- The Siegel function as a phase times the product `P_q(w)`. -/
private theorem siegelFunction_eq_siegelProd (r : Fin 2 → ℝ) (τ : ℂ) :
    siegelFunction r τ =
      -cexp (π * I * bernoulliFun 2 (r 0) * τ) * cexp (π * I * r 1 * (r 0 - 1)) *
        siegelProd (cexp (2 * π * I * τ)) (cexp (2 * π * I * (r 0 * τ + r 1))) := by
  rw [siegelFunction_def, siegelProd, Complex.exp_neg]
  ring

section Analytic

/-! ### Convergence and holomorphy on the upper half-plane -/

/-- On a compact subset of the upper half-plane, `‖e^{2π i τ}‖` is bounded by a constant `< 1`. -/
private theorem exists_norm_cexp_le_of_isCompact {S : Set ℂ} (hS : IsCompact S)
    (hSH : S ⊆ upperHalfPlaneSet) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ τ ∈ S, ‖cexp (2 * π * I * τ)‖ ≤ ρ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, one_pos, by simp⟩
  obtain ⟨τ₀, hτ₀, hmax⟩ := hS.exists_isMaxOn hne
    (show ContinuousOn (fun τ : ℂ ↦ ‖cexp (2 * π * I * τ)‖) S by fun_prop)
  exact ⟨_, norm_nonneg _, norm_exp_two_pi_I_lt_one ⟨τ₀, hSH hτ₀⟩, hmax⟩

/-- For an entire `w`, the half product `∏_{n ≥ 1} (1 - qⁿ w(τ))` converges locally uniformly on
the upper half-plane. -/
private theorem hasProdLocallyUniformlyOn_one_sub_pow_mul {w : ℂ → ℂ} (hw : Continuous w) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) τ ↦ 1 - cexp (2 * π * I * τ) ^ (n + 1) * w τ)
      (fun τ ↦ ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * w τ)) upperHalfPlaneSet := by
  simp_rw [sub_eq_add_neg]
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_upperHalfPlaneSet
    fun S hSH hS ↦ ?_
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ := exists_norm_cexp_le_of_isCompact hS hSH
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hw.continuousOn
  refine ((summable_geometric_of_lt_one hρ₀ hρ₁).mul_left (ρ * M)).hasProdUniformlyOn_nat_one_add
    hS (.of_forall fun n τ hτ ↦ ?_) fun n ↦ by fun_prop
  calc ‖-(cexp (2 * π * I * τ) ^ (n + 1) * w τ)‖
      = ‖cexp (2 * π * I * τ)‖ ^ (n + 1) * ‖w τ‖ := by simp [norm_pow]
    _ ≤ ρ ^ (n + 1) * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hρ τ hτ) _) (hM τ hτ) (norm_nonneg _)
        (pow_nonneg hρ₀ _)
    _ = ρ * M * ρ ^ n := by ring

/-- The half product `∏_{n ≥ 1} (1 - qⁿ w(τ))` is holomorphic on the upper half-plane. -/
private theorem differentiableOn_tprod_one_sub_pow_mul {w : ℂ → ℂ} (hw : Differentiable ℂ w) :
    DifferentiableOn ℂ (fun τ ↦ ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * w τ))
      upperHalfPlaneSet :=
  (hasProdLocallyUniformlyOn_one_sub_pow_mul hw.continuous).differentiableOn
    (.of_forall fun s ↦ by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd fun _ _ ↦ by fun_prop)
    isOpen_upperHalfPlaneSet

/-- On the upper half-plane the Siegel function is the product of its two half products. -/
private theorem siegelFunction_eq_mul_tprod_mul_tprod (r : Fin 2 → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r τ =
      -cexp (π * I * bernoulliFun 2 (r 0) * τ) * cexp (π * I * r 1 * (r 0 - 1)) *
        (1 - cexp (2 * π * I * (r 0 * τ + r 1))) *
        ((∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (2 * π * I * (r 0 * τ + r 1)))) *
          ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) *
            cexp (-(2 * π * I * (r 0 * τ + r 1))))) := by
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  rw [siegelFunction_def, (multipliable_one_sub_pow_mul hq _).tprod_mul
    (multipliable_one_sub_pow_mul hq _)]

/-- **The Siegel function is holomorphic** on the upper half-plane. -/
theorem differentiableOn_siegelFunction (r : Fin 2 → ℝ) :
    DifferentiableOn ℂ (siegelFunction r) upperHalfPlaneSet := by
  refine DifferentiableOn.congr ?_ fun τ hτ ↦ siegelFunction_eq_mul_tprod_mul_tprod r hτ
  refine (DifferentiableOn.mul (by fun_prop) ?_)
  exact (differentiableOn_tprod_one_sub_pow_mul (by fun_prop)).mul
    (differentiableOn_tprod_one_sub_pow_mul (by fun_prop))

/-- `1 - e^{2π i (x τ + y)}` vanishes at a point `τ` of the upper half-plane only when `x = 0` and
`y` is an integer. -/
private theorem one_sub_cexp_ne_zero {x y : ℝ} {τ : ℂ} (hτ : 0 < τ.im)
    (h : ∀ k : ℤ, x = 0 → y ≠ k) : 1 - cexp (2 * π * I * (x * τ + y)) ≠ 0 := by
  rw [sub_ne_zero, ne_comm, Ne, Complex.exp_eq_one_iff]
  rintro ⟨k, hk⟩
  have hk' : (x : ℂ) * τ + y = k := by
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact mul_left_cancel₀ h2 (by rw [hk]; ring)
  have him := congrArg Complex.im hk'
  have hre := congrArg Complex.re hk'
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, intCast_im] at him
  have hx : x = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h (ne_of_gt hτ)
  exact h k hx (by simpa [hx] using hre)

/-- `qⁿ⁺¹ e^{2π i (x τ + y)} = e^{2π i ((n + 1 + x) τ + y)}` for `q = e^{2π i τ}`. -/
private theorem cexp_pow_mul_cexp (n : ℕ) (x y : ℝ) (τ : ℂ) :
    cexp (2 * π * I * τ) ^ (n + 1) * cexp (2 * π * I * (x * τ + y)) =
      cexp (2 * π * I * (((n + 1 + x : ℝ) : ℂ) * τ + y)) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  push_cast
  ring_nf

/-- If the factors `1 - qⁿ⁺¹ w` are nonzero, so is `∏_{n ≥ 1} (1 - qⁿ w)`. -/
private theorem tprod_one_sub_pow_mul_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {w : ℂ}
    (h : ∀ n : ℕ, 1 - q ^ (n + 1) * w ≠ 0) : ∏' n : ℕ, (1 - q ^ (n + 1) * w) ≠ 0 := by
  simp_rw [sub_eq_add_neg] at h ⊢
  refine tprod_one_add_ne_zero_of_summable h ?_
  simpa [norm_pow, pow_succ, mul_assoc] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖ * ‖w‖)

/-- **The Siegel function has no zeros** on the upper half-plane when `r ∉ ℤ²`. -/
theorem siegelFunction_ne_zero {r : Fin 2 → ℝ} (hr : ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ))
    {τ : ℂ} (hτ : 0 < τ.im) : siegelFunction r τ ≠ 0 := by
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hint : ∀ a b : ℤ, r 0 ≠ a ∨ r 1 ≠ b := fun a b ↦ by
    by_contra! h
    exact hr ![a, b] (funext <| Fin.forall_fin_two.mpr ⟨by simp [h.1], by simp [h.2]⟩)
  have hneg : cexp (-(2 * π * I * (r 0 * τ + r 1))) =
      cexp (2 * π * I * (((-r 0 : ℝ) : ℂ) * τ + ((-r 1 : ℝ) : ℂ))) := by
    push_cast
    ring_nf
  rw [siegelFunction_eq_mul_tprod_mul_tprod r hτ]
  refine mul_ne_zero (mul_ne_zero (by simp [exp_ne_zero]) ?_) (mul_ne_zero ?_ ?_)
  · exact one_sub_cexp_ne_zero hτ fun k h0 h1 ↦ (hint 0 k).elim (· (by simpa using h0)) (· h1)
  · refine tprod_one_sub_pow_mul_ne_zero hq fun n ↦ ?_
    rw [cexp_pow_mul_cexp]
    refine one_sub_cexp_ne_zero hτ fun k h0 h1 ↦ (hint (-(n + 1)) k).elim (· ?_) (· h1)
    push_cast
    linarith
  · refine tprod_one_sub_pow_mul_ne_zero hq fun n ↦ ?_
    rw [hneg, cexp_pow_mul_cexp]
    refine one_sub_cexp_ne_zero hτ fun k h0 h1 ↦ (hint (n + 1) (-k)).elim (· ?_) (· ?_)
    · push_cast
      linarith
    · push_cast
      linarith

end Analytic

section Translation

/-! ### Translations of `r` and of `τ` -/

/-- **Translating `r₂` by an integer**: `g_{(r₁, r₂ + n)} = (-1)ⁿ e^{π i n r₁} g_{(r₁, r₂)}`. -/
private theorem siegelFunction_add_zero_intCast (r : Fin 2 → ℝ) (n : ℤ) (τ : ℂ) :
    siegelFunction (r + ![0, (n : ℝ)]) τ =
      (-1) ^ n * cexp (π * I * n * r 0) * siegelFunction r τ := by
  have hw : cexp (2 * π * I * (r 0 * τ + ((r 1 + n : ℝ) : ℂ))) =
      cexp (2 * π * I * (r 0 * τ + r 1)) := by
    rw [show 2 * π * I * (r 0 * τ + ((r 1 + n : ℝ) : ℂ)) =
      2 * π * I * (r 0 * τ + r 1) + n * (2 * π * I) by push_cast; ring,
      Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  have hneg : (-1 : ℂ) ^ n = cexp (n * -(π * I)) := by
    rw [exp_int_mul, Complex.exp_neg, exp_pi_mul_I, inv_neg, inv_one]
  simp only [siegelFunction_eq_siegelProd, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, hw, hneg]
  have h : cexp (π * I * ((r 1 + n : ℝ) : ℂ) * (r 0 - 1)) =
      cexp (n * -(π * I)) * cexp (π * I * n * r 0) * cexp (π * I * r 1 * (r 0 - 1)) := by
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h]
  ring

/-- **Translating `r₁` by one**: `g_{(r₁ + 1, r₂)} = -e^{-π i r₂} g_{(r₁, r₂)}` on the upper
half-plane. -/
private theorem siegelFunction_add_one_zero (r : Fin 2 → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (r + ![1, 0]) τ = -cexp (-(π * I * r 1)) * siegelFunction r τ := by
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hw : cexp (2 * π * I * (((r 0 + 1 : ℝ) : ℂ) * τ + r 1)) =
      cexp (2 * π * I * τ) * cexp (2 * π * I * (r 0 * τ + r 1)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [siegelFunction_eq_siegelProd, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, hw,
    siegelProd_mul_left hq (exp_ne_zero _) (exp_ne_zero _), ← Complex.exp_neg]
  have h : cexp (π * I * bernoulliFun 2 (r 0 + 1) * τ) * cexp (π * I * r 1 * ((r 0 + 1 : ℝ) - 1)) *
      cexp (-(2 * π * I * (r 0 * τ + r 1))) =
      cexp (-(π * I * r 1)) * cexp (π * I * bernoulliFun 2 (r 0) * τ) *
        cexp (π * I * r 1 * (r 0 - 1)) := by
    simp only [← Complex.exp_add, bernoulliFun_two]
    congr 1
    push_cast
    ring
  linear_combination (siegelProd (cexp (2 * π * I * τ)) (cexp (2 * π * I * (r 0 * τ + r 1)))) * h

/-- Translating `r₁` by a natural number `m`. -/
private theorem siegelFunction_add_natCast_zero (r : Fin 2 → ℝ) (m : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (r + ![(m : ℝ), 0]) τ =
      (-1) ^ m * cexp (-(π * I * m * r 1)) * siegelFunction r τ := by
  induction m with
  | zero =>
    rw [show ![((0 : ℕ) : ℝ), 0] = 0 by ext i; fin_cases i <;> simp, add_zero]
    simp
  | succ m ih =>
    have h := siegelFunction_add_one_zero (r + ![(m : ℝ), 0]) hτ
    rw [add_assoc, show ![(m : ℝ), 0] + ![1, 0] = ![((m + 1 : ℕ) : ℝ), 0] by
      ext i; fin_cases i <;> simp] at h
    rw [h, ih]
    simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero]
    have h' : cexp (-(π * I * ((m + 1 : ℕ) : ℂ) * r 1)) =
        cexp (-(π * I * r 1)) * cexp (-(π * I * m * r 1)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h', pow_succ]
    ring

/-- **Translating `r₁` by an integer**: `g_{(r₁ + m, r₂)} = (-1)ᵐ e^{-π i m r₂} g_{(r₁, r₂)}` on
the upper half-plane. -/
private theorem siegelFunction_add_intCast_zero (r : Fin 2 → ℝ) (m : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (r + ![(m : ℝ), 0]) τ =
      (-1) ^ m * cexp (-(π * I * m * r 1)) * siegelFunction r τ := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using siegelFunction_add_natCast_zero r k hτ
  · have h := siegelFunction_add_natCast_zero (r + ![-(k : ℝ), 0]) k hτ
    rw [add_assoc, show ![-(k : ℝ), 0] + ![(k : ℝ), 0] = 0 by
      ext i; fin_cases i <;> simp, add_zero] at h
    simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero] at h
    simp only [Int.cast_neg, Int.cast_natCast]
    have h₁ : ((-1 : ℂ) ^ (-(k : ℤ))) * (-1) ^ k = 1 := by
      rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
    have h₂ : cexp (-(π * I * -(k : ℂ) * r 1)) * cexp (-(π * I * k * r 1)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    rw [h]
    linear_combination (-(siegelFunction (r + ![-(k : ℝ), 0]) τ) *
      cexp (-(π * I * -(k : ℂ) * r 1)) * cexp (-(π * I * k * r 1))) * h₁ -
      siegelFunction (r + ![-(k : ℝ), 0]) τ * h₂

/-- **Translating `r` by an integral vector.** For `s = (s₁, s₂) ∈ ℤ²`,
`g_{r + s} = (-1)^{s₁ s₂ + s₁ + s₂} e^{-π i (s₁ r₂ - s₂ r₁)} g_r` on the upper half-plane. In
particular `g_r` depends on `r` modulo `ℤ²` only up to a root of unity when `r` is rational. -/
theorem siegelFunction_add_intCast (r : Fin 2 → ℝ) (s : Fin 2 → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (r + fun i ↦ (s i : ℝ)) τ =
      (-1) ^ (s 0 * s 1 + s 0 + s 1) * cexp (-(π * I * (s 0 * r 1 - s 1 * r 0))) *
        siegelFunction r τ := by
  have hs : (r + fun i ↦ (s i : ℝ)) = r + ![0, (s 1 : ℝ)] + ![(s 0 : ℝ), 0] := by
    ext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, add_comm]
  rw [hs, siegelFunction_add_intCast_zero _ _ hτ, siegelFunction_add_zero_intCast]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hpow : (-1 : ℂ) ^ (s 0 * s 1 + s 0 + s 1) =
      cexp (-(π * I * s 0 * s 1)) * (-1) ^ s 0 * (-1) ^ s 1 := by
    rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num),
      show -(π * I * s 0 * s 1) = ((s 0 * s 1 : ℤ) : ℂ) * -(π * I) by push_cast; ring,
      exp_int_mul, Complex.exp_neg, exp_pi_mul_I, inv_neg, inv_one]
  have hexp : cexp (-(π * I * s 0 * ((r 1 + s 1 : ℝ) : ℂ))) * cexp (π * I * s 1 * r 0) =
      cexp (-(π * I * s 0 * s 1)) * cexp (-(π * I * (s 0 * r 1 - s 1 * r 0))) := by
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hpow]
  linear_combination ((-1) ^ s 0 * (-1) ^ s 1 * siegelFunction r τ) * hexp

/-- **The translation `τ ↦ τ + 1`**: `g_r(τ + 1) = e^{π i / 6} g_{r T}(τ)`, where
`r T = (r₁, r₁ + r₂)` is the row vector `r` multiplied on the right by `T = [[1, 1], [0, 1]]`. -/
theorem siegelFunction_apply_add_one (r : Fin 2 → ℝ) (τ : ℂ) :
    siegelFunction r (τ + 1) = cexp (π * I / 6) * siegelFunction ![r 0, r 0 + r 1] τ := by
  have hq : cexp (2 * π * I * (τ + 1)) = cexp (2 * π * I * τ) := by
    rw [mul_add, mul_one, Complex.exp_add, exp_two_pi_mul_I, mul_one]
  simp only [siegelFunction_eq_siegelProd, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hq]
  have hw : cexp (2 * π * I * (r 0 * (τ + 1) + r 1)) =
      cexp (2 * π * I * (r 0 * τ + ((r 0 + r 1 : ℝ) : ℂ))) := by
    congr 1
    push_cast
    ring
  have h : cexp (π * I * bernoulliFun 2 (r 0) * (τ + 1)) * cexp (π * I * r 1 * (r 0 - 1)) =
      cexp (π * I / 6) * cexp (π * I * bernoulliFun 2 (r 0) * τ) *
        cexp (π * I * ((r 0 + r 1 : ℝ) : ℂ) * (r 0 - 1)) := by
    simp only [← Complex.exp_add, bernoulliFun_two]
    congr 1
    push_cast
    ring
  rw [hw]
  linear_combination (-siegelProd (cexp (2 * π * I * τ))
    (cexp (2 * π * I * (r 0 * τ + ((r 0 + r 1 : ℝ) : ℂ))))) * h

end Translation

end TauCeti.ModularForm
