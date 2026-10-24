/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
public import TauCeti.Analysis.SpecialFunctions.QPochhammer

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
The phases are exact: no root of unity is lost to a choice of branch. Finally it computes the three
Siegel functions of level two, `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}`,
as explicit products (up to constant factors they are the squares `𝔣₂²`, `𝔣₁²` and `𝔣²` of
Weber's modular functions), proves `g₀ g₁ g₂ = 2 ζ₈` with `ζ₈ = e^{2π i / 8}`, and records how
`τ ↦ τ + 1` permutes them up to roots of unity.

## Main definitions and results

* `TauCeti.ModularForm.siegelFunction r τ`: the Siegel function `g_r(τ)`.
* `TauCeti.ModularForm.siegelFunction_eq_qTheta`,
  `TauCeti.ModularForm.siegelFunction_eq_mul_tprod_mul_tprod`: `g_r` as a phase times the theta
  product `θ_q(w)`, and as a phase times `1 - w` and its two half products.
* `TauCeti.ModularForm.hasProdLocallyUniformlyOn_siegelFunction`: the defining product
  `∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` converges locally uniformly on the upper half-plane.
* `TauCeti.ModularForm.differentiableOn_siegelFunction`: `g_r` is holomorphic on the upper
  half-plane.
* `TauCeti.ModularForm.siegelFunction_ne_zero`: for `r ∉ ℤ²`, `g_r` has no zero on the upper
  half-plane.
* `TauCeti.ModularForm.siegelFunction_add_intCast`: for `s ∈ ℤ²`,
  `g_{r + s} = (-1)^{s₁ s₂ + s₁ + s₂} e^{-π i (s₁ r₂ - s₂ r₁)} g_r`.
* `TauCeti.ModularForm.siegelFunction_apply_add_one`:
  `g_r(τ + 1) = e^{π i / 6} g_{(r₁, r₁ + r₂)}(τ)`, the transformation under the translation
  `T = [[1, 1], [0, 1]]` acting on the row vector `r` on the right.
* `TauCeti.ModularForm.siegelFunction_zero_half`, `TauCeti.ModularForm.siegelFunction_half_zero`,
  `TauCeti.ModularForm.siegelFunction_half_half`: the product expansions of `g₀`, `g₁` and `g₂`.
* `TauCeti.ModularForm.siegelFunction_zero_half_mul_half_zero_mul_half_half`:
  `g₀ g₁ g₂ = 2 ζ₈` on the upper half-plane.
* `TauCeti.ModularForm.siegelFunction_zero_half_apply_add_one`,
  `TauCeti.ModularForm.siegelFunction_half_zero_apply_add_one`,
  `TauCeti.ModularForm.siegelFunction_half_half_apply_add_one`: `τ ↦ τ + 1` sends `g₀, g₁, g₂` to
  `e^{π i / 6} g₀`, `e^{π i / 6} g₂` and `e^{-π i / 3} g₁`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 (the Klein forms and Siegel functions and their transformation properties).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber's functions `𝔣, 𝔣₁, 𝔣₂` and the
  identity `𝔣 𝔣₁ 𝔣₂ = √2`, equivalent to `g₀ g₁ g₂ = 2 ζ₈`).
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

/-- The Siegel function as a phase times the theta product `θ_q(w)`:
`g_r(τ) = -e^{π i B₂(r₁) τ} e^{π i r₂ (r₁ - 1)} θ_q(w)` with `q = e^{2π i τ}` and
`w = e^{2π i (r₁ τ + r₂)}`. -/
theorem siegelFunction_eq_qTheta (r : Fin 2 → ℝ) (τ : ℂ) :
    siegelFunction r τ =
      -cexp (π * I * bernoulliFun 2 (r 0) * τ) * cexp (π * I * r 1 * (r 0 - 1)) *
        qTheta (cexp (2 * π * I * τ)) (cexp (2 * π * I * (r 0 * τ + r 1))) := by
  rw [siegelFunction_def, qTheta_def, Complex.exp_neg]
  ring

section Analytic

/-! ### Convergence and holomorphy on the upper half-plane -/

/-- On the upper half-plane the Siegel function splits into its two half products,
`g_r(τ) = -e^{π i B₂(r₁) τ} e^{π i r₂ (r₁ - 1)} (1 - w) P(w) P(w⁻¹)` where
`P(v) = ∏_{n ≥ 1} (1 - qⁿ v)`, with `q = e^{2π i τ}` and `w = e^{2π i (r₁ τ + r₂)}`. -/
theorem siegelFunction_eq_mul_tprod_mul_tprod (r : Fin 2 → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r τ =
      -cexp (π * I * bernoulliFun 2 (r 0) * τ) * cexp (π * I * r 1 * (r 0 - 1)) *
        (1 - cexp (2 * π * I * (r 0 * τ + r 1))) *
        ((∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (2 * π * I * (r 0 * τ + r 1)))) *
          ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) *
            cexp (-(2 * π * I * (r 0 * τ + r 1))))) := by
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  rw [siegelFunction_def, (multipliable_one_sub_pow_mul hq _).tprod_mul
    (multipliable_one_sub_pow_mul hq _)]

/-- The infinite product `∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` defining the Siegel function, with
`q = e^{2π i τ}` and `w = e^{2π i (r₁ τ + r₂)}`, converges locally uniformly on the upper
half-plane. -/
theorem hasProdLocallyUniformlyOn_siegelFunction (r : Fin 2 → ℝ) :
    HasProdLocallyUniformlyOn
      (fun (n : ℕ) τ ↦ (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (2 * π * I * (r 0 * τ + r 1))) *
        (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (-(2 * π * I * (r 0 * τ + r 1)))))
      (fun τ ↦ ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (2 * π * I * (r 0 * τ + r 1))) *
        (1 - cexp (2 * π * I * τ) ^ (n + 1) * cexp (-(2 * π * I * (r 0 * τ + r 1)))))
      upperHalfPlaneSet := by
  have hw : DifferentiableOn ℂ (fun τ ↦ cexp (2 * π * I * (r 0 * τ + r 1))) upperHalfPlaneSet := by
    fun_prop
  have hw' : DifferentiableOn ℂ (fun τ ↦ cexp (-(2 * π * I * (r 0 * τ + r 1))))
      upperHalfPlaneSet := by
    fun_prop
  have hq : DifferentiableOn ℂ (fun τ : ℂ ↦ cexp (2 * π * I * τ)) upperHalfPlaneSet := by
    fun_prop
  have hq₁ : ∀ τ ∈ upperHalfPlaneSet, ‖cexp (2 * π * I * τ)‖ < 1 := fun τ hτ ↦
    norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have h := (hasProdLocallyUniformlyOn_one_sub_pow_mul isOpen_upperHalfPlaneSet hq.continuousOn
    hq₁ hw.continuousOn).mul₀
    (hasProdLocallyUniformlyOn_one_sub_pow_mul isOpen_upperHalfPlaneSet hq.continuousOn hq₁
      hw'.continuousOn)
    (differentiableOn_tprod_one_sub_pow_mul isOpen_upperHalfPlaneSet hq hq₁ hw).continuousOn
    (differentiableOn_tprod_one_sub_pow_mul isOpen_upperHalfPlaneSet hq hq₁ hw').continuousOn
  refine (h.congr fun s τ _ ↦ ?_).congr_right fun τ hτ ↦ ?_
  · simp [Finset.prod_mul_distrib]
  · have hq : ‖cexp (2 * π * I * τ)‖ < 1 := norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
    exact ((multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _)).symm

/-- **The Siegel function is holomorphic** on the upper half-plane. -/
theorem differentiableOn_siegelFunction (r : Fin 2 → ℝ) :
    DifferentiableOn ℂ (siegelFunction r) upperHalfPlaneSet := by
  refine DifferentiableOn.congr ?_ fun τ hτ ↦ siegelFunction_eq_mul_tprod_mul_tprod r hτ
  have hq₁ : ∀ τ ∈ upperHalfPlaneSet, ‖cexp (2 * π * I * τ)‖ < 1 := fun τ hτ ↦
    norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  refine (DifferentiableOn.mul (by fun_prop) ?_)
  exact (differentiableOn_tprod_one_sub_pow_mul isOpen_upperHalfPlaneSet (by fun_prop) hq₁
    (by fun_prop)).mul
    (differentiableOn_tprod_one_sub_pow_mul isOpen_upperHalfPlaneSet (by fun_prop) hq₁
      (by fun_prop))

/-- **The Siegel function has no zeros** on the upper half-plane when `r ∉ ℤ²`. -/
theorem siegelFunction_ne_zero {r : Fin 2 → ℝ} (hr : ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ))
    {τ : ℂ} (hτ : 0 < τ.im) : siegelFunction r τ ≠ 0 := by
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  rw [siegelFunction_eq_qTheta]
  refine mul_ne_zero (by simp [exp_ne_zero]) (qTheta_ne_zero hq fun k hk ↦ ?_)
  have h : cexp (2 * π * I * τ) ^ (-k) * cexp (2 * π * I * (r 0 * τ + r 1)) = 1 := by
    rw [hk, ← zpow_add₀ (exp_ne_zero _), neg_add_cancel, zpow_zero]
  rw [UpperHalfPlane.exp_two_pi_I_zpow_mul_exp] at h
  refine UpperHalfPlane.one_sub_exp_two_pi_I_ne_zero hτ (fun j h0 h1 ↦ hr ![k, j] ?_)
    (sub_eq_zero.mpr h.symm)
  ext i
  fin_cases i
  · push_cast at h0
    simpa using (neg_add_eq_zero.mp h0).symm
  · simpa using h1

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
  simp only [siegelFunction_eq_qTheta, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, hw]
  have h : cexp (π * I * ((r 1 + n : ℝ) : ℂ) * (r 0 - 1)) =
      cexp (n * -(π * I)) * cexp (π * I * n * r 0) * cexp (π * I * r 1 * (r 0 - 1)) := by
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_neg_pi_mul_I]
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
  simp only [siegelFunction_eq_qTheta, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero, hw,
    qTheta_mul_left hq (exp_ne_zero _) (exp_ne_zero _), ← Complex.exp_neg]
  have h : cexp (π * I * bernoulliFun 2 (r 0 + 1) * τ) * cexp (π * I * r 1 * ((r 0 + 1 : ℝ) - 1)) *
      cexp (-(2 * π * I * (r 0 * τ + r 1))) =
      cexp (-(π * I * r 1)) * cexp (π * I * bernoulliFun 2 (r 0) * τ) *
        cexp (π * I * r 1 * (r 0 - 1)) := by
    simp only [← Complex.exp_add, bernoulliFun_two]
    congr 1
    push_cast
    ring
  linear_combination (qTheta (cexp (2 * π * I * τ)) (cexp (2 * π * I * (r 0 * τ + r 1)))) * h

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
      Complex.exp_int_mul, Complex.exp_neg_pi_mul_I]
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
  simp only [siegelFunction_eq_qTheta, Matrix.cons_val_zero, Matrix.cons_val_one,
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
  linear_combination (-qTheta (cexp (2 * π * I * τ))
    (cexp (2 * π * I * (r 0 * τ + ((r 0 + r 1 : ℝ) : ℂ))))) * h

end Translation

section LevelTwo

/-! ### The Siegel functions of level two

With `s = e^{π i τ}`, so that `q = s²`, the three Siegel functions `g_r` with `r ∈ (½ ℤ)² \ ℤ²`
modulo `ℤ²` are the products below. Multiplying them, Euler's identity
`∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 0} (1 - q^{2n+1}) = 1` collapses every infinite product, leaving the
constant `2 ζ₈`. -/

/-- `g_{(0, 1/2)}(τ) = 2 i e^{π i τ / 6} (∏_{n ≥ 1} (1 + qⁿ))²` on the upper half-plane, where
`q = e^{2π i τ}`. -/
theorem siegelFunction_zero_half {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] τ =
      2 * I * cexp (π * I * τ / 6) * (∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (n + 1))) ^ 2 := by
  have hw : cexp (2 * π * I * (((0 : ℝ) : ℂ) * τ + ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [← exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hB : cexp (π * I * bernoulliFun 2 0 * τ) = cexp (π * I * τ / 6) := by
    rw [bernoulliFun_two]
    congr 1
    push_cast
    ring
  have hph : cexp (π * I * ((1 / 2 : ℝ) : ℂ) * (((0 : ℝ) : ℂ) - 1)) = -I := by
    rw [← exp_neg_pi_div_two_mul_I]
    congr 1
    push_cast
    ring
  rw [siegelFunction_eq_qTheta]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hw, hB, hph, qTheta_neg_one (norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩)]
  ring

/-- `g_{(1/2, 0)}(τ) = -e^{-π i τ / 12} (∏_{n ≥ 0} (1 - s^{2n+1}))²` on the upper half-plane,
where `s = e^{π i τ}`. -/
theorem siegelFunction_half_zero {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] τ =
      -cexp (-(π * I * τ / 12)) * (∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * n + 1))) ^ 2 := by
  have hw : cexp (2 * π * I * (((1 / 2 : ℝ) : ℂ) * τ + ((0 : ℝ) : ℂ))) = cexp (π * I * τ) := by
    congr 1
    push_cast
    ring
  have hB : cexp (π * I * bernoulliFun 2 (1 / 2) * τ) = cexp (-(π * I * τ / 12)) := by
    rw [bernoulliFun_two]
    congr 1
    push_cast
    ring
  rw [siegelFunction_eq_qTheta]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq τ, hw, hB,
    qTheta_sq_self (UpperHalfPlane.norm_exp_pi_I_lt_one hτ)]
  simp

/-- `g_{(1/2, 1/2)}(τ) = -e^{-π i / 4} e^{-π i τ / 12} (∏_{n ≥ 0} (1 + s^{2n+1}))²` on the upper
half-plane, where `s = e^{π i τ}`. -/
theorem siegelFunction_half_half {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 1 / 2] τ =
      -cexp (-(π * I / 4)) * cexp (-(π * I * τ / 12)) *
        (∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 2 := by
  have hs : ‖-cexp (π * I * τ)‖ < 1 := by
    rw [norm_neg]
    exact UpperHalfPlane.norm_exp_pi_I_lt_one hτ
  have hq : cexp (2 * π * I * τ) = (-cexp (π * I * τ)) ^ 2 := by
    rw [neg_sq, UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]
  have hw : cexp (2 * π * I * (((1 / 2 : ℝ) : ℂ) * τ + ((1 / 2 : ℝ) : ℂ))) =
      -cexp (π * I * τ) := by
    rw [← mul_neg_one, ← exp_pi_mul_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hB : cexp (π * I * bernoulliFun 2 (1 / 2) * τ) = cexp (-(π * I * τ / 12)) := by
    rw [bernoulliFun_two]
    congr 1
    push_cast
    ring
  have hph : cexp (π * I * ((1 / 2 : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) - 1)) =
      cexp (-(π * I / 4)) := by
    congr 1
    push_cast
    ring
  rw [siegelFunction_eq_qTheta]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hq, hw, hB, hph, qTheta_sq_self hs]
  simp only [one_sub_neg_pow_odd]
  ring

/-- **The product of the level-two Siegel functions**: `g₀ g₁ g₂ = 2 ζ₈` on the upper half-plane,
where `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}`, `g₂ = g_{(1/2, 1/2)}` and `ζ₈ = e^{2π i / 8}`. -/
theorem siegelFunction_zero_half_mul_half_zero_mul_half_half {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] τ * siegelFunction ![1 / 2, 0] τ *
      siegelFunction ![1 / 2, 1 / 2] τ = 2 * cexp (2 * π * I / 8) := by
  -- Euler's identity in `q = s²` with `s = e^{π i τ}`, the odd product in `q` split into two odd
  -- products in `s`: `E O O⁺ = 1` with `E = ∏ (1 + qⁿ)` and `O, O⁺ = ∏ (1 ∓ s^{2n+1})`.
  have heuler := tprod_one_add_pow_mul_tprod_one_sub_pow_odd (norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩)
  rw [UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq τ,
    ← tprod_one_sub_pow_odd_mul_tprod_one_add_pow_odd (UpperHalfPlane.norm_exp_pi_I_lt_one hτ),
    ← mul_assoc] at heuler
  -- The exponential prefactors multiply to `2 ζ₈`.
  have hexp : 2 * I * cexp (π * I * τ / 6) * cexp (-(π * I * τ / 12)) * cexp (-(π * I / 4)) *
      cexp (-(π * I * τ / 12)) = 2 * cexp (2 * π * I / 8) := by
    rw [show 2 * π * I / 8 = π / 2 * I + π * I * τ / 6 + -(π * I * τ / 12) + -(π * I / 4) +
      -(π * I * τ / 12) by ring]
    simp only [Complex.exp_add, exp_pi_div_two_mul_I]
    ring
  rw [siegelFunction_zero_half hτ, siegelFunction_half_zero hτ, siegelFunction_half_half hτ,
    UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq τ, ← hexp]
  -- Write the right-hand side as the prefactor times `(E O O⁺)² = 1`.
  conv_rhs => rw [← mul_one (2 * I * _ * _ * _ * _), ← (one_pow 2 : (1 : ℂ) ^ 2 = 1), ← heuler]
  ring

/-- `g₀(τ + 1) = e^{π i / 6} g₀(τ)` for `g₀ = g_{(0, 1/2)}`. -/
theorem siegelFunction_zero_half_apply_add_one (τ : ℂ) :
    siegelFunction ![0, 1 / 2] (τ + 1) = cexp (π * I / 6) * siegelFunction ![0, 1 / 2] τ := by
  rw [siegelFunction_apply_add_one]
  simp

/-- `g₁(τ + 1) = e^{π i / 6} g₂(τ)` for `g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}`. -/
theorem siegelFunction_half_zero_apply_add_one (τ : ℂ) :
    siegelFunction ![1 / 2, 0] (τ + 1) = cexp (π * I / 6) * siegelFunction ![1 / 2, 1 / 2] τ := by
  rw [siegelFunction_apply_add_one]
  simp

/-- `g₂(τ + 1) = e^{-π i / 3} g₁(τ)` on the upper half-plane, for `g₁ = g_{(1/2, 0)}` and
`g₂ = g_{(1/2, 1/2)}`. -/
theorem siegelFunction_half_half_apply_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 1 / 2] (τ + 1) =
      cexp (-(π * I / 3)) * siegelFunction ![1 / 2, 0] τ := by
  -- `g₂ T = g_{(1/2, 1)}`, the translate of `g₁` by `(0, 1)`.
  have h := siegelFunction_add_intCast ![1 / 2, 0] ![0, 1] hτ
  rw [show (![1 / 2, 0] + fun i ↦ ((![0, 1] i : ℤ) : ℝ)) = ![1 / 2, 1 / 2 + 1 / 2] by
    ext i; fin_cases i <;> norm_num] at h
  have he : cexp (-(π * I / 3)) = -cexp (π * I / 6) * cexp (π * I / 2) := by
    rw [show -(π * I / 3) = π * I / 6 + π * I / 2 + -(π * I) by ring, Complex.exp_add,
      Complex.exp_add, exp_neg_pi_mul_I]
    ring
  rw [siegelFunction_apply_add_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h ⊢
  rw [h, he]
  push_cast
  ring_nf

end LevelTwo

end TauCeti.ModularForm
