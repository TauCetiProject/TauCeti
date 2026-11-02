/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.JInvariant
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.Analysis.Complex.UpperHalfPlane.CuspCoordinate
import TauCeti.NumberTheory.ModularForms.LevelOne.Invariant

/-!
# The cube root `γ₂` of `j`

Write `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}` for the three Siegel
functions of level two. Their fourth powers satisfy **Weber's linear relation**

  `g₀⁴ + g₁⁴ + g₂⁴ = 0`,

which in Weber's notation is `𝔣⁸ = 𝔣₁⁸ + 𝔣₂⁸` (`g₀⁴ = 𝔣₂⁸`, `g₁⁴ = 𝔣₁⁸`, `g₂⁴ = -𝔣⁸`). This file
proves it and uses it to construct the holomorphic cube root

  `γ₂ = -(g₀⁴ g₁⁴ + g₀⁴ g₂⁴ + g₁⁴ g₂⁴)`

of the modular invariant `j`. Since `g₀⁴ g₁⁴ g₂⁴ = (2 ζ₈)⁴ = -16`, Weber's linear relation shows
`γ₂ g⁴ = g¹² + 16` for each `g = g₀, g₁, g₂`, that is `γ₂ = (g¹² + 16) / g⁴`; cubing and comparing
with Weber's cubic `(g¹² + 16)³ = j g¹²` gives `γ₂³ = j`. The function `γ₂` is invariant under
`τ ↦ -1/τ`, is multiplied by `e^{-2π i / 3}` under `τ ↦ τ + 1`, and has leading Fourier term
`q^{-1/3}`: `γ₂(τ) e^{2π i τ / 3} → 1` at `i∞`.

The proof of the linear relation is a comparison of modular functions. Under `τ ↦ -1/τ` the fourth
powers are permuted, and under `τ ↦ τ + 1` they are permuted and multiplied by `e^{2π i / 3}`, so
the cube of `g₀⁴ + g₁⁴ + g₂⁴` is a holomorphic `SL₂(ℤ)`-invariant function. With `s = e^{π i τ}`
and `P(s) = ∏_{n ≥ 0} (1 - s^{2n+1})`, one has `g₁⁴ + g₂⁴ = e^{-π i τ / 3} (P(s)⁸ - P(-s)⁸)`, which
is `e^{2π i τ / 3}` times a function tending to `-16`, and `g₀⁴ = 16 e^{2π i τ / 3} / P(q)⁸`. So
the sum tends to `0` at `i∞`, and its cube vanishes identically
(`TauCeti.ModularForm.levelOne_eq_of_tendsto_atImInfty`).

## Main definitions and results

* `TauCeti.ModularForm.siegelFunction_pow_four_add_add_eq_zero`: Weber's linear relation
  `g₀⁴ + g₁⁴ + g₂⁴ = 0`.
* `TauCeti.ModularForm.gammaTwo`: the function `γ₂ = -(g₀⁴ g₁⁴ + g₀⁴ g₂⁴ + g₁⁴ g₂⁴)` on the upper
  half-plane.
* `TauCeti.ModularForm.gammaTwo_eq_siegelFunction_zero_half`,
  `TauCeti.ModularForm.gammaTwo_eq_siegelFunction_half_zero`,
  `TauCeti.ModularForm.gammaTwo_eq_siegelFunction_half_half`: `γ₂ = (g¹² + 16) / g⁴` for
  `g = g₀, g₁, g₂`.
* `TauCeti.ModularForm.gammaTwo_pow_three`: `γ₂³ = j`.
* `TauCeti.ModularForm.mdifferentiable_gammaTwo`: `γ₂` is holomorphic on the upper half-plane.
* `TauCeti.ModularForm.gammaTwo_S_smul`, `TauCeti.ModularForm.gammaTwo_T_smul`: the
  transformation of `γ₂` under `S` and `T`.
* `TauCeti.ModularForm.tendsto_gammaTwo_mul_qParam_atImInfty`: the leading Fourier term of `γ₂`
  is `q^{-1/3}`.

## References

* H. Weber, *Lehrbuch der Algebra*, Band III, §§ 34, 54 (the relation `𝔣⁸ = 𝔣₁⁸ + 𝔣₂⁸` and the
  function `γ₂`).
* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber's functions and `γ₂ = (𝔣²⁴ - 16) / 𝔣⁸`).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups Manifold

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-! ### The fourth powers under `S` and `T` -/

/-- The sum `g₀⁴ + g₁⁴ + g₂⁴` of the fourth powers of the level-two Siegel functions is multiplied
by `e^{2π i / 3}` under `τ ↦ τ + 1`. -/
private theorem siegelFunction_pow_four_add_add_apply_add_one (τ : ℂ) :
    siegelFunction ![0, 1 / 2] (τ + 1) ^ 4 + siegelFunction ![1 / 2, 0] (τ + 1) ^ 4 +
        siegelFunction ![1 / 2, 1 / 2] (τ + 1) ^ 4 =
      cexp (2 * π * I / 3) * (siegelFunction ![0, 1 / 2] τ ^ 4 +
        siegelFunction ![1 / 2, 0] τ ^ 4 + siegelFunction ![1 / 2, 1 / 2] τ ^ 4) := by
  have h₆ : cexp (π * I / 6) ^ 4 = cexp (2 * π * I / 3) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h₃ : cexp (-(π * I / 3)) ^ 4 = cexp (2 * π * I / 3) := by
    have harg : ((4 : ℕ) : ℂ) * -(π * I / 3) = 2 * π * I / 3 + ((-1 : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [← Complex.exp_nat_mul, harg, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  rw [siegelFunction_zero_half_apply_add_one, siegelFunction_half_zero_apply_add_one,
    siegelFunction_half_half_apply_add_one, mul_pow, mul_pow, mul_pow, h₆, h₃]
  ring

/-- The sum `g₀⁴ + g₁⁴ + g₂⁴` is invariant under `τ ↦ -1/τ`. -/
private theorem siegelFunction_pow_four_add_add_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] (-1 / τ) ^ 4 + siegelFunction ![1 / 2, 0] (-1 / τ) ^ 4 +
        siegelFunction ![1 / 2, 1 / 2] (-1 / τ) ^ 4 =
      siegelFunction ![0, 1 / 2] τ ^ 4 + siegelFunction ![1 / 2, 0] τ ^ 4 +
        siegelFunction ![1 / 2, 1 / 2] τ ^ 4 := by
  rw [siegelFunction_zero_half_apply_neg_one_div hτ, siegelFunction_half_zero_apply_neg_one_div hτ,
    siegelFunction_half_half_apply_neg_one_div hτ]
  rw [mul_pow, mul_pow, neg_pow, I_pow_four]
  ring

/-- The cube of `g₀⁴ + g₁⁴ + g₂⁴` is invariant under `SL₂(ℤ)`. -/
private theorem siegelFunction_pow_four_add_add_pow_three_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (siegelFunction ![0, 1 / 2] ↑(γ • τ) ^ 4 + siegelFunction ![1 / 2, 0] ↑(γ • τ) ^ 4 +
        siegelFunction ![1 / 2, 1 / 2] ↑(γ • τ) ^ 4) ^ 3 =
      (siegelFunction ![0, 1 / 2] τ ^ 4 + siegelFunction ![1 / 2, 0] τ ^ 4 +
        siegelFunction ![1 / 2, 1 / 2] τ ^ 4) ^ 3 := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing τ with
  | one => rw [one_smul]
  | mem g hg =>
    rcases hg with rfl | rfl
    · have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
        rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
      rw [hS, siegelFunction_pow_four_add_add_apply_neg_one_div τ.im_pos]
    · have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
        rw [modular_T_smul, coe_vadd, add_comm, ofReal_one]
      have h₃ : cexp (2 * π * I / 3) ^ 3 = 1 := by
        rw [← Complex.exp_nat_mul, ← exp_two_pi_mul_I]
        congr 1
        push_cast
        ring
      rw [hT, siegelFunction_pow_four_add_add_apply_add_one, mul_pow, h₃, one_mul]
  | mul g h _ _ hg hh => rw [mul_smul, hg, hh]
  | inv g _ hg => rw [← hg, smul_inv_smul]

/-! ### The fourth powers as products in `s = e^{π i τ}` -/

/-- `e^{-π i τ / 12}⁴ = e^{-π i τ / 3}`. -/
private theorem exp_neg_pi_I_mul_div_twelve_pow_four (τ : ℂ) :
    cexp (-(π * I * τ / 12)) ^ 4 = cexp (-(π * I * τ / 3)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `g₁⁴ = e^{-π i τ / 3} (∏_{n ≥ 0} (1 - s^{2n+1}))⁸` for `s = e^{π i τ}`. -/
private theorem siegelFunction_half_zero_pow_four {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] τ ^ 4 =
      cexp (-(π * I * τ / 3)) * (∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * n + 1))) ^ 8 := by
  rw [siegelFunction_half_zero hτ, mul_pow, neg_pow, exp_neg_pi_I_mul_div_twelve_pow_four,
    ← pow_mul]
  norm_num

/-- `g₂⁴ = -e^{-π i τ / 3} (∏_{n ≥ 0} (1 - (-s)^{2n+1}))⁸` for `s = e^{π i τ}`. -/
private theorem siegelFunction_half_half_pow_four {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 1 / 2] τ ^ 4 =
      -(cexp (-(π * I * τ / 3)) * (∏' n : ℕ, (1 - (-cexp (π * I * τ)) ^ (2 * n + 1))) ^ 8) := by
  have h₄ : cexp (-(π * I / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * -(π * I / 4) = -(π * I) by push_cast; ring,
      Complex.exp_neg, exp_pi_mul_I]
    norm_num
  have hodd : ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1)) =
      ∏' n : ℕ, (1 - (-cexp (π * I * τ)) ^ (2 * n + 1)) :=
    tprod_congr fun n ↦ (one_sub_neg_pow_odd _ n).symm
  rw [siegelFunction_half_half hτ, hodd, mul_pow, mul_pow, neg_pow, h₄,
    exp_neg_pi_I_mul_div_twelve_pow_four, ← pow_mul]
  norm_num

/-- `g₀⁴ g₁⁴ g₂⁴ = -16`, the fourth power of `g₀ g₁ g₂ = 2 ζ₈`. -/
private theorem siegelFunction_pow_four_mul_mul {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4 *
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 = -16 := by
  have h₈ : cexp (2 * π * I / 8) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * (2 * π * I / 8) = π * I by push_cast; ring,
      exp_pi_mul_I]
  rw [← mul_pow, ← mul_pow, siegelFunction_zero_half_mul_half_zero_mul_half_half hτ, mul_pow, h₈]
  norm_num

/-- `g₁⁴ g₂⁴ = -q^{-1/3} (∏_{n ≥ 0} (1 - q^{2n+1}))⁸` for `q = e^{2π i τ}`, where
`q^{1/3} = e^{2π i τ / 3}`. -/
private theorem siegelFunction_half_zero_pow_four_mul {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] τ ^ 4 * siegelFunction ![1 / 2, 1 / 2] τ ^ 4 * 𝕢 3 τ =
      -(∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 8 := by
  have hq : 𝕢 1 τ = cexp (π * I * τ) ^ 2 := by
    rw [Function.Periodic.qParam, ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq, ofReal_one,
      div_one]
  have he : cexp (-(π * I * τ / 3)) ^ 2 * 𝕢 3 τ = 1 := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  rw [siegelFunction_half_zero_pow_four hτ, siegelFunction_half_half_pow_four hτ, hq,
    ← tprod_one_sub_pow_odd_mul_tprod_one_add_pow_odd (UpperHalfPlane.norm_exp_pi_I_lt_one hτ)]
  simp only [one_sub_neg_pow_odd]
  linear_combination (-(∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * n + 1))) ^ 8 *
    (∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 8) * he

/-! ### Limits at `i∞` -/

/-- `P(q)⁸ → 1` at `i∞`, for `P(q) = ∏_{n ≥ 0} (1 - q^{2n+1})`. -/
private theorem tendsto_tprod_one_sub_qParam_pow_odd_pow_eight :
    Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 8) atImInfty (𝓝 1) := by
  have hq := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty one_pos).mono_right
    nhdsWithin_le_nhds
  have h := ((hasDerivAt_tprod_one_sub_pow_odd (𝕜 := ℂ)).continuousAt.tendsto.comp hq).pow 8
  simpa using h

/-- `g₁⁴ + g₂⁴ → 0` at `i∞`. -/
private theorem tendsto_siegelFunction_half_zero_pow_four_add :
    Tendsto (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ ^ 4 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4) atImInfty (𝓝 0) := by
  -- The two slopes of `P(s)⁸` at `0`, in the directions `s` and `-s`.
  have hP : HasDerivAt (fun s : ℂ ↦ (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 8) (-8) 0 := by
    simpa using (hasDerivAt_tprod_one_sub_pow_odd (𝕜 := ℂ)).fun_pow 8
  have hP' : HasDerivAt (fun s : ℂ ↦ (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 8) (-8) (-0) := by
    rw [neg_zero]
    exact hP
  have h₁ := hP.tendsto_slope_zero
  have h₂ := (hP'.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))).tendsto_slope_zero
  have h := (h₁.sub h₂).comp TauCeti.UpperHalfPlane.tendsto_exp_pi_I_atImInfty
  have hq := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty (w := 3) (by norm_num)).mono_right
    nhdsWithin_le_nhds
  have h' := hq.mul h
  rw [zero_mul] at h'
  refine h'.congr fun τ ↦ ?_
  -- `e^{2π i τ / 3} = e^{-π i τ / 3} s`.
  have hs : cexp (π * I * τ) ≠ 0 := Complex.exp_ne_zero _
  have he : 𝕢 3 τ = cexp (-(π * I * τ / 3)) * cexp (π * I * τ) := by
    rw [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [Function.comp_apply, zero_add, smul_eq_mul, neg_zero]
  rw [siegelFunction_half_zero_pow_four τ.im_pos, siegelFunction_half_half_pow_four τ.im_pos, he]
  field_simp
  ring

/-- `g₀⁴ → 0` at `i∞`. -/
private theorem tendsto_siegelFunction_zero_half_pow_four :
    Tendsto (fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ ^ 4) atImInfty (𝓝 0) := by
  have hq := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty (w := 3) (by norm_num)).mono_right
    nhdsWithin_le_nhds
  have h := (hq.const_mul 16).div tendsto_tprod_one_sub_qParam_pow_odd_pow_eight one_ne_zero
  rw [mul_zero, zero_div] at h
  refine h.congr fun τ ↦ ?_
  -- `g₀⁴ = -16 / (g₁⁴ g₂⁴) = 16 q^{1/3} / P(q)⁸`.
  have h₃ := siegelFunction_pow_four_mul_mul τ.im_pos
  have h₂ := siegelFunction_half_zero_pow_four_mul τ.im_pos
  have hP : (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (2 * n + 1))) ^ 8 ≠ 0 := by
    intro h0
    rw [h0, neg_zero] at h₂
    have hq₀ : 𝕢 3 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have : -16 * 𝕢 3 (τ : ℂ) = 0 := by
      linear_combination siegelFunction ![0, 1 / 2] τ ^ 4 * h₂ - 𝕢 3 (τ : ℂ) * h₃
    simp [hq₀] at this
  rw [Pi.div_apply, div_eq_iff hP]
  linear_combination 𝕢 3 (τ : ℂ) * h₃ - siegelFunction ![0, 1 / 2] τ ^ 4 * h₂

/-! ### Weber's linear relation -/

/-- **Weber's linear relation** `𝔣⁸ = 𝔣₁⁸ + 𝔣₂⁸`: the fourth powers of the level-two Siegel
functions `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}` sum to zero. -/
theorem siegelFunction_pow_four_add_add_eq_zero (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ^ 4 + siegelFunction ![1 / 2, 0] τ ^ 4 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 = 0 := by
  refine pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ?_
  refine levelOne_eq_of_tendsto_atImInfty (F := fun τ : ℍ ↦ (siegelFunction ![0, 1 / 2] τ ^ 4 +
    siegelFunction ![1 / 2, 0] τ ^ 4 + siegelFunction ![1 / 2, 1 / 2] τ ^ 4) ^ 3) ?_
    siegelFunction_pow_four_add_add_pow_three_smul ?_ τ
  · exact ((((mdifferentiable_siegelFunction _).pow 4).add
      ((mdifferentiable_siegelFunction _).pow 4)).add
      ((mdifferentiable_siegelFunction _).pow 4)).pow 3
  · have h := (tendsto_siegelFunction_zero_half_pow_four.add
      tendsto_siegelFunction_half_zero_pow_four_add).pow 3
    rw [zero_add, zero_pow three_ne_zero] at h
    exact h.congr fun τ ↦ by ring

/-! ### The function `γ₂` -/

/-- The function `γ₂ = -(g₀⁴ g₁⁴ + g₀⁴ g₂⁴ + g₁⁴ g₂⁴)` on the upper half-plane, where
`g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}` are the level-two Siegel
functions. It is the holomorphic cube root of `j` with leading Fourier term `q^{-1/3}`
(`gammaTwo_pow_three`, `tendsto_gammaTwo_mul_qParam_atImInfty`), and equals `(g¹² + 16) / g⁴`
for each of `g = g₀, g₁, g₂`. -/
noncomputable def gammaTwo (τ : ℍ) : ℂ :=
  -(siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4 +
    siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 1 / 2] τ ^ 4 +
    siegelFunction ![1 / 2, 0] τ ^ 4 * siegelFunction ![1 / 2, 1 / 2] τ ^ 4)

theorem gammaTwo_apply (τ : ℍ) :
    gammaTwo τ = -(siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4 +
      siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 1 / 2] τ ^ 4 +
      siegelFunction ![1 / 2, 0] τ ^ 4 * siegelFunction ![1 / 2, 1 / 2] τ ^ 4) := by
  rfl

/-- `γ₂ g₀⁴ = g₀¹² + 16` for `g₀ = g_{(0, 1/2)}`. -/
theorem gammaTwo_mul_siegelFunction_zero_half_pow_four (τ : ℍ) :
    gammaTwo τ * siegelFunction ![0, 1 / 2] τ ^ 4 = siegelFunction ![0, 1 / 2] τ ^ 12 + 16 := by
  rw [gammaTwo_apply]
  linear_combination (-(siegelFunction ![0, 1 / 2] τ ^ 4) ^ 2) *
    siegelFunction_pow_four_add_add_eq_zero τ - siegelFunction_pow_four_mul_mul τ.im_pos

/-- `γ₂ g₁⁴ = g₁¹² + 16` for `g₁ = g_{(1/2, 0)}`. -/
theorem gammaTwo_mul_siegelFunction_half_zero_pow_four (τ : ℍ) :
    gammaTwo τ * siegelFunction ![1 / 2, 0] τ ^ 4 = siegelFunction ![1 / 2, 0] τ ^ 12 + 16 := by
  rw [gammaTwo_apply]
  linear_combination (-(siegelFunction ![1 / 2, 0] τ ^ 4) ^ 2) *
    siegelFunction_pow_four_add_add_eq_zero τ - siegelFunction_pow_four_mul_mul τ.im_pos

/-- `γ₂ g₂⁴ = g₂¹² + 16` for `g₂ = g_{(1/2, 1/2)}`. -/
theorem gammaTwo_mul_siegelFunction_half_half_pow_four (τ : ℍ) :
    gammaTwo τ * siegelFunction ![1 / 2, 1 / 2] τ ^ 4 =
      siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + 16 := by
  rw [gammaTwo_apply]
  linear_combination (-(siegelFunction ![1 / 2, 1 / 2] τ ^ 4) ^ 2) *
    siegelFunction_pow_four_add_add_eq_zero τ - siegelFunction_pow_four_mul_mul τ.im_pos

/-- The level-two Siegel functions have no zero on the upper half-plane; here `g₀ g₁ g₂ = 2 ζ₈`
makes this immediate. -/
private theorem siegelFunction_pow_four_ne_zero (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ^ 4 ≠ 0 ∧ siegelFunction ![1 / 2, 0] τ ^ 4 ≠ 0 ∧
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 ≠ 0 := by
  have h := siegelFunction_pow_four_mul_mul τ.im_pos
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_, fun h0 ↦ ?_⟩ <;> rw [h0] at h <;> norm_num at h

/-- `γ₂ = (g₀¹² + 16) / g₀⁴` for `g₀ = g_{(0, 1/2)}`. -/
theorem gammaTwo_eq_siegelFunction_zero_half (τ : ℍ) :
    gammaTwo τ = (siegelFunction ![0, 1 / 2] τ ^ 12 + 16) / siegelFunction ![0, 1 / 2] τ ^ 4 := by
  rw [eq_div_iff (siegelFunction_pow_four_ne_zero τ).1,
    gammaTwo_mul_siegelFunction_zero_half_pow_four]

/-- `γ₂ = (g₁¹² + 16) / g₁⁴` for `g₁ = g_{(1/2, 0)}`. -/
theorem gammaTwo_eq_siegelFunction_half_zero (τ : ℍ) :
    gammaTwo τ = (siegelFunction ![1 / 2, 0] τ ^ 12 + 16) / siegelFunction ![1 / 2, 0] τ ^ 4 := by
  rw [eq_div_iff (siegelFunction_pow_four_ne_zero τ).2.1,
    gammaTwo_mul_siegelFunction_half_zero_pow_four]

/-- `γ₂ = (g₂¹² + 16) / g₂⁴` for `g₂ = g_{(1/2, 1/2)}`. -/
theorem gammaTwo_eq_siegelFunction_half_half (τ : ℍ) :
    gammaTwo τ =
      (siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + 16) / siegelFunction ![1 / 2, 1 / 2] τ ^ 4 := by
  rw [eq_div_iff (siegelFunction_pow_four_ne_zero τ).2.2,
    gammaTwo_mul_siegelFunction_half_half_pow_four]

/-- **`γ₂` is a cube root of `j`**: `γ₂³ = j` on the upper half-plane. -/
theorem gammaTwo_pow_three (τ : ℍ) : gammaTwo τ ^ 3 = j τ := by
  have h₀ : (siegelFunction ![0, 1 / 2] τ ^ 4) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (siegelFunction_pow_four_ne_zero τ).1
  refine mul_right_cancel₀ h₀ ?_
  rw [← mul_pow, gammaTwo_mul_siegelFunction_zero_half_pow_four,
    siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three, ← pow_mul]

/-- `γ₂` is holomorphic on the upper half-plane. -/
theorem mdifferentiable_gammaTwo : MDiff gammaTwo := by
  have h₀ := (mdifferentiable_siegelFunction ![0, 1 / 2]).pow 4
  have h₁ := (mdifferentiable_siegelFunction ![1 / 2, 0]).pow 4
  have h₂ := (mdifferentiable_siegelFunction ![1 / 2, 1 / 2]).pow 4
  exact (((h₀.mul h₁).add (h₀.mul h₂)).add (h₁.mul h₂)).neg

/-- `γ₂(-1/τ) = γ₂(τ)`. -/
theorem gammaTwo_S_smul (τ : ℍ) : gammaTwo (ModularGroup.S • τ) = gammaTwo τ := by
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
    rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
  rw [gammaTwo_apply, gammaTwo_apply, hS, siegelFunction_zero_half_apply_neg_one_div τ.im_pos,
    siegelFunction_half_zero_apply_neg_one_div τ.im_pos,
    siegelFunction_half_half_apply_neg_one_div τ.im_pos]
  rw [mul_pow, mul_pow, neg_pow, I_pow_four]
  ring

/-- `γ₂(τ + 1) = e^{-2π i / 3} γ₂(τ)`. -/
theorem gammaTwo_T_smul (τ : ℍ) :
    gammaTwo (ModularGroup.T • τ) = cexp (-(2 * π * I / 3)) * gammaTwo τ := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd, add_comm, ofReal_one]
  -- The fourth powers pick up `e^{2π i / 3}` from `e^{π i / 6}` and from `e^{-π i / 3}`.
  have h₆ : cexp (π * I / 6) ^ 4 * cexp (π * I / 6) ^ 4 = cexp (-(2 * π * I / 3)) := by
    have harg : ((4 : ℕ) : ℂ) * (π * I / 6) + ((4 : ℕ) : ℂ) * (π * I / 6) =
        -(2 * π * I / 3) + ((1 : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, harg, Complex.exp_add,
      exp_int_mul_two_pi_mul_I, mul_one]
  have h₃ : cexp (π * I / 6) ^ 4 * cexp (-(π * I / 3)) ^ 4 = cexp (-(2 * π * I / 3)) := by
    have harg : ((4 : ℕ) : ℂ) * (π * I / 6) + ((4 : ℕ) : ℂ) * -(π * I / 3) =
        -(2 * π * I / 3) := by
      push_cast
      ring
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, harg]
  rw [gammaTwo_apply, gammaTwo_apply, hT, siegelFunction_zero_half_apply_add_one,
    siegelFunction_half_zero_apply_add_one, siegelFunction_half_half_apply_add_one]
  simp only [mul_pow]
  linear_combination
    (-(siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 1 / 2] τ ^ 4)) * h₆ +
    (-(siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4)) * h₃

/-- **The leading Fourier term of `γ₂` is `q^{-1/3}`**: `γ₂(τ) e^{2π i τ / 3} → 1` at `i∞`. -/
theorem tendsto_gammaTwo_mul_qParam_atImInfty :
    Tendsto (fun τ : ℍ ↦ gammaTwo τ * 𝕢 3 τ) atImInfty (𝓝 1) := by
  have hq := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty (w := 3) (by norm_num)).mono_right
    nhdsWithin_le_nhds
  -- `γ₂ q^{1/3} = -g₀⁴ (g₁⁴ + g₂⁴) q^{1/3} - g₁⁴ g₂⁴ q^{1/3}` and `-g₁⁴ g₂⁴ q^{1/3} = P(q)⁸`,
  -- where `q^{1/3} = e^{2π i τ / 3}` and `P(q) = ∏_{n ≥ 0} (1 - q^{2n+1})`.
  have h := ((tendsto_siegelFunction_zero_half_pow_four.mul
    tendsto_siegelFunction_half_zero_pow_four_add).mul hq).neg.add
    tendsto_tprod_one_sub_qParam_pow_odd_pow_eight
  rw [zero_mul, zero_mul, neg_zero, zero_add] at h
  refine h.congr fun τ ↦ ?_
  rw [gammaTwo_apply]
  linear_combination siegelFunction_half_zero_pow_four_mul τ.im_pos

end TauCeti.ModularForm
