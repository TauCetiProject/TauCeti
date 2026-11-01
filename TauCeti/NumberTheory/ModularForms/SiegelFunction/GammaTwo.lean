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
# The cube root `γ₂` of the modular invariant `j`

Let `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}` be the three Siegel
functions of level two. This file proves **Weber's identity**

  `g₀⁴ + g₁⁴ + g₂⁴ = 0`,

which in Weber's notation (`g₀⁴ = 𝔣₂⁸`, `g₁⁴ = 𝔣₁⁸`, `g₂⁴ = -𝔣⁸`) reads `𝔣₁⁸ + 𝔣₂⁸ = 𝔣⁸`, and uses
it to construct the holomorphic cube root

  `γ₂ = (g₀¹² + 16) / g₀⁴ = (g₁¹² + 16) / g₁⁴ = (g₂¹² + 16) / g₂⁴`

of `j`. Weber's cubic `(g¹² + 16)³ = j g¹²`
(`siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three` and its companions) shows that each of
the three quotients is a cube root of `j`; Weber's identity and `g₀ g₁ g₂ = 2 ζ₈` show that they are
the same function. The function `γ₂` is invariant under `S : τ ↦ -1/τ`, is multiplied by
`e^{-2π i / 3}` under `T : τ ↦ τ + 1`, and has leading Fourier term `q^{-1/3}`:
`γ₂(τ) e^{2π i τ / 3} → 1` at `i∞`. Its values at imaginary quadratic points enter the class number
one problem.

Weber's identity is proved by comparing modular functions. With `ω = e^{2π i / 3}`, the function
`F = g₀⁴ + g₁⁴ + g₂⁴` satisfies `F ∘ S = F` and `F ∘ T = ω F`, because `S` exchanges `g₀⁴` and
`g₁⁴` and fixes `g₂⁴`, while `T` multiplies `g₀⁴` by `ω` and sends `g₁⁴, g₂⁴` to `ω g₂⁴, ω g₁⁴`.
Hence `F³` is a holomorphic `SL₂(ℤ)`-invariant function. With `s = e^{π i τ}` and
`P(s) = ∏_{n ≥ 0} (1 - s^{2n+1})`, the product expansions give `g₀⁴ = 16 q^{1/3} / P(q)⁸` and
`g₁⁴ + g₂⁴ = s^{-1/3} (P(s)⁸ - P(-s)⁸) = q^{1/3} (P(s)⁸ - P(-s)⁸) / s`, so `F → 0` at `i∞` and
`F³` is the constant `0` (`TauCeti.ModularForm.levelOne_eq_of_tendsto_atImInfty`).

## Main definitions and results

* `TauCeti.ModularForm.siegelFunction_pow_four_add_add`: Weber's identity `g₀⁴ + g₁⁴ + g₂⁴ = 0`.
* `TauCeti.ModularForm.gammaTwo`: the function `γ₂ = (g₀¹² + 16) / g₀⁴` on the upper half-plane.
* `TauCeti.ModularForm.gammaTwo_eq_siegelFunction_zero_half`,
  `TauCeti.ModularForm.gammaTwo_eq_siegelFunction_half_zero`,
  `TauCeti.ModularForm.gammaTwo_eq_siegelFunction_half_half`: `γ₂ = (g¹² + 16) / g⁴` for each of
  `g = g₀, g₁, g₂`.
* `TauCeti.ModularForm.gammaTwo_pow_three`: `γ₂³ = j`.
* `TauCeti.ModularForm.mdifferentiable_gammaTwo`: `γ₂` is holomorphic on the upper half-plane.
* `TauCeti.ModularForm.gammaTwo_S_smul`, `TauCeti.ModularForm.gammaTwo_T_smul`: `γ₂ ∘ S = γ₂` and
  `γ₂ ∘ T = e^{-2π i / 3} γ₂`.
* `TauCeti.ModularForm.tendsto_gammaTwo_mul_qParam_atImInfty`: `γ₂(τ) e^{2π i τ / 3} → 1` at `i∞`,
  so the leading Fourier term of `γ₂` is `q^{-1/3}`.

## References

* H. Weber, *Lehrbuch der Algebra*, Band III (the identity `𝔣₁⁸ + 𝔣₂⁸ = 𝔣⁸` and the cube root
  of `j`).
* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber's functions and
  `γ₂ = (𝔣²⁴ - 16) / 𝔣⁸ = (𝔣₁²⁴ + 16) / 𝔣₁⁸ = (𝔣₂²⁴ + 16) / 𝔣₂⁸`).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups Manifold

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-! ### The fourth powers as products -/

/-- The odd product `∏_{n ≥ 0} (1 - q^{2n+1})` does not vanish at `q = e^{2π i τ}`. -/
private theorem tprod_one_sub_qParam_pow_odd_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ≠ 0 := by
  have hq : 𝕢 1 τ = cexp (2 * π * I * τ) := by simp [Function.Periodic.qParam]
  rw [hq]
  exact right_ne_zero_of_mul_eq_one
    (tprod_one_add_pow_mul_tprod_one_sub_pow_odd (norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩))

/-- `g₀⁴ = 16 q^{1/3} / (∏_{n ≥ 0} (1 - q^{2n+1}))⁸` for `q = e^{2π i τ}`, where
`q^{1/3} = e^{2π i τ / 3}`. -/
private theorem siegelFunction_zero_half_pow_four {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] τ ^ 4 =
      16 * 𝕢 3 τ / (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 8 := by
  have hq : 𝕢 1 τ = cexp (2 * π * I * τ) := by simp [Function.Periodic.qParam]
  have heuler :=
    tprod_one_add_pow_mul_tprod_one_sub_pow_odd (norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩)
  have he : cexp (π * I * τ / 6) ^ 4 = 𝕢 3 τ := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [eq_div_iff (pow_ne_zero 8 (tprod_one_sub_qParam_pow_odd_ne_zero hτ)), hq,
    siegelFunction_zero_half hτ, ← he]
  calc (2 * I * cexp (π * I * τ / 6) * (∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (n + 1))) ^ 2) ^ 4 *
        (∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (2 * n + 1))) ^ 8
      = 16 * I ^ 4 * cexp (π * I * τ / 6) ^ 4 *
          ((∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (n + 1))) *
            ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (2 * n + 1))) ^ 8 := by ring
    _ = 16 * cexp (π * I * τ / 6) ^ 4 := by rw [heuler, I_pow_four]; ring

/-- `g₁⁴ = s^{-1/3} (∏_{n ≥ 0} (1 - s^{2n+1}))⁸` for `s = e^{π i τ}`, where
`s^{-1/3} = e^{-π i τ / 3}`. -/
private theorem siegelFunction_half_zero_pow_four {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] τ ^ 4 =
      cexp (-(π * I * τ / 3)) * (∏' n : ℕ, (1 - 𝕢 2 τ ^ (2 * n + 1))) ^ 8 := by
  have hs : cexp (π * I * τ) = 𝕢 2 τ := by
    rw [Function.Periodic.qParam]
    congr 1
    push_cast
    ring
  have he : cexp (-(π * I * τ / 12)) ^ 4 = cexp (-(π * I * τ / 3)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [siegelFunction_half_zero hτ, hs, mul_pow, neg_pow, he, ← pow_mul]
  norm_num

/-- `g₂⁴ = -s^{-1/3} (∏_{n ≥ 0} (1 - (-s)^{2n+1}))⁸` for `s = e^{π i τ}`, where
`s^{-1/3} = e^{-π i τ / 3}`. -/
private theorem siegelFunction_half_half_pow_four {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 1 / 2] τ ^ 4 =
      -(cexp (-(π * I * τ / 3)) * (∏' n : ℕ, (1 - (-𝕢 2 τ) ^ (2 * n + 1))) ^ 8) := by
  have hs : cexp (π * I * τ) = 𝕢 2 τ := by
    rw [Function.Periodic.qParam]
    congr 1
    push_cast
    ring
  have he : cexp (-(π * I * τ / 12)) ^ 4 = cexp (-(π * I * τ / 3)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h₄ : cexp (-(π * I / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, ← exp_neg_pi_mul_I]
    congr 1
    push_cast
    ring
  have hodd : ∏' n : ℕ, (1 + 𝕢 2 τ ^ (2 * n + 1)) = ∏' n : ℕ, (1 - (-𝕢 2 τ) ^ (2 * n + 1)) :=
    tprod_congr fun n ↦ (one_sub_neg_pow_odd _ n).symm
  rw [siegelFunction_half_half hτ, hs, hodd, mul_pow, mul_pow, neg_pow, he, h₄, ← pow_mul]
  norm_num

/-- `g₀⁴ g₁⁴ g₂⁴ = -16`, the fourth power of `g₀ g₁ g₂ = 2 ζ₈`. -/
private theorem siegelFunction_pow_four_mul_mul {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4 *
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 = -16 := by
  have h₈ : cexp (2 * π * I / 8) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, ← exp_pi_mul_I]
    congr 1
    push_cast
    ring
  rw [← mul_pow, ← mul_pow, siegelFunction_zero_half_mul_half_zero_mul_half_half hτ, mul_pow, h₈]
  norm_num

/-! ### Weber's identity -/

/-- The function `g₀⁴ + g₁⁴ + g₂⁴`, which Weber's identity shows to vanish. -/
private noncomputable def weberSum (τ : ℂ) : ℂ :=
  siegelFunction ![0, 1 / 2] τ ^ 4 + siegelFunction ![1 / 2, 0] τ ^ 4 +
    siegelFunction ![1 / 2, 1 / 2] τ ^ 4

/-- `S` exchanges `g₀⁴` and `g₁⁴` and fixes `g₂⁴`. -/
private theorem weberSum_S_smul (τ : ℍ) : weberSum ↑(ModularGroup.S • τ) = weberSum τ := by
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
    rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
  rw [weberSum, weberSum, hS, siegelFunction_zero_half_apply_neg_one_div τ.im_pos,
    siegelFunction_half_zero_apply_neg_one_div τ.im_pos,
    siegelFunction_half_half_apply_neg_one_div τ.im_pos, mul_pow, mul_pow, neg_pow, I_pow_four]
  ring

/-- `T` multiplies `g₀⁴ + g₁⁴ + g₂⁴` by `e^{2π i / 3}`. -/
private theorem weberSum_T_smul (τ : ℍ) :
    weberSum ↑(ModularGroup.T • τ) = cexp (2 * π * I / 3) * weberSum τ := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd, add_comm, ofReal_one]
  have h₆ : cexp (π * I / 6) ^ 4 = cexp (2 * π * I / 3) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h₃ : cexp (-(π * I / 3)) ^ 4 = cexp (2 * π * I / 3) := by
    rw [← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * -(π * I / 3) =
      2 * π * I / 3 + ((-1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, Complex.exp_add,
      exp_int_mul_two_pi_mul_I, mul_one]
  rw [weberSum, weberSum, hT, siegelFunction_zero_half_apply_add_one,
    siegelFunction_half_zero_apply_add_one, siegelFunction_half_half_apply_add_one, mul_pow,
    mul_pow, mul_pow, h₆, h₃]
  ring

/-- The cube of `g₀⁴ + g₁⁴ + g₂⁴` is invariant under `SL₂(ℤ)`. -/
private theorem weberSum_pow_three_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    weberSum ↑(γ • τ) ^ 3 = weberSum τ ^ 3 := by
  have hω : cexp (2 * π * I / 3) ^ 3 = 1 := by
    rw [← Complex.exp_nat_mul, ← exp_two_pi_mul_I]
    congr 1
    push_cast
    ring
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing τ with
  | one => rw [one_smul]
  | mem g hg =>
    rcases hg with rfl | rfl
    · rw [weberSum_S_smul]
    · rw [weberSum_T_smul, mul_pow, hω, one_mul]
  | mul g h _ _ hg hh => rw [mul_smul, hg, hh]
  | inv g _ hg => rw [← hg, smul_inv_smul]

/-- `g₀⁴ + g₁⁴ + g₂⁴ → 0` at `i∞`. -/
private theorem tendsto_weberSum_atImInfty :
    Tendsto (fun τ : ℍ ↦ weberSum τ) atImInfty (𝓝 0) := by
  have hq₁ := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty one_pos).mono_right
    nhdsWithin_le_nhds
  have hq₃ := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty (w := 3) (by norm_num)).mono_right
    nhdsWithin_le_nhds
  -- `P(s)⁸ = 1 - 8 s + O(s²)` for `P(s) = ∏_{n ≥ 0} (1 - s^{2n+1})`.
  have hP : HasDerivAt (fun s : ℂ ↦ (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 8) (-8) 0 := by
    simpa using (hasDerivAt_tprod_one_sub_pow_odd (𝕜 := ℂ)).fun_pow 8
  have hP₀ : (∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 1))) ^ 8 = 1 := by simp
  -- `g₀⁴ = 16 q^{1/3} / P(q)⁸ → 0`.
  have h₀ : Tendsto (fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ ^ 4) atImInfty (𝓝 0) := by
    have h := (hq₃.const_mul 16).div (hP.continuousAt.tendsto.comp hq₁) (by simp)
    simp only [mul_zero, zero_div, hP₀] at h
    exact h.congr fun τ ↦ (siegelFunction_zero_half_pow_four τ.im_pos).symm
  -- `g₁⁴ + g₂⁴ = q^{1/3} (P(s)⁸ - P(-s)⁸) / s → 0 · (-16)`.
  have h₁₂ : Tendsto (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ ^ 4 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4) atImInfty (𝓝 0) := by
    have hPneg : HasDerivAt (fun s : ℂ ↦ (∏' n : ℕ, (1 - (-s) ^ (2 * n + 1))) ^ 8) 8 0 := by
      have h : HasDerivAt (fun s : ℂ ↦ (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 8) (-8) (-0) := by
        rw [neg_zero]
        exact hP
      have h' := h.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
      rw [show (-8 : ℂ) * -1 = 8 by norm_num] at h'
      exact h'
    have hslope := ((hP.tendsto_slope_zero.sub hPneg.tendsto_slope_zero).comp
      (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty two_pos))
    have h := hq₃.mul hslope
    rw [zero_mul] at h
    refine h.congr fun τ ↦ ?_
    have hs₀ : 𝕢 2 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have he : 𝕢 3 (τ : ℂ) = cexp (-(π * I * τ / 3)) * 𝕢 2 τ := by
      simp only [Function.Periodic.qParam, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [Function.comp_apply, zero_add, smul_eq_mul, hP₀, neg_zero]
    rw [siegelFunction_half_zero_pow_four τ.im_pos, siegelFunction_half_half_pow_four τ.im_pos, he]
    field_simp
    ring
  have h := h₀.add h₁₂
  rw [zero_add] at h
  exact h.congr fun τ ↦ by rw [weberSum]; ring

/-- **Weber's identity** `g₀⁴ + g₁⁴ + g₂⁴ = 0` for the level-two Siegel functions
`g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}`. In Weber's notation it reads
`𝔣₁⁸ + 𝔣₂⁸ = 𝔣⁸`. -/
theorem siegelFunction_pow_four_add_add (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ^ 4 + siegelFunction ![1 / 2, 0] τ ^ 4 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 = 0 := by
  have h := levelOne_eq_of_tendsto_atImInfty (F := fun τ : ℍ ↦ weberSum τ ^ 3) (c := 0) ?_
    weberSum_pow_three_smul ?_ τ
  · exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h
  · exact ((((mdifferentiable_siegelFunction _).pow 4).add
      ((mdifferentiable_siegelFunction _).pow 4)).add
      ((mdifferentiable_siegelFunction _).pow 4)).pow 3
  · simpa using tendsto_weberSum_atImInfty.pow 3

/-! ### The cube root `γ₂` of `j` -/

/-- **The cube root `γ₂` of `j`**: `γ₂(τ) = (g₀(τ)¹² + 16) / g₀(τ)⁴` for `g₀ = g_{(0, 1/2)}`. It
is holomorphic on the upper half-plane, satisfies `γ₂³ = j` and has leading Fourier term
`q^{-1/3}`. -/
noncomputable def gammaTwo (τ : ℍ) : ℂ :=
  (siegelFunction ![0, 1 / 2] τ ^ 12 + 16) / siegelFunction ![0, 1 / 2] τ ^ 4

/-- `γ₂ = (g₀¹² + 16) / g₀⁴` for `g₀ = g_{(0, 1/2)}`. -/
theorem gammaTwo_eq_siegelFunction_zero_half (τ : ℍ) :
    gammaTwo τ = (siegelFunction ![0, 1 / 2] τ ^ 12 + 16) / siegelFunction ![0, 1 / 2] τ ^ 4 :=
  (rfl)

/-- `(a³ + 16) / a = (b³ + 16) / b` when `a + b + c = 0` and `a b c = -16`. -/
private theorem pow_three_add_sixteen_div_eq {a b c : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : a + b + c = 0) (h₂ : a * b * c = -16) : (a ^ 3 + 16) / a = (b ^ 3 + 16) / b := by
  rw [div_eq_div_iff ha hb]
  linear_combination (a - b) * a * b * h₁ - (a - b) * h₂

/-- The fourth powers of `g₀, g₁, g₂` do not vanish, since their product is `-16`. -/
private theorem siegelFunction_pow_four_ne_zero (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ^ 4 ≠ 0 ∧ siegelFunction ![1 / 2, 0] τ ^ 4 ≠ 0 ∧
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 ≠ 0 := by
  have h : siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4 *
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 ≠ 0 := by
    rw [siegelFunction_pow_four_mul_mul τ.im_pos]
    norm_num
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h), right_ne_zero_of_mul (left_ne_zero_of_mul h),
    right_ne_zero_of_mul h⟩

/-- `γ₂ = (g₁¹² + 16) / g₁⁴` for `g₁ = g_{(1/2, 0)}`. -/
theorem gammaTwo_eq_siegelFunction_half_zero (τ : ℍ) :
    gammaTwo τ = (siegelFunction ![1 / 2, 0] τ ^ 12 + 16) / siegelFunction ![1 / 2, 0] τ ^ 4 := by
  have h := pow_three_add_sixteen_div_eq (siegelFunction_pow_four_ne_zero τ).1
    (siegelFunction_pow_four_ne_zero τ).2.1 (siegelFunction_pow_four_add_add τ)
    (siegelFunction_pow_four_mul_mul τ.im_pos)
  rw [gammaTwo_eq_siegelFunction_zero_half]
  simpa only [← pow_mul, Nat.reduceMul] using h

/-- `γ₂ = (g₂¹² + 16) / g₂⁴` for `g₂ = g_{(1/2, 1/2)}`. -/
theorem gammaTwo_eq_siegelFunction_half_half (τ : ℍ) :
    gammaTwo τ =
      (siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + 16) / siegelFunction ![1 / 2, 1 / 2] τ ^ 4 := by
  have h := pow_three_add_sixteen_div_eq (c := siegelFunction ![1 / 2, 0] τ ^ 4)
    (siegelFunction_pow_four_ne_zero τ).1 (siegelFunction_pow_four_ne_zero τ).2.2
    (by linear_combination siegelFunction_pow_four_add_add τ)
    (by linear_combination siegelFunction_pow_four_mul_mul τ.im_pos)
  rw [gammaTwo_eq_siegelFunction_zero_half]
  simpa only [← pow_mul, Nat.reduceMul] using h

/-- **`γ₂` is a cube root of `j`**: `γ₂³ = j`. -/
@[simp]
theorem gammaTwo_pow_three (τ : ℍ) : gammaTwo τ ^ 3 = j τ := by
  have hg : siegelFunction ![0, 1 / 2] τ ^ 12 ≠ 0 := by
    rw [show (12 : ℕ) = 4 * 3 by rfl, pow_mul]
    exact pow_ne_zero 3 (siegelFunction_pow_four_ne_zero τ).1
  rw [gammaTwo_eq_siegelFunction_zero_half, div_pow, ← pow_mul,
    siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three, mul_div_assoc, div_self hg, mul_one]

/-- `γ₂` is holomorphic on the upper half-plane. -/
theorem mdifferentiable_gammaTwo : MDiff gammaTwo := by
  have hg := mdifferentiable_siegelFunction ![0, 1 / 2]
  have h := ((hg.pow 12).add (mdifferentiable_const (c := (16 : ℂ)))).mul
    ((hg.pow 4).inv fun τ ↦ (siegelFunction_pow_four_ne_zero τ).1)
  convert h using 1
  ext τ
  simp only [gammaTwo_eq_siegelFunction_zero_half, div_eq_mul_inv, Pi.mul_apply, Pi.add_apply,
    Pi.pow_apply, Pi.inv_apply]

/-- `γ₂` is invariant under `S : τ ↦ -1/τ`. -/
theorem gammaTwo_S_smul (τ : ℍ) : gammaTwo (ModularGroup.S • τ) = gammaTwo τ := by
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
    rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
  have hI : (-I) ^ 4 = 1 := by rw [neg_pow, I_pow_four]; norm_num
  rw [gammaTwo_eq_siegelFunction_zero_half, hS,
    siegelFunction_zero_half_apply_neg_one_div τ.im_pos, gammaTwo_eq_siegelFunction_half_zero,
    show (12 : ℕ) = 4 * 3 by rfl, mul_pow, mul_pow, pow_mul, pow_mul, hI]
  simp

/-- `γ₂` is multiplied by `e^{-2π i / 3}` under `T : τ ↦ τ + 1`. -/
theorem gammaTwo_T_smul (τ : ℍ) :
    gammaTwo (ModularGroup.T • τ) = cexp (-(2 * π * I / 3)) * gammaTwo τ := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd, add_comm, ofReal_one]
  have h₄ : cexp (π * I / 6) ^ 4 = cexp (2 * π * I / 3) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h₁₂ : cexp (π * I / 6) ^ 12 = 1 := by
    rw [← Complex.exp_nat_mul, ← exp_two_pi_mul_I]
    congr 1
    push_cast
    ring
  have hinv : cexp (-(2 * π * I / 3)) = (cexp (2 * π * I / 3))⁻¹ := Complex.exp_neg _
  rw [gammaTwo_eq_siegelFunction_zero_half, gammaTwo_eq_siegelFunction_zero_half, hT,
    siegelFunction_zero_half_apply_add_one, mul_pow, mul_pow, h₄, h₁₂, hinv, one_mul,
    mul_div_assoc', inv_mul_eq_div, div_div]

/-- **The leading Fourier term of `γ₂` is `q^{-1/3}`**: `γ₂(τ) e^{2π i τ / 3} → 1` as
`Im τ → ∞`. -/
theorem tendsto_gammaTwo_mul_qParam_atImInfty :
    Tendsto (fun τ : ℍ ↦ gammaTwo τ * 𝕢 3 τ) atImInfty (𝓝 1) := by
  have hq₁ := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty one_pos).mono_right
    nhdsWithin_le_nhds
  have hq₃ := (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty (w := 3) (by norm_num)).mono_right
    nhdsWithin_le_nhds
  have hP : Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 8) atImInfty (𝓝 1) := by
    have h := ((hasDerivAt_tprod_one_sub_pow_odd (𝕜 := ℂ)).continuousAt.tendsto.comp hq₁).pow 8
    simpa using h
  -- `γ₂ q^{1/3} = g₀⁸ q^{1/3} + P(q)⁸` with `g₀⁴ = 16 q^{1/3} / P(q)⁸`.
  have h := ((((hq₃.const_mul 16).div hP one_ne_zero).pow 2).mul hq₃).add hP
  simp only [mul_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add] at h
  refine h.congr fun τ ↦ ?_
  rw [Pi.div_apply]
  have hO := tprod_one_sub_qParam_pow_odd_ne_zero τ.im_pos
  have hq₀ : 𝕢 3 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  rw [gammaTwo_eq_siegelFunction_zero_half, show (12 : ℕ) = 4 * 3 by rfl, pow_mul,
    siegelFunction_zero_half_pow_four τ.im_pos]
  field_simp

end TauCeti.ModularForm
