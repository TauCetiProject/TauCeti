/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.JInvariant
import TauCeti.Analysis.Complex.UpperHalfPlane.CuspCoordinate
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
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

/-! ### Roots of unity -/

/-- `e^{π i / 6}⁴ = e^{2π i / 3}`. -/
private theorem exp_pi_I_div_six_pow_four : cexp (π * I / 6) ^ 4 = cexp (2 * π * I / 3) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e^{2π i / 3}³ = 1`. -/
private theorem exp_two_pi_I_div_three_pow_three : cexp (2 * π * I / 3) ^ 3 = 1 := by
  rw [← Complex.exp_nat_mul, ← exp_two_pi_mul_I]
  congr 1
  push_cast
  ring

/-! ### Weber's identity -/

/-- The function `g₀⁴ + g₁⁴ + g₂⁴`, which Weber's identity shows to vanish. -/
private noncomputable def weberSum (τ : ℂ) : ℂ :=
  siegelFunction ![0, 1 / 2] τ ^ 4 + siegelFunction ![1 / 2, 0] τ ^ 4 +
    siegelFunction ![1 / 2, 1 / 2] τ ^ 4

/-- `S` exchanges `g₀⁴` and `g₁⁴` and fixes `g₂⁴`. -/
private theorem weberSum_S_smul (τ : ℍ) : weberSum ↑(ModularGroup.S • τ) = weberSum τ := by
  rw [weberSum, weberSum, ModularGroup.coe_S_smul,
    siegelFunction_zero_half_apply_neg_one_div τ.im_pos,
    siegelFunction_half_zero_apply_neg_one_div τ.im_pos,
    siegelFunction_half_half_apply_neg_one_div τ.im_pos, mul_pow, mul_pow, neg_pow, I_pow_four]
  ring

/-- `T` multiplies `g₀⁴ + g₁⁴ + g₂⁴` by `e^{2π i / 3}`. -/
private theorem weberSum_T_smul (τ : ℍ) :
    weberSum ↑(ModularGroup.T • τ) = cexp (2 * π * I / 3) * weberSum τ := by
  -- `-4π i / 3 = 2π i / 3 - 2π i`.
  have h₃ : cexp (-(π * I / 3)) ^ 4 = cexp (2 * π * I / 3) := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-1, by push_cast; ring⟩
  rw [weberSum, weberSum, ModularGroup.coe_T_smul, siegelFunction_zero_half_apply_add_one,
    siegelFunction_half_zero_apply_add_one, siegelFunction_half_half_apply_add_one, mul_pow,
    mul_pow, mul_pow, exp_pi_I_div_six_pow_four, h₃]
  ring

/-- The cube of `g₀⁴ + g₁⁴ + g₂⁴` is invariant under `SL₂(ℤ)`. -/
private theorem weberSum_pow_three_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    weberSum ↑(γ • τ) ^ 3 = weberSum τ ^ 3 :=
  TauCeti.Matrix.SpecialLinearGroup.apply_smul_eq_of_S_smul_of_T_smul
    (f := fun τ : ℍ ↦ weberSum τ ^ 3) (fun τ ↦ by rw [weberSum_S_smul])
    (fun τ ↦ by rw [weberSum_T_smul, mul_pow, exp_two_pi_I_div_three_pow_three, one_mul]) γ τ

/-- `g₀⁴ + g₁⁴ + g₂⁴ → 0` at `i∞`. -/
private theorem tendsto_weberSum_atImInfty :
    Tendsto (fun τ : ℍ ↦ weberSum τ) atImInfty (𝓝 0) := by
  have hq₃ := UpperHalfPlane.qParam_tendsto_atImInfty (h := 3) (by norm_num)
  -- `g₀⁴ = 16 q^{1/3} / P(q)⁸ → 0` for `P(s) = ∏_{n ≥ 0} (1 - s^{2n+1})`.
  have h₀ : Tendsto (fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ ^ 4) atImInfty (𝓝 0) := by
    have h := (hq₃.const_mul 16).div (tendsto_tprod_one_sub_qParam_pow_odd_pow 8) one_ne_zero
    rw [mul_zero, zero_div] at h
    exact h.congr fun τ ↦ (siegelFunction_zero_half_pow_four τ.im_pos).symm
  -- `g₁⁴ + g₂⁴ = q^{1/3} (P(s)⁸ - P(-s)⁸) / s → 0 · (-16)` for `s = e^{π i τ}`.
  have h₁₂ : Tendsto (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ ^ 4 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4) atImInfty (𝓝 0) := by
    have h := hq₃.mul ((tendsto_tprod_one_sub_pow_odd_pow_sub_neg_div 8).comp
      (TauCeti.UpperHalfPlane.tendsto_qParam_atImInfty two_pos))
    rw [zero_mul] at h
    refine h.congr fun τ ↦ ?_
    have hs₀ : 𝕢 2 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have he : 𝕢 3 (τ : ℂ) = cexp (-(π * I * τ / 3)) * 𝕢 2 τ := by
      simp only [Function.Periodic.qParam, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [Function.comp_apply, siegelFunction_half_zero_pow_four τ.im_pos,
      siegelFunction_half_half_pow_four τ.im_pos, he]
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

/-- The fourth powers of `g₀, g₁, g₂` do not vanish, since their product is `-16`. -/
private theorem siegelFunction_pow_four_ne_zero (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ^ 4 ≠ 0 ∧ siegelFunction ![1 / 2, 0] τ ^ 4 ≠ 0 ∧
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 ≠ 0 := by
  have h : siegelFunction ![0, 1 / 2] τ ^ 4 * siegelFunction ![1 / 2, 0] τ ^ 4 *
      siegelFunction ![1 / 2, 1 / 2] τ ^ 4 ≠ 0 := by
    rw [siegelFunction_pow_four_mul_mul τ]
    norm_num
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h), right_ne_zero_of_mul (left_ne_zero_of_mul h),
    right_ne_zero_of_mul h⟩

/-- `γ₂ = (g₁¹² + 16) / g₁⁴` for `g₁ = g_{(1/2, 0)}`. -/
theorem gammaTwo_eq_siegelFunction_half_zero (τ : ℍ) :
    gammaTwo τ = (siegelFunction ![1 / 2, 0] τ ^ 12 + 16) / siegelFunction ![1 / 2, 0] τ ^ 4 := by
  have h₁ := siegelFunction_pow_four_add_add τ
  have h₂ := siegelFunction_pow_four_mul_mul τ
  rw [gammaTwo_eq_siegelFunction_zero_half,
    div_eq_div_iff (siegelFunction_pow_four_ne_zero τ).1 (siegelFunction_pow_four_ne_zero τ).2.1]
  generalize siegelFunction ![0, 1 / 2] τ = g₀, siegelFunction ![1 / 2, 0] τ = g₁ at h₁ h₂ ⊢
  linear_combination (g₀ ^ 4 - g₁ ^ 4) * g₀ ^ 4 * g₁ ^ 4 * h₁ - (g₀ ^ 4 - g₁ ^ 4) * h₂

/-- `γ₂ = (g₂¹² + 16) / g₂⁴` for `g₂ = g_{(1/2, 1/2)}`. -/
theorem gammaTwo_eq_siegelFunction_half_half (τ : ℍ) :
    gammaTwo τ =
      (siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + 16) / siegelFunction ![1 / 2, 1 / 2] τ ^ 4 := by
  have h₁ := siegelFunction_pow_four_add_add τ
  have h₂ := siegelFunction_pow_four_mul_mul τ
  rw [gammaTwo_eq_siegelFunction_zero_half,
    div_eq_div_iff (siegelFunction_pow_four_ne_zero τ).1 (siegelFunction_pow_four_ne_zero τ).2.2]
  generalize siegelFunction ![0, 1 / 2] τ = g₀, siegelFunction ![1 / 2, 1 / 2] τ = g₂ at h₁ h₂ ⊢
  linear_combination (g₀ ^ 4 - g₂ ^ 4) * g₀ ^ 4 * g₂ ^ 4 * h₁ - (g₀ ^ 4 - g₂ ^ 4) * h₂

/-- **`γ₂` is a cube root of `j`**: `γ₂³ = j`. -/
@[simp]
theorem gammaTwo_pow_three (τ : ℍ) : gammaTwo τ ^ 3 = j τ := by
  have hg : siegelFunction ![0, 1 / 2] τ ^ 12 ≠ 0 :=
    pow_ne_zero 12 (ne_zero_pow four_ne_zero (siegelFunction_pow_four_ne_zero τ).1)
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

-- Not `@[simp]`: the simpNF linter rewrites the stated LHS through the unconditional simp lemma
-- `ModularGroup.sl_moeb` to the `GL (Fin 2) ℝ`-lifted action, as for `ModularGroup.re_S_smul`.
/-- `γ₂` is invariant under `S : τ ↦ -1/τ`. -/
theorem gammaTwo_S_smul (τ : ℍ) : gammaTwo (ModularGroup.S • τ) = gammaTwo τ := by
  have hI : (-I) ^ 4 = 1 := by rw [neg_pow, I_pow_four]; norm_num
  have hI₁₂ : (-I) ^ 12 = 1 := by
    calc (-I) ^ 12 = ((-I) ^ 4) ^ 3 := by ring
      _ = 1 := by rw [hI, one_pow]
  rw [gammaTwo_eq_siegelFunction_zero_half, ModularGroup.coe_S_smul,
    siegelFunction_zero_half_apply_neg_one_div τ.im_pos, gammaTwo_eq_siegelFunction_half_zero,
    mul_pow, mul_pow, hI, hI₁₂, one_mul, one_mul]

-- Not `@[simp]`: the simpNF linter rewrites the stated LHS through the unconditional simp lemma
-- `ModularGroup.sl_moeb` to the `GL (Fin 2) ℝ`-lifted action, as for `ModularGroup.re_S_smul`.
/-- `γ₂` is multiplied by `e^{-2π i / 3}` under `T : τ ↦ τ + 1`. -/
theorem gammaTwo_T_smul (τ : ℍ) :
    gammaTwo (ModularGroup.T • τ) = cexp (-(2 * π * I / 3)) * gammaTwo τ := by
  have h₁₂ : cexp (π * I / 6) ^ 12 = 1 := (pow_mul _ 4 3).trans <| by
    rw [exp_pi_I_div_six_pow_four, exp_two_pi_I_div_three_pow_three]
  rw [gammaTwo_eq_siegelFunction_zero_half, gammaTwo_eq_siegelFunction_zero_half,
    ModularGroup.coe_T_smul, siegelFunction_zero_half_apply_add_one, mul_pow, mul_pow,
    exp_pi_I_div_six_pow_four, h₁₂, one_mul, Complex.exp_neg]
  have := (siegelFunction_pow_four_ne_zero τ).1
  field_simp

/-- **The leading Fourier term of `γ₂` is `q^{-1/3}`**: `γ₂(τ) e^{2π i τ / 3} → 1` as
`Im τ → ∞`. -/
theorem tendsto_gammaTwo_mul_qParam_atImInfty :
    Tendsto (fun τ : ℍ ↦ gammaTwo τ * 𝕢 3 τ) atImInfty (𝓝 1) := by
  have hq₃ := UpperHalfPlane.qParam_tendsto_atImInfty (h := 3) (by norm_num)
  have hP := tendsto_tprod_one_sub_qParam_pow_odd_pow 8
  -- `γ₂ q^{1/3} = g₀⁸ q^{1/3} + P(q)⁸` with `g₀⁴ = 16 q^{1/3} / P(q)⁸`.
  have h := ((((hq₃.const_mul 16).div hP one_ne_zero).pow 2).mul hq₃).add hP
  simp only [mul_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add] at h
  refine h.congr fun τ ↦ ?_
  rw [Pi.div_apply]
  have hO := tprod_one_sub_pow_odd_ne_zero (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)
  have hq₀ : 𝕢 3 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have h₄ := siegelFunction_zero_half_pow_four τ.im_pos
  have h₁₂ : siegelFunction ![0, 1 / 2] τ ^ 12 =
      (16 * 𝕢 3 τ / (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 8) ^ 3 := by
    rw [← h₄]
    ring
  rw [gammaTwo_eq_siegelFunction_zero_half, h₁₂, h₄]
  field_simp

end TauCeti.ModularForm
