/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Eta
import TauCeti.NumberTheory.ModularForms.LevelOne.Invariant

/-!
# Weber's cubic: the level-two Siegel functions and the modular invariant `j`

The twelfth powers of the three level-two Siegel functions `g₀ = g_{(0, 1/2)}`,
`g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}` are the three roots of

  `(X + 16)³ - j X = X³ + 48 X² + (768 - j) X + 4096`,

so that `(g¹² + 16)³ = j g¹²` for each of them. In Weber's notation `g₀¹² = 𝔣₂²⁴`,
`g₁¹² = 𝔣₁²⁴` and `g₂¹² = -𝔣²⁴`.

The proof compares elementary symmetric functions. The product `g₀¹² g₁¹² g₂¹² = -4096` is the
twelfth power of `g₀ g₁ g₂ = 2 ζ₈`. The cubic with roots `g₀¹², g₁¹², g₂¹²` is invariant under
`SL₂(ℤ)` (`prod_X_sub_C_siegelFunction_pow_twelve_smul`), so `g₀¹² + g₁¹² + g₂¹²` and
`g₀¹² g₁¹² + g₀¹² g₂¹² + g₁¹² g₂¹² + j` are holomorphic `SL₂(ℤ)`-invariant functions. Both have
limits at `i∞`, so they are constant (`TauCeti.ModularForm.levelOne_eq_of_tendsto_atImInfty`), and
the constants are the limits `-48` and `768`.

The limits come from the product expansions. With `s = e^{π i τ}`, `q = s²` and
`Φ(s) = ∏_{n ≥ 0} (1 - s^{2n+1})²⁴`, one has `g₁¹² = s⁻¹ Φ(s)` and `g₂¹² = -s⁻¹ Φ(-s)`, and
`Φ(s) Φ(-s) = Φ(q)`. Since `Φ(s) = 1 - 24 s + O(s²)`, at `i∞`
`g₁¹² + g₂¹² = (Φ(s) - Φ(-s)) / s → -48` and `g₁¹² g₂¹² + q⁻¹ = (1 - Φ(q)) / q → 24`, while
`g₀¹² = 4096 q / Φ(q) → 0`. Together with `j - q⁻¹ → 744` this gives the two constants.

This is the input for the cube root `γ₂ = (g¹² + 16) / g⁴` of `j`.

## Main results

* `TauCeti.ModularForm.prod_X_sub_C_siegelFunction_pow_twelve`: Weber's cubic
  `(X - g₀¹²)(X - g₁¹²)(X - g₂¹²) = (X + 16)³ - j X`.
* `TauCeti.ModularForm.siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three`,
  `TauCeti.ModularForm.siegelFunction_half_zero_pow_twelve_add_sixteen_pow_three`,
  `TauCeti.ModularForm.siegelFunction_half_half_pow_twelve_add_sixteen_pow_three`:
  `(g¹² + 16)³ = j g¹²` for `g = g₀, g₁, g₂`.

## References

* H. Weber, *Lehrbuch der Algebra*, Band III (the functions `𝔣, 𝔣₁, 𝔣₂` and the cubic satisfied
  by their 24th powers).
* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber's functions and `γ₂`).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open Complex Polynomial Filter Topology
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups Manifold

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-! ### The twelfth powers as products in `s = e^{π i τ}` -/

/-- `(∏_{n ≥ 0} (1 - s^{2n+1}))²⁴ = 1 - 24 s + O(s²)`. -/
private theorem hasDerivAt_tprod_one_sub_pow_odd_pow :
    HasDerivAt (fun s : ℂ ↦ (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 24) (-24) 0 := by
  simpa using (hasDerivAt_tprod_one_sub_pow_odd (𝕜 := ℂ)).fun_pow 24

/-- `Φ(s) Φ(-s) = Φ(s²)` for `Φ(s) = (∏_{n ≥ 0} (1 - s^{2n+1}))²⁴` and `‖s‖ < 1`. -/
private theorem tprod_one_sub_pow_odd_pow_mul_neg {s : ℂ} (hs : ‖s‖ < 1) :
    (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 24 * (∏' n : ℕ, (1 - (-s) ^ (2 * n + 1))) ^ 24 =
      (∏' n : ℕ, (1 - (s ^ 2) ^ (2 * n + 1))) ^ 24 := by
  have hodd : ∏' n : ℕ, (1 - (-s) ^ (2 * n + 1)) = ∏' n : ℕ, (1 + s ^ (2 * n + 1)) :=
    tprod_congr fun n ↦ one_sub_neg_pow_odd _ n
  rw [hodd, ← mul_pow, tprod_one_sub_pow_odd_mul_tprod_one_add_pow_odd hs]

private theorem exp_neg_pi_I_mul_div_twelve_pow_twelve (τ : ℂ) :
    cexp (-(π * I * τ / 12)) ^ 12 = (cexp (π * I * τ))⁻¹ := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- `g₁¹² = s⁻¹ (∏_{n ≥ 0} (1 - s^{2n+1}))²⁴` for `s = e^{π i τ}`. -/
private theorem siegelFunction_half_zero_pow_twelve {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] τ ^ 12 =
      (cexp (π * I * τ))⁻¹ * (∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * n + 1))) ^ 24 := by
  rw [siegelFunction_half_zero hτ, mul_pow, neg_pow, exp_neg_pi_I_mul_div_twelve_pow_twelve,
    ← pow_mul]
  norm_num

/-- `g₂¹² = -s⁻¹ (∏_{n ≥ 0} (1 - (-s)^{2n+1}))²⁴` for `s = e^{π i τ}`. -/
private theorem siegelFunction_half_half_pow_twelve {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 1 / 2] τ ^ 12 =
      -((cexp (π * I * τ))⁻¹ * (∏' n : ℕ, (1 - (-cexp (π * I * τ)) ^ (2 * n + 1))) ^ 24) := by
  have h₄ : cexp (-(π * I / 4)) ^ 12 = -1 := by
    have harg : ((12 : ℕ) : ℂ) * -(π * I / 4) = -(π * I) + ((-1 : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [← Complex.exp_nat_mul, harg, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_neg, exp_pi_mul_I]
    norm_num
  have hodd : ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1)) =
      ∏' n : ℕ, (1 - (-cexp (π * I * τ)) ^ (2 * n + 1)) :=
    tprod_congr fun n ↦ (one_sub_neg_pow_odd _ n).symm
  rw [siegelFunction_half_half hτ, hodd, mul_pow, mul_pow, neg_pow,
    exp_neg_pi_I_mul_div_twelve_pow_twelve, h₄, ← pow_mul]
  norm_num

/-- `g₀¹² g₁¹² g₂¹² = -4096`, the twelfth power of `g₀ g₁ g₂ = 2 ζ₈`. -/
private theorem siegelFunction_pow_twelve_mul_mul {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] τ ^ 12 * siegelFunction ![1 / 2, 0] τ ^ 12 *
      siegelFunction ![1 / 2, 1 / 2] τ ^ 12 = -4096 := by
  have h₈ : cexp (2 * π * I / 8) ^ 12 = -1 := by
    have harg : ((12 : ℕ) : ℂ) * (2 * π * I / 8) = π * I + ((1 : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [← Complex.exp_nat_mul, harg, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one,
      exp_pi_mul_I]
  rw [← mul_pow, ← mul_pow, siegelFunction_zero_half_mul_half_zero_mul_half_half hτ, mul_pow, h₈]
  norm_num

/-- `g₁¹² g₂¹² = -q⁻¹ (∏_{n ≥ 0} (1 - q^{2n+1}))²⁴` for `q = e^{2π i τ}`. -/
private theorem siegelFunction_half_zero_pow_twelve_mul {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] τ ^ 12 * siegelFunction ![1 / 2, 1 / 2] τ ^ 12 =
      -((𝕢 1 τ)⁻¹ * (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 24) := by
  have hq : 𝕢 1 τ = cexp (π * I * τ) ^ 2 := by
    rw [Function.Periodic.qParam, ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq, ofReal_one,
      div_one]
  rw [siegelFunction_half_zero_pow_twelve hτ, siegelFunction_half_half_pow_twelve hτ, hq,
    ← tprod_one_sub_pow_odd_pow_mul_neg (UpperHalfPlane.norm_exp_pi_I_lt_one hτ)]
  ring

/-! ### Limits at `i∞` -/

private theorem tendsto_exp_pi_I_atImInfty :
    Tendsto (fun τ : ℍ ↦ cexp (π * I * τ)) atImInfty (𝓝[≠] 0) := by
  refine ((Function.Periodic.qParam_tendsto two_pos).comp tendsto_coe_atImInfty).congr
    fun τ ↦ ?_
  simp only [Function.comp_apply, Function.Periodic.qParam]
  congr 1
  push_cast
  ring

private theorem tendsto_qParam_atImInfty :
    Tendsto (fun τ : ℍ ↦ 𝕢 1 τ) atImInfty (𝓝[≠] 0) :=
  (Function.Periodic.qParam_tendsto one_pos).comp tendsto_coe_atImInfty

/-- `g₁¹² + g₂¹² → -48` at `i∞`. -/
private theorem tendsto_siegelFunction_half_zero_pow_twelve_add :
    Tendsto (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ ^ 12 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 12) atImInfty (𝓝 (-48)) := by
  -- The two slopes of `Φ(s) = (∏ (1 - s^{2n+1}))²⁴` at `0`, in the directions `s` and `-s`.
  have hΦ : HasDerivAt (fun s : ℂ ↦ (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 24) (-24) (-0) := by
    rw [neg_zero]
    exact hasDerivAt_tprod_one_sub_pow_odd_pow
  have h₁ := hasDerivAt_tprod_one_sub_pow_odd_pow.tendsto_slope_zero
  have h₂ := (hΦ.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))).tendsto_slope_zero
  have h := (h₁.sub h₂).comp tendsto_exp_pi_I_atImInfty
  norm_num at h
  refine h.congr fun τ ↦ ?_
  simp only [Function.comp_apply, siegelFunction_half_zero_pow_twelve τ.im_pos,
    siegelFunction_half_half_pow_twelve τ.im_pos]
  ring

/-- `g₁¹² g₂¹² + q⁻¹ → 24` at `i∞`. -/
private theorem tendsto_siegelFunction_half_zero_pow_twelve_mul_add_inv_qParam :
    Tendsto (fun τ : ℍ ↦ siegelFunction ![1 / 2, 0] τ ^ 12 *
      siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + (𝕢 1 τ)⁻¹) atImInfty (𝓝 24) := by
  have h := (hasDerivAt_tprod_one_sub_pow_odd_pow.tendsto_slope_zero.comp
    tendsto_qParam_atImInfty).neg
  norm_num at h
  refine h.congr fun τ ↦ ?_
  simp only [siegelFunction_half_zero_pow_twelve_mul τ.im_pos]
  ring

/-- `g₀¹² → 0` at `i∞`. -/
private theorem tendsto_siegelFunction_zero_half_pow_twelve :
    Tendsto (fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ ^ 12) atImInfty (𝓝 0) := by
  have hq := tendsto_qParam_atImInfty.mono_right nhdsWithin_le_nhds
  have hΦ : Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 24) atImInfty
      (𝓝 1) := by
    have h0 : (∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 1))) ^ 24 = 1 := by simp
    have h := hasDerivAt_tprod_one_sub_pow_odd_pow.continuousAt.tendsto.comp hq
    rwa [h0] at h
  have h : Tendsto (fun τ : ℍ ↦ 4096 * 𝕢 1 τ / (∏' n : ℕ, (1 - 𝕢 1 τ ^ (2 * n + 1))) ^ 24)
      atImInfty (𝓝 0) := by
    have h := (hq.const_mul 4096).div hΦ one_ne_zero
    rwa [mul_zero, zero_div] at h
  refine h.congr fun τ ↦ ?_
  -- `g₀¹² = -4096 / (g₁¹² g₂¹²)`.
  have h₃ := siegelFunction_pow_twelve_mul_mul τ.im_pos
  rw [mul_assoc, siegelFunction_half_zero_pow_twelve_mul τ.im_pos] at h₃
  have hq₀ : 𝕢 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hΦ₀ : (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (2 * n + 1))) ^ 24 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, neg_zero, mul_zero] at h₃
    norm_num at h₃
  rw [div_eq_iff hΦ₀]
  field_simp at h₃
  linear_combination h₃

/-! ### The symmetric functions of the twelfth powers -/

/-- Equal monic cubics have the same first and second elementary symmetric functions of their
roots. -/
private theorem add_add_eq_and_mul_add_mul_add_mul_eq {a b c a' b' c' : ℂ}
    (h : (X - C a) * (X - C b) * (X - C c) = (X - C a') * (X - C b') * (X - C c')) :
    a + b + c = a' + b' + c' ∧ a * b + a * c + b * c = a' * b' + a' * c' + b' * c' := by
  have h₀ := congrArg (eval 0) h
  have h₁ := congrArg (eval 1) h
  have h₂ := congrArg (eval (-1)) h
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h₀ h₁ h₂
  constructor
  · linear_combination (-1 / 2 : ℂ) * h₁ + (-1 / 2 : ℂ) * h₂ + h₀
  · linear_combination (1 / 2 : ℂ) * h₁ - (1 / 2 : ℂ) * h₂

private theorem mdifferentiable_siegelFunction_pow (r : Fin 2 → ℝ) (n : ℕ) :
    MDiff fun τ : ℍ ↦ siegelFunction r τ ^ n := by
  refine MDifferentiable.pow ?_ n
  rw [UpperHalfPlane.mdifferentiable_iff]
  exact (differentiableOn_siegelFunction r).congr fun z hz ↦ by
    simp [Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- `g₀¹² + g₁¹² + g₂¹² = -48`. -/
private theorem siegelFunction_pow_twelve_add_add (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ^ 12 + siegelFunction ![1 / 2, 0] τ ^ 12 +
      siegelFunction ![1 / 2, 1 / 2] τ ^ 12 = -48 := by
  refine levelOne_eq_of_tendsto_atImInfty (F := fun τ : ℍ ↦ siegelFunction ![0, 1 / 2] τ ^ 12 +
    siegelFunction ![1 / 2, 0] τ ^ 12 + siegelFunction ![1 / 2, 1 / 2] τ ^ 12) ?_ ?_ ?_ τ
  · exact ((mdifferentiable_siegelFunction_pow _ 12).add
      (mdifferentiable_siegelFunction_pow _ 12)).add (mdifferentiable_siegelFunction_pow _ 12)
  · exact fun γ τ ↦ (add_add_eq_and_mul_add_mul_add_mul_eq
      (prod_X_sub_C_siegelFunction_pow_twelve_smul γ τ)).1
  · have h := tendsto_siegelFunction_zero_half_pow_twelve.add
      tendsto_siegelFunction_half_zero_pow_twelve_add
    rw [zero_add] at h
    exact h.congr fun τ ↦ by ring

/-- `g₀¹² g₁¹² + g₀¹² g₂¹² + g₁¹² g₂¹² = 768 - j`. -/
private theorem siegelFunction_pow_twelve_mul_add_mul_add_mul (τ : ℍ) :
    siegelFunction ![0, 1 / 2] τ ^ 12 * siegelFunction ![1 / 2, 0] τ ^ 12 +
      siegelFunction ![0, 1 / 2] τ ^ 12 * siegelFunction ![1 / 2, 1 / 2] τ ^ 12 +
      siegelFunction ![1 / 2, 0] τ ^ 12 * siegelFunction ![1 / 2, 1 / 2] τ ^ 12 = 768 - j τ := by
  have h := levelOne_eq_of_tendsto_atImInfty (F := fun τ : ℍ ↦
    siegelFunction ![0, 1 / 2] τ ^ 12 * siegelFunction ![1 / 2, 0] τ ^ 12 +
      siegelFunction ![0, 1 / 2] τ ^ 12 * siegelFunction ![1 / 2, 1 / 2] τ ^ 12 +
      siegelFunction ![1 / 2, 0] τ ^ 12 * siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + j τ) (c := 768)
    ?_ ?_ ?_ τ
  · exact eq_sub_of_add_eq h
  · have h₀ := mdifferentiable_siegelFunction_pow ![0, 1 / 2] 12
    have h₁ := mdifferentiable_siegelFunction_pow ![1 / 2, 0] 12
    have h₂ := mdifferentiable_siegelFunction_pow ![1 / 2, 1 / 2] 12
    exact (((h₀.mul h₁).add (h₀.mul h₂)).add (h₁.mul h₂)).add j_mdifferentiable
  · intro γ τ
    rw [(add_add_eq_and_mul_add_mul_add_mul_eq
      (prod_X_sub_C_siegelFunction_pow_twelve_smul γ τ)).2, j_smul_SL2Z]
  · -- Split as `g₀¹² (g₁¹² + g₂¹²) + (g₁¹² g₂¹² + q⁻¹) + (j - q⁻¹) → 0 · (-48) + 24 + 744`.
    have h := ((tendsto_siegelFunction_zero_half_pow_twelve.mul
      tendsto_siegelFunction_half_zero_pow_twelve_add).add
      tendsto_siegelFunction_half_zero_pow_twelve_mul_add_inv_qParam).add
      tendsto_j_sub_inv_qParam_atImInfty
    norm_num at h
    exact h.congr fun τ ↦ by ring

/-! ### Weber's cubic -/

/-- **Weber's cubic.** The twelfth powers of the level-two Siegel functions `g₀ = g_{(0, 1/2)}`,
`g₁ = g_{(1/2, 0)}` and `g₂ = g_{(1/2, 1/2)}` are the three roots of `(X + 16)³ - j X`. -/
theorem prod_X_sub_C_siegelFunction_pow_twelve (τ : ℍ) :
    (X - C (siegelFunction ![0, 1 / 2] τ ^ 12)) * (X - C (siegelFunction ![1 / 2, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] τ ^ 12)) =
      (X + 16) ^ 3 - C (j τ) * X := by
  have h₁ := siegelFunction_pow_twelve_add_add τ
  have h₂ := siegelFunction_pow_twelve_mul_add_mul_add_mul τ
  have h₃ := siegelFunction_pow_twelve_mul_mul τ.im_pos
  set a := siegelFunction ![0, 1 / 2] τ ^ 12
  set b := siegelFunction ![1 / 2, 0] τ ^ 12
  set c := siegelFunction ![1 / 2, 1 / 2] τ ^ 12
  have key : (X - C a) * (X - C b) * (X - C c) =
      X ^ 3 - C (a + b + c) * X ^ 2 + C (a * b + a * c + b * c) * X - C (a * b * c) := by
    simp only [map_add, map_mul]
    ring
  rw [key, h₁, h₂, h₃]
  simp only [map_neg, map_sub, map_ofNat]
  ring

/-- A root `x` of Weber's cubic satisfies `(x + 16)³ = j x`. -/
private theorem add_sixteen_pow_three_of_eval_eq_zero {x : ℂ} (τ : ℍ)
    (hx : ((X - C (siegelFunction ![0, 1 / 2] τ ^ 12)) *
      (X - C (siegelFunction ![1 / 2, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] τ ^ 12))).eval x = 0) :
    (x + 16) ^ 3 = j τ * x := by
  rw [prod_X_sub_C_siegelFunction_pow_twelve] at hx
  simp only [eval_sub, eval_pow, eval_add, eval_X, eval_ofNat, eval_mul, eval_C] at hx
  linear_combination hx

/-- `(g₀¹² + 16)³ = j g₀¹²` for `g₀ = g_{(0, 1/2)}`. -/
theorem siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three (τ : ℍ) :
    (siegelFunction ![0, 1 / 2] τ ^ 12 + 16) ^ 3 = j τ * siegelFunction ![0, 1 / 2] τ ^ 12 :=
  add_sixteen_pow_three_of_eval_eq_zero τ (by simp)

/-- `(g₁¹² + 16)³ = j g₁¹²` for `g₁ = g_{(1/2, 0)}`. -/
theorem siegelFunction_half_zero_pow_twelve_add_sixteen_pow_three (τ : ℍ) :
    (siegelFunction ![1 / 2, 0] τ ^ 12 + 16) ^ 3 = j τ * siegelFunction ![1 / 2, 0] τ ^ 12 :=
  add_sixteen_pow_three_of_eval_eq_zero τ (by simp)

/-- `(g₂¹² + 16)³ = j g₂¹²` for `g₂ = g_{(1/2, 1/2)}`. -/
theorem siegelFunction_half_half_pow_twelve_add_sixteen_pow_three (τ : ℍ) :
    (siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + 16) ^ 3 =
      j τ * siegelFunction ![1 / 2, 1 / 2] τ ^ 12 :=
  add_sixteen_pow_three_of_eval_eq_zero τ (by simp)

end TauCeti.ModularForm
