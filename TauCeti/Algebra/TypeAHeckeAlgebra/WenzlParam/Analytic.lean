/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Continuity and exponential evaluations of Wenzl's parameters

This file develops the topological continuity, removable limit at `Q = 1`, and trigonometric and
hyperbolic exponential evaluations of `TauCeti.wenzlParam`. Complex root-of-unity evaluations are in
`TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.RootOfUnity`.

## Main results

* `TauCeti.continuousAt_wenzlParam` and `TauCeti.tendsto_one_sub_zpow_div_nhdsNE_one`: continuity
  wherever the denominator is nonzero and the removable limit `(d + 1) / (2 * d)` as `Q → 1`.
* `TauCeti.wenzlParam_exp_mul_I`: `a_k(exp (2 θ i)) = sin ((k + 1) θ) / (2 cos θ sin (k θ))`.
* `TauCeti.wenzlParam_exp_two_mul`, `TauCeti.wenzlParam_exp_neg_two_mul`,
  `TauCeti.wenzlParam_real_exp_two_mul`, `TauCeti.wenzlParam_real_exp_neg_two_mul`, and
  `TauCeti.wenzlParam_neg_two_exp_neg_two_mul`:
  `a_k(exp (± 2 θ)) = sinh ((k + 1) θ) / (2 cosh θ sinh (k θ))` and
  `a_(-2)(exp (± 2 θ)) = (4 cosh² θ)⁻¹`.
* `TauCeti.tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atTop` and
  `TauCeti.tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atBot`: the scalar limits `0` of the
  real hyperbolic Jones parameter as `θ → ±∞`.
-/

public section

open Finset

namespace TauCeti

/-! ### Continuity and the removable value at `Q = 1` -/

section Topology

open Filter Topology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

/-- `a_d` is continuous at every `Q` where its denominator `(1 + Q) * [|d|]_Q` is nonzero. -/
theorem continuousAt_wenzlParam {d : ℤ} {Q : K} (h : (1 + Q) * ∑ i ∈ range d.natAbs, Q ^ i ≠ 0) :
    ContinuousAt (wenzlParam d) Q := by
  obtain ⟨r, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · rw [funext (wenzlParam_natCast r)]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using h)
  · rw [funext (wenzlParam_neg_natCast r)]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using h)

/-- **The removable limit.** As `Q → 1`, the closed form
`(1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))` tends to `a_d(1) = (d + 1) / (2 * d)`. -/
theorem tendsto_one_sub_zpow_div_nhdsNE_one [T1Space K] [CharZero K] {d : ℤ} (hd : d ≠ 0) :
    Tendsto (fun Q : K ↦ (1 - Q ^ (d + 1)) / ((1 + Q) * (1 - Q ^ d))) (𝓝[≠] 1)
      (𝓝 ((d + 1) / (2 * d))) := by
  rw [← wenzlParam_one]
  have hc : ContinuousAt (wenzlParam d) (1 : K) :=
    continuousAt_wenzlParam (by simp [one_add_one_eq_two, hd])
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_ne_nhds (one_ne_zero (α := K)))] with Q hQ₁ hQ₀
  exact wenzlParam_eq_div hQ₀ hQ₁ d

end Topology

/-! ### Exponential evaluations -/

section Exponential

open Complex
open scoped Real Topology

/-- Inversion symmetry at a complex exponential `exp (-z)`: `a_d(exp (-z)) = a_d(exp z)`. -/
@[simp]
theorem wenzlParam_exp_neg (d : ℤ) (z : ℂ) :
    wenzlParam d (exp (-z)) = wenzlParam d (exp z) := by
  rw [exp_neg, wenzlParam_inv]

/-- Inversion symmetry at a real exponential `Real.exp (-x)`: `a_d(exp (-x)) = a_d(exp x)`. -/
@[simp]
theorem wenzlParam_real_exp_neg (d : ℤ) (x : ℝ) :
    wenzlParam d (Real.exp (-x)) = wenzlParam d (Real.exp x) := by
  rw [Real.exp_neg, wenzlParam_inv]

/-- **The trigonometric form.** At `Q = exp (2 θ i)`,
`a_k(Q) = sin ((k + 1) θ) / (2 * cos θ * sin (k θ))`, whenever `cos θ ≠ 0` and `sin (k θ) ≠ 0`. -/
theorem wenzlParam_exp_mul_I (k : ℤ) {θ : ℂ} (hθ : cos θ ≠ 0) (hk : sin (k * θ) ≠ 0) :
    wenzlParam k (exp (2 * θ * I)) = sin ((k + 1) * θ) / (2 * cos θ * sin (k * θ)) := by
  have e₁ (x : ℂ) : exp (-x * I) * exp (x * I) = 1 := by
    rw [neg_mul, exp_neg, inv_mul_cancel₀ (exp_ne_zero _)]
  have e₂ (x : ℂ) : exp (x * I) ^ 2 = exp (2 * x * I) := by
    rw [← exp_natCast_mul, Nat.cast_ofNat, mul_assoc]
  -- `1 - exp (2 x i) = -i * (2 * sin x) * exp (x i)` and `1 + exp (2 x i) = 2 * cos x * exp (x i)`.
  have one_sub_exp (x : ℂ) : 1 - exp (2 * x * I) = -I * (2 * sin x) * exp (x * I) := by
    rw [two_sin]
    linear_combination (-1) * e₁ x + e₂ x + (exp (-x * I) - exp (x * I)) * exp (x * I) * I_sq
  have one_add_exp (x : ℂ) : 1 + exp (2 * x * I) = 2 * cos x * exp (x * I) := by
    simpa only [mul_assoc, cosh_mul_I] using one_add_exp_two_mul (x * I)
  have hpow (n : ℤ) : 1 - exp (2 * θ * I) ^ n = -I * (2 * sin (n * θ)) * exp (n * θ * I) := by
    rw [← exp_intCast_mul, ← one_sub_exp]
    ring_nf
  have hk' : 1 - exp (2 * θ * I) ^ k ≠ 0 := by
    rw [hpow]
    simp [hk, exp_ne_zero, I_ne_zero]
  have hQ₁ : exp (2 * θ * I) ≠ 1 := by
    rintro h
    simp [h] at hk'
  have hexp : exp ((k + 1) * θ * I) = exp (θ * I) * exp (k * θ * I) := by
    rw [← exp_add]
    ring_nf
  rw [wenzlParam_eq_div (exp_ne_zero _) hQ₁, hpow, hpow, one_add_exp]
  push_cast
  rw [hexp]
  field_simp [exp_ne_zero, I_ne_zero]

/-- **The hyperbolic form at `exp (2 θ)`.** At `Q = exp (2 * θ)`,
`a_k(Q) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`, whenever `cosh θ ≠ 0` and
`sinh (k * θ) ≠ 0`. -/
theorem wenzlParam_exp_two_mul (k : ℤ) {θ : ℂ} (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0) :
    wenzlParam k (exp (2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ)) := by
  have hsin_eq (a : ℂ) : sin (a * -(θ * I)) = -(sinh (a * θ) * I) := by
    rw [mul_neg, ← mul_assoc, sin_neg, sin_mul_I]
  have hcos : cos (-(θ * I)) ≠ 0 := by simpa [cos_mul_I] using hθ
  have hsin : sin ((k : ℂ) * -(θ * I)) ≠ 0 := by
    rw [hsin_eq]
    simp [hk, I_ne_zero]
  have h := wenzlParam_exp_mul_I k hcos hsin
  have hphase : 2 * -(θ * I) * I = 2 * θ := by linear_combination -2 * θ * I_sq
  rw [hphase, cos_neg, cos_mul_I, hsin_eq, hsin_eq] at h
  rw [h]
  field_simp [I_ne_zero]

/-- **The hyperbolic form at `exp (-2 θ)`.** At `Q = exp (-2 * θ)`,
`a_k(Q) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`, whenever `cosh θ ≠ 0` and
`sinh (k * θ) ≠ 0`. -/
theorem wenzlParam_exp_neg_two_mul (k : ℤ) {θ : ℂ} (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0) :
    wenzlParam k (exp (-2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ)) := by
  rw [neg_mul, wenzlParam_exp_neg, wenzlParam_exp_two_mul k hθ hk]

/-- **The real hyperbolic form at `Real.exp (2 θ)`.** For `k ≠ 0` and real `θ ≠ 0`,
`a_k(exp (2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`. -/
theorem wenzlParam_real_exp_two_mul {k : ℤ} (hk : k ≠ 0) {θ : ℝ} (hθ : θ ≠ 0) :
    wenzlParam k (Real.exp (2 * θ)) =
      Real.sinh ((k + 1) * θ) / (2 * Real.cosh θ * Real.sinh (k * θ)) := by
  apply Complex.ofReal_injective
  have hs : sinh ((k : ℂ) * θ) ≠ 0 := by
    simpa using sinh_ofReal_ne_zero.2 (mul_ne_zero (Int.cast_ne_zero.2 hk) hθ)
  rw [← Complex.ofRealHom_eq_coe, map_wenzlParam]
  simpa using wenzlParam_exp_two_mul k (cosh_ofReal_ne_zero θ) hs

/-- **The real hyperbolic form at `Real.exp (-2 θ)`.** For `k ≠ 0` and real `θ ≠ 0`,
`a_k(exp (-2 * θ)) = sinh ((k + 1) * θ) / (2 * cosh θ * sinh (k * θ))`. -/
theorem wenzlParam_real_exp_neg_two_mul {k : ℤ} (hk : k ≠ 0) {θ : ℝ} (hθ : θ ≠ 0) :
    wenzlParam k (Real.exp (-2 * θ)) =
      Real.sinh ((k + 1) * θ) / (2 * Real.cosh θ * Real.sinh (k * θ)) := by
  rw [neg_mul, wenzlParam_real_exp_neg, wenzlParam_real_exp_two_mul hk hθ]

/-- **The hyperbolic Jones parameter at `exp (2 θ)`.** For every `θ : ℂ`,
`a_(-2)(exp (2 * θ)) = (4 * cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_exp_two_mul (θ : ℂ) :
    wenzlParam (-2) (exp (2 * θ)) = (4 * cosh θ ^ 2)⁻¹ := by
  have hsq : (1 + exp (2 * θ)) ^ 2 = exp (2 * θ) * (4 * cosh θ ^ 2) := by
    rw [one_add_exp_two_mul, mul_pow, ← exp_natCast_mul, Nat.cast_ofNat]
    ring
  rw [wenzlParam_neg_two, hsq, div_mul_eq_div_div, div_self (exp_ne_zero _), one_div]

/-- **The Jones parameter on the unit circle.** At `Q = exp (2 θ i)`,
`a_(-2)(Q) = (4 * cos θ ^ 2)⁻¹` for every `θ : ℂ`. -/
theorem wenzlParam_neg_two_exp_mul_I (θ : ℂ) :
    wenzlParam (-2) (exp (2 * θ * I)) = (4 * cos θ ^ 2)⁻¹ := by
  simpa only [mul_assoc, cosh_mul_I] using wenzlParam_neg_two_exp_two_mul (θ * I)

/-- **The hyperbolic Jones parameter at `exp (-2 θ)`.** For every `θ : ℂ`,
`a_(-2)(exp (-2 * θ)) = (4 * cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_exp_neg_two_mul (θ : ℂ) :
    wenzlParam (-2) (exp (-2 * θ)) = (4 * cosh θ ^ 2)⁻¹ := by
  rw [neg_mul, wenzlParam_exp_neg, wenzlParam_neg_two_exp_two_mul]

/-- **The real hyperbolic Jones parameter at `Real.exp (2 θ)`.** For every `θ : ℝ`,
`a_(-2)(exp (2 * θ)) = (4 * cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_real_exp_two_mul (θ : ℝ) :
    wenzlParam (-2) (Real.exp (2 * θ)) = (4 * Real.cosh θ ^ 2)⁻¹ := by
  apply Complex.ofReal_injective
  rw [← Complex.ofRealHom_eq_coe, map_wenzlParam]
  simpa using wenzlParam_neg_two_exp_two_mul (θ : ℂ)

/-- **The real hyperbolic Jones parameter at `Real.exp (-2 θ)`.** For every `θ : ℝ`,
`a_(-2)(exp (-2 * θ)) = (4 * Real.cosh θ ^ 2)⁻¹`. -/
theorem wenzlParam_neg_two_real_exp_neg_two_mul (θ : ℝ) :
    wenzlParam (-2) (Real.exp (-2 * θ)) = (4 * Real.cosh θ ^ 2)⁻¹ := by
  rw [neg_mul, wenzlParam_real_exp_neg, wenzlParam_neg_two_real_exp_two_mul]

/-- **Scalar limit of the Jones parameter as `θ → +∞` (`Q → 0⁺`).** -/
theorem tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atTop :
    Filter.Tendsto (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * θ))) Filter.atTop (𝓝 0) := by
  simp_rw [wenzlParam_neg_two_real_exp_neg_two_mul]
  exact tendsto_inv_atTop_zero.comp
    ((Filter.tendsto_const_mul_pow_atTop (by positivity) (by positivity)).comp
      Real.tendsto_cosh_atTop)

/-- **Scalar limit of the Jones parameter as `θ → -∞` (`Q → +∞`).** -/
theorem tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atBot :
    Filter.Tendsto (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * θ))) Filter.atBot (𝓝 0) := by
  have h : (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * θ))) =
      (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * (-θ)))) := by
    ext θ
    rw [wenzlParam_neg_two_real_exp_neg_two_mul, wenzlParam_neg_two_real_exp_neg_two_mul,
      Real.cosh_neg]
  rw [h]
  exact tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atTop.comp Filter.tendsto_neg_atBot_atTop

end Exponential

end TauCeti
