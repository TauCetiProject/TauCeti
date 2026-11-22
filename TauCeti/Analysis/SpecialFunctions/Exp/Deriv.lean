/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Derivatives of exponential functions

Viewed as a function of a real vector variable, `Complex.exp` has the same iterated derivatives
as it has over `ℂ`, restricted to real scalars. Since every complex derivative of `exp` is `exp`,
every real iterated derivative of `Complex.exp` at `z` has norm `‖exp z‖`. This is the input a
Faà di Bruno bound needs for compositions `Complex.exp ∘ f` with a real-differentiable `f`.

For a function `f` on `ℝ`, `f ∘ exp` is differentiable at `y` exactly when `f` is differentiable
at `exp y`, so the chain rule `(f ∘ exp)'(y) = e^y f'(e^y)` holds with no hypothesis on `f`.

## Main results

* `TauCeti.hasDerivAt_mul_exp_neg_mul`: `t ↦ c exp (-k t)` has derivative `-k c exp (-k t)`, so
  it solves `x' = -k x`.
* `TauCeti.differentiableAt_comp_exp_iff`: `f ∘ exp` is differentiable at `y` exactly when `f` is
  differentiable at `exp y`.
* `TauCeti.deriv_comp_exp`: `(f ∘ exp)'(y) = e^y • f'(e^y)`, unconditionally.
* `TauCeti.norm_iteratedFDeriv_real_cexp`: every real iterated derivative of `Complex.exp` at `z`
  has norm `‖exp z‖`.
* `TauCeti.iteratedDeriv_cexp_const_mul_ofReal`: the `n`-th real derivative of
  `s ↦ Complex.exp (z * s)` is `s ↦ z ^ n * Complex.exp (z * s)`.
* `ContinuousLinearMap.norm_iteratedFDeriv_cexp_comp_le`: for a real-linear map `ℓ` to `ℂ`, the
  `n`-th derivative of `x ↦ exp (ℓ x)` has norm at most `‖exp (ℓ x)‖ ‖ℓ‖ ^ n`.
* `ContDiff.isBigO_iteratedFDeriv_succ_exp`: along any filter, the derivative of order `n + 1` of
  `exp ℓ` is `O(ρ)` when the derivatives of `ℓ` of positive order up to that order are `O(ρ)` and
  those of `exp ℓ` of lower order are bounded.
* `ContDiff.isBigO_iteratedFDeriv_exp_sub_one`: along a filter on which `ρ` is bounded, the
  derivative of order `n` of `exp ℓ - 1` is `O(ρ)` when the derivatives of `ℓ` of order at most `n`
  are `O(ρ)`.
* `ContDiffOn.norm_iteratedFDeriv_exp_comp_le`: the pointwise bound
  `‖Dⁿ (exp f) (x)‖ ≤ n! exp (f x) max ε εⁿ` when the derivatives of `f` of orders `1` to `n` at
  `x` have norm at most `ε`.
-/

public section

namespace Real

/-- The derivative of an exponential with linear exponent, as a `HasDerivAt` statement. -/
theorem hasDerivAt_exp_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => exp (a * y)) (a * exp (a * x)) x := by
  simpa only [mul_comm] using (hasDerivAt_const_mul a).exp

/-- The derivative of an exponential with linear exponent. -/
@[simp] theorem deriv_exp_mul (a x : ℝ) :
    deriv (fun y : ℝ => exp (a * y)) x = a * exp (a * x) :=
  (hasDerivAt_exp_mul a x).deriv

/-- The norm of the Fréchet derivative of an exponential with linear exponent. -/
@[simp] theorem norm_fderiv_exp_mul (a x : ℝ) :
    ‖fderiv ℝ (fun y : ℝ => exp (a * y)) x‖ = |a| * exp (a * x) := by
  rw [← norm_deriv_eq_norm_fderiv, deriv_exp_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (exp_pos _)]

end Real

namespace TauCeti

/-- The curve `t ↦ c exp (-k t)` has derivative `-k c exp (-k t)`: it solves `x' = -k x`. -/
theorem hasDerivAt_mul_exp_neg_mul (k c t : ℝ) :
    HasDerivAt (fun s ↦ c * Real.exp (-(k * s))) (-(k * (c * Real.exp (-(k * t))))) t := by
  have h : HasDerivAt (fun s : ℝ ↦ -(k * s)) (-k) t := by
    simpa using ((hasDerivAt_id t).const_mul k).fun_neg
  convert h.exp.const_mul c using 1
  ring

/-- Every real iterated derivative of the complex exponential at `z` has norm `‖exp z‖`. -/
theorem norm_iteratedFDeriv_real_cexp (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n Complex.exp z‖ = ‖Complex.exp z‖ := by
  rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

/-- The `n`-th real derivative of `s ↦ Complex.exp (z * s)` is
`s ↦ z ^ n * Complex.exp (z * s)`. -/
@[simp]
theorem iteratedDeriv_cexp_const_mul_ofReal (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun s : ℝ => Complex.exp (z * s)) =
      fun s : ℝ => z ^ n * Complex.exp (z * s) := by
  induction n with
  | zero =>
    ext s
    simp
  | succ n ih =>
    ext s
    rw [iteratedDeriv_succ, ih]
    have hlin : HasDerivAt (fun t : ℝ => z * (t : ℂ)) z s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).const_mul z
    refine ((hlin.cexp.const_mul (z ^ n)).congr_deriv ?_).deriv
    rw [pow_succ]
    ring

section ExpComp

open Real Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {y : ℝ}

/-- `f ∘ exp` is differentiable at `y` exactly when `f` is differentiable at `exp y`. -/
@[simp]
theorem differentiableAt_comp_exp_iff :
    DifferentiableAt ℝ (fun y ↦ f (exp y)) y ↔ DifferentiableAt ℝ f (exp y) := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.comp y differentiableAt_exp⟩
  have h' : DifferentiableAt ℝ (fun y ↦ f (exp y)) (log (exp y)) := by simpa using h
  refine (h'.comp (exp y) (differentiableAt_log (exp_pos y).ne')).congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds (exp_pos y)] with z hz
  simp [exp_log hz]

/-- The chain rule for `f ∘ exp`, with no differentiability hypothesis: where `f` is not
differentiable at `exp y`, neither is `f ∘ exp` at `y`, and both sides are `0`. -/
theorem deriv_comp_exp : deriv (fun y ↦ f (exp y)) y = exp y • deriv f (exp y) := by
  by_cases hf : DifferentiableAt ℝ f (exp y)
  · exact (hf.hasDerivAt.scomp y (hasDerivAt_exp y)).deriv
  · rw [deriv_zero_of_not_differentiableAt hf, smul_zero,
      deriv_zero_of_not_differentiableAt (mt differentiableAt_comp_exp_iff.1 hf)]

end ExpComp

end TauCeti

namespace ContinuousLinearMap

/-- For a real-linear map `ℓ : E →L[ℝ] ℂ`, the `n`-th derivative of `x ↦ exp (ℓ x)` has norm at
most `‖exp (ℓ x)‖ ‖ℓ‖ ^ n`. For a purely imaginary `ℓ`, such as the phase `x ↦ 2πi ⟪x, w⟫` of a
character, this is `‖ℓ‖ ^ n`. -/
theorem norm_iteratedFDeriv_cexp_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℂ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ Complex.exp (ℓ y)) x‖ ≤ ‖Complex.exp (ℓ x)‖ * ‖ℓ‖ ^ n := by
  have h := ℓ.iteratedFDeriv_comp_right ((Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ) x
    (i := n) (mod_cast le_top)
  rw [Function.comp_def] at h
  rw [h, ← TauCeti.norm_iteratedFDeriv_real_cexp n (ℓ x)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  simp

end ContinuousLinearMap

open Asymptotics in
open scoped ContDiff in
/-- **Asymptotic bounds on the derivatives of `exp ℓ`.** Along any filter, the derivative of order
`n + 1` of `y ↦ exp (ℓ y)` is `O(ρ)` for a `C^(n + 1)` map `ℓ` once the derivatives of `ℓ` of
orders `1` to `n + 1` are `O(ρ)` and those of `exp ℓ` of order at most `n` are bounded: it is the
order-`n` derivative of `exp ℓ • Dℓ`, which `ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear`
bounds. -/
theorem ContDiff.isBigO_iteratedFDeriv_succ_exp {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {ℓ : D → ℝ} {n : ℕ} (hℓ : ContDiff ℝ (n + 1) ℓ) {l : Filter D}
    {ρ : D → ℝ} (hℓn : ∀ i, 1 ≤ i → i ≤ n + 1 → iteratedFDeriv ℝ i ℓ =O[l] ρ)
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[l] fun _ ↦ (1 : ℝ)) :
    iteratedFDeriv ℝ (n + 1) (fun y ↦ Real.exp (ℓ y)) =O[l] ρ := by
  have hB := (ContinuousLinearMap.lsmul ℝ ℝ).isBigO_iteratedFDeriv_of_bilinear
    ((Real.contDiff_exp.comp hℓ).of_le (by norm_cast; omega))
    (hℓ.fderiv_right (m := n) le_rfl) (n := n) le_rfl hen
    (fun i hi ↦ (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans
      (hℓn (i + 1) (by omega) (by omega)))
  simp only [ContinuousLinearMap.lsmul_apply, one_mul, Function.comp_apply] at hB
  have hfe : (fun y ↦ Real.exp (ℓ y) • fderiv ℝ ℓ y) = fderiv ℝ (fun y ↦ Real.exp (ℓ y)) :=
    funext fun y ↦ (fderiv_exp (hℓ.differentiable (by simp) y)).symm
  rw [hfe] at hB
  exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.ge).trans hB

open Asymptotics Filter in
/-- **Asymptotic bounds on the derivatives of `exp ℓ - 1`.** Along a filter on which the weight
`ρ` is bounded, the derivative of order `n` of `y ↦ exp (ℓ y) - 1` is `O(ρ)` for a `Cⁿ` map `ℓ`
whose derivatives of order at most `n` are `O(ρ)`. -/
theorem ContDiff.isBigO_iteratedFDeriv_exp_sub_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {ℓ : D → ℝ} {n : ℕ} (hℓ : ContDiff ℝ n ℓ) {l : Filter D} {ρ : D → ℝ}
    (hρ : ρ =O[l] fun _ ↦ (1 : ℝ)) (hdec : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[l] ρ) :
    iteratedFDeriv ℝ n (fun y ↦ Real.exp (ℓ y) - 1) =O[l] ρ := by
  have hℓρ : ℓ =O[l] ρ :=
    (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.ge).trans (hdec 0 (Nat.zero_le n))
  -- `ℓ` is eventually bounded by some `C`, and then `|exp ℓ - 1| ≤ exp C |ℓ|`.
  obtain ⟨C, hC⟩ := (hℓρ.trans hρ).bound
  have he1 : (fun y ↦ Real.exp (ℓ y) - 1) =O[l] ρ := by
    refine (IsBigO.of_bound (Real.exp C) (hC.mono fun y hy ↦ ?_)).trans hℓρ
    rw [norm_one, mul_one, Real.norm_eq_abs] at hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact (TauCeti.abs_exp_sub_one_le_mul_exp_abs _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hy) (abs_nonneg _))
  -- The derivatives of `exp ℓ` of order at most `n` are bounded.
  have hbdd : ∀ k ≤ n, ∀ i ≤ k, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[l]
      fun _ ↦ (1 : ℝ) := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      obtain rfl : i = 0 := by omega
      refine (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans ?_
      simpa using (he1.trans hρ).add (isBigO_refl (fun _ : D ↦ (1 : ℝ)) l)
    | succ k ih =>
      intro hk i hi
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · exact ih (by omega) i (by omega)
      · exact ((hℓ.of_le (by exact_mod_cast hk)).isBigO_iteratedFDeriv_succ_exp
          (fun i _ hi ↦ hdec i (by omega)) (ih (by omega))).trans hρ
  rcases n with _ | n
  · exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans he1
  · have hexp : ContDiff ℝ (n + 1) (fun y ↦ Real.exp (ℓ y)) := Real.contDiff_exp.comp hℓ
    refine (isBigO_of_le _ fun y ↦ le_of_eq ?_).trans
      ((hℓ.isBigO_iteratedFDeriv_succ_exp (fun i _ hi ↦ hdec i hi) (hbdd n (by omega))))
    rw [fun_iteratedFDeriv_sub_apply (hexp.contDiffAt.of_le (by simp)) contDiffAt_const,
      iteratedFDeriv_const_of_ne n.succ_ne_zero, Pi.zero_apply, sub_zero]

open Set in
open scoped Nat in
/-- **Pointwise bound on the derivatives of `exp f`.** Let `f` be `Cⁿ` on an open set containing
`x`, with derivatives of orders `1` to `n` at `x` of norm at most `ε`. Then the derivative of order
`n` of `y ↦ exp (f y)` at `x` has norm at most `n! exp (f x) max ε εⁿ`; for `n ≥ 1` and `ε ≤ 1`
this is `n! exp (f x) ε`. It is a form of the Faà di Bruno bound `norm_iteratedFDeriv_comp_le`
in which the derivatives of `f` of all positive orders have one bound `ε`. -/
theorem ContDiffOn.norm_iteratedFDeriv_exp_comp_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {s : Set E} {n : ℕ} (hf : ContDiffOn ℝ n f s) (hs : IsOpen s)
    {x : E} (hx : x ∈ s) {ε : ℝ} (hε : 0 ≤ ε)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ n (fun y ↦ Real.exp (f y)) x‖ ≤ n ! * Real.exp (f x) * max ε (ε ^ n) := by
  set t : ℝ := ε ^ ((n : ℝ)⁻¹)
  set D : ℝ := max t ε
  have ht₀ : 0 ≤ t := Real.rpow_nonneg hε _
  -- Every power `Dⁱ` with `1 ≤ i ≤ n` is at least `ε`, and `Dⁿ ≤ max ε εⁿ`.
  have hεD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : ε ≤ D ^ i := by
    rcases le_total 1 ε with h1 | h1
    · exact (le_max_right t ε).trans (le_self_pow₀ (h1.trans (le_max_right t ε)) (by omega))
    · have htn : t ^ n = ε := Real.rpow_inv_natCast_pow hε (by omega)
      have ht₁ : t ≤ 1 := Real.rpow_le_one hε h1 (by positivity)
      calc ε = t ^ n := htn.symm
        _ ≤ t ^ i := pow_le_pow_of_le_one ht₀ ht₁ hin
        _ ≤ D ^ i := pow_le_pow_left₀ ht₀ (le_max_left t ε) i
  have hDn : D ^ n ≤ max ε (ε ^ n) := by
    rcases le_total t ε with h | h
    · rw [show D = ε from max_eq_right h]
      exact le_max_right _ _
    · rw [show D = t from max_eq_left h]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [Real.rpow_inv_natCast_pow hε hn.ne']
        exact le_max_left _ _
  have h := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (t := univ) (C := Real.exp (f x))
    (D := D) Real.contDiff_exp.contDiffOn hf le_rfl uniqueDiffOn_univ hs.uniqueDiffOn
    (mapsTo_univ _ _) hx (fun i _ ↦ by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)])
    (fun i hi hin ↦ by
      rw [iteratedFDerivWithin_of_isOpen i hs hx]
      exact (hD i hi hin).trans (hεD i hi hin))
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at h
  exact h.trans (mul_le_mul_of_nonneg_left hDn (by positivity))
