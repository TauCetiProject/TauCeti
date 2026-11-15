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
import TauCeti.Analysis.SpecialFunctions.Exp.Limits

/-!
# Derivatives of exponential functions

Viewed as a function of a real vector variable, `Complex.exp` has the same iterated derivatives
as it has over `ℂ`, restricted to real scalars. Since every complex derivative of `exp` is `exp`,
every real iterated derivative of `Complex.exp` at `z` has norm `‖exp z‖`. This is the input a
Faà di Bruno bound needs for compositions `Complex.exp ∘ f` with a real-differentiable `f`.

For a function `f` on `ℝ`, `f ∘ exp` is differentiable at `y` exactly when `f` is differentiable
at `exp y`, so the chain rule `(f ∘ exp)'(y) = e^y f'(e^y)` holds with no hypothesis on `f`.

## Main results

* `TauCeti.differentiableAt_comp_exp_iff`: `f ∘ exp` is differentiable at `y` exactly when `f` is
  differentiable at `exp y`.
* `TauCeti.deriv_comp_exp`: `(f ∘ exp)'(y) = e^y • f'(e^y)`, unconditionally.
* `TauCeti.norm_iteratedFDeriv_real_cexp`: every real iterated derivative of `Complex.exp` at `z`
  has norm `‖exp z‖`.
* `ContinuousLinearMap.norm_iteratedFDeriv_cexp_comp_le`: for a real-linear map `ℓ` to `ℂ`, the
  `n`-th derivative of `x ↦ exp (ℓ x)` has norm at most `‖exp (ℓ x)‖ ‖ℓ‖ ^ n`.
* `ContDiff.isBigO_iteratedFDeriv_succ_exp`: along any filter, the derivative of order `n + 1` of
  `exp ℓ` is `O(ρ)` when the derivatives of `ℓ` of positive order up to that order are `O(ρ)` and
  those of `exp ℓ` of lower order are bounded.
* `ContDiff.isBigO_iteratedFDeriv_exp_sub_one`: along a filter on which `ρ → 0`, the order-`n`
  derivative of `exp ℓ - 1` is `O(ρ)` when the derivatives of `ℓ` of order at most `n` are.
-/

public section

namespace Real

/-- The derivative of an exponential with linear exponent. -/
@[simp] theorem deriv_exp_mul (a x : ℝ) :
    deriv (fun y : ℝ => exp (a * y)) x = a * exp (a * x) := by
  simpa [mul_comm] using (((hasDerivAt_id x).const_mul a).exp).deriv

/-- The norm of the Fréchet derivative of an exponential with linear exponent. -/
@[simp] theorem norm_fderiv_exp_mul (a x : ℝ) :
    ‖fderiv ℝ (fun y : ℝ => exp (a * y)) x‖ = |a| * exp (a * x) := by
  rw [← norm_deriv_eq_norm_fderiv, deriv_exp_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (exp_pos _)]

end Real

namespace TauCeti

/-- Every real iterated derivative of the complex exponential at `z` has norm `‖exp z‖`. -/
theorem norm_iteratedFDeriv_real_cexp (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n Complex.exp z‖ = ‖Complex.exp z‖ := by
  rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

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

open Asymptotics Filter Topology in
/-- **Asymptotic bounds on the derivatives of `exp ℓ - 1`.** Along any filter on which `ρ` tends
to zero, if the derivatives of order at most `n` of a `Cⁿ` map `ℓ` are `O(ρ)`, then so is the
order-`n` derivative of `y ↦ exp (ℓ y) - 1`. -/
theorem ContDiff.isBigO_iteratedFDeriv_exp_sub_one {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {ℓ : D → ℝ} {n : ℕ} (hℓ : ContDiff ℝ n ℓ) {l : Filter D} {ρ : D → ℝ}
    (hρ : Tendsto ρ l (𝓝 0)) (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[l] ρ) :
    iteratedFDeriv ℝ n (fun y ↦ Real.exp (ℓ y) - 1) =O[l] ρ := by
  have hℓ0 : ℓ =O[l] ρ :=
    (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.ge).trans (hℓn 0 (Nat.zero_le n))
  have he : ContDiff ℝ n (fun y ↦ Real.exp (ℓ y)) := Real.contDiff_exp.comp hℓ
  -- In positive order, the derivatives of `exp ℓ - 1` are those of `exp ℓ`.
  have hsub (i : ℕ) (hi : i ≠ 0) (hin : i ≤ n) (y : D) :
      iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y) - 1) y =
        iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) y := by
    rw [fun_iteratedFDeriv_sub_apply (he.contDiffAt.of_le (by exact_mod_cast hin))
      contDiffAt_const, iteratedFDeriv_const_of_ne hi, Pi.zero_apply, sub_zero]
  -- Strong induction on the order `j ≤ n`.
  suffices h : ∀ j ≤ n, iteratedFDeriv ℝ j (fun y ↦ Real.exp (ℓ y) - 1) =O[l] ρ from h n le_rfl
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hjn
  rcases j with _ | j
  · exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans
      (Real.isBigO_exp_comp_sub_one (hℓ0.trans_tendsto hρ) hℓ0)
  -- The derivatives of `exp ℓ` of order at most `j` are bounded: `exp ℓ → 1`, and in positive
  -- order they are `O(ρ)` by induction.
  have hen (i : ℕ) (hi : i ≤ j) :
      iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[l] fun _ ↦ (1 : ℝ) := by
    rcases i with _ | i
    · refine (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans ?_
      exact ((Real.continuous_exp.tendsto 0).comp (hℓ0.trans_tendsto hρ)).isBigO_one ℝ
    · exact (isBigO_of_le _ fun y ↦
        (congrArg norm (hsub (i + 1) i.succ_ne_zero (by omega) y)).ge).trans
          ((ih (i + 1) (by omega) (by omega)).trans (hρ.isBigO_one ℝ))
  exact (isBigO_of_le _ fun y ↦ (congrArg norm (hsub (j + 1) j.succ_ne_zero hjn y)).le).trans
    ((hℓ.of_le (by exact_mod_cast hjn)).isBigO_iteratedFDeriv_succ_exp
      (fun i _ hi ↦ hℓn i (hi.trans hjn)) hen)
