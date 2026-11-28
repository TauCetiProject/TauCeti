/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential bounds from a bound on the derivative

If the right derivative of `f` on `[a, b)` has norm at most `M e^{α(t - a)}` with `α ≠ 0`, then
`‖f t - f a‖ ≤ (M / α) (e^{α(t - a)} - 1)` on `[a, b]`; for `α > 0` and `M ≥ 0` this gives
`‖f t‖ ≤ (‖f a‖ + M / α) e^{α(t - a)}`. Iterating this, an exponential bound of positive
rate on the `n`th derivative of a `C^n` function on `[a, ∞)` gives exponential bounds of the
same rate on all lower derivatives. This is the form in which a Laplace integral of an
iterated derivative is shown to converge in the asymptotics of Laplace integrals by
integration by parts (`TauCeti.Analysis.LaplaceTransform.IntegrationByParts`).

## Main results

* `TauCeti.norm_sub_le_mul_exp_sub_one_of_norm_deriv_right_le`: the bound for the increment of
  `f` from the bound for `f'`.
* `TauCeti.norm_le_mul_exp_of_hasDerivWithinAt`: the resulting bound for `f`, for `α > 0`.
* `ContDiffOn.exists_norm_iteratedDerivWithin_le_mul_exp`: the bound for the lower derivatives
  of a `C^n` function.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>):
`Asymptotics.norm_le_mul_exp_of_hasDerivWithinAt` in
`DLMFMathlib/Analysis/Asymptotics/ExponentialGrowth.lean` and the private
`laplace_derivatives_exp_bound` in `DLMF/AsymptoticApproximations/Integrals/Parts.lean`. Here the
increment bound is derived from Mathlib's fencing theorem
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`.
-/

public section

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace TauCeti

/-- If `f` is continuous on `[a, b]`, has right derivative `f' x` at every `x ∈ [a, b)`, and
`‖f' x‖ ≤ M e^{α(x - a)}` there with `α ≠ 0`, then `‖f x - f a‖ ≤ (M / α) (e^{α(x - a)} - 1)` for
every `x ∈ [a, b]`. -/
theorem norm_sub_le_mul_exp_sub_one_of_norm_deriv_right_le {f f' : ℝ → E} {a b α M : ℝ}
    (hα : α ≠ 0) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hb : ∀ x ∈ Ico a b, ‖f' x‖ ≤ M * Real.exp (α * (x - a))) :
    ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ M / α * (Real.exp (α * (x - a)) - 1) := by
  -- the bound `B x = (M / α) (e^{α(x - a)} - 1)` vanishes at `a` and has derivative
  -- `M e^{α(x - a)}`
  have hB (x : ℝ) : HasDerivAt (fun y ↦ M / α * (Real.exp (α * (y - a)) - 1))
      (M * Real.exp (α * (x - a))) x := by
    have h := ((((hasDerivAt_id' x).sub_const a).const_mul α).exp.sub_const 1).const_mul (M / α)
    convert h using 1
    field_simp
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary (hf.sub continuousOn_const)
    (fun x hx ↦ (hf' x hx).sub_const (f a)) (by simp) hB hb

/-- If `f` is continuous on `[a, t]`, has right derivative `f' u` at every `u ∈ [a, t)`, and
`‖f' u‖ ≤ M e^{α(u - a)}` there with `α > 0` and `M ≥ 0`, then
`‖f t‖ ≤ (‖f a‖ + M / α) e^{α(t - a)}`. -/
theorem norm_le_mul_exp_of_hasDerivWithinAt {f f' : ℝ → E} {a α M t : ℝ} (hα : 0 < α)
    (hM : 0 ≤ M) (ht : a ≤ t) (hf : ContinuousOn f (Icc a t))
    (hf' : ∀ u ∈ Ico a t, HasDerivWithinAt f (f' u) (Ici u) u)
    (hb : ∀ u ∈ Ico a t, ‖f' u‖ ≤ M * Real.exp (α * (u - a))) :
    ‖f t‖ ≤ (‖f a‖ + M / α) * Real.exp (α * (t - a)) := by
  have h := norm_sub_le_mul_exp_sub_one_of_norm_deriv_right_le hα.ne' hf hf' hb t ⟨ht, le_rfl⟩
  have he : 1 ≤ Real.exp (α * (t - a)) := Real.one_le_exp (by nlinarith)
  have hMα : 0 ≤ M / α := div_nonneg hM hα.le
  calc ‖f t‖ ≤ ‖f a‖ + ‖f t - f a‖ := norm_le_norm_add_norm_sub' (f t) (f a)
    _ ≤ (‖f a‖ + M / α) * Real.exp (α * (t - a)) := by nlinarith [norm_nonneg (f a)]

end TauCeti

/-- Let `f` be `C^n` on `[a, ∞)` and let its `n`th derivative within `[a, ∞)` have norm at most
`M e^{α(t - a)}` there, with `α > 0`. Then for every `k ≤ n` the `k`th derivative has norm at
most `C e^{α(t - a)}` on `[a, ∞)` for some constant `C`. -/
theorem ContDiffOn.exists_norm_iteratedDerivWithin_le_mul_exp {f : ℝ → E} {a α M : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f (Ici a)) (hα : 0 < α)
    (hb : ∀ t ∈ Ici a, ‖iteratedDerivWithin n f (Ici a) t‖ ≤ M * Real.exp (α * (t - a)))
    {k : ℕ} (hk : k ≤ n) :
    ∃ C, ∀ t ∈ Ici a, ‖iteratedDerivWithin k f (Ici a) t‖ ≤ C * Real.exp (α * (t - a)) := by
  induction hk using Nat.decreasingInduction with
  | self => exact ⟨M, hb⟩
  | of_succ k hk ih =>
    obtain ⟨C, hC⟩ := ih
    have hC₀ : 0 ≤ C := by
      simpa using (norm_nonneg _).trans (hC a self_mem_Ici)
    have hd := hf.differentiableOn_iteratedDerivWithin (mod_cast hk) (uniqueDiffOn_Ici a)
    refine ⟨‖iteratedDerivWithin k f (Ici a) a‖ + C / α, fun t (ht : a ≤ t) ↦
      TauCeti.norm_le_mul_exp_of_hasDerivWithinAt hα hC₀ ht
        (hd.continuousOn.mono Icc_subset_Ici_self) (fun u hu ↦ ?_) fun u hu ↦ hC u hu.1⟩
    rw [iteratedDerivWithin_succ]
    exact ((hd u hu.1).hasDerivWithinAt).mono (Ici_subset_Ici.2 hu.1)
