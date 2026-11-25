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

If the derivative of `f` on `[a, ∞)` has norm at most `M e^{α(t - a)}` with `α > 0`, then
`‖f t‖ ≤ (‖f a‖ + M / α) e^{α(t - a)}` there. Iterating this, an exponential bound of positive
rate on the `n`th derivative of a `C^n` function on `[a, ∞)` gives exponential bounds of the
same rate on all lower derivatives. This is the form in which a Laplace integral of an
iterated derivative is shown to converge in the asymptotics of Laplace integrals by
integration by parts (`TauCeti.Analysis.LaplaceTransform.IntegrationByParts`).

## Main results

* `TauCeti.norm_le_mul_exp_of_hasDerivWithinAt`: the bound for `f` from the bound for `f'`.
* `ContDiffOn.exists_norm_iteratedDerivWithin_le_mul_exp`: the bound for the lower derivatives
  of a `C^n` function.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>):
`Asymptotics.norm_le_mul_exp_of_hasDerivWithinAt` in
`DLMFMathlib/Analysis/Asymptotics/ExponentialGrowth.lean` and the private
`laplace_derivatives_exp_bound` in `DLMF/AsymptoticApproximations/Integrals/Parts.lean`. Here the
first is derived from Mathlib's fencing theorem
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`.
-/

public section

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace TauCeti

/-- If `f` has derivative `f' t` within `[a, ∞)` at every `t ≥ a`, and
`‖f' t‖ ≤ M e^{α(t - a)}` there with `α > 0`, then `‖f t‖ ≤ (‖f a‖ + M / α) e^{α(t - a)}` for
every `t ≥ a`. -/
theorem norm_le_mul_exp_of_hasDerivWithinAt {f f' : ℝ → E} {a α M : ℝ} (hα : 0 < α)
    (hf : ∀ t ∈ Ici a, HasDerivWithinAt f (f' t) (Ici a) t)
    (hb : ∀ t ∈ Ici a, ‖f' t‖ ≤ M * Real.exp (α * (t - a))) {t : ℝ} (ht : a ≤ t) :
    ‖f t‖ ≤ (‖f a‖ + M / α) * Real.exp (α * (t - a)) := by
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hb a self_mem_Ici)
  -- the bound `B u = (‖f a‖ + M / α) e^{α(u - a)}` has derivative at least `M e^{α(u - a)}`
  have hB (u : ℝ) : HasDerivAt (fun v ↦ (‖f a‖ + M / α) * Real.exp (α * (v - a)))
      ((α * ‖f a‖ + M) * Real.exp (α * (u - a))) u := by
    have h := (((hasDerivAt_id' u).sub_const a).const_mul α).exp.const_mul (‖f a‖ + M / α)
    convert h using 1
    field_simp
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun u hu ↦ (hf u hu.1).continuousWithinAt.mono Icc_subset_Ici_self)
    (fun u hu ↦ (hf u hu.1).mono (Ici_subset_Ici.2 hu.1)) (by simpa using div_nonneg hM hα.le) hB
    (fun u hu ↦ (hb u hu.1).trans ?_) ⟨ht, le_rfl⟩
  gcongr
  exact le_add_of_nonneg_left (by positivity)

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
    refine ⟨‖iteratedDerivWithin k f (Ici a) a‖ + C / α, fun t ht ↦
      TauCeti.norm_le_mul_exp_of_hasDerivWithinAt hα (fun u hu ↦ ?_) hC ht⟩
    rw [iteratedDerivWithin_succ]
    exact (hf.differentiableOn_iteratedDerivWithin (mod_cast hk) (uniqueDiffOn_Ici a) u
      hu).hasDerivWithinAt
