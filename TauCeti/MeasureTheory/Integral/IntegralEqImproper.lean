/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives of improper tail integrals

For an integrable function `f` on `(a, ∞)`, its tail integral `t ↦ ∫ s in Ioi t, f s`
has derivative `-f t` at each `t > a` where `f` is continuous. If `f` is continuous on
the whole ray, the derivative identity also gives a formula for every higher iterated
derivative. These results apply to Banach-space-valued integrands and support differential
closure arguments for improper integrals.

## References

* Mathlib's `intervalIntegral.integral_Ioi_sub_Ioi'` and
  `intervalIntegral.integral_hasDerivAt_right`.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace MeasureTheory.IntegrableOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E} {a t : ℝ}

/-- At a continuity point strictly inside an integrable ray, the tail integral has derivative
equal to the negated integrand. -/
theorem hasDerivAt_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : HasDerivAt (fun u ↦ ∫ s in Ioi u, f s) (-f t) t := by
  have hfinite : HasDerivAt (fun u ↦ ∫ s in t..u, f s) (f t) t :=
    integral_hasDerivAt_right IntervalIntegrable.refl
      (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        hint.aestronglyMeasurable (Ioi_mem_nhds ht)) hcont
  have heq : (fun u ↦ (∫ s in Ioi t, f s) - ∫ s in t..u, f s) =ᶠ[𝓝 t]
      (fun u ↦ ∫ s in Ioi u, f s) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [← integral_Ioi_sub_Ioi' (hint.mono_set (Ioi_subset_Ioi ht.le))
      (hint.mono_set (Ioi_subset_Ioi hu.le)), sub_sub_cancel]
  exact (hfinite.const_sub (∫ s in Ioi t, f s)).congr_of_eventuallyEq heq.symm

/-- The derivative of an improper tail integral is the negated integrand at each continuity
point strictly inside the integrable ray. -/
theorem deriv_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : deriv (fun u ↦ ∫ s in Ioi u, f s) t = -f t :=
  (hint.hasDerivAt_integral_Ioi hcont ht).deriv

/-- For a continuous integrand on an integrable ray, the derivative of order `n + 1` of its
tail integral is the negated derivative of order `n` of the integrand at each interior point.
The identity concerns total iterated derivatives and does not assume higher smoothness. -/
theorem iteratedDeriv_integral_Ioi (hint : IntegrableOn f (Ioi a))
    (hcont : ContinuousOn f (Ioi a)) (n : ℕ) (ht : a < t) :
    iteratedDeriv (n + 1) (fun u ↦ ∫ s in Ioi u, f s) t = -iteratedDeriv n f t := by
  have heq : deriv (fun u ↦ ∫ s in Ioi u, f s) =ᶠ[𝓝 t] (fun u ↦ -f u) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact hint.deriv_integral_Ioi (hcont.continuousAt (isOpen_Ioi.mem_nhds hu)) hu
  rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_fun_neg]

end MeasureTheory.IntegrableOn
