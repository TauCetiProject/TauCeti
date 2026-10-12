/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Dynamics.Flow.Stable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite energy of negative gradient trajectories

For a negative gradient trajectory whose function values converge at both ends, the squared
norm of the gradient is integrable on the whole real line, and its integral is the difference
of the limiting values. Integrability is a conclusion, not an assumption. No continuity of the
gradient or nondegeneracy of the limiting points is required: the nonnegative derivative of
`-f ∘ γ` is automatically integrable on compact intervals, and convergence of its primitive
controls the improper integrals.

The half-line formulas identify the energy remaining before or after any time. Mathlib's
`MeasureTheory.tendsto_integral_Iic_zero` and `MeasureTheory.tendsto_integral_Ioi_zero` give the
vanishing of these tails. Together with
`TauCeti.IsIntegralCurveOn.exists_tendsto_comp_atTop` from `Morse.Convergence`, the forward
integrability theorem gives finite energy for a negative gradient trajectory confined to a
compact set. The forward and backward critical-point convergence theorems in that module
similarly supply the limits for the whole-line identity. For a connecting orbit from `p` to `q`,
the total energy is `f p - f q`; in particular it depends only on the endpoints. These energy
formulas apply to the trajectories themselves, without manifold structures on their stable
and unstable sets.

Apply the trajectory lemmas by their qualified names in `TauCeti.IsIntegralCurveOn` and
`TauCeti.IsIntegralCurve`, following the organization of `Morse.GradientFlow`. The
curve predicates themselves are Mathlib's `IsIntegralCurveOn` and `IsIntegralCurve`; the
qualified namespaces above contain the energy lemmas, not new predicates. The
connecting-orbit lemmas are in `TauCeti.Flow.IsNegativeGradient`. With `open TauCeti`, use
`hφ.integrable_norm_gradient_sq_of_mem_unstableSet_inter_stableSet hf hfp hfq hx` for finite
energy, and `hφ.integral_norm_gradient_sq_eq_sub_of_mem_unstableSet_inter_stableSet hf hfp hfq hx`
for the endpoint energy identity.
The restricted-curve lemmas take the interval endpoints before the curve hypothesis; for example,
`TauCeti.IsIntegralCurveOn.integrableOn_Ioi_norm_gradient_sq a hγ hf hplus` proves finite
forward energy after time `a`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (gradient trajectories) and Section 6.5.a (their energy).

The improper-integral arguments use Mathlib's nonnegative-derivative FTC and
`MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_tendsto`.
-/

public section

open Filter Function InnerProductSpace MeasureTheory Set
open scoped Gradient Interval Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {cMinus cPlus : ℝ}

namespace IsIntegralCurveOn

/-- The squared gradient along a negative gradient trajectory is integrable on every compact
time interval, assuming only differentiability of the defining function along that interval. -/
theorem intervalIntegrable_norm_gradient_sq
    (a b : ℝ) (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (uIcc a b))
    (hf : ∀ t ∈ uIcc a b, DifferentiableAt ℝ f (γ t)) :
    IntervalIntegrable (fun t ↦ ‖∇ f (γ t)‖ ^ 2) volume a b := by
  have hd : ∀ t ∈ uIcc a b,
      HasDerivWithinAt (fun t ↦ -f (γ t)) (‖∇ f (γ t)‖ ^ 2) (uIcc a b) t := by
    intro t ht
    simpa only [neg_neg, Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ ht (hf t ht)).fun_neg
  exact intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t _ ↦ sq_nonneg _)

/-- A finite forward limiting value implies finite energy on every forward half-line. -/
theorem integrableOn_Ioi_norm_gradient_sq
    (a : ℝ) (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hf : ∀ t ∈ Ici a, DifferentiableAt ℝ f (γ t))
    (hplus : Tendsto (f ∘ γ) atTop (𝓝 cPlus)) :
    IntegrableOn (fun t ↦ ‖∇ f (γ t)‖ ^ 2) (Ioi a) := by
  apply integrableOn_Ioi_deriv_of_nonneg
    (g := fun t ↦ -f (γ t)) (l := -cPlus)
  · simpa only [Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ self_mem_Ici (hf a self_mem_Ici)).fun_neg
        |>.continuousWithinAt
  · intro t ht
    simpa only [neg_neg, Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ ht.le (hf t ht.le)).fun_neg
        |>.hasDerivAt (Ici_mem_nhds ht)
  · exact fun t _ ↦ sq_nonneg _
  · exact hplus.neg

/-- The energy after time `a` is the drop from the value at `a` to the forward limiting value. -/
theorem integral_Ioi_norm_gradient_sq_eq_sub
    (a : ℝ) (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici a))
    (hf : ∀ t ∈ Ici a, DifferentiableAt ℝ f (γ t))
    (hplus : Tendsto (f ∘ γ) atTop (𝓝 cPlus)) :
    ∫ t in Ioi a, ‖∇ f (γ t)‖ ^ 2 = f (γ a) - cPlus := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun t ↦ -f (γ t)) (g' := fun t ↦ ‖∇ f (γ t)‖ ^ 2)
    (a := a) (l := -cPlus)
    (by simpa only [Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ self_mem_Ici (hf a self_mem_Ici)).fun_neg
        |>.continuousWithinAt)
    (fun t ht ↦ by simpa only [neg_neg, Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ ht.le (hf t ht.le)).fun_neg
        |>.hasDerivAt (Ici_mem_nhds ht))
    (fun t _ ↦ sq_nonneg _) hplus.neg
  simpa only [neg_sub_neg] using h

/-- A finite backward limiting value implies finite energy on every backward half-line. -/
theorem integrableOn_Iic_norm_gradient_sq
    (a : ℝ) (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a))
    (hf : ∀ t ∈ Iic a, DifferentiableAt ℝ f (γ t))
    (hminus : Tendsto (f ∘ γ) atBot (𝓝 cMinus)) :
    IntegrableOn (fun t ↦ ‖∇ f (γ t)‖ ^ 2) (Iic a) := by
  have hinterval (t : ℝ) (ht : t ≤ a) := intervalIntegrable_norm_gradient_sq t a
    (hγ.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Iic_self))
    (fun s hs ↦ hf s (by rw [uIcc_of_le ht] at hs; exact hs.2))
  refine integrableOn_Iic_of_intervalIntegral_norm_tendsto (cMinus - f (γ a)) a
    (fun t ↦ ?_) tendsto_id ?_
  · by_cases ht : t ≤ a
    · exact (hinterval t ht).1
    · simp [Ioc_eq_empty_of_le (le_of_not_ge ht)]
  · apply (hminus.sub_const _).congr'
    filter_upwards [Iic_mem_atBot a] with t ht
    simp only [Real.norm_of_nonneg (sq_nonneg _)]
    exact (IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub
      hγ
      (by rw [uIcc_of_le ht]; exact Icc_subset_Iic_self)
      (fun s hs ↦ hf s (by rw [uIcc_of_le ht] at hs; exact hs.2))
      (hinterval t ht)).symm

/-- The energy before time `a` is the drop from the backward limiting value to the value at `a`. -/
theorem integral_Iic_norm_gradient_sq_eq_sub
    (a : ℝ) (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic a))
    (hf : ∀ t ∈ Iic a, DifferentiableAt ℝ f (γ t))
    (hminus : Tendsto (f ∘ γ) atBot (𝓝 cMinus)) :
    ∫ t in Iic a, ‖∇ f (γ t)‖ ^ 2 = cMinus - f (γ a) := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto
    (f := fun t ↦ -f (γ t)) (f' := fun t ↦ ‖∇ f (γ t)‖ ^ 2)
    (a := a) (m := -cMinus)
    (by simpa only [Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ self_mem_Iic (hf a self_mem_Iic)).fun_neg
        |>.continuousWithinAt)
    (fun t ht ↦ by simpa only [neg_neg, Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ ht.le (hf t ht.le)).fun_neg
        |>.hasDerivAt (Iic_mem_nhds ht))
    (integrableOn_Iic_norm_gradient_sq a hγ hf hminus) hminus.neg
  simpa only [neg_sub_neg] using h

end IsIntegralCurveOn

namespace IsIntegralCurve

/-- A negative gradient trajectory with finite limiting values at both ends has finite total
energy. Neither continuity of the gradient nor nondegeneracy of the endpoints is needed. -/
theorem integrable_norm_gradient_sq
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    (hminus : Tendsto (f ∘ γ) atBot (𝓝 cMinus))
    (hplus : Tendsto (f ∘ γ) atTop (𝓝 cPlus)) :
    Integrable (fun t ↦ ‖∇ f (γ t)‖ ^ 2) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨IsIntegralCurveOn.integrableOn_Iic_norm_gradient_sq 0 (hγ.isIntegralCurveOn (Iic 0))
      (fun t _ ↦ hf t) hminus,
    IsIntegralCurveOn.integrableOn_Ioi_norm_gradient_sq 0 (hγ.isIntegralCurveOn (Ici 0))
      (fun t _ ↦ hf t) hplus⟩

/-- **Total energy identity.** The energy of a negative gradient trajectory with finite limiting
values at both ends equals their difference. Integrability is proved from these limits. -/
theorem integral_norm_gradient_sq_eq_sub_of_tendsto
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    (hminus : Tendsto (f ∘ γ) atBot (𝓝 cMinus))
    (hplus : Tendsto (f ∘ γ) atTop (𝓝 cPlus)) :
    ∫ t, ‖∇ f (γ t)‖ ^ 2 = cMinus - cPlus := by
  have h := integral_of_hasDerivAt_of_tendsto
    (f := fun t ↦ -f (γ t)) (f' := fun t ↦ ‖∇ f (γ t)‖ ^ 2)
    (fun t ↦ by simpa only [neg_neg, Function.comp_def] using
      (hasDerivAt_comp_neg_gradient hγ (hf t)).fun_neg)
    (integrable_norm_gradient_sq hγ hf hminus hplus) hminus.neg hplus.neg
  simpa only [neg_sub_neg] using h

end IsIntegralCurve

namespace Flow

open _root_.Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q x : E}

/-- Every orbit connecting `p` to `q` has integrable squared gradient. -/
theorem IsNegativeGradient.integrable_norm_gradient_sq_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    Integrable (fun t ↦ ‖∇ f (φ t x)‖ ^ 2) :=
  IsIntegralCurve.integrable_norm_gradient_sq (hφ.isIntegralCurve x) hf
    (hfp.tendsto.comp (mem_unstableSet.mp hx.1))
    (hfq.tendsto.comp (mem_stableSet.mp hx.2))

/-- Every orbit connecting `p` to `q` has total energy `f p - f q`. -/
theorem IsNegativeGradient.integral_norm_gradient_sq_eq_sub_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    ∫ t, ‖∇ f (φ t x)‖ ^ 2 = f p - f q :=
  TauCeti.IsIntegralCurve.integral_norm_gradient_sq_eq_sub_of_tendsto (hφ.isIntegralCurve x) hf
    (hfp.tendsto.comp (mem_unstableSet.mp hx.1))
    (hfq.tendsto.comp (mem_stableSet.mp hx.2))

end Flow

end TauCeti
