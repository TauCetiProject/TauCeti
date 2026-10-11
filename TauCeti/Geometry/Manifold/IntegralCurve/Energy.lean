/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The energy identity along an integral curve

Let `γ` be an integral curve of a vector field `X` on a manifold, and `f` a real function,
differentiable along `γ`, that decreases along it: `df(X)(γ t) ≤ 0`. If `f (γ t)` has finite limits
`a` as `t → -∞` and `b` as `t → +∞`, then the rate of decrease `-df(X)(γ t)` is integrable on the
real line, and its integral, the **energy** of `γ`, is the drop `a - b`.

This is the fundamental theorem of calculus on the real line for `f ∘ γ`, whose derivative is
`df(X)(γ t)`. The sign makes the derivative integrable on each half-line.

## Main declarations

* `TauCeti.IsMIntegralCurve.integrable_mvfderiv_apply_of_tendsto`: the rate of decrease is
  integrable.
* `TauCeti.IsMIntegralCurve.integral_neg_mvfderiv_apply_eq_sub_of_tendsto`: the energy identity
  `∫ -df(X)(γ t) dt = a - b`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsMIntegralCurve

variable {γ : ℝ → M} {a b : ℝ} (hγ : IsMIntegralCurve γ X)
  (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t))
  (hnonpos : ∀ t, mvfderiv 𝓘(ℝ, E) f (γ t) (X (γ t)) ≤ 0)
  (hbot : Tendsto (f ∘ γ) atBot (𝓝 a)) (htop : Tendsto (f ∘ γ) atTop (𝓝 b))
include hγ hf hnonpos hbot htop

/-- **The rate of decrease of `f` along an integral curve is integrable.** If `γ` is an integral
curve of `X` along which `f` is differentiable and `df(X) ≤ 0`, and `f ∘ γ` has finite limits as
`t → -∞` and as `t → +∞`, then `t ↦ df(X)(γ t)` is integrable on the real line. -/
theorem integrable_mvfderiv_apply_of_tendsto :
    Integrable fun t ↦ mvfderiv 𝓘(ℝ, E) f (γ t) (X (γ t)) := by
  -- The derivative of `f ∘ γ` is nonpositive, so it is integrable on each half-line, since
  -- `f ∘ γ` has limits at both ends.
  have hderiv (t : ℝ) := Manifold.hasDerivAt_comp_curve (hf t) (hγ t)
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, integrableOn_Ioi_deriv_of_nonpos' (fun t _ ↦ hderiv t) (fun t _ ↦ hnonpos t) htop⟩
  -- Reflect the negative half-line onto the positive one.
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding, neg_preimage, neg_Iio, neg_zero, ← integrableOn_neg_iff]
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun s ↦ f (γ (-s))) (fun s _ ↦ ?_)
    (fun s _ ↦ ?_) (hbot.comp tendsto_neg_atTop_atBot)
  · simpa [comp_def] using (hderiv (-s)).comp s (hasDerivAt_neg s)
  · simpa using hnonpos (-s)

/-- **The energy identity.** If `γ` is an integral curve of `X` along which `f` is differentiable
and `df(X) ≤ 0`, and `f ∘ γ` tends to `a` as `t → -∞` and to `b` as `t → +∞`, then the energy
`∫ -df(X)(γ t) dt` is `a - b`. -/
theorem integral_neg_mvfderiv_apply_eq_sub_of_tendsto :
    ∫ t, -mvfderiv 𝓘(ℝ, E) f (γ t) (X (γ t)) = a - b := by
  -- The fundamental theorem of calculus on the real line.
  rw [integral_neg, integral_of_hasDerivAt_of_tendsto
    (fun t ↦ Manifold.hasDerivAt_comp_curve (hf t) (hγ t))
    (integrable_mvfderiv_apply_of_tendsto hγ hf hnonpos hbot htop) hbot htop, neg_sub]

end IsMIntegralCurve

end TauCeti
