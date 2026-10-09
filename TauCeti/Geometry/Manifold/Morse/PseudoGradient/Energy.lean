/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The energy identity for an adapted pseudo-gradient

Let `X` be a pseudo-gradient field adapted to a function `f` on a compact boundaryless manifold,
and let `γ t = φ_t p` be an orbit of its flow converging to `x` as `t → -∞` and to `y` as
`t → +∞`. Suppose that `f` is differentiable along the orbit and continuous at `x` and `y`. The
**energy** of the orbit, the integral over the whole line of the rate `-df(X)(γ t) ≥ 0` at which `f`
decreases, is finite and equals the drop `f x - f y`.

For a gradient flow the energy is `∫ ‖∇f(γ t)‖²`. For a pseudo-gradient it is `∫ -df(X)(γ t)`,
which is the quantity that the flow actually controls.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.integrable_mvfderiv_apply_of_tendsto`: the rate of decrease of
  `f` along an integral curve of `X` on which `f` has limits at both ends is integrable.
* `TauCeti.IsAdaptedPseudoGradient.integral_neg_mvfderiv_apply_eq_sub_of_tendsto`: the energy
  identity `∫ -df(X)(γ t) dt = a - b` when `f (γ t)` tends to `a` and `b` at `-∞` and `+∞`.
* `IsAdaptedPseudoGradient.integrable_mvfderiv_apply_flow_of_mem_unstableSet_inter_stableSet`
  and `integral_neg_mvfderiv_apply_flow_eq_sub_of_mem_unstableSet_inter_stableSet` (in the same
  namespace): the same for an orbit of the flow connecting `x` to `y`, where the energy is
  `f x - f y`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

section Curve

variable (hX : IsAdaptedPseudoGradient f X) {γ : ℝ → M} {a b : ℝ}
  (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t)) (hγ : IsMIntegralCurve γ X)
  (hbot : Tendsto (f ∘ γ) atBot (𝓝 a)) (htop : Tendsto (f ∘ γ) atTop (𝓝 b))
include hX hf hγ hbot htop

omit [FiniteDimensional ℝ E] in
/-- **The rate of decrease of `f` along an integral curve is integrable.** If `γ` is an integral
curve of `X`, `f` is differentiable along it and `f ∘ γ` has finite limits as `t → -∞` and as
`t → +∞`, then `t ↦ df(X)(γ t)` is integrable on the real line. -/
theorem integrable_mvfderiv_apply_of_tendsto :
    Integrable fun t ↦ mvfderiv 𝓘(ℝ, E) f (γ t) (X (γ t)) := by
  -- The derivative of `f ∘ γ` is nonpositive, so it is integrable on each half-line, since
  -- `f ∘ γ` has limits at both ends.
  have hderiv (t : ℝ) := Manifold.hasDerivAt_comp_curve (hf t) (hγ t)
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, integrableOn_Ioi_deriv_of_nonpos' (fun t _ ↦ hderiv t)
    (fun t _ ↦ hX.mvfderiv_apply_nonpos _) htop⟩
  -- Reflect the negative half-line onto the positive one.
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding, neg_preimage, neg_Iio, neg_zero, ← integrableOn_neg_iff]
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun s ↦ f (γ (-s))) (fun s _ ↦ ?_)
    (fun s _ ↦ ?_) (hbot.comp tendsto_neg_atTop_atBot)
  · simpa [comp_def] using (hderiv (-s)).comp s (hasDerivAt_neg s)
  · simpa using hX.mvfderiv_apply_nonpos _

omit [FiniteDimensional ℝ E] in
/-- **The energy identity.** If `γ` is an integral curve of `X`, `f` is differentiable along it
and `f ∘ γ` tends to `a` as `t → -∞` and to `b` as `t → +∞`, then the energy
`∫ -df(X)(γ t) dt` is `a - b`. -/
theorem integral_neg_mvfderiv_apply_eq_sub_of_tendsto :
    ∫ t, -mvfderiv 𝓘(ℝ, E) f (γ t) (X (γ t)) = a - b := by
  -- The fundamental theorem of calculus on the real line.
  rw [integral_neg, integral_of_hasDerivAt_of_tendsto
    (fun t ↦ Manifold.hasDerivAt_comp_curve (hf t) (hγ t))
    (hX.integrable_mvfderiv_apply_of_tendsto hf hγ hbot htop) hbot htop, neg_sub]

end Curve

variable [CompactSpace M] [T2Space M] (hX : IsAdaptedPseudoGradient f X) {x y p : M}
  (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (hX.flow t p)) (hfx : ContinuousAt f x)
  (hfy : ContinuousAt f y) (hp : p ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y)
include hX hf hfx hfy hp

/-- **The rate of decrease of `f` along a connecting orbit is integrable.** If the orbit of `p`
converges to `x` as `t → -∞` and to `y` as `t → +∞`, `f` is differentiable along it and continuous
at `x` and `y`, then `t ↦ df(X)(φ_t p)` is integrable on the real line. -/
theorem integrable_mvfderiv_apply_flow_of_mem_unstableSet_inter_stableSet :
    Integrable fun t ↦ mvfderiv 𝓘(ℝ, E) f (hX.flow t p) (X (hX.flow t p)) :=
  hX.integrable_mvfderiv_apply_of_tendsto hf (hX.isMIntegralCurve_flow p)
    (hfx.tendsto.comp (Flow.mem_unstableSet.1 hp.1)) (hfy.tendsto.comp (Flow.mem_stableSet.1 hp.2))

/-- **The energy identity for a connecting orbit.** If the orbit of `p` converges to `x` as
`t → -∞` and to `y` as `t → +∞`, `f` is differentiable along it and continuous at `x` and `y`, its
energy `∫ -df(X)(φ_t p) dt` is the drop `f x - f y`. -/
theorem integral_neg_mvfderiv_apply_flow_eq_sub_of_mem_unstableSet_inter_stableSet :
    ∫ t, -mvfderiv 𝓘(ℝ, E) f (hX.flow t p) (X (hX.flow t p)) = f x - f y :=
  hX.integral_neg_mvfderiv_apply_eq_sub_of_tendsto hf (hX.isMIntegralCurve_flow p)
    (hfx.tendsto.comp (Flow.mem_unstableSet.1 hp.1)) (hfy.tendsto.comp (Flow.mem_stableSet.1 hp.2))

end IsAdaptedPseudoGradient

end TauCeti
