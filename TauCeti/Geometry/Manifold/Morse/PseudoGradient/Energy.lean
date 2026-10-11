/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow
public import TauCeti.Geometry.Manifold.IntegralCurve.Energy

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

* `IsAdaptedPseudoGradient.integrable_mvfderiv_apply_flow_of_mem_unstableSet_inter_stableSet`
  and `integral_neg_mvfderiv_apply_flow_eq_sub_of_mem_unstableSet_inter_stableSet` (in the same
  namespace): along an orbit of the flow connecting `x` to `y`, the rate of decrease of `f` is
  integrable and the energy is `f x - f y`. They specialize the energy identity for integral
  curves, `TauCeti.IsMIntegralCurve.integral_neg_mvfderiv_apply_eq_sub_of_tendsto`, to the flow.

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

variable [CompactSpace M] [T2Space M] (hX : IsAdaptedPseudoGradient f X) {x y p : M}
  (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (hX.flow t p)) (hfx : ContinuousAt f x)
  (hfy : ContinuousAt f y) (hp : p ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y)
include hX hf hfx hfy hp

/-- **The rate of decrease of `f` along a connecting orbit is integrable.** If the orbit of `p`
converges to `x` as `t → -∞` and to `y` as `t → +∞`, `f` is differentiable along it and continuous
at `x` and `y`, then `t ↦ df(X)(φ_t p)` is integrable on the real line. -/
theorem integrable_mvfderiv_apply_flow_of_mem_unstableSet_inter_stableSet :
    Integrable fun t ↦ mvfderiv 𝓘(ℝ, E) f (hX.flow t p) (X (hX.flow t p)) :=
  IsMIntegralCurve.integrable_mvfderiv_apply_of_tendsto (hX.isMIntegralCurve_flow p) hf
    (fun _ ↦ hX.mvfderiv_apply_nonpos _) (hfx.tendsto.comp (Flow.mem_unstableSet.1 hp.1))
    (hfy.tendsto.comp (Flow.mem_stableSet.1 hp.2))

/-- **The energy identity for a connecting orbit.** If the orbit of `p` converges to `x` as
`t → -∞` and to `y` as `t → +∞`, `f` is differentiable along it and continuous at `x` and `y`, its
energy `∫ -df(X)(φ_t p) dt` is the drop `f x - f y`. -/
theorem integral_neg_mvfderiv_apply_flow_eq_sub_of_mem_unstableSet_inter_stableSet :
    ∫ t, -mvfderiv 𝓘(ℝ, E) f (hX.flow t p) (X (hX.flow t p)) = f x - f y :=
  IsMIntegralCurve.integral_neg_mvfderiv_apply_eq_sub_of_tendsto (hX.isMIntegralCurve_flow p) hf
    (fun _ ↦ hX.mvfderiv_apply_nonpos _) (hfx.tendsto.comp (Flow.mem_unstableSet.1 hp.1))
    (hfy.tendsto.comp (Flow.mem_stableSet.1 hp.2))

end IsAdaptedPseudoGradient

end TauCeti
