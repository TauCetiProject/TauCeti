/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Dynamics.Flow.Stable
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

/-!
# The flow of an adapted pseudo-gradient

Let `f` be a Morse function on a compact boundaryless manifold and `X` a pseudo-gradient field
adapted to `f`. The flow of `X` decreases `f` along every non-constant orbit, its rest points are
the critical points of `f`, and every orbit converges to a critical point both forward and backward
in time. Consequently the manifold is the disjoint union of the stable sets `W^s(x)` of the
critical points `x`, and also of their unstable sets `W^u(x)`.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.flow`: the flow of an adapted pseudo-gradient on a compact
  manifold.
* `TauCeti.IsAdaptedPseudoGradient.contMDiff_flow_uncurry` and
  `TauCeti.IsAdaptedPseudoGradient.flowDiffeomorph`: the flow is smooth in time and space, and its
  time-`t` map is a diffeomorphism.
* `TauCeti.IsAdaptedPseudoGradient.hasDerivAt_comp_flow`: the derivative of `f` along an orbit is
  `df(X)`.
* `TauCeti.IsAdaptedPseudoGradient.flow_apply_of_mfderiv_eq_zero`: critical points are rest points.
* `TauCeti.IsAdaptedPseudoGradient.exists_tendsto_atTop` and
  `TauCeti.IsAdaptedPseudoGradient.exists_tendsto_atBot`: every orbit converges to a critical point
  forward, respectively backward, in time.
* `TauCeti.IsAdaptedPseudoGradient.iUnion_stableSet` and
  `TauCeti.IsAdaptedPseudoGradient.iUnion_unstableSet`: the stable sets of the critical points
  cover the manifold, and so do their unstable sets. Together with
  `Flow.disjoint_stableSet` and `Flow.disjoint_unstableSet`, these are the
  partitions `M = ⊔ₓ W^s(x) = ⊔ₓ W^u(x)` over the critical points.
* `TauCeti.IsAdaptedPseudoGradient.stableSet_eq_compl_of_critical_eq_or_eq` and
  `TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_compl_of_critical_eq_or_eq`: with at most two
  critical points, one of which has a trivial stable (respectively unstable) set, the stable
  (respectively unstable) set of the other is the rest of the manifold.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6 and Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-- An adapted pseudo-gradient on a compact boundaryless manifold is complete. -/
theorem maximalIntegralCurveInterval_eq_univ (hX : IsAdaptedPseudoGradient f X) (x : M) :
    maximalIntegralCurveInterval X x = univ :=
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  maximalIntegralCurveInterval_eq_univ_of_compactSpace (hX.contMDiff.of_le (by simp))

/-- The flow of an adapted pseudo-gradient on a compact boundaryless manifold. -/
noncomputable def flow (hX : IsAdaptedPseudoGradient f X) : Flow ℝ M :=
  globalFlow X (hX.contMDiff.of_le (by simp)) hX.maximalIntegralCurveInterval_eq_univ

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- The flow at time `t` is the maximal integral curve of the pseudo-gradient at time `t`. -/
theorem flow_apply (t : ℝ) (y : M) : hX.flow t y = maximalIntegralCurve X y t := by
  rw [flow, globalFlow_apply]

/-- The orbits of the flow are integral curves of the pseudo-gradient. -/
theorem isMIntegralCurve_flow (y : M) : IsMIntegralCurve (fun t ↦ hX.flow t y) X :=
  isMIntegralCurve_globalFlow _ hX.maximalIntegralCurveInterval_eq_univ y

/-- The flow of an adapted pseudo-gradient is smooth in time and space. -/
theorem contMDiff_flow_uncurry :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ fun p : ℝ × M ↦ hX.flow p.1 p.2 :=
  contMDiff_globalFlow_uncurry hX.maximalIntegralCurveInterval_eq_univ (n := ⊤) le_top
    hX.contMDiff

/-- For a fixed time `t`, the time-`t` map of the flow is smooth. -/
theorem contMDiff_flow_apply (t : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hX.flow t) :=
  contMDiff_globalFlow_apply hX.maximalIntegralCurveInterval_eq_univ (n := ⊤) le_top
    hX.contMDiff t

omit hX in
/-- The time-`t` map of the flow of an adapted pseudo-gradient, as a diffeomorphism. Its inverse
is the time-`(-t)` map. -/
noncomputable def flowDiffeomorph (hX : IsAdaptedPseudoGradient f X) (t : ℝ) :
    M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  globalFlowDiffeomorph hX.maximalIntegralCurveInterval_eq_univ (n := ⊤) le_top hX.contMDiff t

/-- The diffeomorphism `flowDiffeomorph t` is the time-`t` map of the flow. -/
@[simp]
theorem flowDiffeomorph_apply (t : ℝ) (y : M) : hX.flowDiffeomorph t y = hX.flow t y := by
  rw [flowDiffeomorph, globalFlowDiffeomorph_apply, hX.flow_apply, globalFlow_apply]

/-- The inverse of `flowDiffeomorph t` is the time-`(-t)` map of the flow. -/
@[simp]
theorem flowDiffeomorph_symm_apply (t : ℝ) (y : M) :
    (hX.flowDiffeomorph t).symm y = hX.flow (-t) y := by
  rw [flowDiffeomorph, globalFlowDiffeomorph_symm_apply, hX.flow_apply, globalFlow_apply]

/-- The derivative of `f` along an orbit of the flow is `df(X)`. -/
theorem hasDerivAt_comp_flow {y : M} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (hX.flow t y)) :
    HasDerivAt (fun s ↦ f (hX.flow s y)) (mvfderiv 𝓘(ℝ, E) f (hX.flow t y) (X (hX.flow t y))) t :=
  Manifold.hasDerivAt_comp_curve (γ := fun s ↦ hX.flow s y) hf (hX.isMIntegralCurve_flow y t)

/-- `f` is antitone along every orbit of the flow. -/
theorem antitone_flow (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (y : M) :
    Antitone fun t ↦ f (hX.flow t y) :=
  hX.antitone_comp (fun _ ↦ hf _) (hX.isMIntegralCurve_flow y)

/-- Critical points of `f` are rest points of the flow. -/
theorem flow_apply_of_mfderiv_eq_zero {x : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (t : ℝ) :
    hX.flow t x = x :=
  globalFlow_eq_of_isMIntegralCurve _ hX.maximalIntegralCurveInterval_eq_univ
    (isMIntegralCurve_const (hX.eq_zero_of_mfderiv_eq_zero hx)) t

/-- A point along whose orbit `f` is constant is a critical point of `f`. -/
theorem mfderiv_eq_zero_of_forall_eq {z : M} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f z)
    (hz : ∀ t, f (hX.flow t z) = f z) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 := by
  by_contra hcrit
  have hd := hX.hasDerivAt_comp_flow (t := 0) (by rwa [Flow.map_zero_apply])
  have horbit : (fun s ↦ f (hX.flow s z)) = fun _ ↦ f z := funext hz
  rw [horbit, Flow.map_zero_apply] at hd
  exact (hX.mvfderiv_apply_lt_zero z hcrit).ne (hd.unique (hasDerivAt_const _ _))

/-- **Every orbit converges forward in time to a critical point.** -/
theorem exists_tendsto_atTop (hf : IsMorse 𝓘(ℝ, E) f) (y : M) :
    ∃ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧ Tendsto (fun t ↦ hX.flow t y) atTop (𝓝 x) :=
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  Flow.exists_tendsto_atTop_of_antitone hX.flow hf.contMDiff.continuous (hX.antitone_flow hdf)
    hf.finite_setOf_mfderiv_eq_zero (fun z hz ↦ hX.mfderiv_eq_zero_of_forall_eq (hdf z) hz) y

/-- **Every orbit converges backward in time to a critical point.** -/
theorem exists_tendsto_atBot (hf : IsMorse 𝓘(ℝ, E) f) (y : M) :
    ∃ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧ Tendsto (fun t ↦ hX.flow t y) atBot (𝓝 x) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  obtain ⟨x, hx, htend⟩ := Flow.exists_tendsto_atTop_of_antitone hX.flow.reverse
    hf.contMDiff.continuous.neg
    (fun y ↦ fun s t hst ↦ by
      simp only [Flow.reverse_apply, Pi.neg_apply]
      exact neg_le_neg (hX.antitone_flow hdf y (neg_le_neg hst)))
    hf.finite_setOf_mfderiv_eq_zero
    (fun z hz ↦ hX.mfderiv_eq_zero_of_forall_eq (hdf z) fun t ↦ by
      have := hz (-t)
      simp only [Flow.reverse_apply, neg_neg, Pi.neg_apply] at this
      exact neg_inj.1 this) y
  refine ⟨x, hx, ?_⟩
  have := htend.comp tendsto_neg_atBot_atTop
  simpa [comp_def, Flow.reverse_apply] using this

/-- **The stable sets of the critical points cover the manifold.** -/
theorem iUnion_stableSet (hf : IsMorse 𝓘(ℝ, E) f) :
    ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.stableSet x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  obtain ⟨x, hx, htend⟩ := hX.exists_tendsto_atTop hf y
  exact mem_iUnion₂.2 ⟨x, hx, Flow.mem_stableSet.2 htend⟩

/-- **The unstable sets of the critical points cover the manifold.** -/
theorem iUnion_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) :
    ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.unstableSet x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  obtain ⟨x, hx, htend⟩ := hX.exists_tendsto_atBot hf y
  exact mem_iUnion₂.2 ⟨x, hx, Flow.mem_unstableSet.2 htend⟩

/-- **Two critical points.** If every critical point of a Morse function is one of two distinct
points `a` and `b`, and the stable set of `a` is `{a}`, then the stable set of `b` is everything
else. -/
theorem stableSet_eq_compl_of_critical_eq_or_eq (hf : IsMorse 𝓘(ℝ, E) f) {a b : M}
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y = a ∨ y = b) (hab : a ≠ b)
    (ha : hX.flow.stableSet a = {a}) : hX.flow.stableSet b = {a}ᶜ := by
  ext p
  refine ⟨fun hp hpa ↦ ?_, fun hpa ↦ ?_⟩
  · rw [mem_singleton_iff] at hpa
    subst hpa
    exact disjoint_left.1 (Flow.disjoint_stableSet hab) (ha ▸ rfl) hp
  · obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.1 ((hX.iUnion_stableSet hf).symm ▸ mem_univ p :
      p ∈ ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.stableSet x)
    rcases hcrit c hc with rfl | rfl
    · exact absurd (ha ▸ hpc) hpa
    · exact hpc

/-- **Two critical points.** If every critical point of a Morse function is one of two distinct
points `a` and `b`, and the unstable set of `b` is `{b}`, then the unstable set of `a` is everything
else. -/
theorem unstableSet_eq_compl_of_critical_eq_or_eq (hf : IsMorse 𝓘(ℝ, E) f) {a b : M}
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y = a ∨ y = b) (hab : a ≠ b)
    (hb : hX.flow.unstableSet b = {b}) : hX.flow.unstableSet a = {b}ᶜ := by
  ext p
  refine ⟨fun hp hpb ↦ ?_, fun hpb ↦ ?_⟩
  · rw [mem_singleton_iff] at hpb
    subst hpb
    exact disjoint_left.1 (Flow.disjoint_unstableSet hab) hp (hb ▸ rfl)
  · obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.1 ((hX.iUnion_unstableSet hf).symm ▸ mem_univ p :
      p ∈ ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.unstableSet x)
    rcases hcrit c hc with rfl | rfl
    · exact hpc
    · exact absurd (hb ▸ hpc) hpb

end IsAdaptedPseudoGradient

end TauCeti
