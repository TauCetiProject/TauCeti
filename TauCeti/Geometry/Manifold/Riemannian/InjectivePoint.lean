/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.InjectivePoint
public import TauCeti.Topology.MetricSpace.Antilipschitz
import TauCeti.Analysis.Calculus.FDeriv.Antilipschitz
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# Injective points in Riemannian manifolds are quantitatively injective

Let `f : M → N` be a map between Riemannian manifolds, both carrying their Riemannian distances. A
point `x` is an injective point of `f` (`TauCeti.IsInjectivePoint`) when the manifold derivative of
`f` at `x` is injective and `x` is the only point with image `f x`. This file shows that, for a
continuous map differentiable at `x`, from a compact boundaryless source modelled on a
finite-dimensional space, this qualitative condition is equivalent to the quantitative one

`dist x y ≤ K * dist (f x) (f y)` for every `y` in `M`,

that is, `f` is antilipschitz from `x` (`TauCeti.AntilipschitzWithFrom`), for some constant `K`.

* **Near `x`.** If the derivative of `f` at `x` is injective, then
  `dist x y ≤ K * dist (f x) (f y)` for `y` near `x`
  (`TauCeti.exists_eventually_dist_le_mul_dist_of_injective_mfderiv`). In the extended charts at
  `x` and `f x` this is the corresponding estimate for the coordinate expression of `f`, whose
  derivative is the manifold derivative
  (`HasFDerivWithinAt.exists_eventually_dist_le_mul_dist`), and both charts are bi-Lipschitz at
  their centres for the Riemannian distances
  (`TauCeti.Manifold.exists_eventually_dist_extChartAt_le_mul_dist`,
  `TauCeti.Manifold.exists_eventually_dist_le_mul_dist_extChartAt`). The source may have boundary
  here. Conversely, on a boundaryless source, such a bound near `x` at a point of
  differentiability makes the derivative injective
  (`MDifferentiableAt.injective_mfderiv_of_eventually_dist_le_mul_dist`), by
  `HasFDerivAt.antilipschitzWith_of_eventually_dist_le_mul_dist`.
* **On a compact source.** If moreover `x` is alone in its fibre and `f` is continuous, the bound
  near `x` extends to all of a compact source
  (`Continuous.exists_antilipschitzWithFrom_of_eventually`). Hence, for a continuous map
  differentiable at `x`, `x` is an injective point exactly when `f` is antilipschitz from `x` with
  some constant (`Continuous.isInjectivePoint_iff_exists_antilipschitzWithFrom`), and a
  differentiable map is somewhere injective exactly when it is antilipschitz from some point with
  some constant (`Continuous.isSomewhereInjective_iff_exists_antilipschitzWithFrom`).

For a fixed constant `K` the pairs of a continuous map and a point from which it is antilipschitz
with constant `K` form a closed set (`TauCeti.isClosed_setOfPred_antilipschitzWithFrom`). In the
transversality theory of pseudoholomorphic spheres, these sets intersected with a bound `K` on the
derivatives are the pieces of the exhaustion of the simple curves, the somewhere injective ones.
The theorems above say that, for continuous differentiable maps from a compact boundaryless
Riemannian source modelled on a finite-dimensional space, every somewhere injective map satisfies
the first condition for some `K`, and only those do.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012, §2.5 (simple curves and injective
  points) and §3.2 (the exhaustion of the simple curves in the proof of transversality).
-/

public section

open Bundle Filter Function Manifold Set
open scoped Manifold NNReal Topology

namespace TauCeti

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}

section Local

variable {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [PseudoMetricSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {x : M}

/-- **A lower distance bound near a point with injective derivative.** For a map between Riemannian
manifolds, the source modelled on a finite-dimensional space, whose manifold derivative at `x` is
injective, `dist x y ≤ K * dist (f x) (f y)` for every `y` near `x`, for some constant `K`. The
source may have boundary. -/
theorem exists_eventually_dist_le_mul_dist_of_injective_mfderiv [FiniteDimensional ℝ E]
    (hinj : Injective (mfderiv I J f x)) :
    ∃ K : ℝ≥0, ∀ᶠ y in 𝓝 x, dist x y ≤ K * dist (f x) (f y) := by
  have hf : MDifferentiableAt I J f x := mdifferentiableAt_of_mfderiv_injective hinj
  -- In the extended charts, the derivative of the coordinate expression of `f` within `range I`
  -- is `mfderiv I J f x` read in the model spaces. It is injective, so the coordinate expression
  -- satisfies the bound near `extChartAt I x x`. The casts in `f'` are exactly those in Mathlib's
  -- definition of `HasMFDerivAt`, so `hf.hasMFDerivAt.2` has derivative `f'` syntactically. They
  -- are needed: the tangent spaces carry the Riemannian norms, while the coordinate estimate
  -- requires `f'` to be antilipschitz for the model-space norms.
  let f' : E →L[ℝ] E' := (tangentSpaceCastModel J (f x) : TangentSpace J (f x) →L[ℝ] E') ∘L
    mfderiv I J f x ∘L ((tangentSpaceCastModel I x).symm : E →L[ℝ] TangentSpace I x)
  have hf' : Injective f' := by
    simpa only [f', ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp] using hinj
  obtain ⟨A, -, hA⟩ := (LinearMap.injective_iff_antilipschitz f'.toLinearMap).1 hf'
  obtain ⟨K₁, hK₁⟩ := hf.hasMFDerivAt.2.exists_eventually_dist_le_mul_dist hA
  -- Both extended charts are bi-Lipschitz at their centres.
  obtain ⟨K₀, hK₀⟩ := Manifold.exists_eventually_dist_le_mul_dist_extChartAt (I := I) x
  obtain ⟨K₂, hK₂⟩ := Manifold.exists_eventually_dist_extChartAt_le_mul_dist (I := J) (f x)
  have hφ : Tendsto (extChartAt I x) (𝓝 x) (𝓝[range I] (extChartAt I x x)) := by
    rw [← map_extChartAt_nhds]
    exact tendsto_map
  refine ⟨K₀ * K₁ * K₂, ?_⟩
  filter_upwards [hK₀, hφ.eventually hK₁, extChartAt_source_mem_nhds (I := I) x,
    hf.continuousAt.eventually hK₂] with y h₀ h₁ hy h₂
  rw [writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x),
    writtenInExtChartAt_apply_extChartAt hy] at h₁
  calc dist x y ≤ K₀ * dist (extChartAt I x x) (extChartAt I x y) := h₀
    _ ≤ K₀ * (K₁ * dist (extChartAt J (f x) (f x)) (extChartAt J (f x) (f y))) := by gcongr
    _ ≤ K₀ * (K₁ * (K₂ * dist (f x) (f y))) := by gcongr
    _ = (K₀ * K₁ * K₂ : ℝ≥0) * dist (f x) (f y) := by push_cast; ring

/-- **A lower distance bound near a point makes the derivative injective.** For a map between
Riemannian manifolds, the source without boundary, differentiable at `x`, if
`dist x y ≤ K * dist (f x) (f y)` for every `y` near `x`, then the manifold derivative of `f` at `x`
is injective. -/
theorem _root_.MDifferentiableAt.injective_mfderiv_of_eventually_dist_le_mul_dist [I.Boundaryless]
    {K : ℝ≥0} (hf : MDifferentiableAt I J f x) (hK : ∀ᶠ y in 𝓝 x, dist x y ≤ K * dist (f x) (f y)) :
    Injective (mfderiv I J f x) := by
  -- Without boundary, the coordinate expression of `f` has derivative `mfderiv I J f x` at
  -- `extChartAt I x x`.
  have hg := hf.hasMFDerivAt.2
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at hg
  -- Both extended charts are bi-Lipschitz at their centres.
  obtain ⟨K₀, hK₀⟩ := Manifold.exists_eventually_dist_extChartAt_le_mul_dist (I := I) x
  obtain ⟨K₂, hK₂⟩ := Manifold.exists_eventually_dist_le_mul_dist_extChartAt (I := J) (f x)
  -- So the coordinate expression satisfies a lower distance bound near `extChartAt I x x`.
  have hφ : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    have := (continuousAt_extChartAt_symm (I := I) x).tendsto
    rwa [(extChartAt I x).left_inv (mem_extChartAt_source x)] at this
  have hinj := (hg.antilipschitzWith_of_eventually_dist_le_mul_dist (C := K₀ * K * K₂) ?_).injective
  · simpa only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp] using hinj
  filter_upwards [extChartAt_target_mem_nhds (I := I) x, hφ.eventually hK₀, hφ.eventually hK,
    hφ.eventually (hf.continuousAt.eventually hK₂)] with a ha h₀ h₁ h₂
  set y := (extChartAt I x).symm a
  have hy : y ∈ (extChartAt I x).source := (extChartAt I x).map_target ha
  have hay : extChartAt I x y = a := (extChartAt I x).right_inv ha
  rw [hay] at h₀
  rw [← hay, writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x),
    writtenInExtChartAt_apply_extChartAt hy, hay]
  calc dist (extChartAt I x x) a ≤ K₀ * dist x y := h₀
    _ ≤ K₀ * (K * dist (f x) (f y)) := by gcongr
    _ ≤ K₀ * (K * (K₂ * dist (extChartAt J (f x) (f x)) (extChartAt J (f x) (f y)))) := by
      gcongr
    _ = (K₀ * K * K₂ : ℝ≥0) * dist (extChartAt J (f x) (f x)) (extChartAt J (f x) (f y)) := by
      push_cast; ring

end Local

section Compact

variable {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [IsContinuousRiemannianBundle E' (fun y : N ↦ TangentSpace J y)]
  [FiniteDimensional ℝ E] [I.Boundaryless] {f : M → N}

/-- **Injective points are quantitatively injective.** Let `f : M → N` be a continuous map between
Riemannian manifolds, the source compact, without boundary and modelled on a finite-dimensional
space, and let `f` be differentiable at `x`. Then `x` is an injective point of `f` if and only if
`f` is antilipschitz from `x` with some constant `K`: `dist x y ≤ K * dist (f x) (f y)` for every
`y` in `M`. -/
theorem _root_.Continuous.isInjectivePoint_iff_exists_antilipschitzWithFrom {x : M}
    (hf : Continuous f) (hfx : MDifferentiableAt I J f x) :
    IsInjectivePoint I J f x ↔ ∃ K, AntilipschitzWithFrom K f x := by
  refine ⟨fun h ↦ ?_, fun ⟨K, hK⟩ ↦ ⟨?_, fun y hy ↦ hK.eq_of_apply_eq hy⟩⟩
  · obtain ⟨K, hK⟩ := exists_eventually_dist_le_mul_dist_of_injective_mfderiv h.injective_mfderiv
    exact hf.exists_antilipschitzWithFrom_of_eventually h.eq_of_apply_eq hK
  · exact hfx.injective_mfderiv_of_eventually_dist_le_mul_dist
      (.of_forall (antilipschitzWithFrom_iff_le_mul_dist.1 hK))

/-- **Somewhere injective maps are quantitatively injective somewhere.** A continuous
differentiable map between Riemannian manifolds, the source compact, without boundary and modelled
on a finite-dimensional space, is somewhere injective if and only if it is antilipschitz from some
point with some constant. -/
theorem _root_.Continuous.isSomewhereInjective_iff_exists_antilipschitzWithFrom
    (hf : Continuous f) (hdf : MDifferentiable I J f) :
    IsSomewhereInjective I J f ↔ ∃ K x, AntilipschitzWithFrom K f x := by
  simp only [isSomewhereInjective_iff, hf.isInjectivePoint_iff_exists_antilipschitzWithFrom (hdf _)]
  exact exists_comm

end Compact

end TauCeti
