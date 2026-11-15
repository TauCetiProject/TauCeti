/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.WithMetric
public import TauCeti.Topology.Covering.LocalSection
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Topology.Covering.Clopen

/-!
# Local isometries from complete manifolds are coverings

Let `f : M → N` be a local Riemannian isometry, where every geodesic of `M` is defined for all
time. Then `f` is a covering map; if moreover `M` is nonempty and `N` is connected, `f` is
surjective. Completeness of `M` cannot be dropped: the restriction of the universal covering
`ℝ → S¹` to `ℝ ∖ {0}` is a surjective local isometry which is not a covering map.

The proof uses the exponential map. Since `M` is geodesically complete, `f` intertwines the
exponential maps, `f ∘ exp_e = exp_{f e} ∘ df_e`. Every point `y` of `N` has a uniformly normal
neighbourhood `W`: there is `r > 0` such that for every `q ∈ W` the tangent ball of radius `r`
at `q` is a normal domain whose exponential image contains `W`, with logarithm `log_q`. For every
point `e` with `f e ∈ W`, the map `z ↦ exp_e (df_e⁻¹ (log_{f e} z))` is then a continuous section
of `f` over `W` through `e`. Since `f` is a local diffeomorphism, local sections through every
point make it a covering map (`IsCoveringMap.of_isLocalHomeomorph_of_forall_exists_section`).
No metric and no completeness are needed on `N`.

The same conclusion holds for a local diffeomorphism `f` from a complete Riemannian manifold
which does not decrease the length of tangent vectors, `|v| ≤ |df_x v|`. The pullback `f^* g_N`
of the metric of `N` dominates the metric of `M`, so it is geodesically complete
(`TauCeti.WithMetric.isGeodesicallyCompleteAt_of_sq_norm_le`), and `f` is a local isometry for
it. This is the form of the criterion used in the Cartan–Hadamard theorem, for the exponential
map of a manifold of nonpositive curvature.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.isCoveringMap`: a local Riemannian isometry from a
  geodesically complete manifold is a covering map.
* `TauCeti.IsLocalRiemannianIsometry.surjective`: it is surjective when the source is nonempty
  and the target connected.
* `TauCeti.IsLocalRiemannianIsometry.isCoveringMap_of_completeSpace` and
  `TauCeti.IsLocalRiemannianIsometry.surjective_of_completeSpace`: the same for a source which is
  complete for its Riemannian distance.
* `TauCeti.Manifold.isCoveringMap_of_norm_le_norm_mfderiv`: **a local diffeomorphism from a
  nonempty complete Riemannian manifold to a connected one which does not decrease lengths is a
  surjective covering map.**

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §3, Lemma 3.3 and
  Proposition 3.4.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 6.23 (local isometries from complete manifolds are coverings) and Problem 6-20.
-/

public section

open Bundle Function Manifold Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

namespace IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

section Topological

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {f : M → N}

omit [FiniteDimensional ℝ F] [J.Boundaryless] [T2Space N] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
/-- A local Riemannian isometry from a manifold without boundary is a local homeomorphism. -/
theorem isLocalHomeomorph (hf : IsLocalRiemannianIsometry I J f) : IsLocalHomeomorph f :=
  (isLocalDiffeomorph_of_mfderiv_eq hf.contMDiff (n := ∞) (by simp)
    fun x ↦ hf.isInvertible_mfderiv x).isLocalHomeomorph

/-- **A local isometry from a geodesically complete manifold is a covering map.** If every
geodesic of `M` is defined for all time, a local Riemannian isometry `f : M → N` is a covering
map. -/
theorem isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hM : ∀ x : M, IsGeodesicallyCompleteAt I M x) : IsCoveringMap f := by
  have : LocallyConnectedSpace H' := J.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace N := ChartedSpace.locallyConnectedSpace H' N
  refine IsCoveringMap.of_isLocallyInjective_of_forall_exists_section
    hf.isLocalHomeomorph.continuous hf.isLocalHomeomorph.isLocallyInjective
    (T2Space.isSeparatedMap f) fun y ↦ ?_
  obtain ⟨r, -, W, hW, hWn⟩ := exists_mem_nhds_forall_isNormalDomain_ball (I := J) (M := N) y
  refine ⟨W, hW, fun e he ↦ ?_⟩
  obtain ⟨hn, hWe⟩ := hWn (f e) he
  obtain ⟨A, hA⟩ := hf.isInvertible_mfderiv e
  have hexp : Continuous (riemannianExp I M e) := by
    rw [← continuousOn_univ, ← expDomain_eq_univ_iff.2 (hM e)]
    exact continuousOn_riemannianExp e
  refine ⟨fun z ↦ riemannianExp I M e (A.symm (riemannianLog J N (f e) (Metric.ball 0 r) z)),
    hexp.comp_continuousOn (A.symm.continuous.comp_continuousOn
      (hn.continuousOn_riemannianLog.mono hWe)), fun z hz ↦ ?_, ?_⟩
  · rw [← hf.riemannianExp_mfderiv (hM e), ← hA, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, Manifold.riemannianExp_riemannianLog (hWe hz)]
  · simp only [hn.riemannianLog_self, map_zero, riemannianExp_zero]

/-- A local Riemannian isometry from a nonempty geodesically complete manifold to a connected
manifold is surjective. -/
theorem surjective [Nonempty M] [PreconnectedSpace N] (hf : IsLocalRiemannianIsometry I J f)
    (hM : ∀ x : M, IsGeodesicallyCompleteAt I M x) : Surjective f :=
  (hf.isCoveringMap hM).surjective

end Topological

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] {f : M → N}

/-- **A local isometry from a complete Riemannian manifold is a covering map.** -/
theorem isCoveringMap_of_completeSpace (hf : IsLocalRiemannianIsometry I J f) :
    IsCoveringMap f :=
  hf.isCoveringMap isGeodesicallyCompleteAt_of_completeSpace

/-- A local isometry from a nonempty complete Riemannian manifold to a connected Riemannian
manifold is surjective. -/
theorem surjective_of_completeSpace [Nonempty M] [PreconnectedSpace N]
    (hf : IsLocalRiemannianIsometry I J f) : Surjective f :=
  hf.isCoveringMap_of_completeSpace.surjective

end Metric

end IsLocalRiemannianIsometry

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] [Nonempty M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun x : N ↦ TangentSpace J x)]
  [IsContMDiffRiemannianBundle J ∞ E' (fun x : N ↦ TangentSpace J x)] [ConnectedSpace N]

/-- **Covering criterion for length-nondecreasing local diffeomorphisms.** Let `f : M → N` be a
smooth local diffeomorphism from a nonempty Riemannian manifold `M`, complete for its Riemannian
distance, to a connected Riemannian manifold `N`. If `f` does not decrease the length of tangent
vectors, `|v| ≤ |df_x v|`, then `f` is a surjective covering map. -/
theorem isCoveringMap_of_norm_le_norm_mfderiv {f : M → N} (hf : ContMDiff I J ∞ f)
    (hloc : IsLocalDiffeomorph I J ∞ f)
    (hexp : ∀ x (v : TangentSpace I x), ‖v‖ ≤ ‖mfderiv I J f x v‖) :
    Surjective f ∧ IsCoveringMap f := by
  have hinv (x : M) : (mfderiv I J f x).IsInvertible := (hloc x).isInvertible_mfderiv (by simp)
  have hf' : ContMDiff I J (∞ + 1) f := by simpa using hf
  set g := (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := J) (n := ∞)
    (F := E') (V := fun y : N ↦ TangentSpace J y)).pullback f hf' fun x ↦ (hinv x).injective
  have hg (x : M) (v : TangentSpace I x) : ‖v‖ ^ 2 ≤ g.inner x v v := by
    rw [ContMDiffRiemannianMetric.pullback_inner,
      ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
    change ‖v‖ ^ 2 ≤ inner ℝ (mfderiv I J f x v) (mfderiv I J f x v)
    rw [real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hexp x v) 2
  have hF : IsLocalRiemannianIsometry I J (f ∘ WithMetric.ofWithMetric : WithMetric g → N) :=
    { contMDiff := hf.comp WithMetric.contMDiff_ofWithMetric
      isInvertible_mfderiv := fun x ↦ by
        rw [WithMetric.mfderiv_comp_ofWithMetric]
        refine (hinv x.ofWithMetric).comp ?_
        rw [WithMetric.mfderiv_ofWithMetric]
        exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
      inner_mfderiv := fun x v w ↦ by
        rw [WithMetric.inner_def, WithMetric.mfderiv_comp_ofWithMetric,
          ContMDiffRiemannianMetric.pullback_inner,
          ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
        rfl }
  have hfF : f = (f ∘ WithMetric.ofWithMetric) ∘ (WithMetric.homeomorph g).symm := by
    ext x
    simp
  have hcov : IsCoveringMap f := hfF ▸
    (hF.isCoveringMap (fun p ↦ WithMetric.isGeodesicallyCompleteAt_of_sq_norm_le_mul
      (C := 1) (by norm_num) (by simpa using hg) p)).comp_homeomorph
      (WithMetric.homeomorph g).symm
  exact ⟨hcov.surjective, hcov⟩

end Manifold

end TauCeti
