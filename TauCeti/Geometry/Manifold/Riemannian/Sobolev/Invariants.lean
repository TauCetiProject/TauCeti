/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Laplacian
public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Continuous.LpKoopman
public import TauCeti.RepresentationTheory.Continuous.Unitary.Reducing

/-!
# The Laplacian on the invariant functions of a finite group of isometries

Let a group `G` act on a closed Riemannian manifold `M` by smooth maps whose differentials preserve
the metric. Each translation `x ↦ g • x` preserves the Riemannian volume
(`TauCeti.measurePreserving_smul_riemannianVolume`), so `G` acts on `L²(M)` by the unitary
pullback representation `(g · f)(x) = f (g⁻¹ • x)` (`TauCeti.lpKoopman`). Its invariant vectors
form the closed subspace `L²(M)^G` of the classes `f` with `f (g • x) = f x` almost everywhere
(`TauCeti.mem_invariants_lpKoopman_iff`).

The nonnegative Laplacian `Δ⁺ = -div grad` of `M`, realized as a self-adjoint operator on `L²(M)`
(`TauCeti.Manifold.SobolevH1.negLaplacian`), is natural under Riemannian isometries, so every
`g · ` preserves its domain and commutes with it
(`TauCeti.Manifold.SobolevH1.intertwines_negLaplacian_lpKoopman`). When `G` is finite, the
orthogonal projection onto `L²(M)^G` is the average `f ↦ |G|⁻¹ ∑_g g · f` of these unitaries, so
it too preserves the domain and commutes with `Δ⁺`: the invariant subspace **reduces** `Δ⁺`
(`TauCeti.Manifold.SobolevH1.isReducing_negLaplacian_invariants`). The reduced part, the
restriction of `Δ⁺` to the invariant functions, is then self-adjoint
(`TauCeti.Manifold.SobolevH1.isSelfAdjoint_negLaplacian_restrict_invariants`) with compact
resolvent (`TauCeti.Manifold.SobolevH1.hasCompactResolvent_negLaplacian_restrict_invariants`).

For a subgroup `H` acting freely, the invariant subspace `L²(M)^H` is the image of `L²(M / H)`
under the normalized pullback along the quotient map (compare
`IsQuotientCoveringMap.mem_range_normalizedPullbackLp_iff`). Since `L²(M)^H` reduces `Δ⁺`, the
spectral theory of `Δ⁺` splits along `L²(M) = L²(M)^H ⊕ (L²(M)^H)ᗮ`.

## Main results

* `TauCeti.Manifold.SobolevH1.intertwines_negLaplacian_lpKoopman`: each element of `G` acts on
  `L²(M)` by a unitary preserving the domain of `Δ⁺` and commuting with it.
* `TauCeti.Manifold.SobolevH1.isReducing_negLaplacian_invariants`: for finite `G`, the subspace
  `L²(M)^G` of invariant functions reduces `Δ⁺`.
* `TauCeti.Manifold.SobolevH1.isSelfAdjoint_negLaplacian_restrict_invariants`,
  `TauCeti.Manifold.SobolevH1.hasCompactResolvent_negLaplacian_restrict_invariants`: the
  restriction of `Δ⁺` to `L²(M)^G` is self-adjoint with compact resolvent.

## References

* P. Bérard, *Transplantation et isospectralité. I*, Math. Ann. 292 (1992), §II.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265 (2012),
  Section 1.4 (reducing subspaces).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]
  (hG : ∀ (g : G) (x : M) (u w : TangentSpace I x),
    ⟪mfderiv I I (g • ·) x u, mfderiv I I (g • ·) x w⟫_ℝ = ⟪u, w⟫_ℝ)

/-- **Isometries commute with the Laplacian.** For a group acting on a closed manifold by smooth
maps preserving the metric, the unitary `f ↦ f (g⁻¹ • ·)` of `L²(M)` preserves the domain of
`Δ⁺` and commutes with it. -/
theorem intertwines_negLaplacian_lpKoopman (g : G) :
    (negLaplacian I M).Intertwines (negLaplacian I M)
      (lpKoopman ℝ ℝ 2 (riemannianVolume I M)
        (fun k ↦ measurePreserving_smul_riemannianVolume k (hG k)) g) := by
  rw [LinearPMap.intertwines_iff_forall_mem_graph]
  intro p hp
  simpa only [lpKoopman_apply, RiemannianIsometry.coe_constSMul] using
    (mem_graph_negLaplacian_compMeasurePreserving_iff
      (RiemannianIsometry.constSMul g⁻¹ (hG g⁻¹))).2 hp

/-- **Invariant functions reduce the Laplacian.** For a finite group acting on a closed manifold
by smooth maps preserving the metric, the subspace `L²(M)^G` of invariant functions reduces `Δ⁺`:
the orthogonal projection onto it, the average of the action over `G`, preserves the domain of
`Δ⁺` and commutes with `Δ⁺`. -/
theorem isReducing_negLaplacian_invariants [Finite G] :
    (negLaplacian I M).IsReducing
      (lpKoopman ℝ ℝ 2 (riemannianVolume I M)
        (fun g ↦ measurePreserving_smul_riemannianVolume g (hG g))).invariants :=
  isUnitary_lpKoopman.isReducing_invariants fun g x y h ↦
    LinearPMap.intertwines_iff_forall_mem_graph.1 (intertwines_negLaplacian_lpKoopman hG g)
      (x, y) h

/-- **The Laplacian on invariant functions is self-adjoint.** For a finite group acting on a closed
manifold by smooth maps preserving the metric, the restriction of `Δ⁺` to the subspace
`L²(M)^G` of invariant functions is a self-adjoint operator on `L²(M)^G`. -/
theorem isSelfAdjoint_negLaplacian_restrict_invariants [Finite G] :
    IsSelfAdjoint ((negLaplacian I M).restrict
      (isReducing_negLaplacian_invariants hG).isInvariant.apply_mem) :=
  (isReducing_negLaplacian_invariants hG).isSelfAdjoint_restrict isSelfAdjoint_negLaplacian

variable [I.Boundaryless] in
/-- **The Laplacian on invariant functions has compact resolvent.** For a finite group acting on a
closed manifold by smooth maps preserving the metric, the restriction of `Δ⁺` to the subspace
`L²(M)^G` of invariant functions has compact resolvent. Together with self-adjointness
(`TauCeti.Manifold.SobolevH1.isSelfAdjoint_negLaplacian_restrict_invariants`), this is the
hypothesis under which a spectrum consists of isolated eigenvalues of finite multiplicity. -/
theorem hasCompactResolvent_negLaplacian_restrict_invariants [Finite G] :
    ((negLaplacian I M).restrict
      (isReducing_negLaplacian_invariants hG).isInvariant.apply_mem).HasCompactResolvent :=
  (isReducing_negLaplacian_invariants hG).hasCompactResolvent_restrict
    hasCompactResolvent_negLaplacian

end TauCeti.Manifold.SobolevH1
