/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Boundary.HalfSpaceChart
public import TauCeti.Geometry.Manifold.ContMDiff.ExtendTrans

/-!
# Smooth embeddings of regular domains

Suppose a subset of a boundaryless manifold carries half-space charts obtained by restricting
smooth ambient charts along a sign condition. Its inclusion into the ambient manifold is a
smooth embedding, including at boundary points. This is the regular-domain property needed to
regard closed tubular discs as smoothly embedded manifolds with boundary.

The proof uses the local normal form for immersions, rather than a differential criterion
requiring a boundaryless source. In matching ambient and half-space charts the inclusion is a
linear isomorphism restricted to the half-space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 5.47
  (regular domains).
-/

public section

open Function Set Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  {m : ℕ∞ω} [IsManifold I m M] [FiniteDimensional ℝ E] {n : ℕ} {s : Set M}
  [ChartedSpace (EuclideanHalfSpace (n + 1)) s] [IsManifold (𝓡∂ (n + 1)) m s]

/-- A regular domain whose charts are half-space restrictions of smooth ambient charts is
smoothly embedded in the ambient manifold of the same dimension. No compactness or closedness
assumption is needed. -/
theorem isSmoothEmbedding_subtypeVal_of_forall_chartAt_eq_halfSpaceChart
    (hn : Module.finrank ℝ E = n + 1)
    (h : ∀ x : s,
      ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
        (he : ∀ w ∈ e.source, w ∈ s ↔ 0 ≤ e w 0) (y : s),
        e.IsExtendTransChart I m ∧
          chartAt (EuclideanHalfSpace (n + 1)) x = e.halfSpaceChart he y) :
    IsSmoothEmbedding (𝓡∂ (n + 1)) I m (Subtype.val : s → M) := by
  refine ⟨IsImmersionOfComplement.isImmersion (F := Fin 0 → ℝ) fun x ↦ ?_,
    Topology.IsEmbedding.subtypeVal⟩
  obtain ⟨e, he, y, hc, hchart⟩ := h x
  let L : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin, hn])
  -- Read the ambient chart back in H through a linear, rather than nonlinear, identification.
  let d : OpenPartialHomeomorph M H :=
    e.trans (L.toHomeomorph.trans I.toHomeomorph.symm).toOpenPartialHomeomorph
  have hdsource : d.source = e.source :=
    e.trans_continuousLinearEquiv_trans_modelSymm_source L
  have hdapply (w : M) : I (d w) = L (e w) :=
    e.trans_continuousLinearEquiv_trans_modelSymm_apply L w
  have hx : (x : M) ∈ e.source := by
    have hx' := mem_chart_source (EuclideanHalfSpace (n + 1)) x
    rwa [hchart, OpenPartialHomeomorph.halfSpaceChart_source] at hx'
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ _ _).trans L)
    (chartAt (EuclideanHalfSpace (n + 1)) x) d (mem_chart_source _ x)
    (by rwa [hdsource]) (IsManifold.chart_mem_maximalAtlas _)
    (hc.trans_continuousLinearEquiv_trans_modelSymm_mem_maximalAtlas L) ?_ ?_
  · rw [hchart, OpenPartialHomeomorph.halfSpaceChart_source, hdsource]
  · intro v hv
    have hv' : v ∈ range (𝓡∂ (n + 1)) :=
      (chartAt (EuclideanHalfSpace (n + 1)) x).extend_target_subset_range hv
    -- The half-space model is the subtype inclusion into its Euclidean vector space.
    have hmodel : ((𝓡∂ (n + 1)).symm v).1 = v :=
      (𝓡∂ (n + 1)).right_inv hv'
    rw [OpenPartialHomeomorph.extend_target, hchart] at hv
    have hz : (𝓡∂ (n + 1)).symm v ∈ (e.halfSpaceChart he y).target := hv.1
    have hev : v ∈ e.target := by
      rw [OpenPartialHomeomorph.halfSpaceChart_target, mem_preimage] at hz
      simpa only [modelWithCornersEuclideanHalfSpace_toFun, hmodel] using hz
    simp only [comp_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodUnique_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm]
    rw [hchart, OpenPartialHomeomorph.coe_halfSpaceChart_symm_apply he y
      (by rwa [hmodel]), hmodel, hdapply, e.right_inv hev]

end TauCeti
