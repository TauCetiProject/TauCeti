/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.HalfSpace
public import TauCeti.Geometry.Manifold.ModelTransport.Boundary
public import TauCeti.Geometry.Manifold.PLGroupoid.Map

/-!
# Changing the model space of a PL manifold

Let `Φ : H ≃ₜ H'` be a homeomorphism between two model spaces which is PL in both directions,
for models with corners `I` on `H` and `I'` on `H'`. Conjugating a chart change of the PL groupoid
of `I` by `Φ` gives a chart change of the PL groupoid of `I'`
(`Homeomorph.symm_trans_trans_mem_PLGroupoid`). Consequently, a PL manifold modelled on `I` is a
PL manifold modelled on `I'` for the composite charts `ChartedSpace.comp H' H M`, where `H` carries
the single chart `Φ` (`Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`). This is the PL
counterpart of `Diffeomorph.isManifold_chartedSpaceComp`, and its proof follows that one.

The main instance is the product half-space `{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}`, on which the
realizations of combinatorial manifolds carry their PL atlases, and Mathlib's half-space
`EuclideanHalfSpace (n + 1)`, the model of manifolds with boundary used elsewhere, for instance by
the boundary charts of `TauCeti.boundaryChartedSpace`. The homeomorphism
`TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` between them is linear in the model vector spaces,
so PL in both directions (`TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace`,
`TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace_symm`), and a PL manifold over either model
is a PL manifold over the other. Since it is read as a linear equivalence in the model vector
spaces, it also keeps the manifold boundary
(`TauCeti.modelWithCornersEuclideanHalfSpace_boundary_chartedSpaceComp`).

## Main results

* `Homeomorph.symm_trans_trans_mem_PLGroupoid`: conjugating by a PL homeomorphism of models
  carries the PL groupoid of `I` into the PL groupoid of `I'`.
* `Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`: a PL manifold modelled on `I` is a PL
  manifold modelled on `I'` for the composite charts.
* `TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace` and
  `TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace_symm`: the product half-space and
  `EuclideanHalfSpace (n + 1)` are PL homeomorphic models.
* `TauCeti.modelWithCornersEuclideanHalfSpace_boundary_chartedSpaceComp`: the change between
  these two models keeps the manifold boundary.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1 (PL manifolds).
-/

public section

open Set Function
open scoped Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}

open TauCeti

namespace Homeomorph

variable (Φ : H ≃ₜ H')

/-- Conjugating a map of `H` which is PL on `s` by a PL homeomorphism `Φ` of models gives a map of
`H'` which is PL on `Φ '' s`, written as the preimage under `Φ.symm`. -/
private theorem isPLOn_conj (hΦ : IsPLMap I I' Φ) (hΦ' : IsPLMap I' I Φ.symm) {f : H → H}
    {s : Set H} (hf : IsPLOn (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)) :
    IsPLOn (I' ∘ (Φ ∘ f ∘ Φ.symm) ∘ I'.symm) (I'.symm ⁻¹' (Φ.symm ⁻¹' s) ∩ range I') := by
  have hg := (isPLMap_iff_isPLOn_range.1 hΦ).2
  have hg' := (isPLMap_iff_isPLOn_range.1 hΦ').2
  -- Read in the model vector spaces, the conjugate is `g ∘ (I ∘ f ∘ I.symm) ∘ g'`.
  have hcomp := hg.comp (hf.comp (hg'.mono inter_subset_right)
    fun y (hy : y ∈ I'.symm ⁻¹' (Φ.symm ⁻¹' s) ∩ range I') =>
      ⟨by simpa using hy.1, mem_range_self _⟩) fun _ _ => mem_range_self _
  exact hcomp.congr fun y _ => by simp

/-- **Changing the model of the PL groupoid.** Conjugating a member of the PL groupoid of `I` by a
homeomorphism of models `Φ` which is PL in both directions gives a member of the PL groupoid of
`I'`. -/
theorem symm_trans_trans_mem_PLGroupoid (hΦ : IsPLMap I I' Φ) (hΦ' : IsPLMap I' I Φ.symm)
    {e : OpenPartialHomeomorph H H} (he : e ∈ PLGroupoid I) :
    Φ.toOpenPartialHomeomorph.symm ≫ₕ (e ≫ₕ Φ.toOpenPartialHomeomorph) ∈ PLGroupoid I' := by
  rw [mem_PLGroupoid_iff] at he ⊢
  have hsource : (Φ.toOpenPartialHomeomorph.symm ≫ₕ (e ≫ₕ Φ.toOpenPartialHomeomorph)).source =
      Φ.symm ⁻¹' e.source := by
    ext; simp
  have htarget : (Φ.toOpenPartialHomeomorph.symm ≫ₕ (e ≫ₕ Φ.toOpenPartialHomeomorph)).target =
      Φ.symm ⁻¹' e.target := by
    ext; simp
  rw [hsource, htarget]
  exact ⟨isPLOn_conj Φ hΦ hΦ' he.1, isPLOn_conj Φ hΦ hΦ' he.2⟩

/-- **A PL manifold over one model is a PL manifold over a PL homeomorphic model.** If `Φ : H ≃ₜ H'`
is PL in both directions, a PL manifold modelled on `I` is a PL manifold modelled on `I'` for the
composite charts `ChartedSpace.comp H' H M`, when `H` carries the single chart `Φ`. -/
theorem hasGroupoid_PLGroupoid_chartedSpaceComp (hΦ : IsPLMap I I' Φ) (hΦ' : IsPLMap I' I Φ.symm)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M (PLGroupoid I)] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    HasGroupoid M (PLGroupoid I') := by
  let := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, φ, hφ, rfl⟩ ⟨c', hc', φ', hφ', rfl⟩
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ hφ
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ' hφ'
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc c.symm]
  exact Φ.symm_trans_trans_mem_PLGroupoid hΦ hΦ' (HasGroupoid.compatible hc hc')

end Homeomorph

namespace TauCeti

variable {n : ℕ}

/-- The product half-space `{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}` and `EuclideanHalfSpace (n + 1)`, read
in their model vector spaces, are identified by the continuous linear equivalence
`q ↦ TauCeti.euclideanFinConsEquiv rfl (q.2, q.1)`. -/
theorem modelWithCornersEuclideanHalfSpace_halfSpaceHomeomorphEuclideanHalfSpace
    (q : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}) :
    (𝓡∂ (n + 1)) (halfSpaceHomeomorphEuclideanHalfSpace n q) =
      ((ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans (euclideanFinConsEquiv rfl))
        (modelWithCornersHalfSpace (Fin n → ℝ) q) := by
  simp [coe_halfSpaceHomeomorphEuclideanHalfSpace, Prod.swap]

/-- The homeomorphism of the product half-space onto `EuclideanHalfSpace (n + 1)` is PL. -/
theorem isPLMap_halfSpaceHomeomorphEuclideanHalfSpace :
    IsPLMap (modelWithCornersHalfSpace (Fin n → ℝ)) (𝓡∂ (n + 1))
      (halfSpaceHomeomorphEuclideanHalfSpace n) := by
  let L := (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans (euclideanFinConsEquiv rfl)
  refine isPLMap_iff_isPLOn_range.2 ⟨(halfSpaceHomeomorphEuclideanHalfSpace n).continuous,
    (isPLOn_continuousAffineMap (L : _ →L[ℝ] _).toContinuousAffineMap _).congr ?_⟩
  rintro q ⟨q, rfl⟩
  simp only [comp_apply, ModelWithCorners.left_inv, ContinuousLinearMap.coe_toContinuousAffineMap,
    ContinuousLinearEquiv.coe_coe]
  exact modelWithCornersEuclideanHalfSpace_halfSpaceHomeomorphEuclideanHalfSpace q

/-- The inverse of the homeomorphism of the product half-space onto `EuclideanHalfSpace (n + 1)`
is PL. -/
theorem isPLMap_halfSpaceHomeomorphEuclideanHalfSpace_symm :
    IsPLMap (𝓡∂ (n + 1)) (modelWithCornersHalfSpace (Fin n → ℝ))
      (halfSpaceHomeomorphEuclideanHalfSpace n).symm := by
  let L := (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans (euclideanFinConsEquiv rfl)
  refine isPLMap_iff_isPLOn_range.2 ⟨(halfSpaceHomeomorphEuclideanHalfSpace n).symm.continuous,
    (isPLOn_continuousAffineMap (L.symm : _ →L[ℝ] _).toContinuousAffineMap _).congr ?_⟩
  rintro y ⟨y, rfl⟩
  simp only [comp_apply, ModelWithCorners.left_inv, ContinuousLinearMap.coe_toContinuousAffineMap,
    ContinuousLinearEquiv.coe_coe]
  rw [L.eq_symm_apply, ← modelWithCornersEuclideanHalfSpace_halfSpaceHomeomorphEuclideanHalfSpace,
    Homeomorph.apply_symm_apply]

/-- Moving a charted space over the product half-space to `EuclideanHalfSpace (n + 1)` along
`TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` keeps its manifold boundary. -/
theorem modelWithCornersEuclideanHalfSpace_boundary_chartedSpaceComp (M : Type*)
    [TopologicalSpace M] [ChartedSpace {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} M] :
    letI := (halfSpaceHomeomorphEuclideanHalfSpace n).toOpenPartialHomeomorph.singletonChartedSpace
      (by simp)
    letI := ChartedSpace.comp (EuclideanHalfSpace (n + 1)) {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} M
    (𝓡∂ (n + 1)).boundary M = (modelWithCornersHalfSpace (Fin n → ℝ)).boundary M :=
  (halfSpaceHomeomorphEuclideanHalfSpace n).boundary_chartedSpaceComp
    ((ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans
      (euclideanFinConsEquiv rfl)).toHomeomorph
    modelWithCornersEuclideanHalfSpace_halfSpaceHomeomorphEuclideanHalfSpace M

end TauCeti
