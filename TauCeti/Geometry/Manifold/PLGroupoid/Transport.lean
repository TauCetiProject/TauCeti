/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.ProductHalfSpace.Model
public import TauCeti.Geometry.Manifold.ModelTransport.Homeomorph
public import TauCeti.Geometry.Manifold.PLGroupoid.Basic

/-!
# Changing the model space of a PL manifold

Let `φ : H ≃ₜ H'` be a homeomorphism between two model spaces which is piecewise linear in both
directions when read through models with corners `I` on `H` and `I'` on `H'`. Conjugation by `φ`
carries the PL groupoid of `I` into that of `I'`
(`Homeomorph.symm_trans_trans_mem_PLGroupoid`). Hence a PL manifold modelled on `H` is a PL
manifold modelled on `H'` for the atlas of its charts followed by `φ`, the charted space
`Homeomorph.chartedSpaceComp` (`Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`).

This is how a PL structure built in one coordinate model is read in another. For instance, the
homeomorphism `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` of the half-space
`{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}` of `TauCeti.modelWithCornersHalfSpace` with Mathlib's
`EuclideanHalfSpace (n + 1)`, the restriction of the linear isomorphism `(v, t) ↦ (t, v)`, is PL in
both directions.

## Main results

* `Homeomorph.symm_trans_trans_mem_PLGroupoid`: conjugating a PL coordinate change by a
  homeomorphism of model spaces which is PL in both directions gives a PL coordinate change.
* `Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp`: a PL atlas followed by such a
  homeomorphism is a PL atlas for the new model.
* `TauCeti.isPLOn_halfSpaceHomeomorphEuclideanHalfSpace` and
  `TauCeti.isPLOn_halfSpaceHomeomorphEuclideanHalfSpace_symm`: the homeomorphism of the product
  half-space with the Euclidean half-space is PL in both directions.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}

/-- Read in the models, the conjugate of a coordinate change `e` by `φ` is the reading of `e`
between the readings of `φ.symm` and of `φ`, so it is PL when these three are. -/
private theorem isPLOn_symm_trans_trans (φ : H ≃ₜ H')
    (hφ : IsPLOn (I' ∘ φ ∘ I.symm) (range I))
    (hφ' : IsPLOn (I ∘ φ.symm ∘ I'.symm) (range I')) {e : OpenPartialHomeomorph H H}
    (he : IsPLOn (I ∘ e ∘ I.symm) (I.symm ⁻¹' e.source ∩ range I)) :
    IsPLOn (I' ∘ (φ.symm.toOpenPartialHomeomorph ≫ₕ e ≫ₕ φ.toOpenPartialHomeomorph) ∘ I'.symm)
      (I'.symm ⁻¹' (φ.symm.toOpenPartialHomeomorph ≫ₕ e ≫ₕ φ.toOpenPartialHomeomorph).source ∩
        range I') := by
  refine (hφ.comp (he.comp (hφ'.mono inter_subset_right) ?_) ?_).congr fun y _ => ?_
  · rintro y ⟨hy, -⟩
    simp only [mfld_simps] at hy ⊢
    exact hy
  · exact fun _ _ => mem_range_self _
  · simp only [mfld_simps]

/-- Conjugating a PL coordinate change of the model `I` by a homeomorphism `φ : H ≃ₜ H'` which is
PL in both directions, read through `I` and `I'`, gives a PL coordinate change of the model `I'`. -/
theorem _root_.Homeomorph.symm_trans_trans_mem_PLGroupoid (φ : H ≃ₜ H')
    (hφ : IsPLOn (I' ∘ φ ∘ I.symm) (range I))
    (hφ' : IsPLOn (I ∘ φ.symm ∘ I'.symm) (range I')) {e : OpenPartialHomeomorph H H}
    (he : e ∈ PLGroupoid I) :
    φ.symm.toOpenPartialHomeomorph ≫ₕ e ≫ₕ φ.toOpenPartialHomeomorph ∈ PLGroupoid I' := by
  rw [mem_PLGroupoid_iff] at he ⊢
  refine ⟨isPLOn_symm_trans_trans φ hφ hφ' he.1, ?_⟩
  -- The inverse of the conjugate of `e` is the conjugate of the inverse of `e`.
  have hsymm : (φ.symm.toOpenPartialHomeomorph ≫ₕ e ≫ₕ φ.toOpenPartialHomeomorph).symm =
      φ.symm.toOpenPartialHomeomorph ≫ₕ e.symm ≫ₕ φ.toOpenPartialHomeomorph := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, Homeomorph.symm_toOpenPartialHomeomorph,
      OpenPartialHomeomorph.symm_symm]
  rw [← OpenPartialHomeomorph.symm_source, hsymm]
  exact isPLOn_symm_trans_trans φ hφ hφ' he.2

/-- **Changing the model of a PL manifold.** If `φ : H ≃ₜ H'` is PL in both directions, read
through `I` and `I'`, then a PL manifold modelled on `H` is a PL manifold modelled on `H'`, for the
composite atlas `φ.chartedSpaceComp M` whose charts are its charts followed by `φ`. -/
theorem _root_.Homeomorph.hasGroupoid_PLGroupoid_chartedSpaceComp (φ : H ≃ₜ H')
    (hφ : IsPLOn (I' ∘ φ ∘ I.symm) (range I))
    (hφ' : IsPLOn (I ∘ φ.symm ∘ I'.symm) (range I'))
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M (PLGroupoid I)] :
    letI := φ.chartedSpaceComp M
    HasGroupoid M (PLGroupoid I') := by
  let := φ.chartedSpaceComp M
  refine ⟨?_⟩
  rw [φ.atlas_chartedSpaceComp M]
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc, Homeomorph.symm_toOpenPartialHomeomorph] using
    φ.symm_trans_trans_mem_PLGroupoid hφ hφ' (HasGroupoid.compatible hc hc')

/-- Read in the models, `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` is PL. -/
theorem isPLOn_halfSpaceHomeomorphEuclideanHalfSpace (n : ℕ) :
    IsPLOn ((𝓡∂ (n + 1)) ∘ halfSpaceHomeomorphEuclideanHalfSpace n ∘
      (modelWithCornersHalfSpace (Fin n → ℝ)).symm) (range (modelWithCornersHalfSpace _)) := by
  refine (isPLOn_continuousAffineMap
    (halfSpaceLinearEquiv n : _ →L[ℝ] _).toContinuousAffineMap _).congr ?_
  rintro q hq
  rw [range_modelWithCornersHalfSpace] at hq
  simp [coe_modelWithCornersHalfSpace_symm_apply _ hq]

/-- Read in the models, the inverse of `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` is PL. -/
theorem isPLOn_halfSpaceHomeomorphEuclideanHalfSpace_symm (n : ℕ) :
    IsPLOn (modelWithCornersHalfSpace (Fin n → ℝ) ∘
      (halfSpaceHomeomorphEuclideanHalfSpace n).symm ∘ (𝓡∂ (n + 1)).symm)
      (range (𝓡∂ (n + 1))) := by
  refine (isPLOn_continuousAffineMap
    ((halfSpaceLinearEquiv n).symm : _ →L[ℝ] _).toContinuousAffineMap _).congr ?_
  rintro y hy
  rw [range_modelWithCornersEuclideanHalfSpace] at hy
  simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy]

end TauCeti
