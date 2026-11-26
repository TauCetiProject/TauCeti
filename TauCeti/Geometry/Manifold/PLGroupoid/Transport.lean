/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PLGroupoid.Basic

/-!
# Changing the model space of a PL manifold

Let `φ : H ≃ₜ H'` be a homeomorphism between two model spaces which is piecewise linear in both
directions when read through models with corners `I` on `H` and `I'` on `H'`. Conjugation by `φ`
carries the PL groupoid of `I` into that of `I'`
(`Homeomorph.symm_trans_trans_mem_PLGroupoid`). Hence a PL manifold modelled on `H` is a PL
manifold modelled on `H'` for the atlas of its charts followed by `φ`, Mathlib's composite charted
space `ChartedSpace.comp` (`Homeomorph.hasGroupoid_PLGroupoid_comp`).

This is how a PL structure built in one coordinate model is read in another. For instance, the
half-space `{q : E × ℝ | 0 ≤ q.2}` of `TauCeti.modelWithCornersHalfSpace` and Mathlib's
`EuclideanHalfSpace`, or the coordinate space `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)`, are
related by linear isomorphisms which restrict to homeomorphisms of the model spaces.

## Main results

* `Homeomorph.symm_trans_trans_mem_PLGroupoid`: conjugating a PL coordinate change by a
  homeomorphism of model spaces which is PL in both directions gives a PL coordinate change.
* `Homeomorph.hasGroupoid_PLGroupoid_comp`: a PL atlas followed by such a homeomorphism is a PL
  atlas for the new model.
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
composite atlas whose charts are its charts followed by `φ`. -/
theorem _root_.Homeomorph.hasGroupoid_PLGroupoid_comp (φ : H ≃ₜ H')
    (hφ : IsPLOn (I' ∘ φ ∘ I.symm) (range I))
    (hφ' : IsPLOn (I ∘ φ.symm ∘ I'.symm) (range I'))
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M (PLGroupoid I)] :
    letI : ChartedSpace H' H :=
      φ.toOpenPartialHomeomorph.singletonChartedSpace φ.toOpenPartialHomeomorph_source
    letI : ChartedSpace H' M := ChartedSpace.comp H' H M
    HasGroupoid M (PLGroupoid I') := by
  let : ChartedSpace H' H :=
    φ.toOpenPartialHomeomorph.singletonChartedSpace φ.toOpenPartialHomeomorph_source
  let : ChartedSpace H' M := ChartedSpace.comp H' H M
  refine ⟨?_⟩
  rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
  rw [OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ f hf,
    OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ f' hf',
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc e.symm, ← Homeomorph.symm_toOpenPartialHomeomorph]
  exact φ.symm_trans_trans_mem_PLGroupoid hφ hφ' (HasGroupoid.compatible he he')

end TauCeti
