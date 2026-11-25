/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ChartData.ChangeAtlas
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic

/-!
# Independence of the Sobolev space of sections over a surface with boundary from the atlas

Let `M` be a `C¹` manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a surface with boundary, let `V → M` be a real vector bundle with finite-dimensional
model fibre `F`, and let `A`, `A'` be two finite bundle atlases. The Sobolev spaces `W^{k,p}(V)` of
`TauCeti.BorderedSobolevSection A p k` and `TauCeti.BorderedSobolevSection A' p k` consist of
tuples of chartwise components of sections, on the interiors in `ℂ` of the images of the charts of
`A` and of `A'`. This file shows that, whenever every section with `W^{k,p}` components in the
charts of `A` also has `W^{k,p}` components in the charts of `A'`
(`TauCeti.BorderedSobolevSection.TransfersTo A A' p k`), sending an element to the element of the
other atlas with the same section is a continuous linear map
(`TauCeti.BorderedSobolevSection.changeAtlas`). When the property holds in both directions the
two spaces are isomorphic Banach spaces (`TauCeti.BorderedSobolevSection.atlasEquiv`), so their
norms are equivalent (`TauCeti.BorderedSobolevSection.exists_norm_changeAtlas_le`).

The construction is the change of chart data `TauCeti.SectionChartData.changeAtlas` of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Equiv`, which also gives the boundaryless
`TauCeti.SobolevSection.changeAtlas`. What it needs here is that the chart data of `A'` are read off
from those of `A` (`TauCeti.FiniteBundleAtlas.readsFrom_halfSectionChartData`): on the part of the
interior of the image of a chart of `A'` lying over the domain of a chart of `A`, the reading of a
section is the coordinate change of the bundle applied to its reading in the chart of `A`
(`TauCeti.FiniteBundleAtlas.halfCoord_eq_coordChangeL_halfCoord`), at the chart transition, which
keeps interior points interior and carries null sets to null sets
(`TauCeti.FiniteBundleAtlas.ae_restrict_halfImage_chart_symm`).

## Main definitions

* `TauCeti.BorderedSobolevSection.TransfersTo A A' p k`: every section with `W^{k,p}` components
  in the charts of `A` has `W^{k,p}` components in the charts of `A'`.
* `TauCeti.BorderedSobolevSection.changeAtlas`: the continuous linear map between the Sobolev
  spaces of two atlases sending an element to the element with the same section.
* `TauCeti.BorderedSobolevSection.atlasEquiv`: the isomorphism of Banach spaces between them.

## Main results

* `TauCeti.FiniteBundleAtlas.readsFrom_halfSectionChartData`: the chart data of one atlas are
  read off from those of any other.
* `TauCeti.BorderedSobolevSection.chartValueL_changeAtlas_ae`: the chart data of
  `changeAtlas h w` are the readings in `A'` of any section of `w`.
* `TauCeti.BorderedSobolevSection.exists_norm_changeAtlas_le`: when sections transfer in both
  directions the norms of the two atlases are equivalent.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Appendix C.1.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped Manifold Topology ENNReal

namespace TauCeti

section Sobolev

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A A' : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

omit [FiniteDimensional ℝ F] in
/-- The chart data of a finite bundle atlas over a base with boundary are read off from those of
any other: on the part of the interior of the image of chart `i'` of `A'` lying over the domain of
chart `i` of `A`, the reading in chart `i'` is the coordinate change of the bundle applied to the
reading in chart `i` at the chart transition, which carries null sets to null sets. -/
theorem FiniteBundleAtlas.readsFrom_halfSectionChartData
    [IsManifold closedUpperHalfPlaneModel 1 M] :
    A.halfSectionChartData.ReadsFrom A'.halfSectionChartData volume :=
  .intro (fun i i' ↦ {y | (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i})
    (fun i i' y ↦ A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)))
    (fun i i' y ↦ (A.triv i).coordChangeL ℝ (A'.triv i')
      ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)))
    (fun _ ↦ ae_of_all _ fun _ ↦ A.exists_mem_dom _)
    (fun _ i' _ h ↦ A.ae_restrict_halfImage_chart_symm A' i' h)
    fun i i' s ↦ by
      filter_upwards [ae_restrict_mem (A'.halfImage i').isOpen.measurableSet] with y hyU hdom
      rw [A'.halfSectionChartData_coord_of_mem s hyU,
        A.halfSectionChartData_coord_of_mem s (A.coe_chart_mem_halfImage A' hyU hdom)]
      exact A.halfCoord_eq_coordChangeL_halfCoord A' s
        (A'.dom_subset_baseSet i' (A'.symm_mem_dom (A'.mem_halfImage.1 hyU).1)) hdom

namespace BorderedSobolevSection

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Transfer of Sobolev sections between atlases.** Every section whose chart data in the charts
of `A` are those of an element of `W^{k,p}(V)` for `A` also has chart data in the charts of `A'`
that are those of an element of `W^{k,p}(V)` for `A'`
(`TauCeti.BorderedSobolevSection.transfersTo_iff`). -/
abbrev TransfersTo : Prop :=
  A.halfSectionChartData.TransfersTo A'.halfSectionChartData volume p k

variable {A A' p k}

/-- Unfolding `TauCeti.BorderedSobolevSection.TransfersTo` in terms of the readings
`A.halfCoord i s`, for establishing and using the transfer property outside this file. -/
theorem transfersTo_iff : TransfersTo A A' p k ↔
    ∀ (w : BorderedSobolevSection A p k) (s : ∀ x, V x),
      (∀ i, A.halfSectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) →
        ∃ w' : BorderedSobolevSection A' p k,
          ∀ i', A'.halfSectionChartData.chartValueL volume p k i' w'
            =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s :=
  SectionChartData.transfersTo_iff.trans <| forall₂_congr fun _ _ ↦
    imp_congr (forall_congr' fun _ ↦ A.ae_eq_halfSectionChartData_coord_iff)
      (exists_congr fun _ ↦ forall_congr' fun _ ↦ A'.ae_eq_halfSectionChartData_coord_iff)

theorem transfersTo_refl : TransfersTo A A p k :=
  SectionChartData.transfersTo_refl

theorem TransfersTo.trans {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h : TransfersTo A A' p k) (h' : TransfersTo A' A'' p k) : TransfersTo A A'' p k :=
  SectionChartData.TransfersTo.trans h h'

variable [IsManifold closedUpperHalfPlaneModel 1 M]

/-- **Change of atlas.** Given the transfer property `h` from `A` to `A'`, the continuous linear map
from `W^{k,p}(V)` for `A` to `W^{k,p}(V)` for `A'` sending an element to the element whose chart
data are the readings of the same section
(`TauCeti.BorderedSobolevSection.chartValueL_changeAtlas_ae`).
It is `TauCeti.SectionChartData.changeAtlas` for the chart data of the two atlases. -/
def changeAtlas (h : TransfersTo A A' p k) :
    BorderedSobolevSection A p k →L[ℝ] BorderedSobolevSection A' p k :=
  SectionChartData.changeAtlas (A.readsFrom_halfSectionChartData A') h

/-- The chart data of `changeAtlas h w` are the readings in the charts of `A'` of any section whose
readings in the charts of `A` are the chart data of `w`. -/
theorem chartValueL_changeAtlas_ae (h : TransfersTo A A' p k) {w : BorderedSobolevSection A p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i' : Fin A'.n) :
    A'.halfSectionChartData.chartValueL volume p k i' (changeAtlas h w)
      =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s :=
  A'.ae_eq_halfSectionChartData_coord_iff.1 <| SectionChartData.chartValueL_changeAtlas_ae _ h
    (fun i ↦ A.ae_eq_halfSectionChartData_coord_iff.2 (hs i)) i'

/-- **Identification of the change of atlas.** An element `w'` for `A'` whose chart data are the
readings in the charts of `A'` of a section of `w` is the image of `w`. -/
theorem changeAtlas_eq_of_ae_eq_halfCoord (h : TransfersTo A A' p k)
    {w : BorderedSobolevSection A p k} {w' : BorderedSobolevSection A' p k} {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (hs' : ∀ i', A'.halfSectionChartData.chartValueL volume p k i' w'
      =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s) :
    changeAtlas h w = w' :=
  eq_of_ae_eq_halfCoord (chartValueL_changeAtlas_ae h hs) hs'

theorem changeAtlas_refl_apply (w : BorderedSobolevSection A p k) :
    changeAtlas (transfersTo_refl (A := A) (p := p) (k := k)) w = w :=
  SectionChartData.changeAtlas_refl_apply w

@[simp]
theorem changeAtlas_refl :
    changeAtlas (transfersTo_refl (A := A) (p := p) (k := k)) = ContinuousLinearMap.id ℝ _ :=
  SectionChartData.changeAtlas_refl

@[simp]
theorem changeAtlas_changeAtlas {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h : TransfersTo A A' p k) (h' : TransfersTo A' A'' p k) (w : BorderedSobolevSection A p k) :
    changeAtlas h' (changeAtlas h w) = changeAtlas (h.trans h') w :=
  SectionChartData.changeAtlas_changeAtlas _ _ _ h h' w

@[simp]
theorem changeAtlas_comp {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h : TransfersTo A A' p k) (h' : TransfersTo A' A'' p k) :
    (changeAtlas h').comp (changeAtlas h) = changeAtlas (h.trans h') :=
  SectionChartData.changeAtlas_comp _ _ _ h h'

/-- The change of atlas is injective: two sections with the same readings almost everywhere in the
charts of `A'` have the same readings almost everywhere in the charts of `A`. -/
theorem changeAtlas_injective (h : TransfersTo A A' p k) :
    Function.Injective (changeAtlas h) :=
  SectionChartData.changeAtlas_injective _ (A'.readsFrom_halfSectionChartData A) h

/-- The change of atlas commutes with forgetting the highest derivative. -/
theorem lowerOrderL_changeAtlas (h : TransfersTo A A' p (k + 1)) (h₀ : TransfersTo A A' p k)
    (w : BorderedSobolevSection A p (k + 1)) :
    A'.halfSectionChartData.lowerOrderL volume p k (changeAtlas h w) =
      changeAtlas h₀ (A.halfSectionChartData.lowerOrderL volume p k w) :=
  SectionChartData.lowerOrderL_changeAtlas _ h h₀ w

/-- The change of atlas sends the Sobolev section of a `Cᵏ` section for `A` to the Sobolev section
of the same `Cᵏ` section for `A'`. -/
@[simp]
theorem changeAtlas_ofContMDiffSection [IsManifold closedUpperHalfPlaneModel k M]
    [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel] (h : TransfersTo A A' p k)
    (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    changeAtlas h (ofContMDiffSection A p k s) = ofContMDiffSection A' p k s :=
  changeAtlas_eq_of_ae_eq_halfCoord h (chartValueL_ofContMDiffSection_ae A p k s)
    (chartValueL_ofContMDiffSection_ae A' p k s)

/-- **Independence of the atlas.** If sections transfer between `A` and `A'` in both directions,
the Sobolev spaces of sections for the two atlases are isomorphic Banach spaces, an element
corresponding to the element with the same section. In particular their norms are equivalent.
It is `TauCeti.SectionChartData.atlasEquiv` for the chart data of the two atlases. -/
def atlasEquiv (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k) :
    BorderedSobolevSection A p k ≃L[ℝ] BorderedSobolevSection A' p k :=
  SectionChartData.atlasEquiv (A.readsFrom_halfSectionChartData A')
    (A'.readsFrom_halfSectionChartData A) h h'

@[simp]
theorem toContinuousLinearMap_atlasEquiv (h : TransfersTo A A' p k)
    (h' : TransfersTo A' A p k) :
    (atlasEquiv h h' : BorderedSobolevSection A p k →L[ℝ] BorderedSobolevSection A' p k) =
      changeAtlas h :=
  SectionChartData.toContinuousLinearMap_atlasEquiv _ _ h h'

@[simp]
theorem atlasEquiv_apply (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k)
    (w : BorderedSobolevSection A p k) : atlasEquiv h h' w = changeAtlas h w :=
  SectionChartData.atlasEquiv_apply _ _ h h' w

theorem atlasEquiv_symm_apply (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k)
    (w : BorderedSobolevSection A' p k) : (atlasEquiv h h').symm w = changeAtlas h' w :=
  SectionChartData.atlasEquiv_symm_apply _ _ h h' w

@[simp]
theorem atlasEquiv_symm (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k) :
    (atlasEquiv h h').symm = atlasEquiv h' h :=
  SectionChartData.atlasEquiv_symm _ _ h h'

@[simp]
theorem atlasEquiv_refl :
    atlasEquiv (transfersTo_refl (A := A) (p := p) (k := k)) transfersTo_refl =
      ContinuousLinearEquiv.refl ℝ _ :=
  SectionChartData.atlasEquiv_refl

@[simp]
theorem atlasEquiv_trans {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h₁ : TransfersTo A A' p k) (h₁' : TransfersTo A' A p k) (h₂ : TransfersTo A' A'' p k)
    (h₂' : TransfersTo A'' A' p k) :
    (atlasEquiv h₁ h₁').trans (atlasEquiv h₂ h₂') = atlasEquiv (h₁.trans h₂) (h₂'.trans h₁') :=
  SectionChartData.atlasEquiv_trans _ _ _ _ _ _ h₁ h₁' h₂ h₂'

/-- **Equivalence of norms.** If sections transfer between `A` and `A'` in both directions, the
norms of the Sobolev spaces of sections for the two atlases are equivalent: there is a positive
constant `C` bounding the norm of each element by `C` times the norm of the element of the other
atlas with the same section. -/
theorem exists_norm_changeAtlas_le (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : BorderedSobolevSection A p k,
      ‖changeAtlas h w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖changeAtlas h w‖ :=
  SectionChartData.exists_norm_changeAtlas_le _ (A'.readsFrom_halfSectionChartData A) h h'

end BorderedSobolevSection

end Sobolev

end TauCeti
