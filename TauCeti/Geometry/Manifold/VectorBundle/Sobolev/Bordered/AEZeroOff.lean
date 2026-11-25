/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.ExtensionByZero
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.SMul
import TauCeti.MeasureTheory.Function.Lp.Closed

/-!
# Bordered Sobolev sections vanishing off a set, and extension by zero from one chart

Let `M` be a manifold modelled on the closed upper half-plane, let `V → M` be a real vector bundle
with finite-dimensional model fibre `F`, and let `A` be a finite bundle atlas. This file is the
analogue for bases with boundary of `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff`.

For a set `L ⊆ M`, `TauCeti.BorderedSobolevSection.aeZeroOff A p k L` is the closed subspace of
`W^{k,p}(V)` of the elements whose chart data vanish almost everywhere over the complement of `L`.
For `L` inside the domain of chart `i`, such an element is determined by its chart-`i` components
(`TauCeti.BorderedSobolevSection.chartRestrictL_injective`), which lie in the closed subspace
`TauCeti.BorderedSobolevSection.chartAeZeroOff A p k i L` of chart-`i` tuples vanishing almost
everywhere off `L`. For closed `L` and a `Cⁿ` bundle with `1 ≤ n` and `k ≤ n`, every such tuple
arises in this way (`TauCeti.BorderedSobolevSection.chartRestrictL_surjective`, from the extension
by zero `TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord_of_eq_zero`). So the
chart-`i` components form a linear equivalence
(`TauCeti.BorderedSobolevSection.chartRestrictEquiv`). Its inverse followed by the inclusion is the
extension by zero `TauCeti.BorderedSobolevSection.extendByZeroL`, which is continuous by the closed
graph theorem.

## Main definitions

* `TauCeti.BorderedSobolevSection.aeZeroOff`: the elements of `W^{k,p}(V)` vanishing almost
  everywhere off a set `L ⊆ M`.
* `TauCeti.BorderedSobolevSection.chartAeZeroOff`: the tuples of chart-`i` Sobolev functions
  vanishing almost everywhere off `L`.
* `TauCeti.BorderedSobolevSection.chartRestrictL`: the chart-`i` components of an element
  vanishing off `L`.
* `TauCeti.BorderedSobolevSection.chartRestrictEquiv`,
  `TauCeti.BorderedSobolevSection.extendByZeroL`: for closed `L` inside the domain of chart `i`,
  the chart-`i` components as a linear equivalence, and its inverse, extension by zero, as a
  continuous linear map.

## Main results

* `TauCeti.BorderedSobolevSection.isClosed_aeZeroOff`,
  `TauCeti.BorderedSobolevSection.isClosed_chartAeZeroOff`: both subspaces are closed.
* `TauCeti.BorderedSobolevSection.mem_aeZeroOff_of_ae_eq_halfCoord`: an element given by a section
  vanishing off `L` vanishes off `L`.
* `TauCeti.BorderedSobolevSection.contMDiffSMulL_mem_aeZeroOff`: `φ • w` vanishes off
  `tsupport φ`.
* `TauCeti.BorderedSobolevSection.chartRestrictL_injective`,
  `TauCeti.BorderedSobolevSection.chartRestrictL_surjective`: the chart-`i` components of the
  elements vanishing off a closed subset `L` of the domain of chart `i` are a bijection onto the
  chart-`i` tuples vanishing off `L`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

namespace TauCeti

open FiniteBundleAtlas

namespace BorderedSobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The elements of `W^{k,p}(V)` vanishing almost everywhere off a set `L ⊆ M`: in every chart
`i` the chart data vanish almost everywhere at the points of `A.halfImage i` lying over the
complement of `L`. For closed `L` these are the elements supported in `L`. -/
def aeZeroOff (L : Set M) : Submodule ℝ (BorderedSobolevSection A p k) where
  carrier := {w | ∀ i, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
    (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L →
      A.halfSectionChartData.chartValueL volume p k i w z = 0}
  add_mem' {w w'} hw hw' i := by
    filter_upwards [hw i, hw' i, Lp.coeFn_add (A.halfSectionChartData.chartValueL volume p k i w)
      (A.halfSectionChartData.chartValueL volume p k i w')] with y hy hy' hadd hL
    rw [Submodule.coe_add, map_add, hadd, Pi.add_apply, hy hL, hy' hL, add_zero]
  zero_mem' i := by
    filter_upwards [Lp.coeFn_zero F p (volume.restrict (A.halfImage i : Set ℂ))] with y hy _
    rw [ZeroMemClass.coe_zero, map_zero]
    exact hy
  smul_mem' c w hw i := by
    filter_upwards [hw i, Lp.coeFn_smul c (A.halfSectionChartData.chartValueL volume p k i w)]
      with y hy hsmul hL
    rw [Submodule.coe_smul, map_smul, hsmul, Pi.smul_apply, hy hL, smul_zero]

variable {A p k} in
theorem mem_aeZeroOff {L : Set M} {w : BorderedSobolevSection A p k} :
    w ∈ aeZeroOff A p k L ↔ ∀ i, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L →
        A.halfSectionChartData.chartValueL volume p k i w z = 0 :=
  Iff.rfl

variable {A p k} in
theorem aeZeroOff_mono {L L' : Set M} (h : L ⊆ L') :
    aeZeroOff A p k L ≤ aeZeroOff A p k L' := fun _ hw i ↦ by
  filter_upwards [hw i] with y hy hL using hy fun h' ↦ hL (h h')

/-- The elements of `W^{k,p}(V)` vanishing off `L` form a closed subspace. -/
theorem isClosed_aeZeroOff (L : Set M) :
    IsClosed (aeZeroOff A p k L : Set (BorderedSobolevSection A p k)) := by
  have : (aeZeroOff A p k L : Set (BorderedSobolevSection A p k)) = ⋂ i : Fin A.n,
      (fun w : BorderedSobolevSection A p k ↦ A.halfSectionChartData.chartValueL volume p k i w) ⁻¹'
        {f | ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
          (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → f z = 0} := by
    ext w
    simp only [SetLike.mem_coe, mem_aeZeroOff, mem_iInter, mem_preimage, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((A.halfSectionChartData.chartValueL volume p k i).continuous.comp continuous_subtypeVal)

instance aeZeroOff.instCompleteSpace [IsManifold closedUpperHalfPlaneModel 1 M] (L : Set M) :
    CompleteSpace (aeZeroOff A p k L) :=
  (isClosed_aeZeroOff A p k L).completeSpace_coe

/-- The tuples of chart-`i` Sobolev functions, one for each vector of the basis
`Module.finBasis ℝ F`, vanishing almost everywhere at the points of `A.halfImage i` lying over the
complement of `L ⊆ M`. -/
def chartAeZeroOff (i : Fin A.n) (L : Set M) :
    Submodule ℝ (Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) where
  carrier := {g | ∀ j, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
    (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → Wkp.value k (g j) z = 0}
  add_mem' {g g'} hg hg' j := by
    filter_upwards [hg j, hg' j, Lp.coeFn_add (Wkp.value k (g j)) (Wkp.value k (g' j))]
      with y hy hy' hadd hL
    rw [Pi.add_apply, Wkp.value_add, hadd, Pi.add_apply, hy hL, hy' hL, add_zero]
  zero_mem' j := by
    filter_upwards [Lp.coeFn_zero ℝ p (volume.restrict (A.halfImage i : Set ℂ))] with y hy _
    rw [Pi.zero_apply, ← Wkp.valueL_apply, map_zero, hy, Pi.zero_apply]
  smul_mem' c g hg j := by
    filter_upwards [hg j, Lp.coeFn_smul c (Wkp.value k (g j))] with y hy hsmul hL
    rw [Pi.smul_apply, Wkp.value_smul, hsmul, Pi.smul_apply, hy hL, smul_zero]

omit [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
variable {A p k} in
theorem mem_chartAeZeroOff {i : Fin A.n} {L : Set M}
    {g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k} :
    g ∈ chartAeZeroOff A p k i L ↔ ∀ j, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → Wkp.value k (g j) z = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- The chart-`i` tuples vanishing off `L` form a closed subspace. -/
theorem isClosed_chartAeZeroOff (i : Fin A.n) (L : Set M) :
    IsClosed (chartAeZeroOff A p k i L :
      Set (Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k)) := by
  have : (chartAeZeroOff A p k i L :
      Set (Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k)) =
      ⋂ j, (fun g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k ↦ Wkp.valueL k (g j)) ⁻¹'
        {f | ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
          (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → f z = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_chartAeZeroOff, mem_iInter, mem_preimage, mem_ofPred_eq,
      Wkp.valueL_apply]
  rw [this]
  exact isClosed_iInter fun j ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((Wkp.valueL k).continuous.comp (continuous_apply j))

omit [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
instance chartAeZeroOff.instCompleteSpace (i : Fin A.n) (L : Set M) :
    CompleteSpace (chartAeZeroOff A p k i L) :=
  (isClosed_chartAeZeroOff A p k i L).completeSpace_coe

variable {A p k} in
/-- The chart-`i` components of an element vanishing off `L` vanish off `L`. -/
theorem mem_chartAeZeroOff_of_mem_aeZeroOff {L : Set M} {w : BorderedSobolevSection A p k}
    (hw : w ∈ aeZeroOff A p k L) (i : Fin A.n) :
    (w : A.halfSectionChartData.SobolevData volume p k) i ∈ chartAeZeroOff A p k i L :=
  fun j ↦ by
    filter_upwards [hw i, A.halfSectionChartData.chartValueL_apply_ae volume p k i w]
      with y hy happ hL
    have h := congrArg (fun v ↦ (finBasis ℝ F).repr v j) ((happ.symm.trans (hy hL)))
    rwa [(finBasis ℝ F).repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h

/-- The chart-`i` components of the elements of `W^{k,p}(V)` vanishing off `L`, as a continuous
linear map into the chart-`i` tuples vanishing off `L`. -/
def chartRestrictL (i : Fin A.n) (L : Set M) :
    aeZeroOff A p k L →L[ℝ] chartAeZeroOff A p k i L :=
  ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun i : Fin A.n ↦ Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) i).comp
    ((A.halfSectionChartData.sobolevSections volume p k).subtypeL.comp
      (aeZeroOff A p k L).subtypeL)).codRestrict _
    fun w ↦ mem_chartAeZeroOff_of_mem_aeZeroOff w.property i

@[simp]
theorem coe_chartRestrictL_apply (i : Fin A.n) (L : Set M) (w : aeZeroOff A p k L) :
    (chartRestrictL A p k i L w : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) =
      ((w : BorderedSobolevSection A p k) : A.halfSectionChartData.SobolevData volume p k) i :=
  (rfl)

variable {A p k}

/-- If the chart data of `w` are the readings of a section `s`, then the chart-`i` components of
`w` are the coordinates of `A.halfCoord i s` in the basis `Module.finBasis ℝ F`. -/
theorem value_ae_eq_repr_halfCoord {w : BorderedSobolevSection A p k} {s : ∀ x, V x}
    {i : Fin A.n}
    (hs : A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((w : A.halfSectionChartData.SobolevData volume p k) i j) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).repr (A.halfCoord i s z) j := by
  filter_upwards [SectionChartData.value_ae_eq_repr_coord
      (hs.trans (A.halfSectionChartData_coord_ae_eq i s).symm) j,
    ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z h hz
  rw [h, A.halfSectionChartData_coord_of_mem _ hz]

/-- An element whose chart data are the readings of a section vanishing off `L` vanishes almost
everywhere off `L`. -/
theorem mem_aeZeroOff_of_ae_eq_halfCoord {L : Set M} {w : BorderedSobolevSection A p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (hsL : ∀ x ∉ L, s x = 0) : w ∈ aeZeroOff A p k L := fun i ↦ by
  filter_upwards [hs i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hzi hL
  rw [hz, halfCoord_def]
  exact A.coord_eq_zero (A.mem_halfImage.1 hzi).1 (hsL _ hL)

/-- Multiplication by a smooth function `φ` takes values in the elements vanishing off
`tsupport φ`. -/
theorem contMDiffSMulL_mem_aeZeroOff [IsManifold closedUpperHalfPlaneModel ∞ M] {φ : M → ℝ}
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ) (w : BorderedSobolevSection A p k) :
    contMDiffSMulL A p k hφ w ∈ aeZeroOff A p k (tsupport φ) := fun i ↦ by
  filter_upwards [chartValueL_contMDiffSMulL_ae hφ w i] with y hy hL
  rw [hy, image_eq_zero_of_notMem_tsupport hL, zero_smul]

/-- An element vanishing off a subset `L` of the domain of chart `i` is determined by its
chart-`i` components: over `L` its components in every other chart are coordinate changes of its
chart-`i` components. -/
theorem chartRestrictL_injective [IsManifold closedUpperHalfPlaneModel 1 M] {i : Fin A.n}
    {L : Set M} (hLi : L ⊆ A.dom i) : Function.Injective (chartRestrictL A p k i L) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  have hC := A.aeTransition_halfSectionChartData
  have hslot : ((w : BorderedSobolevSection A p k) :
      A.halfSectionChartData.SobolevData volume p k) i = 0 := by
    rw [← coe_chartRestrictL_apply, hw]
    rfl
  have hi : ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      A.halfSectionChartData.chartValueL volume p k i w z = 0 := by
    filter_upwards [A.halfSectionChartData.chartValueL_apply_ae volume p k i w,
      Lp.coeFn_zero ℝ p (volume.restrict (A.halfImage i : Set ℂ))] with z hz h0
    rw [hz]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hslot, Pi.zero_apply, ← Wkp.valueL_apply, map_zero]
    exact (congrArg (· • finBasis ℝ F j) h0).trans (zero_smul ℝ _)
  refine Subtype.ext (eq_of_ae_eq_halfCoord (s := 0) (fun (i' : Fin A.n) ↦ ?_)
    fun (i' : Fin A.n) ↦ ?_)
  · have hcomp := (A.halfSectionChartData.compatible_iff volume p k).1
      (A.halfSectionChartData.compatible_of_mem hC (w : BorderedSobolevSection A p k).property
        i i')
    have htr := A.halfSectionChartData.aeTransition_iff.1 hC (i' := i') hi
    have hov : ∀ᵐ z ∂volume.restrict (A.halfImage i' : Set ℂ), z ∈ A.halfOverlap i i' →
        A.halfSectionChartData.chartValueL volume p k i' w z = 0 := by
      have h' : ∀ᵐ z ∂volume.restrict (A.halfOverlap i i'),
          A.halfSectionChartData.chartValueL volume p k i' w z = 0 := by
        filter_upwards [hcomp, htr] with z hz htr
        rw [hz, htr, map_zero]
      exact ae_restrict_of_ae ((ae_restrict_iff' (A.isOpen_halfOverlap i i').measurableSet).1 h')
    filter_upwards [w.property i', hov, ae_restrict_mem (A.halfImage i').isOpen.measurableSet]
      with z hz hzo hzi
    obtain ⟨hzi, hz0⟩ := A.mem_halfImage.1 hzi
    rw [halfCoord_def, A.coord_zero i' hzi]
    by_cases hL : (A.chart i').symm (closedUpperHalfPlaneModel.symm z) ∈ L
    · refine hzo (A.mem_halfOverlap.2 ⟨?_, hz0⟩)
      obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hzi
      rw [← hxz, (A.chart i').left_inv (A.dom_subset_chart_source i' hx)] at hL
      rw [← hxz]
      exact A.chart_mem_overlap (hLi hL) hx
    · exact hz hL
  · simp only [ZeroMemClass.coe_zero, map_zero]
    filter_upwards [Lp.coeFn_zero F p (volume.restrict (A.halfImage i' : Set ℂ)),
      ae_restrict_mem (A.halfImage i').isOpen.measurableSet] with z h0 hz
    rw [halfCoord_def, A.coord_zero i' (A.mem_halfImage.1 hz).1]
    exact h0

/-- **Extension by zero.** For a `Cⁿ` bundle with `1 ≤ n` and `k ≤ n`, every tuple of chart-`i`
Sobolev functions vanishing almost everywhere off a closed subset `L` of the domain of chart `i`
consists of the chart-`i` components of an element of `W^{k,p}(V)` vanishing off `L`. -/
theorem chartRestrictL_surjective {n : ℕ} [IsManifold closedUpperHalfPlaneModel n M]
    [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel] (hn : 1 ≤ n) (hkn : k ≤ n)
    {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i) :
    Function.Surjective (chartRestrictL A p k i L) := by
  classical
  intro g
  -- The section equal in chart `i` to the tuple `g` over `L`, and zero elsewhere.
  set G : ℂ → F := fun z ↦ ∑ j,
    Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) j) z • finBasis ℝ F j
  set s : ∀ x, V x := A.chartSection i fun y ↦
    if (A.chart i).symm y ∈ L then G (y : ℂ) else 0
  have hsL (x : M) (hx : x ∉ L) : s x = 0 := chartSection_eq_zero fun hxi ↦ by
    simp [(A.chart i).left_inv (A.dom_subset_chart_source i hxi), hx]
  have hsi {z : ℂ} (hz : z ∈ A.halfImage i) : A.halfCoord i s z =
      if (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ L then G z else 0 := by
    obtain ⟨hzi, hz0⟩ := A.mem_halfImage.1 hz
    rw [halfCoord_def, coord_chartSection _ hzi,
      coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]
  have hv (m : Fin (finrank ℝ F)) :
      (Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) m) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord m (A.halfCoord i s z) := by
    filter_upwards [g.property m, ae_restrict_mem (A.halfImage i).isOpen.measurableSet]
      with z h0 hz
    rw [hsi hz]
    split_ifs with hL'
    · rw [Basis.coord_apply, (finBasis ℝ F).repr_sum_self]
    · rw [h0 hL', map_zero]
  obtain ⟨w, hw⟩ :=
    exists_chartValueL_ae_eq_halfCoord_of_eq_zero hn hkn hL hLi hsL fun m ↦ ⟨_, hv m⟩
  refine ⟨⟨w, mem_aeZeroOff_of_ae_eq_halfCoord hw hsL⟩, Subtype.ext (funext fun m ↦ ?_)⟩
  exact Wkp.ext k (Lp.ext ((value_ae_eq_repr_halfCoord (hw i) m).trans (hv m).symm))

section Extension

variable {n : ℕ} [IsManifold closedUpperHalfPlaneModel n M]
  [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel]

variable (A p k) in
/-- For a `Cⁿ` bundle with `1 ≤ n` and `k ≤ n` and a closed subset `L` of the domain of chart `i`,
the chart-`i` components of the elements of `W^{k,p}(V)` vanishing off `L` form a linear
equivalence onto the chart-`i` tuples vanishing off `L`. -/
def chartRestrictEquiv (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : aeZeroOff A p k L ≃ₗ[ℝ] chartAeZeroOff A p k i L :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  LinearEquiv.ofBijective (chartRestrictL A p k i L).toLinearMap
    ⟨chartRestrictL_injective hLi, chartRestrictL_surjective hn hkn hL hLi⟩

@[simp]
theorem chartRestrictEquiv_apply (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A p k L) :
    chartRestrictEquiv A p k hn hkn hL hLi w = chartRestrictL A p k i L w :=
  (rfl)

/-- **Extension by zero.** Let `L` be a closed subset of the domain of chart `i`, for a `Cⁿ` bundle
with `1 ≤ n` and `k ≤ n`. A tuple of chart-`i` Sobolev functions vanishing almost everywhere off
`L` defines an element of `W^{k,p}(V)`, vanishing off `L`, whose chart-`i` components are the given
functions. This is a continuous linear map from the closed subspace
`TauCeti.BorderedSobolevSection.chartAeZeroOff A p k i L` into `W^{k,p}(V)`, by the closed graph
theorem. -/
def extendByZeroL (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : chartAeZeroOff A p k i L →L[ℝ] BorderedSobolevSection A p k :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  ContinuousLinearMap.ofSeqClosedGraph
    (g := (aeZeroOff A p k L).subtype ∘ₗ
      (chartRestrictEquiv A p k hn hkn hL hLi).symm.toLinearMap)
    fun u x y hu hy ↦ by
      set e := chartRestrictEquiv A p k hn hkn hL hLi
      -- The limit `y` vanishes off `L`, and its chart-`i` components are the limit `x`.
      have hyL : y ∈ aeZeroOff A p k L :=
        (isClosed_aeZeroOff A p k L).mem_of_tendsto hy
          (Eventually.of_forall fun n ↦ (e.symm (u n)).property)
      have hconv : Tendsto (fun n ↦ e.symm (u n)) atTop (𝓝 ⟨y, hyL⟩) := tendsto_subtype_rng.2 hy
      have hx : chartRestrictL A p k i L ⟨y, hyL⟩ = x :=
        tendsto_nhds_unique (((chartRestrictL A p k i L).continuous.tendsto _).comp hconv)
          (hu.congr fun n ↦ by
            rw [Function.comp_apply, ← chartRestrictEquiv_apply hn hkn hL hLi,
              e.apply_symm_apply])
      rw [← hx, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        ← chartRestrictEquiv_apply hn hkn hL hLi, e.symm_apply_apply, Submodule.subtype_apply]

theorem extendByZeroL_apply (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A p k i L) :
    extendByZeroL hn hkn hL hLi g = (chartRestrictEquiv A p k hn hkn hL hLi).symm g := by
  have : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  rw [extendByZeroL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Submodule.subtype_apply]

/-- An element vanishing off `L` is the extension by zero of its chart-`i` components. -/
@[simp]
theorem extendByZeroL_chartRestrictL (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A p k L) :
    extendByZeroL hn hkn hL hLi (chartRestrictL A p k i L w) = w := by
  rw [extendByZeroL_apply, ← chartRestrictEquiv_apply hn hkn hL hLi,
    LinearEquiv.symm_apply_apply]

end Extension

end BorderedSobolevSection

end TauCeti
