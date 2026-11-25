/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Equiv
import TauCeti.Analysis.Sobolev.Local.Compactness
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Transfer
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich

/-!
# Rellich compactness for Sobolev sections over a surface with boundary

Let `M` be a Hausdorff `Cⁿ` manifold modelled on the closed upper half-plane, for instance a
compact surface with boundary, let `V → M` be a `Cⁿ` real vector bundle with finite-dimensional
model fibre `F`, and let `A` be a finite bundle atlas. For `1 ≤ p ≤ ∞` and every order `k` with
`k + 1 ≤ n`, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` of the bordered Sobolev spaces
`TauCeti.BorderedSobolevSection` is a compact operator
(`TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrderL`).

## The argument

Compactness into the Sobolev sections is componentwise
(`TauCeti.SectionChartData.isCompactOperator_of_forall_apply`). The chart image `A.halfImage j`
need not have its closure inside a set on which the chart data are controlled, so the data are
read in a larger atlas instead. Enlarge the chart domains: an atlas `B` with the same centres as
`A` and domains `U j` containing `closure (A.dom j)` (`TauCeti.FiniteBundleAtlas.enlarge`).
Sections transfer from `A` to `B`
(`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`), so the change of atlas
`TauCeti.BorderedSobolevSection.changeAtlas` is a continuous linear map, and the chart-`j`
components of an element for `A` are the restrictions to `A.halfImage j` of the
chart-`j` components of its image for `B`, since the two atlases read sections in the same charts.
The closure of `A.halfImage j` is compact and lies in the image of chart `j` of `B`, up to the real
axis, so Rellich compactness up to the real axis
(`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf`) applies on each component.

## Main results

* `TauCeti.FiniteBundleAtlas.enlarge`, `TauCeti.FiniteBundleAtlas.exists_enlarge`: an atlas with
  the same charts and chart domains containing the closures of those of `A`.
* `TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrderL`: **Rellich's theorem** for
  Sobolev sections over a base with boundary.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold Topology ENNReal

namespace TauCeti

namespace FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [TopologicalSpace F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V]

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- The finite bundle atlas with the centres of `A` and larger chart domains `U j`, open with
compact closure inside the source of the chart and the base set of the bundle chart. -/
@[expose, simps n center dom]
def enlarge (U : Fin A.n → Set M) (hU : ∀ j, IsOpen (U j))
    (hAU : ∀ j, A.dom j ⊆ U j) (hUc : ∀ j, IsCompact (closure (U j)))
    (hUs : ∀ j, closure (U j) ⊆ (A.chart j).source ∩ (A.triv j).baseSet) :
    FiniteBundleAtlas ClosedUpperHalfPlane M F V where
  n := A.n
  center := A.center
  dom := U
  isOpen_dom := hU
  isCompact_closure_dom := hUc
  closure_dom_subset_source j := (hUs j).trans inter_subset_left
  closure_dom_subset_baseSet j := (hUs j).trans inter_subset_right
  iUnion_dom := eq_univ_of_forall fun x ↦ by
    obtain ⟨j, hj⟩ := A.exists_mem_dom x
    exact mem_iUnion.2 ⟨j, hAU j hj⟩

section Enlarge

variable {A} {U : Fin A.n → Set M} {hU : ∀ j, IsOpen (U j)} {hAU : ∀ j, A.dom j ⊆ U j}
  {hUc : ∀ j, IsCompact (closure (U j))}
  {hUs : ∀ j, closure (U j) ⊆ (A.chart j).source ∩ (A.triv j).baseSet}

/-- The charts of `A.enlarge U hU hAU hUc hUs` are those of `A`. -/
@[simp]
theorem chart_enlarge (j : Fin A.n) : (A.enlarge U hU hAU hUc hUs).chart j = A.chart j :=
  (rfl)

/-- The bundle charts of `A.enlarge U hU hAU hUc hUs` are those of `A`. -/
@[simp]
theorem triv_enlarge (j : Fin A.n) : (A.enlarge U hU hAU hUc hUs).triv j = A.triv j :=
  (rfl)

/-- Sections are read in the charts of `A.enlarge U hU hAU hUc hUs` as in those of `A`. -/
@[simp]
theorem coord_enlarge (j : Fin A.n) : (A.enlarge U hU hAU hUc hUs).coord j = A.coord j := by
  funext s y
  rw [(A.enlarge U hU hAU hUc hUs).coord_def j s y, A.coord_def j s y, chart_enlarge,
    triv_enlarge]

/-- The readings of a section in the charts of `A.enlarge U hU hAU hUc hUs` are its readings in
`A`. -/
@[simp]
theorem halfCoord_enlarge (j : Fin A.n) (s : ∀ x, V x) :
    (A.enlarge U hU hAU hUc hUs).halfCoord j s = A.halfCoord j s := by
  ext z
  rw [(A.enlarge U hU hAU hUc hUs).halfCoord_def j s z, A.halfCoord_def j s z, coord_enlarge]

end Enlarge

/-- **Enlarging the chart domains.** On a Hausdorff base there are open sets `U j` containing the
closures of the chart domains of `A`, with compact closure inside the source of the chart and the
base set of the bundle chart. -/
theorem exists_enlarge [T2Space M] :
    ∃ U : Fin A.n → Set M, (∀ j, IsOpen (U j)) ∧ (∀ j, closure (A.dom j) ⊆ U j) ∧
      (∀ j, IsCompact (closure (U j))) ∧
        ∀ j, closure (U j) ⊆ (A.chart j).source ∩ (A.triv j).baseSet := by
  have : LocallyCompactSpace ClosedUpperHalfPlane :=
    (isClosed_le continuous_const Complex.continuous_im).locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ClosedUpperHalfPlane M
  choose U hU hAU hUs hUc using fun j ↦ exists_open_between_and_isCompact_closure
    (A.isCompact_closure_dom j) ((A.chart j).open_source.inter (A.triv j).open_baseSet)
    (subset_inter (A.closure_dom_subset_source j) (A.closure_dom_subset_baseSet j))
  exact ⟨U, hU, hAU, hUc, hUs⟩

end FiniteBundleAtlas

namespace BorderedSobolevSection

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] [T2Space M]
  {n : ℕ} [IsManifold closedUpperHalfPlaneModel n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- Forgetting a derivative commutes with restriction, through intermediate open sets. -/
private theorem lowerOrder_restrictL_eq {O₁ O₂ O₃ O₄ : Opens ℂ} (h₂₁ : O₂ ≤ O₁) (h₃₂ : O₃ ≤ O₂)
    (h₄₃ : O₄ ≤ O₃) (h₄₁ : O₄ ≤ O₁) (u : Wkp volume O₁ p (k + 1)) :
    Wkp.lowerOrder k (Wkp.restrictL h₄₁ (k + 1) u) =
      Wkp.restrictL h₄₃ k
        (Wkp.restrictL h₃₂ k (Wkp.lowerOrderL k (Wkp.restrictL h₂₁ (k + 1) u))) := by
  refine Wkp.ext k (Lp.ext ?_)
  set v := Wkp.lowerOrderL k (Wkp.restrictL h₂₁ (k + 1) u)
  filter_upwards [Wkp.value_restrictL_ae h₄₁ (k + 1) u,
    Wkp.value_restrictL_ae h₄₃ k (Wkp.restrictL h₃₂ k v),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 h₄₃)
      (Wkp.value_restrictL_ae h₃₂ k v),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (h₄₃.trans h₃₂))
      (Wkp.value_restrictL_ae h₂₁ (k + 1) u)] with z h₁ h₂ h₃ h₄
  rw [← Wkp.value_succ, h₁, h₂, h₃, ← h₄]
  simp only [v, Wkp.value_succ]
  rw [Wkp.lowerOrderL_apply]

omit [T2Space M] in
/-- **Components under a change of atlas.** If chart `jA` of `A` and chart `jB` of `B` read
sections in the same way and the interior of the image of chart `jA` lies in that of chart `jB`,
the chart-`jA` components of an element for `A` are the restrictions of the chart-`jB` components of
its image for `B`. -/
private theorem component_eq_restrictL_changeAtlas [IsManifold closedUpperHalfPlaneModel 1 M]
    {A B : FiniteBundleAtlas ClosedUpperHalfPlane M F V} (htr : TransfersTo A B p (k + 1))
    {jA : Fin A.n} {jB : Fin B.n} (hBA : ∀ s : ∀ x, V x, B.halfCoord jB s = A.halfCoord jA s)
    (hle : A.halfImage jA ≤ B.halfImage jB) (x : BorderedSobolevSection A p (k + 1))
    (m : Fin (finrank ℝ F)) :
    (x : A.halfSectionChartData.SobolevData volume p (k + 1)) jA m =
      Wkp.restrictL hle (k + 1)
        ((changeAtlas htr x : B.halfSectionChartData.SobolevData volume p (k + 1)) jB m) := by
  obtain ⟨s, hs⟩ := A.halfSectionChartData.exists_section volume p (k + 1) x
  have hs' (i : Fin A.n) := (hs i).trans (A.halfSectionChartData_coord_ae_eq i s)
  have hgB := (SectionChartData.chartValueL_ae_eq_coord_iff _ _ _ _).1
    ((chartValueL_changeAtlas_ae htr hs' jB).trans (B.halfSectionChartData_coord_ae_eq jB s).symm) m
  refine Wkp.ext (k + 1) (Lp.ext ?_)
  filter_upwards [(SectionChartData.chartValueL_ae_eq_coord_iff _ _ _ _).1 (hs jA) m,
    (A.halfSectionChartData_coord_ae_eq jA s).fun_comp ((finBasis ℝ F).coord m),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hle) hgB,
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hle)
      ((B.halfSectionChartData_coord_ae_eq jB s).fun_comp ((finBasis ℝ F).coord m)),
    Wkp.value_restrictL_ae hle (k + 1)
      ((changeAtlas htr x : B.halfSectionChartData.SobolevData volume p (k + 1)) jB m)]
    with z h₁ h₂ h₃ h₄ h₅
  simp only [Function.comp_apply] at h₂ h₄
  rw [h₁, h₂, ← hBA]
  exact h₄.symm.trans (h₃.symm.trans h₅.symm)

/-- **Rellich's theorem over a base with boundary.** For a `Cⁿ` vector bundle over a Hausdorff
`Cⁿ` manifold modelled on the closed upper half-plane, `1 ≤ p ≤ ∞` and `k + 1 ≤ n`, the inclusion
`W^{k+1,p}(V) → W^{k,p}(V)` of Sobolev sections is a compact operator. -/
theorem isCompactOperator_lowerOrderL (hkn : k + 1 ≤ n)
    (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) :
    IsCompactOperator (A.halfSectionChartData.lowerOrderL volume p k) := by
  have : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast (Nat.le_add_left 1 k).trans hkn)
  obtain ⟨U, hU, hAU, hUc, hUs⟩ := A.exists_enlarge
  set B := A.enlarge U hU (fun j ↦ subset_closure.trans (hAU j)) hUc hUs
  have htr : TransfersTo A B p (k + 1) := transfersTo_iff.2 fun w _ hs ↦
    exists_chartValueL_ae_eq_halfCoord (le_add_self.trans hkn) hkn w hs B
  refine SectionChartData.isCompactOperator_of_forall_apply A.aeTransition_halfSectionChartData
    fun j m ↦ ?_
  -- The open set `W` with upper half the interior of the image of chart `j` of `B`.
  set W : Opens ℂ := B.halfOpen j
  have h1 : W.upperHalf ≤ B.halfImage j := fun z hz ↦
    B.mem_halfImage.2 ⟨B.mem_halfOpen.1 (Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2⟩
  have hA : (A.halfImage j : Set ℂ) ⊆ B.halfImage j := fun z hz ↦ by
    obtain ⟨hz, hz0⟩ := A.mem_halfImage.1 hz
    obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hz
    exact B.mem_halfImage.2 ⟨B.mem_image.2 ⟨x, subset_closure.trans (hAU j) hx, hxz⟩, hz0⟩
  -- The closure of `A.halfImage j` is compact and lies in `W`.
  have hVc := A.isCompact_closure_halfImage j
  have hVW : closure (A.halfImage j : Set ℂ) ⊆ W := fun z hz ↦ by
    obtain ⟨x, hx, hxz⟩ := A.exists_mem_closure_dom_of_mem_closure_halfImage hz
    exact B.mem_halfOpen.2 (hxz ▸ B.mem_image.2 ⟨x, hAU j hx, rfl⟩)
  have h3 : A.halfImage j ≤ (A.halfImage j).upperHalf :=
    fun z hz ↦ Opens.mem_upperHalf.2 ⟨hz, (A.mem_halfImage.1 hz).2⟩
  -- The compact operator: change atlas, take the component, restrict and forget a derivative.
  have hR := Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf (p := p) hVc hVW k
  have hT := ((hR.comp_clm ((Wkp.restrictL h1 (k + 1)).comp
    ((ContinuousLinearMap.proj m).comp ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun i : Fin B.halfSectionChartData.n ↦
        Fin (finrank ℝ F) → Wkp volume (B.halfSectionChartData.image i) p (k + 1)) j).comp
      ((B.halfSectionChartData.sobolevSections volume p (k + 1)).subtypeL.comp
        (changeAtlas htr)))))).clm_comp (Wkp.restrictL h3 k))
  have hle' : A.halfImage j ≤ B.halfImage j := fun z hz ↦ hA hz
  have hle := Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans hVW))
  -- The two maps agree pointwise; their codomains agree up to unfolding `halfSectionChartData`.
  convert hT using 1
  all_goals try rfl
  refine heq_of_eq (funext fun x ↦ ?_)
  simp only [Function.comp_apply, SectionChartData.lowerOrderL_apply]
  rw [component_eq_restrictL_changeAtlas htr (fun s ↦ halfCoord_enlarge j s) hle' x m]
  exact lowerOrder_restrictL_eq h1 hle h3 hle'
    ((changeAtlas htr x : B.halfSectionChartData.SobolevData volume p (k + 1)) j m)

end BorderedSobolevSection

end TauCeti
