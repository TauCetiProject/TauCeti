/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bilinear
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Transfer
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Supercritical
import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc

/-!
# Multiplication by Sobolev coefficients over a surface with boundary

Let `M` be a `Cⁿ` manifold modelled on the closed upper half-plane, for instance a compact surface
with boundary, let `V₁` and `V₂` be `Cⁿ` real vector bundles over `M` with finite-dimensional model
fibres, and let `A` be a finite bundle atlas of `V₁` whose chart domains have closures in the base
sets of the preferred trivializations of `V₂`. For `1 < p < ∞` and orders `k ≤ n` with `kp > 2`, a
section `α` of the bundle `x ↦ V₁ x →L[ℝ] V₂ x` in `W^{k,p}` acts on sections `ξ` of `V₁` in
`W^{k,p}` by `x ↦ α x (ξ x)`, giving a section of `V₂` in `W^{k,p}`, and this is a bounded bilinear
map (`TauCeti.BorderedSobolevSection.homMulL`). This is multiplication by `W^{k,p}` coefficients
for `kp > 2`, up to the boundary.

## The argument

The product lies in `W^{k,p}(V₂)` (`TauCeti.BorderedSobolevSection.hasAeProducts_hom`): in chart `j`
both factors lie in the local Sobolev classes up to the real axis on the part of the target of the
extended chart lying over the base sets of the bundle charts
(`TauCeti.FiniteBundleAtlas.memWkpLoc_halfCoord_extChartAt_target`), so their product does
(`TauCeti.MemWkpLoc.clm_apply_of_two_lt_mul_halfPlane`), and the closure of the chart image is a
compact subset of that part. Boundedness needs no further estimate: the product of Sobolev
sections with these chart data is bounded by the closed graph theorem
(`TauCeti.SectionChartData.bilinOfAeEq`).

## Main definitions

* `TauCeti.BorderedSobolevSection.homMulL`: the action of `W^{k,p}` hom sections on `W^{k,p}`
  sections, as a continuous bilinear map.

## Main results

* `TauCeti.BorderedSobolevSection.hasAeProducts_hom`: the products lie in `W^{k,p}(V₂)`.
* `TauCeti.BorderedSobolevSection.chartValueL_homMulL_ae`,
  `TauCeti.BorderedSobolevSection.chartValueL_homMulL_ae_halfCoord`: in every chart the product is
  the pointwise application of the chart data, and of section representatives.
* `TauCeti.BorderedSobolevSection.exists_norm_homMulL_apply_le`: `‖α ξ‖ ≤ C ‖α‖ ‖ξ‖`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19 and Appendix C.1.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal NNReal

namespace TauCeti

namespace BorderedSobolevSection

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] {n : ℕ}
  [IsManifold closedUpperHalfPlaneModel n M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle n F₁ V₁ closedUpperHalfPlaneModel]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle ℝ F₂ V₂] [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle n F₂ V₂ closedUpperHalfPlaneModel]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F₁ V₁)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {k : ℕ}

omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] [IsManifold closedUpperHalfPlaneModel n M]
  [ContMDiffVectorBundle n F₁ V₁ closedUpperHalfPlaneModel]
  [ContMDiffVectorBundle n F₂ V₂ closedUpperHalfPlaneModel] [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- `kp > 2` forces `k ≥ 1`, so `k ≤ n` gives `1 ≤ n`. -/
private theorem one_le_of_two_lt_mul (hkn : k ≤ n) (hkp : 2 < (k : ℝ≥0) * p) : 1 ≤ n :=
  (Nat.one_le_iff_ne_zero.2 fun hk ↦ by simp [hk] at hkp).trans hkn

/-- In chart `j`, the reading of `x ↦ φ x (s x)` has `W^{k,p}` components on the interior of the
chart image, when the readings of `φ` and `s` are the chart data of Sobolev sections. -/
private theorem exists_wkp_coord_hom_apply (hkn : k ≤ n) (hp : 1 < p)
    (hkp : 2 < (k : ℝ≥0) * p) {α : BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k}
    {ξ : BorderedSobolevSection A p k} {φ : ∀ x, V₁ x →L[ℝ] V₂ x} {s : ∀ x, V₁ x}
    (hφ : ∀ i, (A.hom (𝕜 := ℝ) h).halfSectionChartData.chartValueL volume p k i α
      =ᵐ[volume.restrict ((A.hom (𝕜 := ℝ) h).halfImage i : Set ℂ)] (A.hom (𝕜 := ℝ) h).halfCoord i φ)
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i ξ
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (j : Fin A.n) (m : Fin (finrank ℝ F₂)) :
    ∃ v : Wkp volume ((A.ofBaseSet h).halfImage j) p k,
      (Wkp.value k v : ℂ → ℝ) =ᵐ[volume.restrict ((A.ofBaseSet h).halfImage j : Set ℂ)]
        fun z ↦ (finBasis ℝ F₂).coord m
          ((A.ofBaseSet h).halfSectionChartData.coord j (fun x ↦ φ x (s x)) z) := by
  rw [A.halfImage_ofBaseSet]
  have hn := one_le_of_two_lt_mul hkn hkp
  -- Both readings are in the local classes over the base sets of both bundle charts.
  set e := extChartAt closedUpperHalfPlaneModel (A.center j)
  obtain ⟨Ω, hΩ, hΩe⟩ := exists_isOpen_extChartAt_target_inter_preimage (A.center j)
    ((A.triv j).open_baseSet.inter (trivializationAt F₂ V₂ (A.center j)).open_baseSet)
  have hα := ((A.hom (𝕜 := ℝ) h).memWkpLoc_halfCoord_extChartAt_target (A.hom (𝕜 := ℝ) h) hn hkn
    (memWkpLoc_halfCoord α hφ) j).congr_mono (fun _ _ ↦ rfl) (hΩe.symm.trans (by
      rw [triv, hom_trivializationAt_baseSet, hom_center])).le
  have hξ := (A.memWkpLoc_halfCoord_extChartAt_target A hn hkn (memWkpLoc_halfCoord ξ hs)
    j).congr_mono (fun _ _ ↦ rfl) (hΩe.ge.trans
      (inter_subset_inter_right _ (preimage_mono inter_subset_left)))
  -- The closure of the chart image is a compact subset of `Ω`.
  have hcl : closure (A.halfImage j : Set ℂ) ⊆ Ω := fun z hz ↦
    (hΩe.subset ⟨A.closure_halfImage_subset_extChartAt_target j hz, by
      simp only [mem_preimage, extChartAt_coe_symm, Function.comp_apply]
      exact ⟨A.chart_symm_mem_baseSet_of_mem_closure_halfImage hz,
        (A.ofBaseSet h).chart_symm_mem_baseSet_of_mem_closure_halfImage
          (by rwa [A.halfImage_ofBaseSet])⟩⟩ :
      z ∈ Ω ∩ {z | 0 ≤ z.im}).1
  have hle : A.halfImage j ≤ (A.halfImage j).upperHalf :=
    fun z hz ↦ Opens.mem_upperHalf.2 ⟨hz, (A.mem_halfImage.1 hz).2⟩
  obtain ⟨v, hv⟩ := ((MemWkpLoc.clm_apply_of_two_lt_mul_halfPlane (Ω := ⟨Ω, hΩ⟩) hp hkp hα
    hξ).clm_comp (LinearMap.toContinuousLinearMap ((finBasis ℝ F₂).coord m))).exists_wkp_upperHalf
      (A.isCompact_closure_halfImage j) hcl
  refine ⟨Wkp.restrictL hle k v, (Wkp.value_restrictL_ae hle k v).trans ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hle hv,
    ae_restrict_mem (A.halfImage j).isOpen.measurableSet] with z hz hzj
  rw [hz, (A.ofBaseSet h).halfSectionChartData_coord_of_mem _ ((A.halfImage_ofBaseSet j).ge hzj),
    ← A.halfCoord_hom_apply h j φ s (A.mem_halfImage.1 hzj).1,
    LinearMap.coe_toContinuousLinearMap']

omit [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] [IsManifold closedUpperHalfPlaneModel n M]
  [ContMDiffVectorBundle n F₁ V₁ closedUpperHalfPlaneModel]
  [ContMDiffVectorBundle n F₂ V₂ closedUpperHalfPlaneModel] in
private theorem subset_hom (i : Fin A.n) :
    ((A.ofBaseSet h).halfImage i : Set ℂ) ⊆ (A.hom (𝕜 := ℝ) h).halfImage i :=
  SetLike.coe_subset_coe.2 ((A.halfImage_ofBaseSet i).trans (A.halfImage_hom h i).symm).le

omit [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [VectorBundle ℝ F₁ V₁] [NormedSpace ℝ F₂] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [FiniteDimensional ℝ F₂] [VectorBundle ℝ F₂ V₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [IsManifold closedUpperHalfPlaneModel n M]
  [ContMDiffVectorBundle n F₁ V₁ closedUpperHalfPlaneModel]
  [ContMDiffVectorBundle n F₂ V₂ closedUpperHalfPlaneModel] in
private theorem subset_self (i : Fin A.n) :
    ((A.ofBaseSet h).halfImage i : Set ℂ) ⊆ A.halfImage i :=
  SetLike.coe_subset_coe.2 (A.halfImage_ofBaseSet i).le

omit [IsManifold closedUpperHalfPlaneModel n M]
  [ContMDiffVectorBundle n F₁ V₁ closedUpperHalfPlaneModel]
  [ContMDiffVectorBundle n F₂ V₂ closedUpperHalfPlaneModel] in
/-- The chart product of the hom action is the application of the chart data. -/
private theorem chartProduct_hom (α : BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k)
    (ξ : BorderedSobolevSection A p k) (i : Fin A.n) (z : ℂ) :
    (A.ofBaseSet h).halfSectionChartData.chartProduct (A.hom (𝕜 := ℝ) h).halfSectionChartData
      A.halfSectionChartData (ContinuousLinearMap.id ℝ (F₁ →L[ℝ] F₂)) (fun i ↦ i) (fun i ↦ i)
      α ξ i z = (A.hom (𝕜 := ℝ) h).halfSectionChartData.chartValueL volume p k i α z
        (A.halfSectionChartData.chartValueL volume p k i ξ z) := by
  -- The chart indices of the three chart data agree only after unfolding the hom atlas, so
  -- `chartProduct_apply` is instantiated explicitly rather than found by `rw` or `simp`.
  refine (SectionChartData.chartProduct_apply (C₃ := (A.ofBaseSet h).halfSectionChartData)
    (C₁ := (A.hom (𝕜 := ℝ) h).halfSectionChartData) (C₂ := A.halfSectionChartData)
    (b := ContinuousLinearMap.id ℝ (F₁ →L[ℝ] F₂)) (e₁ := fun i ↦ i) (e₂ := fun i ↦ i)
    α ξ i z).trans ?_
  rw [ContinuousLinearMap.id_apply]

/-- **Products lie in `W^{k,p}`.** For `1 < p`, orders `k ≤ n` with `kp > 2`, a `W^{k,p}`
section `α` of the hom bundle and a `W^{k,p}` section `ξ` of `V₁`, some `W^{k,p}` section of `V₂`
has, in every chart, chart data equal almost everywhere to the pointwise application of the chart
data of `α` to those of `ξ`. -/
theorem hasAeProducts_hom (hkn : k ≤ n) (hp : 1 < p) (hkp : 2 < (k : ℝ≥0) * p) :
    (A.ofBaseSet h).halfSectionChartData.HasAeProducts (A.hom (𝕜 := ℝ) h).halfSectionChartData
      A.halfSectionChartData (ContinuousLinearMap.id ℝ (F₁ →L[ℝ] F₂)) (fun i ↦ i) (fun i ↦ i)
      volume p p p k k k := by
  refine SectionChartData.hasAeProducts_iff.2 fun α ξ ↦ ?_
  obtain ⟨φ, hφ⟩ := (A.hom (𝕜 := ℝ) h).halfSectionChartData.exists_section volume p k α
  obtain ⟨s, hs⟩ := A.halfSectionChartData.exists_section volume p k ξ
  have hφ' (i : Fin A.n) := (hφ i).trans ((A.hom (𝕜 := ℝ) h).halfSectionChartData_coord_ae_eq i φ)
  have hs' (i : Fin A.n) := (hs i).trans (A.halfSectionChartData_coord_ae_eq i s)
  obtain ⟨w, hw⟩ := exists_chartValueL_ae_eq_halfCoord_of_forall_exists_wkp
    (A := A.ofBaseSet h) (s := fun x ↦ φ x (s x))
    (exists_wkp_coord_hom_apply A h hkn hp hkp hφ' hs')
  refine ⟨w, fun i ↦ (hw i).trans ?_⟩
  have h₁ := subset_hom A h i
  have h₂ := subset_self A h i
  filter_upwards [ae_restrict_of_ae_restrict_of_subset h₁ (hφ' i),
    ae_restrict_of_ae_restrict_of_subset h₂ (hs' i),
    ae_restrict_of_ae_restrict_of_subset h₂
      (ae_restrict_mem (A.halfImage i).isOpen.measurableSet)]
    with z hφz hsz hz
  -- `ContinuousLinearMap.id` applies as the identity, so the product is `φ z (s z)`.
  exact ((congrArg₂ (fun (f : F₁ →L[ℝ] F₂) (v : F₁) ↦ f v) hφz hsz).trans
    (A.halfCoord_hom_apply h i φ s (A.mem_halfImage.1 hz).1)).symm.trans
      (chartProduct_hom A h α ξ i z).symm

omit [ContMDiffVectorBundle n F₁ V₁ closedUpperHalfPlaneModel]
  [ContMDiffVectorBundle n F₂ V₂ closedUpperHalfPlaneModel] in
private theorem isManifold_one (hn : 1 ≤ n) : IsManifold closedUpperHalfPlaneModel 1 M :=
  IsManifold.of_le (n := n) (by exact_mod_cast hn)

/-- **Multiplication by `W^{k,p}` coefficients.** For `1 < p`, orders `k ≤ n` with `kp > 2`,
applying `W^{k,p}` sections of the bundle `x ↦ V₁ x →L[ℝ] V₂ x` to `W^{k,p}` sections of `V₁`
pointwise is a continuous bilinear map into the `W^{k,p}` sections of `V₂`. -/
def homMulL (hkn : k ≤ n) (hp : 1 < p) (hkp : 2 < (k : ℝ≥0) * p) :
    BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k →L[ℝ] BorderedSobolevSection A p k →L[ℝ]
      BorderedSobolevSection (A.ofBaseSet h) p k :=
  letI := isManifold_one (M := M) (one_le_of_two_lt_mul hkn hkp)
  SectionChartData.bilinOfAeEq (subset_hom A h) (subset_self A h)
    (hasAeProducts_hom A h hkn hp hkp)

/-- The chart data of `homMulL α ξ` are the pointwise application of the chart data of `α` to
those of `ξ`. -/
theorem chartValueL_homMulL_ae (hkn : k ≤ n) (hp : 1 < p)
    (hkp : 2 < (k : ℝ≥0) * p) (α : BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k)
    (ξ : BorderedSobolevSection A p k) (j : Fin A.n) :
    (A.ofBaseSet h).halfSectionChartData.chartValueL volume p k j (homMulL A h hkn hp hkp α ξ)
      =ᵐ[volume.restrict (A.halfImage j : Set ℂ)] fun z ↦
        (A.hom (𝕜 := ℝ) h).halfSectionChartData.chartValueL volume p k j α z
          (A.halfSectionChartData.chartValueL volume p k j ξ z) :=
  letI := isManifold_one (M := M) (one_le_of_two_lt_mul hkn hkp)
  ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (A.halfImage_ofBaseSet j).ge)
    ((SectionChartData.chartValueL_bilinOfAeEq_ae (subset_hom A h) (subset_self A h)
      (hasAeProducts_hom A h hkn hp hkp) α ξ j).trans
        (Eventually.of_forall fun z ↦ chartProduct_hom A h α ξ j z))

/-- **Sections.** If the chart data of `α` and `ξ` are the readings of sections `φ` and `s`, those
of `homMulL α ξ` are the readings of `x ↦ φ x (s x)`. -/
theorem chartValueL_homMulL_ae_halfCoord (hkn : k ≤ n) (hp : 1 < p)
    (hkp : 2 < (k : ℝ≥0) * p) {α : BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k}
    {ξ : BorderedSobolevSection A p k} {φ : ∀ x, V₁ x →L[ℝ] V₂ x} {s : ∀ x, V₁ x} {j : Fin A.n}
    (hφ : (A.hom (𝕜 := ℝ) h).halfSectionChartData.chartValueL volume p k j α
      =ᵐ[volume.restrict (A.halfImage j : Set ℂ)] (A.hom (𝕜 := ℝ) h).halfCoord j φ)
    (hs : A.halfSectionChartData.chartValueL volume p k j ξ
      =ᵐ[volume.restrict (A.halfImage j : Set ℂ)] A.halfCoord j s) :
    (A.ofBaseSet h).halfSectionChartData.chartValueL volume p k j (homMulL A h hkn hp hkp α ξ)
      =ᵐ[volume.restrict (A.halfImage j : Set ℂ)] (A.ofBaseSet h).halfCoord j
        (fun x ↦ φ x (s x)) := by
  filter_upwards [chartValueL_homMulL_ae A h hkn hp hkp α ξ j, hφ, hs,
    ae_restrict_mem (A.halfImage j).isOpen.measurableSet] with z hz hφz hsz hzj
  rw [hz, hφz, hsz, A.halfCoord_hom_apply h j φ s (A.mem_halfImage.1 hzj).1]

/-- **Bound.** There is a constant `C` with `‖homMulL α ξ‖ ≤ C ‖α‖ ‖ξ‖`. -/
theorem exists_norm_homMulL_apply_le (hkn : k ≤ n) (hp : 1 < p)
    (hkp : 2 < (k : ℝ≥0) * p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k)
      (ξ : BorderedSobolevSection A p k), ‖homMulL A h hkn hp hkp α ξ‖ ≤ C * ‖α‖ * ‖ξ‖ := by
  -- The operator norm uses the norms of the three Sobolev spaces of sections.
  let _ : NormedAddCommGroup (BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k) := inferInstance
  let _ : NormedSpace ℝ (BorderedSobolevSection (A.hom (𝕜 := ℝ) h) p k) := inferInstance
  let _ : NormedAddCommGroup (BorderedSobolevSection A p k) := inferInstance
  let _ : NormedSpace ℝ (BorderedSobolevSection A p k) := inferInstance
  let _ : NormedAddCommGroup (BorderedSobolevSection (A.ofBaseSet h) p k) := inferInstance
  let _ : NormedSpace ℝ (BorderedSobolevSection (A.ofBaseSet h) p k) := inferInstance
  let _ : NormedAddCommGroup (BorderedSobolevSection A p k →L[ℝ]
    BorderedSobolevSection (A.ofBaseSet h) p k) := inferInstance
  let _ : NormedSpace ℝ (BorderedSobolevSection A p k →L[ℝ]
    BorderedSobolevSection (A.ofBaseSet h) p k) := inferInstance
  exact ⟨‖homMulL A h hkn hp hkp‖, norm_nonneg _, (homMulL A h hkn hp hkp).le_opNorm₂⟩

end BorderedSobolevSection

end TauCeti
