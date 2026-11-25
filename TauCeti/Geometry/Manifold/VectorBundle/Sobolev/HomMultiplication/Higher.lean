/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bilinear
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher

/-!
# Multiplication by higher-order Sobolev coefficients on a surface without boundary

Let `M` be a `Cⁿ` surface without boundary, modelled on `ℂ`, let `V₁` and `V₂` be `Cⁿ` real
vector bundles over `M` with finite-dimensional model fibres, and let `A` be a finite bundle atlas
of `V₁` whose chart domains have closures in the base sets of the preferred trivializations of
`V₂`. For `p > 2`, `1 < q ≤ p` and positive orders `k + 1 ≤ n`, a section `α` of the bundle
`x ↦ V₁ x →L[ℝ] V₂ x` in `W^{k+1,p}` acts on sections `ξ` of `V₁` in `W^{k+1,q}` by
`x ↦ α x (ξ x)`, giving a section of `V₂` in `W^{k+1,q}`, and this is a bounded bilinear map
(`TauCeti.SobolevSection.homMulSuccL`). At `q = p` it is the algebra property of `W^{k+1,p}` for
`p > 2`. The order-zero case, with `L^p` coefficients acting from `W^{1,q}` to `L^q`, is
`TauCeti.SobolevSection.homMulL`.

## The argument

The product lies in `W^{k+1,q}(V₂)` (`TauCeti.SobolevSection.hasAeProducts_hom_succ`): in chart `j`
the readings of both factors lie in the local Sobolev classes on the part of the chart target lying
over the base set of the hom trivialization
(`TauCeti.SobolevSection.memWkpLoc_trivialization_comp_chart_symm`), so the pointwise application
does (`TauCeti.MemWkpLoc.clm_apply_succ`). There it is the reading of the product section
(`TauCeti.FiniteBundleAtlas.coord_hom_apply_of_mem_baseSet`), and this open set contains the closure
of the chart image. Boundedness needs no further estimate: the product of Sobolev sections with
these chart data is bounded by the closed graph theorem (`TauCeti.SectionChartData.bilinOfAeEq`).

## Main definitions

* `TauCeti.SobolevSection.homMulSuccL`: the action of `W^{k+1,p}` hom sections on `W^{k+1,q}`
  sections, as a continuous bilinear map.

## Main results

* `TauCeti.SobolevSection.hasAeProducts_hom_succ`: the products lie in `W^{k+1,q}(V₂)`.
* `TauCeti.SobolevSection.chartValueL_homMulSuccL_ae`,
  `TauCeti.SobolevSection.chartValueL_homMulSuccL_ae_coord`: in every chart the product is the
  pointwise application of the chart data, and of section representatives.
* `TauCeti.SobolevSection.lowerOrderL_homMulSuccL`: the products at consecutive orders commute
  with forgetting the highest weak derivative.
* `TauCeti.SobolevSection.exists_norm_homMulSuccL_apply_le`: `‖α ξ‖ ≤ C ‖α‖ ‖ξ‖`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19 and Appendix C.1.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal NNReal

namespace TauCeti

namespace SobolevSection

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {n : WithTop ℕ∞}
  [IsManifold 𝓘(ℝ, ℂ) n M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle n F₁ V₁ 𝓘(ℝ, ℂ)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle ℝ F₂ V₂] [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle n F₂ V₂ 𝓘(ℝ, ℂ)]
  (A : FiniteBundleAtlas ℂ M F₁ V₁)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] {k : ℕ}

omit [IsManifold 𝓘(ℝ, ℂ) n M] [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
  [ContMDiffVectorBundle n F₁ V₁ 𝓘(ℝ, ℂ)] [ContMDiffVectorBundle n F₂ V₂ 𝓘(ℝ, ℂ)] in
/-- The chart images of `A.ofBaseSet h` lie in those of the hom atlas. -/
private theorem subset_hom (i : Fin A.n) :
    ((A.ofBaseSet h).image i : Set ℂ) ⊆ (A.hom (𝕜 := ℝ) h).image i :=
  SetLike.coe_subset_coe.2
    ((image_ofBaseSet (h := h) i).trans (image_hom (𝕜 := ℝ) (h := h) i).symm).le

omit [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [VectorBundle ℝ F₁ V₁] [NormedSpace ℝ F₂] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [FiniteDimensional ℝ F₂] [VectorBundle ℝ F₂ V₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)] [IsManifold 𝓘(ℝ, ℂ) n M]
  [ContMDiffVectorBundle n F₁ V₁ 𝓘(ℝ, ℂ)] [ContMDiffVectorBundle n F₂ V₂ 𝓘(ℝ, ℂ)] in
/-- The chart images of `A.ofBaseSet h` are those of `A`. -/
private theorem subset_self (i : Fin A.n) :
    ((A.ofBaseSet h).image i : Set ℂ) ⊆ A.image i :=
  SetLike.coe_subset_coe.2 (image_ofBaseSet (h := h) i).le

omit [IsManifold 𝓘(ℝ, ℂ) n M] [ContMDiffVectorBundle n F₁ V₁ 𝓘(ℝ, ℂ)]
  [ContMDiffVectorBundle n F₂ V₂ 𝓘(ℝ, ℂ)] in
/-- The chart product of the hom action is the application of the chart data. -/
private theorem chartProduct_hom (α : SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1))
    (ξ : SobolevSection A volume q (k + 1)) (i : Fin A.n) (z : ℂ) :
    (A.ofBaseSet h).sectionChartData.chartProduct (A.hom (𝕜 := ℝ) h).sectionChartData
      A.sectionChartData (ContinuousLinearMap.id ℝ (F₁ →L[ℝ] F₂)) (fun i ↦ i) (fun i ↦ i)
      α ξ i z = (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL volume p (k + 1) i α z
        (A.sectionChartData.chartValueL volume q (k + 1) i ξ z) := by
  -- The chart indices of the three chart data agree only after unfolding the hom atlas, so
  -- `chartProduct_apply` is instantiated explicitly rather than found by `rw` or `simp`.
  refine (SectionChartData.chartProduct_apply (C₃ := (A.ofBaseSet h).sectionChartData)
    (C₁ := (A.hom (𝕜 := ℝ) h).sectionChartData) (C₂ := A.sectionChartData)
    (b := ContinuousLinearMap.id ℝ (F₁ →L[ℝ] F₂)) (e₁ := fun i ↦ i) (e₂ := fun i ↦ i)
    α ξ i z).trans ?_
  rw [ContinuousLinearMap.id_apply]

/-- In chart `j`, the reading of `x ↦ φ x (s x)` lies in the local class `W^{k+1,q}_loc` on the
part of the chart target over the base set of the hom trivialization, when the readings of `φ`
and `s` are the chart data of Sobolev sections of orders `k + 1` and exponents `p > 2` and
`1 < q ≤ p`. -/
private theorem memWkpLoc_coord_hom_apply (hkn : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {α : SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1)}
    {ξ : SobolevSection A volume q (k + 1)} {φ : ∀ x, V₁ x →L[ℝ] V₂ x} {s : ∀ x, V₁ x}
    (hφ : ∀ i, (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL volume p (k + 1) i α
      =ᵐ[volume.restrict ((A.hom (𝕜 := ℝ) h).image i)] (A.hom (𝕜 := ℝ) h).coord i φ)
    (hs : ∀ i, A.sectionChartData.chartValueL volume q (k + 1) i ξ
      =ᵐ[volume.restrict (A.image i)] A.coord i s) (j : Fin A.n) :
    MemWkpLoc q ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((A.hom (𝕜 := ℝ) h).triv j).baseSet)
      (k + 1) ((A.ofBaseSet h).coord j fun x ↦ φ x (s x)) := by
  have hn : n ≠ 0 := by
    rintro rfl
    norm_num at hkn
  let Ω : Opens ℂ := ⟨_, (A.chart j).isOpen_inter_preimage_symm
    ((A.hom (𝕜 := ℝ) h).triv j).open_baseSet⟩
  have hα : MemWkpLoc p Ω (k + 1) ((A.hom (𝕜 := ℝ) h).coord j φ) := by
    rw [funext ((A.hom (𝕜 := ℝ) h).coord_def j φ)]
    exact memWkpLoc_trivialization_comp_chart_symm α hφ (IsManifold.chart_mem_maximalAtlas _)
      ((A.hom (𝕜 := ℝ) h).triv j) hn hkn
  have hξ : MemWkpLoc q Ω (k + 1) (A.coord j s) := by
    refine (memWkpLoc_trivialization_comp_chart_symm ξ hs (IsManifold.chart_mem_maximalAtlas _)
      (A.triv j) hn hkn).congr_mono (fun y _ ↦ A.coord_def j s y) ?_
    exact inter_subset_inter_right _ (preimage_mono inter_subset_left)
  refine (hα.clm_apply_succ hp hq hqp hξ).congr fun y hy ↦ ?_
  exact (A.coord_hom_apply_of_mem_baseSet h j φ s hy.2.1 hy.2.2).symm

/-- **Products lie in `W^{k+1,q}`.** For `p > 2`, `1 < q ≤ p`, orders `k + 1 ≤ n`, a `W^{k+1,p}`
section `α` of the hom bundle and a `W^{k+1,q}` section `ξ` of `V₁`, some `W^{k+1,q}` section of
`V₂` has, in every chart, chart data equal almost everywhere to the pointwise application of the
chart data of `α` to those of `ξ`. -/
theorem hasAeProducts_hom_succ (hkn : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p) :
    (A.ofBaseSet h).sectionChartData.HasAeProducts (A.hom (𝕜 := ℝ) h).sectionChartData
      A.sectionChartData (ContinuousLinearMap.id ℝ (F₁ →L[ℝ] F₂)) (fun i ↦ i) (fun i ↦ i)
      volume p q q (k + 1) (k + 1) (k + 1) := by
  refine SectionChartData.hasAeProducts_iff.2 fun α ξ ↦ ?_
  obtain ⟨φ, hφ⟩ := exists_section_ae_eq_coord (A.hom (𝕜 := ℝ) h) volume p (k + 1) α
  obtain ⟨s, hs⟩ := exists_section_ae_eq_coord A volume q (k + 1) ξ
  -- The product section is a Sobolev section: its readings are in the local classes on
  -- neighbourhoods of the closures of the chart images.
  obtain ⟨w, hw⟩ := exists_ae_eq_coord_of_memWkpLoc (A := A.ofBaseSet h) (p := q) (k := k + 1)
    (s := fun x ↦ φ x (s x)) fun (j : Fin A.n) ↦ ⟨_, (A.chart j).isOpen_inter_preimage_symm
      ((A.hom (𝕜 := ℝ) h).triv j).open_baseSet, by
        rw [image_ofBaseSet, ← image_hom (𝕜 := ℝ) (h := h)]
        exact (A.hom (𝕜 := ℝ) h).closure_image_subset_target_inter_preimage_baseSet j,
      memWkpLoc_coord_hom_apply A h (by exact_mod_cast hkn) hp hq hqp hφ hs j⟩
  refine ⟨w, fun i ↦ (hw i).trans ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_hom A h i) (hφ i),
    ae_restrict_of_ae_restrict_of_subset (subset_self A h i) (hs i),
    ae_restrict_of_ae_restrict_of_subset (subset_self A h i)
      (ae_restrict_mem (A.image i).isOpen.measurableSet)] with z hφz hsz hz
  -- `ContinuousLinearMap.id` applies as the identity, so the product is `φ z (s z)`.
  exact ((congrArg₂ (fun (f : F₁ →L[ℝ] F₂) (v : F₁) ↦ f v) hφz hsz).trans
    (A.coord_hom_apply h i φ s hz)).symm.trans (chartProduct_hom A h α ξ i z).symm

omit [ContMDiffVectorBundle n F₁ V₁ 𝓘(ℝ, ℂ)] [ContMDiffVectorBundle n F₂ V₂ 𝓘(ℝ, ℂ)] in
private theorem isManifold_one (hkn : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) :
    IsManifold 𝓘(ℝ, ℂ) 1 M :=
  IsManifold.of_le (n := n) ((by exact_mod_cast Nat.le_add_left 1 k : (1 : WithTop ℕ∞) ≤ _).trans
    hkn)

/-- **Multiplication by `W^{k+1,p}` coefficients.** For `p > 2`, `1 < q ≤ p` and orders
`k + 1 ≤ n`, applying `W^{k+1,p}` sections of the bundle `x ↦ V₁ x →L[ℝ] V₂ x` to `W^{k+1,q}`
sections of `V₁` pointwise is a continuous bilinear map into the `W^{k+1,q}` sections of `V₂`. -/
def homMulSuccL (hkn : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) :
    SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1) →L[ℝ]
      SobolevSection A volume q (k + 1) →L[ℝ] SobolevSection (A.ofBaseSet h) volume q (k + 1) :=
  letI := isManifold_one (M := M) hkn
  SectionChartData.bilinOfAeEq (subset_hom A h) (subset_self A h)
    (hasAeProducts_hom_succ A h hkn hp hq hqp)

/-- The chart data of `homMulSuccL α ξ` are the pointwise application of the chart data of `α` to
those of `ξ`. -/
theorem chartValueL_homMulSuccL_ae (hkn : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (α : SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1))
    (ξ : SobolevSection A volume q (k + 1)) (j : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL volume q (k + 1) j
        (homMulSuccL A h hkn hp hq hqp α ξ)
      =ᵐ[volume.restrict (A.image j)] fun z ↦
        (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL volume p (k + 1) j α z
          (A.sectionChartData.chartValueL volume q (k + 1) j ξ z) :=
  letI := isManifold_one (M := M) hkn
  ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (A.image_ofBaseSet j).ge)
    ((SectionChartData.chartValueL_bilinOfAeEq_ae (subset_hom A h) (subset_self A h)
      (hasAeProducts_hom_succ A h hkn hp hq hqp) α ξ j).trans
        (Eventually.of_forall fun z ↦ chartProduct_hom A h α ξ j z))

/-- **Sections.** If the chart data of `α` and `ξ` are the readings of sections `φ` and `s`, those
of `homMulSuccL α ξ` are the readings of `x ↦ φ x (s x)`. -/
theorem chartValueL_homMulSuccL_ae_coord (hkn : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {α : SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1)}
    {ξ : SobolevSection A volume q (k + 1)} {φ : ∀ x, V₁ x →L[ℝ] V₂ x} {s : ∀ x, V₁ x}
    {j : Fin A.n}
    (hφ : (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL volume p (k + 1) j α
      =ᵐ[volume.restrict (A.image j)] (A.hom (𝕜 := ℝ) h).coord j φ)
    (hs : A.sectionChartData.chartValueL volume q (k + 1) j ξ
      =ᵐ[volume.restrict (A.image j)] A.coord j s) :
    (A.ofBaseSet h).sectionChartData.chartValueL volume q (k + 1) j
        (homMulSuccL A h hkn hp hq hqp α ξ)
      =ᵐ[volume.restrict (A.image j)] (A.ofBaseSet h).coord j (fun x ↦ φ x (s x)) := by
  filter_upwards [chartValueL_homMulSuccL_ae A h hkn hp hq hqp α ξ j, hφ, hs,
    ae_restrict_mem (A.image j).isOpen.measurableSet] with z hz hφz hsz hzj
  rw [hz, hφz, hsz, A.coord_hom_apply h j φ s hzj]

/-- **Compatibility with the order.** Forgetting the highest weak derivative of the product of a
`W^{k+2,p}` coefficient and a `W^{k+2,q}` section gives the product at order `k + 1` of the
coefficient and the section regarded as one order rougher. -/
theorem lowerOrderL_homMulSuccL (hkn : ((k + 1 + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (α : SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1 + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) :
    (A.ofBaseSet h).sectionChartData.lowerOrderL volume q (k + 1)
        (homMulSuccL A h hkn hp hq hqp α ξ) =
      homMulSuccL A h
        ((Nat.cast_le.2 (Nat.le_succ (k + 1)) : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ _).trans hkn) hp hq hqp
        ((A.hom (𝕜 := ℝ) h).sectionChartData.lowerOrderL volume p (k + 1) α)
        (A.sectionChartData.lowerOrderL volume q (k + 1) ξ) := by
  refine SectionChartData.eq_of_chartValueL_ae_eq fun j ↦ ?_
  rw [SectionChartData.chartValueL_coe_lowerOrderL]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_self A h j)
      (chartValueL_homMulSuccL_ae A h hkn hp hq hqp α ξ j),
    ae_restrict_of_ae_restrict_of_subset (subset_self A h j)
      (chartValueL_homMulSuccL_ae (n := n) A h _ hp hq hqp _ _ j)] with z h₁ h₂
  -- The chart index lives in `Fin (A.ofBaseSet h).sectionChartData.n`, so the lowering lemmas are
  -- instantiated explicitly at the hom and section chart data.
  rw [h₁, h₂, (A.hom (𝕜 := ℝ) h).sectionChartData.chartValueL_coe_lowerOrderL volume p (k + 1) α j,
    A.sectionChartData.chartValueL_coe_lowerOrderL volume q (k + 1) ξ j]

/-- **Bound.** There is a constant `C` with `‖homMulSuccL α ξ‖ ≤ C ‖α‖ ‖ξ‖`. -/
theorem exists_norm_homMulSuccL_apply_le (hkn : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1))
      (ξ : SobolevSection A volume q (k + 1)),
        ‖homMulSuccL A h hkn hp hq hqp α ξ‖ ≤ C * ‖α‖ * ‖ξ‖ := by
  -- The operator norm uses the norms of the three Sobolev spaces of sections.
  let _ : NormedAddCommGroup (SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1)) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection (A.hom (𝕜 := ℝ) h) volume p (k + 1)) := inferInstance
  let _ : NormedAddCommGroup (SobolevSection A volume q (k + 1)) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection A volume q (k + 1)) := inferInstance
  let _ : NormedAddCommGroup (SobolevSection (A.ofBaseSet h) volume q (k + 1)) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection (A.ofBaseSet h) volume q (k + 1)) := inferInstance
  let _ : NormedAddCommGroup (SobolevSection A volume q (k + 1) →L[ℝ]
    SobolevSection (A.ofBaseSet h) volume q (k + 1)) := inferInstance
  let _ : NormedSpace ℝ (SobolevSection A volume q (k + 1) →L[ℝ]
    SobolevSection (A.ofBaseSet h) volume q (k + 1)) := inferInstance
  exact ⟨‖homMulSuccL A h hkn hp hq hqp‖, norm_nonneg _, (homMulSuccL A h hkn hp hq hqp).le_opNorm₂⟩

end SobolevSection

end TauCeti
