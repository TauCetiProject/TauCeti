/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Local
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Sobolev.ChartTransition
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.SmoothCoefficients

/-!
# Localizations of Sobolev sections in arbitrary charts and trivializations

Let `M` be a `C¹` manifold without boundary modelled on `ℂ`, let `V → M` be a `C¹` real vector
bundle with finite-dimensional model fibre `F`, and let `A` be a finite bundle atlas. An element of
the Sobolev space `W^{k,p}(V)` of `TauCeti.SobolevSection A volume p k` is read in the charts and
trivializations of `A` as maps in the local Sobolev classes `TauCeti.MemWkpLoc`
(`TauCeti.SobolevSection.memWkpLoc_coord`). This file shows, for orders `k ≤ 1`, that the same holds
in every chart `φ` of the maximal `C¹` atlas of `M` and every trivialization `e` of the bundle's
trivialization atlas: the expression `y ↦ (e ⟨φ.symm y, s (φ.symm y)⟩).2` of the section `s`
lies in `MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' e.baseSet) k`. Conversely, a section whose expressions
in a family of such charts and trivializations are in the local classes on open sets covering `M`
defines an element of `W^{k,p}(V)`. Isothermal charts of a Riemann surface, being holomorphic
charts, are a special case. For `Cⁿ` sections the localization holds at every order `n`
(`TauCeti.memWkpLoc_trivialization_comp_chart_symm_of_contMDiff`).

On the part of `φ.target` lying over the domain of chart `i` of `A`, the expression of `s` in
`(φ, e)` is the coordinate change `e.coordChangeL` of the bundle applied to `A.coord i s` composed
with the chart transition `A.chart i ∘ φ.symm`. The chart transition is a `C¹` diffeomorphism
between open planar sets, so it preserves the local classes of order at most one
(`TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`), and the coordinate change is a `C¹`
field of linear maps, which preserves them as well (`TauCeti.MemWkpLoc.contDiffOn_clm_apply`).
Both steps need the order `k` to be at most one: the planar change of variables is only available
for `k ≤ 1`, and a field of linear maps with `C¹` coefficients preserves the local classes only up
to order one. The pieces are glued over the charts of `A` by the locality of the local classes
(`TauCeti.memWkpLoc_iff_forall_inter`).

## Main results

* `TauCeti.MemWkpLoc.trivialization_comp_chart_symm`: changes of chart and trivialization
  preserve the local classes of order at most one of the expressions of a section.
* `TauCeti.memWkpLoc_trivialization_comp_chart_symm_of_cover`: the expression of a section in a
  chart and trivialization is in the local class if its expressions in a covering family are.
* `TauCeti.SobolevSection.memWkpLoc_trivialization_comp_chart_symm`: the expressions of an element
  of `W^{k,p}(V)` in arbitrary charts and trivializations are in the local classes.
* `TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm`: a
  section whose expressions in a covering family of charts and trivializations are in the local
  classes defines an element of `W^{k,p}(V)`.

## Checks

* `TauCeti.SobolevSection.not_ae_eq_indicator_re_pos`: no component of an element of `W^{1,p}(V)`,
  read in any chart and trivialization, is almost everywhere equal to the indicator of the right
  half-plane on a domain meeting the imaginary axis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle MeasureTheory Set TopologicalSpace
open scoped Manifold ENNReal

namespace TauCeti

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {p : ℝ≥0∞} {k : ℕ}

variable [ContMDiffVectorBundle 1 F V 𝓘(ℝ, ℂ)]

/-- **Changes of chart and trivialization preserve the local classes of order at most one.** Let
`φ`, `ψ` be charts of the maximal `C¹` atlas of `M` and `e`, `e'` trivializations of the bundle's
trivialization atlas. If the expression `z ↦ (e' ⟨ψ.symm z, s (ψ.symm z)⟩).2` of a section `s` in
`(ψ, e')` lies in `MemWkpLoc p U k` on an open set `U`, with `k ≤ 1`, then its expression in
`(φ, e)` lies in the local class on the open set of points of `φ.target` lying over
`e.baseSet ∩ e'.baseSet ∩ (ψ.source ∩ ψ ⁻¹' U)`. -/
theorem MemWkpLoc.trivialization_comp_chart_symm (hk : k ≤ 1)
    {φ ψ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M) (e e' : Trivialization F (π F V))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] {s : ∀ x, V x} {U : Set ℂ}
    (hU : IsOpen U) (h : MemWkpLoc p U k fun z ↦ (e' ⟨ψ.symm z, s (ψ.symm z)⟩).2) :
    MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (e.baseSet ∩ e'.baseSet ∩ (ψ.source ∩ ψ ⁻¹' U))) k
      fun y ↦ (e ⟨φ.symm y, s (φ.symm y)⟩).2 := by
  have hW : IsOpen (φ.target ∩ φ.symm ⁻¹' (e.baseSet ∩ e'.baseSet ∩ (ψ.source ∩ ψ ⁻¹' U))) :=
    φ.isOpen_inter_preimage_symm ((e.open_baseSet.inter e'.open_baseSet).inter
      (ψ.continuousOn.isOpen_inter_preimage ψ.open_source hU))
  -- The expression in `(ψ, e')` composed with the chart transition.
  have h₁ := (h.comp_symm_trans_of_mem_maximalAtlas hk hφ hψ).mono
    (V := φ.target ∩ φ.symm ⁻¹' (e.baseSet ∩ e'.baseSet ∩ (ψ.source ∩ ψ ⁻¹' U)))
    fun y hy ↦ ⟨⟨hy.1, hy.2.2.1⟩, hy.2.2.2⟩
  -- The coordinate change from `e'` to `e`, read in the chart `φ`, is a `C¹` field of linear maps.
  have hT : ContDiffOn ℝ 1 (fun y ↦ (e'.coordChangeL ℝ e (φ.symm y) : F →L[ℝ] F))
      (φ.target ∩ φ.symm ⁻¹' (e'.baseSet ∩ e.baseSet)) :=
    (contMDiffOn_coordChangeL e' e).contDiffOn_comp_symm_of_mem_maximalAtlas hφ
  have h₂ := h₁.contDiffOn_clm_apply (Ω := ⟨_, φ.isOpen_inter_preimage_symm
    (e'.open_baseSet.inter e.open_baseSet)⟩) hT (by exact_mod_cast hk)
    fun y hy ↦ ⟨hy.1, hy.2.1.2, hy.2.1.1⟩
  -- Pointwise, the coordinate change maps the expression in `e'` to the expression in `e`.
  refine h₂.congr_ae (ae_restrict_of_forall_mem hW.measurableSet fun y hy ↦ ?_)
  -- `rw`, not `simp`: the base point also occurs in the type of the section value.
  beta_reduce
  rw [ψ.left_inv hy.2.2.1]
  simp [Trivialization.coordChangeL_apply, hy.2.1.1, hy.2.1.2]

/-- **Gluing localizations over a cover.** Let `φ` be a chart of the maximal `C¹` atlas of `M` and
`e` a trivialization of the bundle's trivialization atlas. Let `(ψ j, e' j)` be a family of such
charts and trivializations and `U j` open sets such that every point `x` of `φ.source ∩ e.baseSet`
lies in the source of some `ψ j` and the base set of `e' j` with `ψ j x ∈ U j`. If the expression of
a section `s` in `(ψ j, e' j)` lies in `MemWkpLoc p (U j) k` for every `j`, with `k ≤ 1`, then its
expression in `(φ, e)` lies in `MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' e.baseSet) k`. -/
theorem memWkpLoc_trivialization_comp_chart_symm_of_cover (hk : k ≤ 1)
    {φ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] {ι : Type*}
    (ψ : ι → OpenPartialHomeomorph M ℂ) (hψ : ∀ j, ψ j ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (e' : ι → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e' j)] (U : ι → Set ℂ)
    (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x ∈ φ.source ∩ e.baseSet,
      ∃ j, x ∈ (ψ j).source ∧ x ∈ (e' j).baseSet ∧ ψ j x ∈ U j) {s : ∀ x, V x}
    (hs : ∀ j, MemWkpLoc p (U j) k fun z ↦ (e' j ⟨(ψ j).symm z, s ((ψ j).symm z)⟩).2) :
    MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' e.baseSet) k fun y ↦ (e ⟨φ.symm y, s (φ.symm y)⟩).2 := by
  -- The part of the chart `φ` lying over the domain of `(ψ j, e' j)`.
  let O (j : ι) : Opens ℂ := ⟨φ.target ∩ φ.symm ⁻¹' (e.baseSet ∩ (e' j).baseSet ∩
      ((ψ j).source ∩ ψ j ⁻¹' U j)),
    φ.isOpen_inter_preimage_symm ((e.open_baseSet.inter (e' j).open_baseSet).inter
      ((ψ j).continuousOn.isOpen_inter_preimage (ψ j).open_source (hU j)))⟩
  refine (memWkpLoc_iff_forall_inter O fun y hy ↦ ?_).2 fun j ↦
    ((hs j).trivialization_comp_chart_symm hk hφ (hψ j) e (e' j) (hU j)).mono inter_subset_right
  obtain ⟨j, hj⟩ := hcover (φ.symm y) ⟨φ.map_target hy.1, hy.2⟩
  exact mem_iUnion.2 ⟨j, hy.1, ⟨hy.2, hj.2.1⟩, hj.1, hj.2.2⟩

namespace SobolevSection

variable [IsManifold 𝓘(ℝ, ℂ) 1 M] {A : FiniteBundleAtlas ℂ M F V} [Fact (1 ≤ p)]

/-- **Localization in arbitrary charts and trivializations.** Let `w` be an element of
`W^{k,p}(V)`, `k ≤ 1`, whose chart data are the coordinates of the section `s`. For every chart `φ`
of the maximal `C¹` atlas of `M` and every trivialization `e` of the bundle's trivialization atlas,
the expression `y ↦ (e ⟨φ.symm y, s (φ.symm y)⟩).2` of `s` lies in the local Sobolev class
`MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' e.baseSet) k`. For the charts and trivializations of `A` this
is `TauCeti.SobolevSection.memWkpLoc_coord`. -/
theorem memWkpLoc_trivialization_comp_chart_symm (hk : k ≤ 1) (w : SobolevSection A volume p k)
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    {φ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] :
    MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' e.baseSet) k fun y ↦ (e ⟨φ.symm y, s (φ.symm y)⟩).2 :=
  memWkpLoc_trivialization_comp_chart_symm_of_cover hk hφ e A.chart
    (fun _ ↦ IsManifold.chart_mem_maximalAtlas _) A.triv (fun i ↦ A.image i)
    (fun i ↦ (A.image i).isOpen)
    (fun x _ ↦ let ⟨i, hi⟩ := A.exists_mem_dom x
      ⟨i, A.dom_subset_chart_source i hi, A.dom_subset_baseSet i hi, A.mem_image.2 ⟨_, hi, rfl⟩⟩)
    fun i ↦ by simpa only [funext (A.coord_def i s)] using memWkpLoc_coord w hs i

/-- **Sobolev sections from localizations in arbitrary charts.** Let `(φ j, e j)` be a family of
charts of the maximal `C¹` atlas of `M` and trivializations of the bundle's trivialization atlas,
and let `U j` be open sets such that every point `x` of `M` lies in the source of some `φ j` and the
base set of `e j` with `φ j x ∈ U j`. If the expression of a section `s` in `(φ j, e j)` lies in
`MemWkpLoc p (U j) k` for every `j`, with `k ≤ 1`, then `s` defines an element of `W^{k,p}(V)`:
there is an element whose chart data are the coordinates of `s`. It is unique by
`TauCeti.SobolevSection.eq_of_ae_eq_coord`. -/
theorem exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm (hk : k ≤ 1) {ι : Type*}
    (φ : ι → OpenPartialHomeomorph M ℂ) (hφ : ∀ j, φ j ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (e : ι → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e j)] (U : ι → Set ℂ)
    (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, x ∈ (φ j).source ∧ x ∈ (e j).baseSet ∧ φ j x ∈ U j) {s : ∀ x, V x}
    (hs : ∀ j, MemWkpLoc p (U j) k fun z ↦ (e j ⟨(φ j).symm z, s ((φ j).symm z)⟩).2) :
    ∃ w : SobolevSection A volume p k,
      ∀ i, A.sectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.image i)] A.coord i s := by
  refine exists_ae_eq_coord_of_memWkpLoc fun i ↦ ⟨_, (A.chart i).isOpen_inter_preimage_symm
    (A.triv i).open_baseSet, (A.closure_image_subset_chart_image_closure_dom i).trans
      (A.chart_image_closure_dom_subset i), ?_⟩
  rw [funext (A.coord_def i s)]
  exact memWkpLoc_trivialization_comp_chart_symm_of_cover hk (IsManifold.chart_mem_maximalAtlas _)
    (A.triv i) φ hφ e U hU (fun x _ ↦ hcover x) hs

/-- **Not the half-plane indicator.** Let `w` be an element of `W^{1,p}(V)` whose chart data are the
coordinates of the section `s`. In no chart `φ` of the maximal `C¹` atlas of `M` and trivialization
`e` of the bundle's trivialization atlas is a component `ℓ` of the expression of `s` almost
everywhere equal to the indicator of the right half-plane, provided the domain of the expression
meets the imaginary axis, across which that indicator jumps. -/
theorem not_ae_eq_indicator_re_pos (w : SobolevSection A volume p 1) {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    {φ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (ℓ : F →L[ℝ] ℝ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ φ.target ∩ φ.symm ⁻¹' e.baseSet) (hre : z₀.re = 0) :
    ¬ (fun y ↦ ℓ (e ⟨φ.symm y, s (φ.symm y)⟩).2) =ᵐ[volume.restrict
        (φ.target ∩ φ.symm ⁻¹' e.baseSet)] {z : ℂ | 0 < z.re}.indicator fun _ ↦ (1 : ℝ) := fun h ↦
  not_memWkpLoc_indicator_re_pos (k := 0)
    ((φ.isOpen_inter_preimage_symm e.open_baseSet).interior_eq.symm ▸ hz₀) hre
    (((memWkpLoc_trivialization_comp_chart_symm le_rfl w hs hφ e).clm_comp ℓ).congr_ae h)

end SobolevSection

end TauCeti
