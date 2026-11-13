/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Wkp
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Localizations of Sobolev sections over surfaces

Let `M` be a manifold without boundary modelled on `ℂ`, let `V → M` be a real vector bundle with
finite-dimensional model fibre `F`, and let `A` be a finite bundle atlas. This file compares the
Sobolev space `W^{k,p}(V)` of `TauCeti.SobolevSection A volume p k` with the local Sobolev classes
`TauCeti.MemWkpLoc` of planar maps: an element of `W^{k,p}(V)` is read in chart `i` and the
trivialization of chart `i` as a map in the local class `MemWkpLoc p (A.image i) k`, and conversely.

An element `w` of `W^{k,p}(V)` consists of the components of a section `s`
(`TauCeti.SectionChartData.exists_section`). In chart `i` the components of `A.coord i s` in the
basis `Module.finBasis ℝ F` are, almost everywhere on `A.image i`, the values of the scalar Sobolev
functions `w i j ∈ W^{k,p}(A.image i)`. Restricting these to relatively compact open subsets of
`A.image i` and applying the comparison `TauCeti.memWkpLoc_iff_forall_wkp` componentwise, through
the coordinate criterion `Module.Basis.memWkpLoc_iff`, shows that `A.coord i s` lies in
`MemWkpLoc p (A.image i) k` (`TauCeti.SobolevSection.memWkpLoc_coord`).

Conversely, membership in `MemWkpLoc` on the open image `A.image i` alone does not control the
behaviour of a section near the boundary of `A.image i`, so it does not give an element of
`W^{k,p}(A.image i)`. If instead the chart expression `A.coord i s` lies in `MemWkpLoc p O k` for
an open neighbourhood `O` of the compact closure of `A.image i`, for every chart `i`, then its
components restrict to elements of `W^{k,p}(A.image i)` (`TauCeti.MemWkpLoc.exists_wkp`) and these
form an element of `W^{k,p}(V)` with section `s`
(`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc`, through
`TauCeti.SectionChartData.chartValueL_ae_eq_coord`). That element is unique
(`TauCeti.SobolevSection.eq_of_ae_eq_coord`). The chart expressions of a `Cᵏ` section satisfy this
hypothesis for every exponent, as do their expressions in every chart of the maximal atlas and
every trivialization of the trivialization atlas
(`TauCeti.memWkpLoc_trivialization_comp_chart_symm_of_contMDiff`); the corresponding element of
`W^{k,p}(V)` is `TauCeti.SobolevSection.ofContMDiffSection`.

The localizations of elements of `W^{k,p}(V)` are taken here in the charts and trivializations of
the atlas `A`. For orders `k ≤ n` with `k ≤ 1` or `p < ∞`, localization in every chart of the
maximal `Cⁿ` atlas, such as an isothermal chart of a Riemann surface, and every trivialization of
the trivialization atlas is
`TauCeti.SobolevSection.memWkpLoc_trivialization_comp_chart_symm`, with converse
`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm`, in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart`.

## Main results

* `TauCeti.SobolevSection.memWkpLoc_coord`: the chart expressions of an element of `W^{k,p}(V)`
  are in the local classes `MemWkpLoc`.
* `TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc`: a section whose chart expressions are
  in `MemWkpLoc` on neighbourhoods of the closures of the chart images defines an element of
  `W^{k,p}(V)`.
* `TauCeti.memWkpLoc_trivialization_comp_chart_symm_of_contMDiff`: the expressions of a `Cᵏ`
  section in every chart and trivialization are in `MemWkpLoc`, up to the boundary of the chart
  images for the charts of `A`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal

namespace TauCeti

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ℂ M F V)

/-- **`Cᵏ` sections are locally Sobolev in every chart and trivialization.** The expression in a
chart `φ` of the maximal `Cᵏ` atlas of `M` and a trivialization `e` of the bundle's trivialization
atlas of a `Cᵏ` section of a `Cᵏ` vector bundle lies in `MemWkpLoc p U k` for every exponent `p`,
on the open set `U` of points of `φ.target` lying over `e.baseSet`. For the charts and
trivializations of `A`, the expression is `A.coord i s` and `U` contains the closure of
`A.image i` (`TauCeti.FiniteBundleAtlas.closure_image_subset_chart_image_closure_dom`). -/
theorem memWkpLoc_trivialization_comp_chart_symm_of_contMDiff {k : ℕ}
    [ContMDiffVectorBundle k F V 𝓘(ℝ, ℂ)] {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) k fun x ↦ TotalSpace.mk' F x (s x))
    {φ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) k M)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (p : ℝ≥0∞) :
    MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' e.baseSet) k fun y ↦ (e ⟨φ.symm y, s (φ.symm y)⟩).2 :=
  (contDiffOn_trivialization_comp_chart_symm_of_contMDiff hs hφ e).memWkpLoc
    (Ω := ⟨_, φ.isOpen_inter_preimage_symm e.open_baseSet⟩) subset_rfl

namespace SobolevSection

variable {A} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Localization.** If the chart data of an element `w` of `W^{k,p}(V)` are the coordinates of
the section `s`, then in every chart `i` the chart expression `A.coord i s` lies in the local
Sobolev class `MemWkpLoc p (A.image i) k`. -/
theorem memWkpLoc_coord (w : SobolevSection A volume p k) {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) : MemWkpLoc p (A.image i) k (A.coord i s) := by
  refine (finBasis ℝ F).memWkpLoc_iff.2 fun j ↦
    memWkpLoc_of_forall_wkp (Ω := A.image i) fun W _ hWΩ ↦ ?_
  have hW : W ≤ A.image i := SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)
  have hcs := A.sectionChartData_coord_ae_eq volume i s
  have hrepr := (SectionChartData.value_ae_eq_repr_coord ((hs i).trans hcs.symm) j).trans
    (hcs.fun_comp fun v ↦ (finBasis ℝ F).repr v j)
  exact ⟨Wkp.restrictL hW k ((w : A.sectionChartData.SobolevData volume p k) i j),
    (Wkp.value_restrictL_ae hW k _).trans (ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.2 hW) hrepr)⟩

/-- **Sobolev sections from local classes.** Let `s` be a section of `V` whose chart expression
`A.coord i s` lies, for every chart `i`, in the local Sobolev class `MemWkpLoc p O k` on some open
neighbourhood `O` of the closure of `A.image i`. Then `s` defines an element of `W^{k,p}(V)`: there
is an element whose chart data are the coordinates of `s`. It is unique by
`TauCeti.SobolevSection.eq_of_ae_eq_coord`. -/
theorem exists_ae_eq_coord_of_memWkpLoc {s : ∀ x, V x}
    (hs : ∀ i, ∃ O : Set ℂ, IsOpen O ∧ closure (A.image i : Set ℂ) ⊆ O ∧
      MemWkpLoc p O k (A.coord i s)) :
    ∃ w : SobolevSection A volume p k,
      ∀ i, A.sectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.image i)] A.coord i s := by
  have hv (i : Fin A.n) (j : Fin (finrank ℝ F)) : ∃ v : Wkp volume (A.image i) p k,
      (Wkp.value k v : ℂ → ℝ) =ᵐ[volume.restrict (A.image i)]
        fun y ↦ (finBasis ℝ F).coord j (A.sectionChartData.coord i s y) := by
    obtain ⟨O, hO, hcl, hsO⟩ := hs i
    obtain ⟨v, hv⟩ := ((finBasis ℝ F).memWkpLoc_iff.1 hsO j).exists_wkp (Ω := ⟨O, hO⟩)
      (A.isCompact_closure_image i) hcl
    refine ⟨v, hv.trans ?_⟩
    filter_upwards [A.sectionChartData_coord_ae_eq volume i s] with y hy
    rw [hy, Basis.coord_apply]
  choose v hv using hv
  have hcoord (i : Fin A.n) : A.sectionChartData.chartValueL volume p k i v
      =ᵐ[volume.restrict (A.image i)] A.sectionChartData.coord i s :=
    A.sectionChartData.chartValueL_ae_eq_coord volume p k (hv i)
  exact ⟨⟨v, (A.sectionChartData.mem_sobolevSections_iff volume p k).2 ⟨s, hcoord⟩⟩,
    fun i ↦ (hcoord i).trans (A.sectionChartData_coord_ae_eq volume i s)⟩

end SobolevSection

end TauCeti
