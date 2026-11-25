/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.ChartData
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Measure

/-!
# Independence of the Sobolev space of sections from the bundle atlas

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real inner product
space `E`, let `V → M` be a real vector bundle with finite-dimensional model fibre `F`, and let `A`,
`A'` be two finite bundle atlases. The Sobolev spaces `W^{k,p}(V)` of
`TauCeti.SobolevSection A μ p k` and `TauCeti.SobolevSection A' μ p k` consist of tuples of
chartwise components of sections in the charts of `A` and of `A'`. This file shows that, whenever
every section with `W^{k,p}` components in the charts of `A` also has `W^{k,p}` components in the
charts of `A'` (`TauCeti.SobolevSection.TransfersTo A A' μ p k`), sending an element to the element
of the other atlas with the same section is a continuous linear map
(`TauCeti.SobolevSection.changeAtlas`). When the property holds in both directions the two spaces
are isomorphic Banach spaces (`TauCeti.SobolevSection.atlasEquiv`), so their norms are equivalent.

The construction is the change of chart data `TauCeti.SectionChartData.changeAtlas` of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.ChartData`, which also serves bases with
boundary. What it needs here is that the chart data of `A'` are read off from those of `A`
(`TauCeti.FiniteBundleAtlas.readsFrom_sectionChartData`): on the part of the image of a chart of
`A'` lying over the domain of a chart of `A`, the reading of a section is the coordinate change of
the bundle applied to its reading in the chart of `A`, at the chart transition, which carries null
sets to null sets (`TauCeti.FiniteBundleAtlas.ae_restrict_image_chart_symm`).

For surfaces, `M` modelled on `ℂ` with the Lebesgue measure, and a `Cⁿ` bundle, `n ≠ 0`, the
transfer property holds at every order `k ≤ n`
(`TauCeti.SobolevSection.transfersTo`), by the localization of Sobolev sections in arbitrary charts
and trivializations of `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic`. For a smooth
(`C^∞`) bundle over a smooth Hausdorff manifold modelled on any finite-dimensional real inner
product space, the transfer property holds between any two finite bundle atlases, for every order
`k` and every `1 ≤ p ≤ ∞` (`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`, in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Transfer`).

## Main definitions

* `TauCeti.SobolevSection.TransfersTo A A' μ p k`: every section with `W^{k,p}` components in the
  charts of `A` has `W^{k,p}` components in the charts of `A'`.
* `TauCeti.SobolevSection.changeAtlas`: the continuous linear map between the Sobolev spaces of two
  atlases sending an element to the element with the same section.
* `TauCeti.SobolevSection.atlasEquiv`: the isomorphism of Banach spaces between them.

## Main results

* `TauCeti.SobolevSection.chartValueL_changeAtlas_ae`: the chart data of `changeAtlas h w` are the
  readings in `A'` of any section of `w`.
* `TauCeti.SobolevSection.exists_norm_changeAtlas_le`: when sections transfer in both directions the
  norms of the two atlases are equivalent.
* `TauCeti.SobolevSection.transfersTo`: the transfer property for `Cⁿ` bundles over surfaces at
  orders `k ≤ n`.
* `TauCeti.SobolevSection.exists_norm_changeAtlas_le_of_surface`: for such bundles and orders the
  norms of two finite bundle atlases are equivalent.

The transfer property for smooth bundles in every dimension,
`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`, is proved in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Transfer`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections).
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped Manifold Topology ENNReal

universe u

namespace TauCeti

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A A' : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ F] in
/-- The chart data of a finite bundle atlas are read off from those of any other: on the part of
the image of chart `i'` of `A'` lying over the domain of chart `i` of `A`, the reading in chart
`i'` is the coordinate change of the bundle applied to the reading in chart `i` at the chart
transition, which carries null sets to null sets. -/
theorem FiniteBundleAtlas.readsFrom_sectionChartData [IsManifold 𝓘(ℝ, E) 1 M] :
    A.sectionChartData.ReadsFrom A'.sectionChartData μ :=
  .intro (fun i i' ↦ {y | (A'.chart i').symm y ∈ A.dom i})
    (fun i i' y ↦ A.chart i ((A'.chart i').symm y))
    (fun i i' y ↦ (A.triv i).coordChangeL ℝ (A'.triv i') ((A'.chart i').symm y))
    (fun _ ↦ ae_of_all _ fun _ ↦ A.exists_mem_dom _)
    (fun _ i' _ h ↦ A.ae_restrict_image_chart_symm A' i' h)
    fun i i' s ↦ by
      filter_upwards [ae_restrict_mem (A'.image i').isOpen.measurableSet] with y hyU hdom
      rw [A'.sectionChartData_coord_of_mem s hyU,
        A.sectionChartData_coord_of_mem s (A.mem_image.2 ⟨_, hdom, rfl⟩)]
      exact A.coord_eq_coordChangeL_coord A' s (A'.dom_subset_baseSet i' (A'.symm_mem_dom hyU))
        hdom

namespace SobolevSection

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Transfer of Sobolev sections between atlases.** Every section whose chart data in the charts
of `A` are those of an element of `W^{k,p}(V)` for `A` also has chart data in the charts of `A'`
that are those of an element of `W^{k,p}(V)` for `A'` (`TauCeti.SobolevSection.transfersTo_iff`).
For `Cⁿ` bundles over surfaces this holds at orders `k ≤ n` (`TauCeti.SobolevSection.transfersTo`).
For smooth bundles over smooth Hausdorff manifolds in every dimension it holds at every order and
every `1 ≤ p ≤ ∞` (`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`). -/
abbrev TransfersTo : Prop :=
  A.sectionChartData.TransfersTo A'.sectionChartData μ p k

variable {A A' μ p k}

/-- Unfolding `TauCeti.SobolevSection.TransfersTo` in terms of the readings `A.coord i s`, for
establishing and using the transfer property outside this file. -/
theorem transfersTo_iff : TransfersTo A A' μ p k ↔
    ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
      (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
        ∃ w' : SobolevSection A' μ p k,
          ∀ i', A'.sectionChartData.chartValueL μ p k i' w' =ᵐ[μ.restrict (A'.image i')]
            A'.coord i' s :=
  SectionChartData.transfersTo_iff.trans <| forall₂_congr fun _ _ ↦
    imp_congr (forall_congr' fun _ ↦ A.ae_eq_sectionChartData_coord_iff μ)
      (exists_congr fun _ ↦ forall_congr' fun _ ↦ A'.ae_eq_sectionChartData_coord_iff μ)

theorem transfersTo_refl : TransfersTo A A μ p k :=
  SectionChartData.transfersTo_refl

theorem TransfersTo.trans {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) : TransfersTo A A'' μ p k :=
  SectionChartData.TransfersTo.trans h h'

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- **Change of atlas.** Given the transfer property `h` from `A` to `A'`, the continuous linear map
from `W^{k,p}(V)` for `A` to `W^{k,p}(V)` for `A'` sending an element to the element whose chart
data are the readings of the same section (`TauCeti.SobolevSection.chartValueL_changeAtlas_ae`).
It is `TauCeti.SectionChartData.changeAtlas` for the chart data of the two atlases. -/
def changeAtlas (h : TransfersTo A A' μ p k) :
    SobolevSection A μ p k →L[ℝ] SobolevSection A' μ p k :=
  SectionChartData.changeAtlas (A.readsFrom_sectionChartData A' μ) h

/-- The chart data of `changeAtlas h w` are the readings in the charts of `A'` of any section whose
readings in the charts of `A` are the chart data of `w`. -/
theorem chartValueL_changeAtlas_ae (h : TransfersTo A A' μ p k) {w : SobolevSection A μ p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i' : Fin A'.n) :
    A'.sectionChartData.chartValueL μ p k i' (changeAtlas h w)
      =ᵐ[μ.restrict (A'.image i')] A'.coord i' s :=
  (A'.ae_eq_sectionChartData_coord_iff μ).1 <| SectionChartData.chartValueL_changeAtlas_ae _ h
    (fun i ↦ (A.ae_eq_sectionChartData_coord_iff μ).2 (hs i)) i'

/-- **Identification of the change of atlas.** An element `w'` for `A'` whose chart data are the
readings in the charts of `A'` of a section of `w` is the image of `w`. -/
theorem changeAtlas_eq_of_ae_eq_coord (h : TransfersTo A A' μ p k) {w : SobolevSection A μ p k}
    {w' : SobolevSection A' μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (hs' : ∀ i', A'.sectionChartData.chartValueL μ p k i' w'
      =ᵐ[μ.restrict (A'.image i')] A'.coord i' s) :
    changeAtlas h w = w' :=
  eq_of_ae_eq_coord (chartValueL_changeAtlas_ae h hs) hs'

theorem changeAtlas_refl_apply (w : SobolevSection A μ p k) :
    changeAtlas (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) w = w :=
  SectionChartData.changeAtlas_refl_apply w

@[simp]
theorem changeAtlas_refl :
    changeAtlas (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) =
      ContinuousLinearMap.id ℝ _ :=
  SectionChartData.changeAtlas_refl

@[simp]
theorem changeAtlas_changeAtlas {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) (w : SobolevSection A μ p k) :
    changeAtlas h' (changeAtlas h w) = changeAtlas (h.trans h') w :=
  SectionChartData.changeAtlas_changeAtlas _ _ _ h h' w

@[simp]
theorem changeAtlas_comp {A'' : FiniteBundleAtlas E M F V} (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A'' μ p k) :
    (changeAtlas h').comp (changeAtlas h) = changeAtlas (h.trans h') :=
  SectionChartData.changeAtlas_comp _ _ _ h h'

/-- The change of atlas is injective: two sections with the same readings almost everywhere in the
charts of `A'` have the same readings almost everywhere in the charts of `A`. -/
theorem changeAtlas_injective (h : TransfersTo A A' μ p k) :
    Function.Injective (changeAtlas h) :=
  SectionChartData.changeAtlas_injective _ (A'.readsFrom_sectionChartData A μ) h

/-- The change of atlas commutes with forgetting the highest derivative. -/
theorem lowerOrderL_changeAtlas (h : TransfersTo A A' μ p (k + 1)) (h₀ : TransfersTo A A' μ p k)
    (w : SobolevSection A μ p (k + 1)) :
    A'.sectionChartData.lowerOrderL μ p k (changeAtlas h w) =
      changeAtlas h₀ (A.sectionChartData.lowerOrderL μ p k w) :=
  SectionChartData.lowerOrderL_changeAtlas _ h h₀ w

/-- The change of atlas sends the Sobolev section of a `Cᵏ` section for `A` to the Sobolev section
of the same `Cᵏ` section for `A'`. -/
@[simp]
theorem changeAtlas_ofContMDiffSection [IsManifold 𝓘(ℝ, E) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, E)] (h : TransfersTo A A' μ p k)
    (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    changeAtlas h (ofContMDiffSection A μ p k s) = ofContMDiffSection A' μ p k s :=
  changeAtlas_eq_of_ae_eq_coord h (chartValueL_ofContMDiffSection_ae A μ p k s)
    (chartValueL_ofContMDiffSection_ae A' μ p k s)

/-- **Independence of the atlas.** If sections transfer between `A` and `A'` in both directions,
the Sobolev spaces of sections for the two atlases are isomorphic Banach spaces, an element
corresponding to the element with the same section. In particular their norms are equivalent.
It is `TauCeti.SectionChartData.atlasEquiv` for the chart data of the two atlases. -/
def atlasEquiv (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    SobolevSection A μ p k ≃L[ℝ] SobolevSection A' μ p k :=
  SectionChartData.atlasEquiv (A.readsFrom_sectionChartData A' μ)
    (A'.readsFrom_sectionChartData A μ) h h'

@[simp]
theorem toContinuousLinearMap_atlasEquiv (h : TransfersTo A A' μ p k)
    (h' : TransfersTo A' A μ p k) :
    (atlasEquiv h h' : SobolevSection A μ p k →L[ℝ] SobolevSection A' μ p k) = changeAtlas h :=
  SectionChartData.toContinuousLinearMap_atlasEquiv _ _ h h'

@[simp]
theorem atlasEquiv_apply (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k)
    (w : SobolevSection A μ p k) : atlasEquiv h h' w = changeAtlas h w :=
  SectionChartData.atlasEquiv_apply _ _ h h' w

theorem atlasEquiv_symm_apply (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k)
    (w : SobolevSection A' μ p k) : (atlasEquiv h h').symm w = changeAtlas h' w :=
  SectionChartData.atlasEquiv_symm_apply _ _ h h' w

@[simp]
theorem atlasEquiv_symm (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    (atlasEquiv h h').symm = atlasEquiv h' h :=
  SectionChartData.atlasEquiv_symm _ _ h h'

@[simp]
theorem atlasEquiv_refl :
    atlasEquiv (transfersTo_refl (A := A) (μ := μ) (p := p) (k := k)) transfersTo_refl =
      ContinuousLinearEquiv.refl ℝ _ :=
  SectionChartData.atlasEquiv_refl

@[simp]
theorem atlasEquiv_trans {A'' : FiniteBundleAtlas E M F V} (h₁ : TransfersTo A A' μ p k)
    (h₁' : TransfersTo A' A μ p k) (h₂ : TransfersTo A' A'' μ p k)
    (h₂' : TransfersTo A'' A' μ p k) :
    (atlasEquiv h₁ h₁').trans (atlasEquiv h₂ h₂') = atlasEquiv (h₁.trans h₂) (h₂'.trans h₁') :=
  SectionChartData.atlasEquiv_trans _ _ _ _ _ _ h₁ h₁' h₂ h₂'

/-- **Equivalence of norms.** If sections transfer between `A` and `A'` in both directions, the
norms of the Sobolev spaces of sections for the two atlases are equivalent: there is a positive
constant `C` bounding the norm of each element by `C` times the norm of the element of the other
atlas with the same section. -/
theorem exists_norm_changeAtlas_le (h : TransfersTo A A' μ p k) (h' : TransfersTo A' A μ p k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : SobolevSection A μ p k,
      ‖changeAtlas h w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖changeAtlas h w‖ :=
  SectionChartData.exists_norm_changeAtlas_le _ (A'.readsFrom_sectionChartData A μ) h h'

end SobolevSection

end Sobolev

namespace SobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {n : WithTop ℕ∞}
  [IsManifold 𝓘(ℝ, ℂ) n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V 𝓘(ℝ, ℂ)] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Transfer over surfaces.** For a `Cⁿ` bundle over a `Cⁿ` surface, `n ≠ 0`, and an order
`k ≤ n`, every element of `W^{k,p}(V)` for one finite bundle atlas defines
an element for any other: its expressions in the charts and trivializations of the first atlas are
in the local Sobolev classes, and these determine an element for the second. -/
theorem transfersTo (hn : n ≠ 0) (hkn : (k : WithTop ℕ∞) ≤ n)
    (A A' : FiniteBundleAtlas ℂ M F V) : TransfersTo A A' volume p k :=
  transfersTo_iff.2 fun w s hs ↦
  haveI : IsManifold 𝓘(ℝ, ℂ) 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm A.chart
    (fun _ ↦ IsManifold.chart_mem_maximalAtlas _) A.triv (fun i ↦ A.image i)
    (fun i ↦ (A.image i).isOpen)
    (fun x ↦ let ⟨i, hi⟩ := A.exists_mem_dom x
      ⟨i, A.dom_subset_chart_source i hi, A.dom_subset_baseSet i hi, A.mem_image.2 ⟨_, hi, rfl⟩⟩)
    (fun i ↦ by simpa only [funext (A.coord_def i s)] using memWkpLoc_coord w hs i) hn hkn

/-- **Equivalence of norms over surfaces.** For a `Cⁿ` bundle over a `Cⁿ` surface, `n ≠ 0`, and an
order `k ≤ n`, the norms of `W^{k,p}(V)` for two finite bundle atlases are
equivalent: there is a positive constant `C` bounding the norm of each element by `C` times the
norm of the element of the other atlas with the same section. -/
theorem exists_norm_changeAtlas_le_of_surface [IsManifold 𝓘(ℝ, ℂ) 1 M] (hn : n ≠ 0)
    (hkn : (k : WithTop ℕ∞) ≤ n) (A A' : FiniteBundleAtlas ℂ M F V) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : SobolevSection A volume p k,
      ‖changeAtlas (transfersTo hn hkn A A') w‖ ≤ C * ‖w‖ ∧
        ‖w‖ ≤ C * ‖changeAtlas (transfersTo hn hkn A A') w‖ :=
  exists_norm_changeAtlas_le (transfersTo hn hkn A A') (transfersTo hn hkn A' A)

end SobolevSection

end TauCeti
