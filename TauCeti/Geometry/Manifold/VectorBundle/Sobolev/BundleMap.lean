/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Smooth bundle maps acting on Sobolev sections

Let `M` be a smooth manifold without boundary modelled on a finite-dimensional real inner product
space `E`, and let `Φ x : V x →L[ℝ] W x` be a smooth morphism between smooth real vector bundles
with finite-dimensional model fibres `F` and `G`, a smooth section of the hom bundle. This file
shows that `s ↦ Φ s` is a continuous linear map `W^{k,p}(V) → W^{k,p}(W)` for every order `k` and
every `1 ≤ p ≤ ∞`, and that `θ ↦ Φ ∘ θ` is a continuous linear map between the Sobolev spaces of
`V`-valued and of `W`-valued one-forms. When every `Φ x` is invertible these maps are isomorphisms
of Banach spaces.

The Sobolev spaces are built on finite bundle atlases. The space of `W` uses the charts of the
atlas `A` of `V`, as the atlas `A.ofBaseSet h` of `W`, whose chart domains have closures in the
base sets of the preferred trivializations of `W` (such joint atlases exist on every compact
Hausdorff manifold, `TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`). In chart `i`
the reading of `Φ s` is the reading of `Φ` in the hom-bundle atlas `A.hom h`, a smooth
operator-valued function, applied to the reading of `s`
(`TauCeti.FiniteBundleAtlas.coord_hom_apply`), so the map multiplies the chart data by a smooth
operator coefficient (`TauCeti.Wkp.contDiffOnCLMApplyL`).

This is first done for abstract chart data (`TauCeti.SectionChartData.IsCoeffMap`): a map of
sections whose readings in each chart of the target are a smooth operator coefficient applied to
the readings in a chart of the source with larger image acts continuously on the Sobolev sections
(`TauCeti.SectionChartData.IsCoeffMap.mapL`).

## Main definitions

* `TauCeti.SectionChartData.IsCoeffMap`: a map of sections is read in charts as a smooth operator
  coefficient.
* `TauCeti.SectionChartData.IsCoeffMap.mapL`: its action on Sobolev sections.
* `TauCeti.SobolevSection.bundleMapL`: the action `s ↦ Φ s` of a smooth bundle morphism on
  `W^{k,p}` sections, and `TauCeti.SobolevSection.tangentHomMapL` its action `θ ↦ Φ ∘ θ` on
  `W^{k,p}` one-forms.
* `TauCeti.SobolevSection.bundleEquivL`, `TauCeti.SobolevSection.tangentHomEquivL`: the
  isomorphisms induced by a smooth bundle isomorphism.

## Main results

* `TauCeti.SectionChartData.IsCoeffMap.chartValueL_mapL_ae_coord`: the image of an element with
  section `s` has section `f s`.
* `TauCeti.FiniteBundleAtlas.isCoeffMap_bundleMap`,
  `TauCeti.FiniteBundleAtlas.isCoeffMap_tangentHomMap`: smooth bundle morphisms act on sections
  and one-forms by smooth coefficients.
* `TauCeti.SobolevSection.chartValueL_bundleMapL_ae_coord`,
  `TauCeti.SobolevSection.chartValueL_tangentHomMapL_ae_coord`: the images of an element with
  section `s` and of a one-form with section `θ` have sections `Φ s` and `Φ ∘ θ`.
* `TauCeti.SobolevSection.bundleMapL_ofContMDiffSection`: on smooth sections the map is `Φ`.
* `TauCeti.SobolevSection.bundleEquivL_symm_apply`,
  `TauCeti.SobolevSection.tangentHomEquivL_symm_apply`: the inverses are the actions of `Φ⁻¹`
  (`TauCeti.FiniteBundleAtlas.isCoeffMap_ofBaseSet_bundleMap`,
  `TauCeti.FiniteBundleAtlas.isCoeffMap_ofBaseSet_tangentHomMap`).
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {S : Type*} [AddCommGroup S] [Module ℝ S] {S' : Type*} [AddCommGroup S'] [Module ℝ S']

/-- **Maps of sections read as smooth operator coefficients.** A map `f` from the sections of
chart data `C` to those of chart data `C'` such that, on the image of each chart `i` of `C'`, the
reading of `f s` is a smooth operator-valued function `g` applied to the reading of `s` in a chart
`j` of `C` whose image contains that of `i`. The coefficient `g` is smooth on an open set `U`
containing the compact closure of the image of chart `i`. -/
def IsCoeffMap (C : SectionChartData E F S) (C' : SectionChartData E G S') (f : S → S') : Prop :=
  ∀ i, ∃ (j : Fin C.n) (U : Set E) (g : E → F →L[ℝ] G), C'.image i ≤ C.image j ∧
    IsCompact (closure (C'.image i : Set E)) ∧ IsOpen U ∧ closure (C'.image i : Set E) ⊆ U ∧
      ContDiffOn ℝ ∞ g U ∧ ∀ s, ∀ y ∈ C'.image i, C'.coord i (f s) y = g y (C.coord j s y)

namespace IsCoeffMap

variable {C : SectionChartData E F S} {C' : SectionChartData E G S'} {f : S → S'}
  (hf : C.IsCoeffMap C' f)

/-- A chart of `C` in which the readings in chart `i` of `C'` are computed. -/
private def chart (i : Fin C'.n) : Fin C.n := (hf i).choose

/-- An open set on which the coefficient of chart `i` is smooth. -/
private def domain (i : Fin C'.n) : Set E := (hf i).choose_spec.choose

/-- The operator coefficient of chart `i`. -/
private def coeff (i : Fin C'.n) : E → F →L[ℝ] G := (hf i).choose_spec.choose_spec.choose

private theorem image_le (i : Fin C'.n) : C'.image i ≤ C.image (hf.chart i) :=
  (hf i).choose_spec.choose_spec.choose_spec.1

include hf in
private theorem isCompact_closure_image (i : Fin C'.n) :
    IsCompact (closure (C'.image i : Set E)) :=
  (hf i).choose_spec.choose_spec.choose_spec.2.1

private theorem isOpen_domain (i : Fin C'.n) : IsOpen (hf.domain i) :=
  (hf i).choose_spec.choose_spec.choose_spec.2.2.1

private theorem closure_image_subset_domain (i : Fin C'.n) :
    closure (C'.image i : Set E) ⊆ hf.domain i :=
  (hf i).choose_spec.choose_spec.choose_spec.2.2.2.1

private theorem contDiffOn_coeff (i : Fin C'.n) : ContDiffOn ℝ ∞ (hf.coeff i) (hf.domain i) :=
  (hf i).choose_spec.choose_spec.choose_spec.2.2.2.2.1

private theorem coord_apply (i : Fin C'.n) (s : S) {y : E} (hy : y ∈ C'.image i) :
    C'.coord i (f s) y = hf.coeff i y (C.coord (hf.chart i) s y) :=
  (hf i).choose_spec.choose_spec.choose_spec.2.2.2.2.2 s y hy

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ G] (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The action of `f` on tuples of components: in chart `i` of `C'`, the components of chart
`hf.chart i` of `C` are restricted to the image of chart `i` and multiplied by the matrix of the
coefficient `hf.coeff i`. -/
private def dataL : C.SobolevData μ p k →L[ℝ] C'.SobolevData μ p k :=
  ContinuousLinearMap.pi fun i ↦
    (Wkp.contDiffOnCLMApplyL (hf.isOpen_domain i).uniqueDiffOn (hf.isCompact_closure_image i)
      (hf.closure_image_subset_domain i) k (finBasis ℝ F) (finBasis ℝ G)
      (hf.contDiffOn_coeff i)).comp
    ((ContinuousLinearMap.piMap fun _ : Fin (finrank ℝ F) ↦ Wkp.restrictL (hf.image_le i) k).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin C.n ↦
        ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p k) (hf.chart i)))

private theorem dataL_apply (w : C.SobolevData μ p k) (i : Fin C'.n) :
    hf.dataL μ p k w i =
      Wkp.contDiffOnCLMApplyL (hf.isOpen_domain i).uniqueDiffOn (hf.isCompact_closure_image i)
        (hf.closure_image_subset_domain i) k (finBasis ℝ F) (finBasis ℝ G) (hf.contDiffOn_coeff i)
        fun l ↦ Wkp.restrictL (hf.image_le i) k (w (hf.chart i) l) :=
  (rfl)

/-- **The chart formula.** In chart `i` of `C'`, the chart data of the image of a tuple are the
coefficient `hf.coeff i` applied to its chart data in chart `hf.chart i` of `C`. -/
private theorem chartValueL_dataL_ae (w : C.SobolevData μ p k) (i : Fin C'.n) :
    C'.chartValueL μ p k i (hf.dataL μ p k w) =ᵐ[μ.restrict (C'.image i)]
      fun y ↦ hf.coeff i y (C.chartValueL μ p k (hf.chart i) w y) := by
  have h₂ := ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hf.image_le i))
    (C.chartValueL_apply_ae μ p k (hf.chart i) w)
  have h₃ : ∀ᵐ y ∂μ.restrict (C'.image i), ∀ m,
      Wkp.value k (hf.dataL μ p k w i m) y = (finBasis ℝ G).repr (hf.coeff i y
        (∑ l, Wkp.value k (Wkp.restrictL (hf.image_le i) k (w (hf.chart i) l)) y •
          finBasis ℝ F l)) m :=
    ae_all_iff.2 fun m ↦ by
      rw [dataL_apply]
      exact Wkp.value_contDiffOnCLMApplyL_ae _ _ _ k _ _ _ _ m
  have h₄ : ∀ᵐ y ∂μ.restrict (C'.image i), ∀ l,
      Wkp.value k (Wkp.restrictL (hf.image_le i) k (w (hf.chart i) l)) y =
        Wkp.value k (w (hf.chart i) l) y :=
    ae_all_iff.2 fun l ↦ Wkp.value_restrictL_ae (hf.image_le i) k _
  filter_upwards [C'.chartValueL_apply_ae μ p k i (hf.dataL μ p k w), h₂, h₃, h₄]
    with y h₁ h₂ h₃ h₄
  simp only [h₁, h₂, h₃, h₄, Basis.sum_repr]

/-- The image of the components of a section `s` consists of the components of `f s`. -/
private theorem chartValueL_dataL_ae_coord {w : C.SobolevData μ p k} {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) (i : Fin C'.n) :
    C'.chartValueL μ p k i (hf.dataL μ p k w) =ᵐ[μ.restrict (C'.image i)] C'.coord i (f s) := by
  filter_upwards [hf.chartValueL_dataL_ae μ p k w i,
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hf.image_le i))
      (hs (hf.chart i)), ae_restrict_mem (C'.image i).isOpen.measurableSet] with y h₁ h₂ hy
  rw [h₁, h₂, hf.coord_apply i s hy]

/-- **The action on Sobolev sections.** The continuous linear map sending an element of
`W^{k,p}` for `C` with section `s` to the element of `W^{k,p}` for `C'` with section `f s`
(`TauCeti.SectionChartData.IsCoeffMap.chartValueL_mapL_ae_coord`). It depends only on `f`. -/
def mapL : C.sobolevSections μ p k →L[ℝ] C'.sobolevSections μ p k :=
  ((hf.dataL μ p k).comp (C.sobolevSections μ p k).subtypeL).codRestrict _ fun w ↦ by
    obtain ⟨s, hs⟩ := C.exists_section μ p k w
    exact (C'.mem_sobolevSections_iff μ p k).2 ⟨f s, hf.chartValueL_dataL_ae_coord μ p k hs⟩

variable {hf μ p k} in
/-- The image under `hf.mapL` of an element with section `s` has section `f s`. -/
theorem chartValueL_mapL_ae_coord {w : C.sobolevSections μ p k} {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) (i : Fin C'.n) :
    C'.chartValueL μ p k i (hf.mapL μ p k w) =ᵐ[μ.restrict (C'.image i)] C'.coord i (f s) :=
  hf.chartValueL_dataL_ae_coord μ p k hs i

/-- If `f'` is a left inverse of `f`, then `hf'.mapL` is a left inverse of `hf.mapL`. -/
theorem leftInverse_mapL {f' : S' → S} (hf' : C'.IsCoeffMap C f') (h : Function.LeftInverse f' f) :
    Function.LeftInverse (hf'.mapL μ p k) (hf.mapL μ p k) := fun w ↦ by
  obtain ⟨s, hs⟩ := C.exists_section μ p k w
  refine eq_of_ae_eq_coord (s := s) (fun i ↦ ?_) hs
  rw [← h s]
  exact chartValueL_mapL_ae_coord (chartValueL_mapL_ae_coord hs) i

/-- **Isomorphisms of Sobolev sections.** Mutually inverse maps of sections read as smooth
operator coefficients induce an isomorphism of the Sobolev sections. -/
def mapEquivL {f' : S' → S} (hf' : C'.IsCoeffMap C f') (h : Function.LeftInverse f' f)
    (h' : Function.RightInverse f' f) : C.sobolevSections μ p k ≃L[ℝ] C'.sobolevSections μ p k :=
  .ofContinuousLinearMap (hf.mapL μ p k) (hf'.mapL μ p k)
    (ContinuousLinearMap.ext (hf'.leftInverse_mapL μ p k hf h'))
    (ContinuousLinearMap.ext (hf.leftInverse_mapL μ p k hf' h))

@[simp]
theorem coe_mapEquivL {f' : S' → S} (hf' : C'.IsCoeffMap C f') (h : Function.LeftInverse f' f)
    (h' : Function.RightInverse f' f) :
    (hf.mapEquivL μ p k hf' h h' : C.sobolevSections μ p k →L[ℝ] C'.sobolevSections μ p k) =
      hf.mapL μ p k :=
  (rfl)

@[simp]
theorem coe_mapEquivL_symm {f' : S' → S} (hf' : C'.IsCoeffMap C f') (h : Function.LeftInverse f' f)
    (h' : Function.RightInverse f' f) :
    ((hf.mapEquivL μ p k hf' h h').symm :
      C'.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k) = hf'.mapL μ p k :=
  (rfl)

end IsCoeffMap

end SectionChartData

/-! ### Smooth bundle morphisms -/

namespace FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet)
  {Φ : ∀ x, V x →L[ℝ] W x}

/-- **A smooth bundle morphism acts on sections by its chart readings.** The map `s ↦ Φ s` from
the sections of `V`, read in the charts of `A`, to those of `W`, read in the same charts as the
atlas `A.ofBaseSet h`, with the reading of `Φ` in the hom-bundle atlas `A.hom h` as coefficient. -/
theorem isCoeffMap_bundleMap
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x)) :
    A.sectionChartData.IsCoeffMap (A.ofBaseSet h).sectionChartData fun s x ↦ Φ x (s x) :=
  fun (i : Fin A.n) ↦ ⟨i, _, _, (image_ofBaseSet (h := h) i).le,
    (A.ofBaseSet h).isCompact_closure_image i,
    ((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
      ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet,
    by
      rw [A.sectionChartData_image_ofBaseSet h, ← image_hom (𝕜 := ℝ) (h := h)]
      exact (A.hom (𝕜 := ℝ) h).closure_image_subset_target_inter_preimage_baseSet i,
    (A.hom (𝕜 := ℝ) h).contDiffOn_coord hΦ i, fun s y hy ↦ by
      have hy' : y ∈ A.image i := (A.sectionChartData_image_ofBaseSet h i).subset hy
      rw [sectionChartData_coord_of_mem _ _ hy, sectionChartData_coord_of_mem _ _ hy',
        A.coord_hom_apply h i Φ s hy']⟩

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- **A smooth bundle morphism acts on one-forms by its chart readings.** The map `θ ↦ Φ ∘ θ` from
`V`-valued to `W`-valued one-forms, read in the charts of `A` and of `A.ofBaseSet h`, with the
composition with the reading of `Φ` as coefficient. -/
theorem isCoeffMap_tangentHomMap
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x)) :
    (A.tangentHom 𝓘(ℝ, E)).sectionChartData.IsCoeffMap
      ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).sectionChartData
      fun θ x ↦ (Φ x).comp (θ x) := by
  intro (i : Fin A.n)
  have hL : ContDiff ℝ ∞ (ContinuousLinearMap.compL ℝ E F G) := ContinuousLinearMap.contDiff _
  refine ⟨i, _, ContinuousLinearMap.compL ℝ E F G ∘ (A.hom (𝕜 := ℝ) h).coord i Φ,
    SetLike.coe_subset_coe.1 ((A.sectionChartData_image_tangentHom_ofBaseSet h i).trans
      (A.sectionChartData_image_tangentHom i).symm).subset,
    ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).isCompact_closure_image i,
    ((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
      ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet,
    ?_, hL.comp_contDiffOn ((A.hom (𝕜 := ℝ) h).contDiffOn_coord hΦ i), fun θ y hy ↦ ?_⟩
  · rw [A.sectionChartData_image_tangentHom_ofBaseSet h, ← image_hom (𝕜 := ℝ) (h := h)]
    exact (A.hom (𝕜 := ℝ) h).closure_image_subset_target_inter_preimage_baseSet i
  have hy' : y ∈ A.image i := (A.sectionChartData_image_tangentHom_ofBaseSet h i).subset hy
  have hyA : y ∈ (A.tangentHom 𝓘(ℝ, E)).image i :=
    (A.sectionChartData_image_tangentHom i).symm.subset hy'
  have hx : (A.chart i).symm y ∈ (trivializationAt F V (A.center i)).baseSet :=
    A.dom_subset_baseSet i (A.symm_mem_dom hy')
  refine (((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).sectionChartData_coord_of_mem _ hy).trans ?_
  refine ((A.ofBaseSet h).coord_tangentHom 𝓘(ℝ, E) i _ y).trans ?_
  refine (ContinuousLinearMap.inCoordinates_comp _ _ hx).trans ?_
  rw [(A.tangentHom 𝓘(ℝ, E)).sectionChartData_coord_of_mem _ hyA, coord_tangentHom,
    Function.comp_apply, coord_hom, ContinuousLinearMap.compL_apply]
  simp only [ofBaseSet_center, chart_ofBaseSet]

omit [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)] in
/-- A smooth bundle morphism `Ψ : W → V` acts on sections by its chart readings, from the atlas
`A.ofBaseSet h` of `W` back to the atlas `A` of `V`. -/
theorem isCoeffMap_ofBaseSet_bundleMap {Ψ : ∀ x, W x →L[ℝ] V x}
    (hΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
      fun x ↦ TotalSpace.mk' (G →L[ℝ] F) (E := fun x ↦ W x →L[ℝ] V x) x (Ψ x)) :
    (A.ofBaseSet h).sectionChartData.IsCoeffMap A.sectionChartData fun t x ↦ Ψ x (t x) := by
  have := (A.ofBaseSet h).isCoeffMap_bundleMap A.closure_dom_subset_baseSet hΨ
  rwa [ofBaseSet_ofBaseSet (A := A) (h := h) A.closure_dom_subset_baseSet] at this

/-- A smooth bundle morphism `Ψ : W → V` acts on one-forms by its chart readings, from the atlas
`A.ofBaseSet h` of `W` back to the atlas `A` of `V`. -/
theorem isCoeffMap_ofBaseSet_tangentHomMap {Ψ : ∀ x, W x →L[ℝ] V x}
    (hΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
      fun x ↦ TotalSpace.mk' (G →L[ℝ] F) (E := fun x ↦ W x →L[ℝ] V x) x (Ψ x)) :
    ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).sectionChartData.IsCoeffMap
      (A.tangentHom 𝓘(ℝ, E)).sectionChartData
      fun θ x ↦ (Ψ x).comp (θ x) := by
  have := (A.ofBaseSet h).isCoeffMap_tangentHomMap A.closure_dom_subset_baseSet hΨ
  rwa [ofBaseSet_ofBaseSet (A := A) (h := h) A.closure_dom_subset_baseSet] at this

end FiniteBundleAtlas

namespace SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet)
  {Φ : ∀ x, V x →L[ℝ] W x}
  (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
    fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x))
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Smooth bundle morphisms act on Sobolev sections.** The continuous linear map
`W^{k,p}(V) → W^{k,p}(W)` induced by a smooth bundle morphism `Φ`, sending an element with section
`s` to the element with section `Φ s` (`TauCeti.SobolevSection.chartValueL_bundleMapL_ae_coord`). -/
def bundleMapL : SobolevSection A μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k :=
  (A.isCoeffMap_bundleMap h hΦ).mapL μ p k

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- **Smooth bundle morphisms act on Sobolev one-forms.** The continuous linear map from `W^{k,p}`
`V`-valued one-forms to `W^{k,p}` `W`-valued one-forms induced by a smooth bundle morphism `Φ`,
sending an element with one-form `θ` to the element with one-form `Φ ∘ θ`
(`TauCeti.SobolevSection.chartValueL_tangentHomMapL_ae_coord`). -/
def tangentHomMapL [IsManifold 𝓘(ℝ, E) 1 M] :
    SobolevSection (A.tangentHom 𝓘(ℝ, E)) μ p k →L[ℝ]
      SobolevSection ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)) μ p k :=
  (A.isCoeffMap_tangentHomMap h hΦ).mapL μ p k

variable {A h hΦ μ p k}

/-- The image under `bundleMapL` of an element with section `s` has section `Φ s`. -/
theorem chartValueL_bundleMapL_ae_coord {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (bundleMapL A h hΦ μ p k w)
      =ᵐ[μ.restrict ((A.ofBaseSet h).image i)] (A.ofBaseSet h).coord i fun x ↦ Φ x (s x) :=
  ((A.ofBaseSet h).ae_eq_sectionChartData_coord_iff μ).1 <|
    SectionChartData.IsCoeffMap.chartValueL_mapL_ae_coord (hf := A.isCoeffMap_bundleMap h hΦ)
      (fun i ↦ (A.ae_eq_sectionChartData_coord_iff μ).2 (hs i)) i

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- The image under `tangentHomMapL` of an element with one-form `θ` has one-form `Φ ∘ θ`. -/
theorem chartValueL_tangentHomMapL_ae_coord [IsManifold 𝓘(ℝ, E) 1 M]
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, E)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}
    (hθ : ∀ i, (A.tangentHom 𝓘(ℝ, E)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, E)).image i)]
        (A.tangentHom 𝓘(ℝ, E)).coord i θ) (i : Fin A.n) :
    ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).sectionChartData.chartValueL μ p k i
        (tangentHomMapL A h hΦ μ p k w)
      =ᵐ[μ.restrict (((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).image i)]
        ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).coord i fun x ↦ (Φ x).comp (θ x) :=
  (((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).ae_eq_sectionChartData_coord_iff μ).1 <|
    SectionChartData.IsCoeffMap.chartValueL_mapL_ae_coord
      (hf := A.isCoeffMap_tangentHomMap h hΦ)
      (fun i ↦ ((A.tangentHom 𝓘(ℝ, E)).ae_eq_sectionChartData_coord_iff μ).2 (hθ i)) i

/-- On a smooth section `s`, the map induced by `Φ` is the Sobolev section of the smooth section
`Φ s`. -/
theorem bundleMapL_ofContMDiffSection (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    bundleMapL A h hΦ μ p k (ofContMDiffSection A μ p k s) =
      ofContMDiffSection (A.ofBaseSet h) μ p k
        ⟨fun x ↦ Φ x (s x),
          ContMDiff.clm_bundle_apply (hΦ.of_le (m := k) (by exact_mod_cast le_top)) s.contMDiff⟩ :=
  eq_of_ae_eq_coord (s := fun x ↦ Φ x (s x))
    (fun i ↦ chartValueL_bundleMapL_ae_coord (chartValueL_ofContMDiffSection_ae A μ p k s) i)
    (chartValueL_ofContMDiffSection_ae (A.ofBaseSet h) μ p k _)

/-! ### Smooth bundle isomorphisms -/

section Equiv

variable (A h μ p k) [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {Φ : ∀ x, V x ≃L[ℝ] W x}

variable (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞ fun x ↦
  TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x : V x →L[ℝ] W x))

/-- **Smooth bundle isomorphisms act on Sobolev sections.** The isomorphism of Banach spaces
`W^{k,p}(V) ≃ W^{k,p}(W)` induced by a smooth bundle isomorphism `Φ`, sending an element with
section `s` to the element with section `Φ s`. Its inverse is induced by `Φ⁻¹`. -/
def bundleEquivL : SobolevSection A μ p k ≃L[ℝ] SobolevSection (A.ofBaseSet h) μ p k :=
  (A.isCoeffMap_bundleMap h hΦ).mapEquivL μ p k
    (A.isCoeffMap_ofBaseSet_bundleMap h hΦ.clm_bundle_equiv_symm)
    (fun _ ↦ funext fun x ↦ (Φ x).symm_apply_apply _)
    (fun _ ↦ funext fun x ↦ (Φ x).apply_symm_apply _)

@[simp]
theorem coe_bundleEquivL :
    (bundleEquivL A h μ p k hΦ :
      SobolevSection A μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k) =
      bundleMapL A h hΦ μ p k :=
  (rfl)

/-- The inverse of `bundleEquivL` is the action of `Φ⁻¹` on sections
(`FiniteBundleAtlas.isCoeffMap_ofBaseSet_bundleMap`). -/
@[simp]
theorem coe_bundleEquivL_symm :
    ((bundleEquivL A h μ p k hΦ).symm :
      SobolevSection (A.ofBaseSet h) μ p k →L[ℝ] SobolevSection A μ p k) =
      (A.isCoeffMap_ofBaseSet_bundleMap h hΦ.clm_bundle_equiv_symm).mapL μ p k :=
  (rfl)

@[simp]
theorem bundleEquivL_apply (w : SobolevSection A μ p k) :
    bundleEquivL A h μ p k hΦ w = bundleMapL A h hΦ μ p k w :=
  (rfl)

@[simp]
theorem bundleEquivL_symm_apply (w : SobolevSection (A.ofBaseSet h) μ p k) :
    (bundleEquivL A h μ p k hΦ).symm w =
      (A.isCoeffMap_ofBaseSet_bundleMap h hΦ.clm_bundle_equiv_symm).mapL μ p k w :=
  (rfl)

variable {A h μ p k hΦ} in
/-- The image under the inverse of `bundleEquivL` of an element with section `t` has section
`Φ⁻¹ t`. -/
theorem chartValueL_bundleEquivL_symm_ae_coord {w : SobolevSection (A.ofBaseSet h) μ p k}
    {t : ∀ x, W x} (ht : ∀ i, (A.ofBaseSet h).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.ofBaseSet h).image i)] (A.ofBaseSet h).coord i t) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i ((bundleEquivL A h μ p k hΦ).symm w)
      =ᵐ[μ.restrict (A.image i)] A.coord i fun x ↦ (Φ x).symm (t x) :=
  (A.ae_eq_sectionChartData_coord_iff μ).1 <|
    SectionChartData.IsCoeffMap.chartValueL_mapL_ae_coord
      (hf := A.isCoeffMap_ofBaseSet_bundleMap h hΦ.clm_bundle_equiv_symm)
      (fun i ↦ ((A.ofBaseSet h).ae_eq_sectionChartData_coord_iff μ).2 (ht i)) i

/-- **Smooth bundle isomorphisms act on Sobolev one-forms.** The isomorphism of Banach spaces
between `W^{k,p}` `V`-valued and `W`-valued one-forms induced by a smooth bundle isomorphism `Φ`,
sending an element with one-form `θ` to the element with one-form `Φ ∘ θ`. -/
def tangentHomEquivL [IsManifold 𝓘(ℝ, E) 1 M] :
    SobolevSection (A.tangentHom 𝓘(ℝ, E)) μ p k ≃L[ℝ]
      SobolevSection ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)) μ p k :=
  (A.isCoeffMap_tangentHomMap h hΦ).mapEquivL μ p k
    (A.isCoeffMap_ofBaseSet_tangentHomMap h hΦ.clm_bundle_equiv_symm)
    (fun _ ↦ funext fun x ↦ ContinuousLinearMap.ext fun _ ↦ (Φ x).symm_apply_apply _)
    (fun _ ↦ funext fun x ↦ ContinuousLinearMap.ext fun _ ↦ (Φ x).apply_symm_apply _)

@[simp]
theorem coe_tangentHomEquivL [IsManifold 𝓘(ℝ, E) 1 M] :
    (tangentHomEquivL A h μ p k hΦ :
      SobolevSection (A.tangentHom 𝓘(ℝ, E)) μ p k →L[ℝ]
        SobolevSection ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)) μ p k) =
      tangentHomMapL A h hΦ μ p k :=
  (rfl)

/-- The inverse of `tangentHomEquivL` is the action of `Φ⁻¹` on one-forms
(`FiniteBundleAtlas.isCoeffMap_ofBaseSet_tangentHomMap`). -/
@[simp]
theorem coe_tangentHomEquivL_symm [IsManifold 𝓘(ℝ, E) 1 M] :
    ((tangentHomEquivL A h μ p k hΦ).symm :
      SobolevSection ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)) μ p k →L[ℝ]
        SobolevSection (A.tangentHom 𝓘(ℝ, E)) μ p k) =
      (A.isCoeffMap_ofBaseSet_tangentHomMap h hΦ.clm_bundle_equiv_symm).mapL μ p k :=
  (rfl)

@[simp]
theorem tangentHomEquivL_apply [IsManifold 𝓘(ℝ, E) 1 M]
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, E)) μ p k) :
    tangentHomEquivL A h μ p k hΦ w = tangentHomMapL A h hΦ μ p k w :=
  (rfl)

@[simp]
theorem tangentHomEquivL_symm_apply [IsManifold 𝓘(ℝ, E) 1 M]
    (w : SobolevSection ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)) μ p k) :
    (tangentHomEquivL A h μ p k hΦ).symm w =
      (A.isCoeffMap_ofBaseSet_tangentHomMap h hΦ.clm_bundle_equiv_symm).mapL μ p k w :=
  (rfl)

variable {A h μ p k hΦ} in
/-- The image under the inverse of `tangentHomEquivL` of an element with one-form `θ` has one-form
`Φ⁻¹ ∘ θ`. -/
theorem chartValueL_tangentHomEquivL_symm_ae_coord [IsManifold 𝓘(ℝ, E) 1 M]
    {w : SobolevSection ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] W x}
    (hθ : ∀ i, ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).image i)]
        ((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).coord i θ)
    (i : Fin A.n) :
    (A.tangentHom 𝓘(ℝ, E)).sectionChartData.chartValueL μ p k i
        ((tangentHomEquivL A h μ p k hΦ).symm w)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, E)).image i)]
        (A.tangentHom 𝓘(ℝ, E)).coord i fun x ↦ ((Φ x).symm : W x →L[ℝ] V x).comp (θ x) :=
  ((A.tangentHom 𝓘(ℝ, E)).ae_eq_sectionChartData_coord_iff μ).1 <|
    SectionChartData.IsCoeffMap.chartValueL_mapL_ae_coord
      (hf := A.isCoeffMap_ofBaseSet_tangentHomMap h hΦ.clm_bundle_equiv_symm)
      (fun i ↦ (((A.ofBaseSet h).tangentHom 𝓘(ℝ, E)).ae_eq_sectionChartData_coord_iff μ).2
        (hθ i)) i

end Equiv

end SobolevSection

end TauCeti
