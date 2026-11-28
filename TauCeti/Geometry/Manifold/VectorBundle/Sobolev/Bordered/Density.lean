/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.AEZeroOff
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Sobolev.Wkp.HalfPlaneDensity
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation

/-!
# Sections smooth up to the boundary are dense in bordered Sobolev spaces

Let `M` be a Hausdorff smooth manifold modelled on the closed upper half-plane, for instance a
compact surface with boundary, let `V → M` be a smooth real vector bundle with finite-dimensional
model fibre `F`, and let `A` be a finite bundle atlas (so `M` is compact). This file shows that for
`1 ≤ p < ∞` and every order `k` the sections smooth up to the boundary are dense in the Sobolev
space `W^{k,p}(V)` of `TauCeti.BorderedSobolevSection A p k`
(`TauCeti.BorderedSobolevSection.denseRange_ofContMDiffSection_comp_ofLE`), and hence so are the
`Cᵏ` sections (`TauCeti.BorderedSobolevSection.denseRange_ofContMDiffSection`). The exponent must
be finite: smooth functions are not dense in `W^{1,∞}`, as `|x|` on an interval shows.

The argument localizes with a smooth partition of unity `χ` subordinate to the chart domains of
`A`: every `w` is the finite sum of the products `χ i • w`
(`TauCeti.BorderedSobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one`), and `χ i • w`
vanishes off the closed subset `tsupport (χ i)` of the domain of chart `i`. Such an element is the
extension by zero of its chart-`i` components, and extension by zero is continuous
(`TauCeti.BorderedSobolevSection.extendByZeroL`). The chart-`i` components vanish off a compact
subset of the chart image, which may meet the real axis, so they are limits of restrictions of test
functions on the whole plane
(`TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf`). Multiplied by a smooth
cutoff `ψ` equal to one on `tsupport (χ i)` and supported in the chart domain, these are the chart
readings of sections smooth up to the boundary
(`TauCeti.FiniteBundleAtlas.contMDiff_smul_chartSection_coe`).

This is the analogue for bases with boundary of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density`, following the proof of
`TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE`.

## Main results

* `TauCeti.BorderedSobolevSection.denseRange_ofContMDiffSection_comp_ofLE`: the sections smooth up
  to the boundary are dense in `W^{k,p}(V)` for `1 ≤ p < ∞`.
* `TauCeti.BorderedSobolevSection.denseRange_ofContMDiffSection`: the `Cᵏ` sections are dense.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.1.
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology Distributions

namespace TauCeti

open FiniteBundleAtlas

namespace BorderedSobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}
  [IsManifold closedUpperHalfPlaneModel ∞ M]
  [ContMDiffVectorBundle ∞ F V closedUpperHalfPlaneModel]

/-- An element of `W^{k,p}` of the upper half `U` of an open planar set `Ω`, vanishing off a
compact subset of `Ω`, is a limit of restrictions of test functions on the whole plane. This is
`TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf` for an open set `U` equal
to the upper half of `Ω`. -/
private theorem mem_closure_range_restrictL_of_upperHalf_eq {Ω U : Opens ℂ}
    (hU : Ω.upperHalf = U) (hp : p ≠ ⊤) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (u : Wkp volume U p k)
    (hu : ∀ᵐ z ∂volume.restrict (U : Set ℂ), z ∉ K → Wkp.value k u z = 0) :
    u ∈ closure (range fun φ : 𝓓((⊤ : Opens ℂ), ℝ) ↦
      Wkp.restrictL (le_top : U ≤ ⊤) k (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k φ)) := by
  subst hU
  exact Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf hp hK hKΩ k u hu

/-- **A smooth section built from test functions in one chart.** Let `ψ` be smooth with
`tsupport ψ` inside the domain of chart `i`, and let `φ j` be test functions on the plane. Then `ψ`
times the section with chart-`i` coordinates `∑ j, φ j • finBasis ℝ F j` is a section smooth up to
the boundary; its element of `W^{k,p}(V)` vanishes off `tsupport ψ`, and its chart-`i` components
are the products of the `φ j` with `ψ` read in chart `i`. -/
private theorem exists_mem_range_value_ae {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) (hψi : tsupport ψ ⊆ A.dom i)
    (φ : Fin (finrank ℝ F) → 𝓓((⊤ : Opens ℂ), ℝ)) :
    ∃ a ∈ LinearMap.range ((ofContMDiffSection A p k).comp
      (ContMDiffSection.ofLE (I := closedUpperHalfPlaneModel) (F := F) (V := V)
        ENat.LEInfty.out)),
      a ∈ aeZeroOff A p k (tsupport ψ) ∧ ∀ j,
        (Wkp.value k ((a : A.halfSectionChartData.SobolevData volume p k) i j) : ℂ → ℝ)
          =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
            fun z ↦ ψ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) * φ j z := by
  set G : ℂ → F := fun z ↦ ∑ j, φ j z • finBasis ℝ F j with hGdef
  have hG : ContDiff ℝ ∞ G := ContDiff.sum fun j _ ↦ (φ j).contDiff.smul contDiff_const
  let s : Cₛ^∞⟮closedUpperHalfPlaneModel; F, V⟯ :=
    ⟨fun x ↦ ψ x • A.chartSection i (fun y : ClosedUpperHalfPlane ↦ G y) x,
      A.contMDiff_smul_chartSection_coe hψ hψi hG.contDiffOn⟩
  have hs : ⇑s = fun x ↦ ψ x • A.chartSection i (fun y : ClosedUpperHalfPlane ↦ G y) x :=
    ContMDiffSection.coeFn_mk _ _
  have has (j : Fin A.n) := chartValueL_ofContMDiffSection_ae A p k
    (ContMDiffSection.ofLE ENat.LEInfty.out s) j
  simp only [ContMDiffSection.coe_ofLE] at has
  refine ⟨_, ⟨s, rfl⟩, mem_aeZeroOff_of_ae_eq_halfCoord has fun y hy ↦ by
    simp [s, image_eq_zero_of_notMem_tsupport hy],
    fun j ↦ (value_ae_eq_repr_halfCoord (has i) j).trans ?_⟩
  filter_upwards [ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz
  rw [hs, A.halfCoord_smul_chartSection_coe ψ G (A.halfImage_subset_halfClosedImage i hz),
    map_smul, Finsupp.smul_apply, hGdef, (finBasis ℝ F).repr_sum_self, smul_eq_mul]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] [IsManifold closedUpperHalfPlaneModel ∞ M]
  [ContMDiffVectorBundle ∞ F V closedUpperHalfPlaneModel] in
/-- A function on `A.halfImage i` vanishing almost everywhere at the points lying over the
complement of `L` vanishes almost everywhere off the image of `L` in `ℂ`. -/
private theorem ae_eq_zero_of_notMem_image {i : Fin A.n} {L : Set M} {g : ℂ → ℝ}
    (hg : ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → g z = 0) :
    ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      z ∉ (fun x ↦ (A.chart i x : ℂ)) '' L → g z = 0 := by
  filter_upwards [hg, ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z h hz hzK
  refine h fun hzL ↦ hzK ⟨_, hzL, ?_⟩
  obtain ⟨hzi, hz0⟩ := A.mem_halfImage.1 hz
  obtain ⟨y, hy, hyz⟩ := A.mem_image.1 hzi
  simp only
  rw [← hyz, (A.chart i).left_inv (A.dom_subset_chart_source i hy), hyz,
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V closedUpperHalfPlaneModel] in
/-- Multiplication by the chart-`i` reading of a smooth function `ψ` equal to one on `L` fixes the
chart-`i` functions vanishing off `L`. -/
private theorem contDiffOnSMulL_eq_self {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) {L : Set M} (hψL : ∀ x ∈ L, ψ x = 1)
    {g : Wkp volume (A.halfImage i) p k}
    (hg : ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → Wkp.value k g z = 0) :
    Wkp.contDiffOnSMulL (uniqueDiffOn_extChartAt_target (I := closedUpperHalfPlaneModel)
      (A.center i)) (A.isCompact_closure_halfImage i)
      (A.closure_halfImage_subset_extChartAt_target i) k
      (A.contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm hψ i) g = g :=
  Wkp.ext k <| Lp.ext <| by
    filter_upwards [Wkp.value_contDiffOnSMulL_ae _ _ _ k _ g, hg] with z h1 h2
    rw [h1]
    by_cases hz : (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ L
    · rw [hψL _ hz, one_mul]
    · rw [h2 hz, mul_zero]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [IsManifold closedUpperHalfPlaneModel ∞ M]
  [ContMDiffVectorBundle ∞ F V closedUpperHalfPlaneModel] in
/-- A chart-`i` function vanishing almost everywhere at the points lying over the complement of a
closed subset `L` of the domain of chart `i` is a limit of restrictions of test functions on the
whole plane: it vanishes off the image of `L` in `ℂ`, a compact subset of `A.halfOpen i`. -/
private theorem mem_closure_range_restrictL_of_ae_eq_zero (hp : p ≠ ⊤) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) {g : Wkp volume (A.halfImage i) p k}
    (hg : ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → Wkp.value k g z = 0) :
    g ∈ closure (range fun φ : 𝓓((⊤ : Opens ℂ), ℝ) ↦
      Wkp.restrictL (le_top : A.halfImage i ≤ ⊤) k
        (Wkp.ofTestFunctionₗ (mu := volume) (p := p) k φ)) := by
  have := A.compactSpace
  have hK : IsCompact ((fun x ↦ (A.chart i x : ℂ)) '' L) := hL.isCompact.image_of_continuousOn
    (continuous_subtypeVal.comp_continuousOn
      ((A.chart i).continuousOn.mono (hLi.trans (A.dom_subset_chart_source i))))
  have hKi : (fun x ↦ (A.chart i x : ℂ)) '' L ⊆ A.halfOpen i := by
    rintro _ ⟨x, hx, rfl⟩
    refine A.mem_halfOpen.2 ?_
    rw [closedUpperHalfPlaneModel_symm_coe]
    exact A.mem_image.2 ⟨x, hLi hx, rfl⟩
  exact mem_closure_range_restrictL_of_upperHalf_eq (A.upperHalf_halfOpen i) hp hK hKi g
    (ae_eq_zero_of_notMem_image hg)

/-- **The localized density step.** An element vanishing off a closed subset `L` of the domain of
chart `i` is a limit of elements given by sections smooth up to the boundary. Take a smooth cutoff
`ψ` equal to one on `L` with support in the chart domain, approximate the chart-`i` components by
test functions on the plane, and multiply them by `ψ`: these are the chart readings of smooth
sections vanishing off `tsupport ψ`, and extension by zero is continuous. -/
private theorem mem_closure_range_of_mem_aeZeroOff [T2Space M] (hp : p ≠ ⊤) {i : Fin A.n}
    {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i) {u : BorderedSobolevSection A p k}
    (hu : u ∈ aeZeroOff A p k L) :
    u ∈ Submodule.topologicalClosure (LinearMap.range ((ofContMDiffSection A p k).comp
      (ContMDiffSection.ofLE (I := closedUpperHalfPlaneModel) (F := F) (V := V)
        ENat.LEInfty.out))) := by
  have := A.compactSpace
  -- A smooth cutoff `ψ`, equal to one on `L`, with support in the domain of chart `i`.
  obtain ⟨O, hO, hLO, hOi⟩ := normal_exists_closure_subset hL (A.isOpen_dom i) hLi
  obtain ⟨ψ, hψ, -, hψO, hψL⟩ :=
    exists_contMDiff_support_eq_eq_one_iff closedUpperHalfPlaneModel (n := ⊤) hO hL hLO
  have hψi : tsupport ψ ⊆ A.dom i := by rw [tsupport, hψO]; exact hOi
  have hu' := aeZeroOff_mono (fun x hx ↦ subset_tsupport ψ (by
    rw [Function.mem_support, (hψL x).1 hx]; exact one_ne_zero)) hu
  -- Multiplication by `ψ`, read in chart `i`, fixes the chart-`i` components of `u`.
  let T : Wkp volume (A.halfImage i) p k →L[ℝ] Wkp volume (A.halfImage i) p k :=
    Wkp.contDiffOnSMulL (uniqueDiffOn_extChartAt_target (I := closedUpperHalfPlaneModel)
      (A.center i)) (A.isCompact_closure_halfImage i)
      (A.closure_halfImage_subset_extChartAt_target i) k
      (A.contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm hψ i)
  have hT (v : Wkp volume (A.halfImage i) p k) : (Wkp.value k (T v) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun z ↦
        ψ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) * Wkp.value k v z :=
    Wkp.value_contDiffOnSMulL_ae _ _ _ k _ v
  set ui := ((u : BorderedSobolevSection A p k) : A.halfSectionChartData.SobolevData volume p k) i
  have hui := mem_chartAeZeroOff.1 (mem_chartAeZeroOff_of_mem_aeZeroOff hu i)
  have hTu (j : Fin (finrank ℝ F)) : T (ui j) = ui j :=
    contDiffOnSMulL_eq_self hψ (fun x hx ↦ (hψL x).1 hx) (hui j)
  -- Test functions approximating the chart-`i` components.
  choose v hvr hvlim using fun j ↦ mem_closure_iff_seq_limit.1
    (mem_closure_range_restrictL_of_ae_eq_zero hp hL hLi (hui j))
  choose φ hφ using fun j m ↦ hvr j m
  choose a ha haψ hav using fun m ↦ exists_mem_range_value_ae (p := p) (k := k) hψ hψi
    fun j ↦ φ j m
  -- Convergence of the chart-`i` components, hence of the elements.
  have hconv : Tendsto (fun m ↦ chartRestrictL A p k i (tsupport ψ) ⟨a m, haψ m⟩) atTop
      (𝓝 (chartRestrictL A p k i (tsupport ψ) ⟨u, hu'⟩)) := by
    refine tendsto_subtype_rng.2 (tendsto_pi_nhds.2 fun j ↦ ?_)
    have hcomp (m : ℕ) : ((a m : BorderedSobolevSection A p k) :
        A.halfSectionChartData.SobolevData volume p k) i j = T (v j m) := by
      rw [← hφ j m]
      refine Wkp.ext k (Lp.ext ((hav m j).trans (EventuallyEq.symm ((hT _).trans ?_))))
      filter_upwards [Wkp.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p)
        (le_top : A.halfImage i ≤ ⊤) k (φ j m)] with z h
      rw [h]
    simp only [coe_chartRestrictL_apply, hcomp]
    have hT' := (T.continuous.tendsto _).comp (hvlim j)
    rw [hTu j] at hT'
    exact hT'
  have hE := tendsto_subtype_rng.1 (tendsto_of_tendsto_chartRestrictL (n := k + 1) (by omega)
    (by omega) (isClosed_tsupport ψ) hψi hconv)
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hE
    (Eventually.of_forall fun m ↦ Submodule.le_topologicalClosure _ (ha m))

variable (A p k) in
/-- **Density of sections smooth up to the boundary.** For `1 ≤ p < ∞`, the elements of the
bordered Sobolev space `W^{k,p}(V)` given by sections smooth up to the boundary are dense. -/
theorem denseRange_ofContMDiffSection_comp_ofLE [T2Space M] (hp : p ≠ ⊤) :
    DenseRange ((ofContMDiffSection A p k).comp
      (ContMDiffSection.ofLE (I := closedUpperHalfPlaneModel) (F := F) (V := V)
        ENat.LEInfty.out)) := by
  have := A.compactSpace
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate closedUpperHalfPlaneModel
    isClosed_univ A.dom A.isOpen_dom (by rw [A.iUnion_dom])
  intro w
  rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe, SetLike.mem_coe,
    ← sum_contMDiffSMulL_eq_self_of_sum_eq_one (fun i ↦ (χ i).contMDiff)
      (fun x ↦ by simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)) w]
  exact Submodule.sum_mem _ fun i _ ↦ mem_closure_range_of_mem_aeZeroOff hp
    (isClosed_tsupport _) (hχ i) (contMDiffSMulL_mem_aeZeroOff _ w)

variable (A p k) in
/-- **Density of `Cᵏ` sections.** For `1 ≤ p < ∞`, the elements of the bordered Sobolev space
`W^{k,p}(V)` given by `Cᵏ` sections are dense. -/
theorem denseRange_ofContMDiffSection [T2Space M] (hp : p ≠ ⊤) :
    DenseRange (ofContMDiffSection A p k) :=
  (denseRange_ofContMDiffSection_comp_ofLE A p k hp).mono <| by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩

end BorderedSobolevSection

end TauCeti
