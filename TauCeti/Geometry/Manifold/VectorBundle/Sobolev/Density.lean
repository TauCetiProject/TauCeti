/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Wkp
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin

/-!
# Smooth sections are dense in `W^{k,p}(V)`

Let `M` be a compact smooth manifold without boundary modelled on `ℂ`, let `V → M` be a smooth
real vector bundle with finite-dimensional model fibre `F`, and let `A` be a finite bundle atlas.
This file shows that for `1 ≤ p < ∞` and `k ≤ 1` the smooth sections of `V` are dense in the
Sobolev space `W^{k,p}(V)` of `TauCeti.SobolevSection A volume p k`
(`TauCeti.SobolevSection.denseRange_ofContMDiffSection`).

The proof localizes with a smooth partition of unity `χ` subordinate to the chart domains of `A`:
every `w` is the finite sum of the products `χ i • w` (`TauCeti.SobolevSection.sum_contMDiffSMulL`),
and `χ i • w` is supported in the closed set `tsupport (χ i) ⊆ A.dom i`
(`TauCeti.SobolevSection.contMDiffSMulL_mem_supportedIn`). An element supported in a closed
subset `L` of the domain of chart `i` is determined by its chart-`i` components, and every tuple of
chart-`i` Sobolev functions vanishing almost everywhere off `L` arises in this way. By the open
mapping theorem the inverse correspondence is a continuous linear map
`TauCeti.SobolevSection.extendLocalL` from the closed subspace
`TauCeti.SobolevSection.chartSupportedIn A p k i L` of such tuples into `W^{k,p}(V)`: it extends a
function on the chart by zero to a section. Existence of the extension is the only place where the
order `k ≤ 1` enters, through the invariance of the local Sobolev classes under changes of chart
(`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm`). The
localization step and the density are stated with this gluing property
`TauCeti.SobolevSection.HasChartGluing A p k` as a hypothesis, and it holds for `k ≤ 1`
(`TauCeti.SobolevSection.hasChartGluing_of_le_one`).

To approximate `u` supported in `L`, take a smooth cutoff `ψ` equal to one on `L` with support in
the chart domain, approximate the chart-`i` components of `u` by functions smooth on the chart image
(Meyers–Serrin, `TauCeti.Wkp.exists_contDiffOn_approximation`), and multiply them by `ψ`. The
products are the chart readings of smooth sections supported in `tsupport ψ`, whose chart-`i`
components converge to those of `u`; continuity of `extendLocalL` gives convergence in
`W^{k,p}(V)`.

## Main definitions

* `TauCeti.SobolevSection.supportedIn`: the elements of `W^{k,p}(V)` vanishing off a set `L ⊆ M`.
* `TauCeti.SobolevSection.chartSupportedIn`: the tuples of chart-`i` Sobolev functions vanishing
  off `L`.
* `TauCeti.SobolevSection.chartRestrictL`: the chart-`i` components of an element supported in
  `L`.
* `TauCeti.SobolevSection.HasChartGluing`: sections whose chart readings are locally `W^{k,p}` on
  a cover define elements of `W^{k,p}(V)`.
* `TauCeti.SobolevSection.extendLocalL`: extension by zero from the chart-`i` tuples vanishing
  off `L` to `W^{k,p}(V)`.

## Main results

* `TauCeti.SobolevSection.isClosed_supportedIn`, `TauCeti.SobolevSection.isClosed_chartSupportedIn`:
  both subspaces are closed, hence complete.
* `TauCeti.SobolevSection.sum_contMDiffSMulL`: a finite family of smooth functions summing to one
  decomposes every element of `W^{k,p}(V)`.
* `TauCeti.SobolevSection.chartRestrictL_extendLocalL`,
  `TauCeti.SobolevSection.extendLocalL_chartRestrictL`: extension by zero and the chart
  components are inverse to each other.
* `TauCeti.SobolevSection.dense_setOf_ae_eq_coord_of_hasChartGluing`: under the gluing property,
  the elements given by smooth sections are dense.
* `TauCeti.SobolevSection.dense_setOf_ae_eq_coord`,
  `TauCeti.SobolevSection.denseRange_ofContMDiffSection`: smooth sections are dense in
  `W^{k,p}(V)` for `p < ∞` and `k ≤ 1`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

open FiniteBundleAtlas

namespace SobolevSection

/-- The `Lᵖ` classes vanishing almost everywhere on the set where `P` holds form a closed set:
convergence in `Lᵖ` gives almost everywhere convergence along a subsequence. -/
private theorem isClosed_setOf_ae_imp_eq_zero {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] {ν : Measure X} (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : X → Prop) :
    IsClosed {f : Lp G p ν | ∀ᵐ y ∂ν, P y → f y = 0} := by
  refine IsSeqClosed.isClosed fun {f f₀} hf hlim ↦ ?_
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂ν, ∀ m, P y → f (ns m) y = 0 := ae_all_iff.2 fun m ↦ hf (ns m)
  filter_upwards [hae, hall] with y hy hm hP
  exact tendsto_nhds_unique hy (tendsto_const_nhds.congr fun m ↦ (hm m hP).symm)

section General

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (k : ℕ)

/-- The elements of `W^{k,p}(V)` supported in a set `L ⊆ M`: in every chart `i` the chart data
vanish almost everywhere at the points of `A.image i` lying over the complement of `L`. -/
def supportedIn (L : Set M) : Submodule ℝ (SobolevSection A μ p k) where
  carrier := {w | ∀ i, ∀ᵐ y ∂μ.restrict (A.image i),
    (A.chart i).symm y ∉ L → A.sectionChartData.chartValueL μ p k i w y = 0}
  add_mem' {w w'} hw hw' i := by
    filter_upwards [hw i, hw' i, Lp.coeFn_add (A.sectionChartData.chartValueL μ p k i w)
      (A.sectionChartData.chartValueL μ p k i w')] with y hy hy' hadd hL
    rw [Submodule.coe_add, map_add, hadd, Pi.add_apply, hy hL, hy' hL, add_zero]
  zero_mem' i := by
    filter_upwards [Lp.coeFn_zero F p (μ.restrict (A.image i))] with y hy _
    rw [ZeroMemClass.coe_zero, map_zero]
    exact hy
  smul_mem' c w hw i := by
    filter_upwards [hw i, Lp.coeFn_smul c (A.sectionChartData.chartValueL μ p k i w)]
      with y hy hsmul hL
    rw [Submodule.coe_smul, map_smul, hsmul, Pi.smul_apply, hy hL, smul_zero]

variable {A μ p k} in
theorem mem_supportedIn {L : Set M} {w : SobolevSection A μ p k} :
    w ∈ supportedIn A μ p k L ↔ ∀ i, ∀ᵐ y ∂μ.restrict (A.image i),
      (A.chart i).symm y ∉ L → A.sectionChartData.chartValueL μ p k i w y = 0 :=
  Iff.rfl

variable {A μ p k} in
theorem supportedIn_mono {L L' : Set M} (h : L ⊆ L') :
    supportedIn A μ p k L ≤ supportedIn A μ p k L' := fun _ hw i ↦ by
  filter_upwards [hw i] with y hy hL using hy fun h' ↦ hL (h h')

/-- The elements of `W^{k,p}(V)` supported in `L` form a closed subspace. -/
theorem isClosed_supportedIn (L : Set M) :
    IsClosed (supportedIn A μ p k L : Set (SobolevSection A μ p k)) := by
  have : (supportedIn A μ p k L : Set (SobolevSection A μ p k)) = ⋂ i : Fin A.n,
      (fun w : SobolevSection A μ p k ↦ A.sectionChartData.chartValueL μ p k i w) ⁻¹'
        {f | ∀ᵐ y ∂μ.restrict (A.image i), (A.chart i).symm y ∉ L → f y = 0} := by
    ext w
    simp only [SetLike.mem_coe, mem_supportedIn, mem_iInter, mem_preimage, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((A.sectionChartData.chartValueL μ p k i).continuous.comp continuous_subtype_val)

instance supportedIn.instCompleteSpace [IsManifold 𝓘(ℝ, E) 1 M] (L : Set M) :
    CompleteSpace (supportedIn A μ p k L) :=
  (isClosed_supportedIn A μ p k L).completeSpace_coe

/-- The tuples of chart-`i` Sobolev functions, one for each vector of the basis
`Module.finBasis ℝ F`, vanishing almost everywhere at the points of `A.image i` lying over the
complement of `L ⊆ M`. -/
def chartSupportedIn (i : Fin A.n) (L : Set M) :
    Submodule ℝ (Fin (finrank ℝ F) → Wkp μ (A.image i) p k) where
  carrier := {g | ∀ j, ∀ᵐ y ∂μ.restrict (A.image i),
    (A.chart i).symm y ∉ L → Wkp.value k (g j) y = 0}
  add_mem' {g g'} hg hg' j := by
    filter_upwards [hg j, hg' j, Lp.coeFn_add (Wkp.value k (g j)) (Wkp.value k (g' j))]
      with y hy hy' hadd hL
    rw [Pi.add_apply, Wkp.value_add, hadd, Pi.add_apply, hy hL, hy' hL, add_zero]
  zero_mem' j := by
    filter_upwards [Lp.coeFn_zero ℝ p (μ.restrict (A.image i))] with y hy _
    rw [Pi.zero_apply, ← Wkp.valueL_apply, map_zero, hy, Pi.zero_apply]
  smul_mem' c g hg j := by
    filter_upwards [hg j, Lp.coeFn_smul c (Wkp.value k (g j))] with y hy hsmul hL
    rw [Pi.smul_apply, Wkp.value_smul, hsmul, Pi.smul_apply, hy hL, smul_zero]

omit [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
variable {A μ p k} in
theorem mem_chartSupportedIn {i : Fin A.n} {L : Set M}
    {g : Fin (finrank ℝ F) → Wkp μ (A.image i) p k} :
    g ∈ chartSupportedIn A μ p k i L ↔ ∀ j, ∀ᵐ y ∂μ.restrict (A.image i),
      (A.chart i).symm y ∉ L → Wkp.value k (g j) y = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- The chart-`i` tuples vanishing off `L` form a closed subspace. -/
theorem isClosed_chartSupportedIn (i : Fin A.n) (L : Set M) :
    IsClosed (chartSupportedIn A μ p k i L : Set (Fin (finrank ℝ F) → Wkp μ (A.image i) p k)) := by
  have : (chartSupportedIn A μ p k i L : Set (Fin (finrank ℝ F) → Wkp μ (A.image i) p k)) =
      ⋂ j, (fun g : Fin (finrank ℝ F) → Wkp μ (A.image i) p k ↦ Wkp.valueL k (g j)) ⁻¹'
        {f | ∀ᵐ y ∂μ.restrict (A.image i), (A.chart i).symm y ∉ L → f y = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_chartSupportedIn, mem_iInter, mem_preimage, mem_ofPred_eq,
      Wkp.valueL_apply]
  rw [this]
  exact isClosed_iInter fun j ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((Wkp.valueL k).continuous.comp (continuous_apply j))

instance chartSupportedIn.instCompleteSpace (i : Fin A.n) (L : Set M) :
    CompleteSpace (chartSupportedIn A μ p k i L) :=
  (isClosed_chartSupportedIn A μ p k i L).completeSpace_coe

variable {A μ p k} in
/-- The chart-`i` components of an element supported in `L` vanish off `L`. -/
theorem mem_chartSupportedIn_of_mem_supportedIn {L : Set M} {w : SobolevSection A μ p k}
    (hw : w ∈ supportedIn A μ p k L) (i : Fin A.n) :
    (w : A.sectionChartData.SobolevData μ p k) i ∈ chartSupportedIn A μ p k i L := fun j ↦ by
  filter_upwards [hw i, A.sectionChartData.chartValueL_apply_ae μ p k i w] with y hy happ hL
  have h := congrArg (fun v ↦ (finBasis ℝ F).repr v j) ((happ.symm.trans (hy hL)))
  rw [(finBasis ℝ F).repr_sum_self, map_zero] at h
  exact h

/-- The chart-`i` components of the elements of `W^{k,p}(V)` supported in `L`, as a continuous
linear map into the chart-`i` tuples vanishing off `L`. -/
def chartRestrictL (i : Fin A.n) (L : Set M) :
    supportedIn A μ p k L →L[ℝ] chartSupportedIn A μ p k i L :=
  ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun i : Fin A.n ↦ Fin (finrank ℝ F) → Wkp μ (A.image i) p k) i).comp
    ((A.sectionChartData.sobolevSections μ p k).subtypeL.comp
      (supportedIn A μ p k L).subtypeL)).codRestrict _
    fun w ↦ mem_chartSupportedIn_of_mem_supportedIn w.2 i

@[simp]
theorem coe_chartRestrictL_apply (i : Fin A.n) (L : Set M) (w : supportedIn A μ p k L) :
    (chartRestrictL A μ p k i L w : Fin (finrank ℝ F) → Wkp μ (A.image i) p k) =
      ((w : SobolevSection A μ p k) : A.sectionChartData.SobolevData μ p k) i :=
  (rfl)

variable {A μ p k}

variable [IsManifold 𝓘(ℝ, E) ∞ M] {φ : M → ℝ}

/-- Multiplication by a smooth function `φ` takes values in the elements supported in
`tsupport φ`. -/
theorem contMDiffSMulL_mem_supportedIn (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection A μ p k) :
    contMDiffSMulL A μ p k hφ w ∈ supportedIn A μ p k (tsupport φ) := fun i ↦ by
  filter_upwards [chartValueL_contMDiffSMulL_ae hφ w i] with y hy hL
  rw [hy, image_eq_zero_of_notMem_tsupport hL, zero_smul]

/-- Smooth multiplication depends only on the multiplier, not on the proof of its smoothness. -/
private theorem contMDiffSMulL_congr {φ ψ : M → ℝ} (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) (h : φ = ψ) :
    contMDiffSMulL A μ p k hφ = contMDiffSMulL A μ p k hψ := by
  subst h
  rfl

/-- **Partition of unity.** If smooth functions `φ i`, finitely many, sum to one at every point,
then every element of `W^{k,p}(V)` is the sum of its products with the `φ i`. -/
theorem sum_contMDiffSMulL {ι : Type*} [Fintype ι] {φ : ι → M → ℝ}
    (hφ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (φ i)) (h : ∀ x, ∑ i, φ i x = 1)
    (w : SobolevSection A μ p k) : ∑ i, contMDiffSMulL A μ p k (hφ i) w = w := by
  classical
  -- The sum over a finite set `s` is multiplication by the partial sum of the `φ i`.
  have key : ∀ s : Finset ι, ∃ hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ fun x ↦ ∑ i ∈ s, φ i x,
      ∑ i ∈ s, contMDiffSMulL A μ p k (hφ i) w = contMDiffSMulL A μ p k hs w := by
    intro s
    induction s using Finset.cons_induction with
    | empty =>
      refine ⟨by simpa using contMDiff_const (c := (0 : ℝ)), ?_⟩
      rw [Finset.sum_empty, contMDiffSMulL_congr _ (contMDiff_const (c := (0 : ℝ)))
        (funext fun x ↦ Finset.sum_empty), contMDiffSMulL_const]
      simp
    | cons a s ha ih =>
      obtain ⟨hs, hsum⟩ := ih
      have hcons : (fun x ↦ ∑ i ∈ Finset.cons a s ha, φ i x) =
          φ a + fun x ↦ ∑ i ∈ s, φ i x := funext fun x ↦ by rw [Finset.sum_cons, Pi.add_apply]
      refine ⟨hcons ▸ (hφ a).add hs, ?_⟩
      rw [Finset.sum_cons, hsum, contMDiffSMulL_congr _ ((hφ a).add hs) hcons, contMDiffSMulL_add,
        add_apply]
  obtain ⟨hs, hsum⟩ := key Finset.univ
  rw [hsum, contMDiffSMulL_congr _ (contMDiff_const (c := (1 : ℝ))) (funext h),
    contMDiffSMulL_const]
  simp

end General

section Chart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ℂ M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Gluing from chart readings at order `k`.** Every section `s` of `V` defines an element of
`W^{k,p}(V)` as soon as its readings `A.coord i s` lie in the local Sobolev classes
`MemWkpLoc p (U i) k` on open sets `U i` such that every point `x` of `M` lies in the domain of a
chart `i` with `A.chart i x ∈ U i`. This holds for `k ≤ 1`
(`TauCeti.SobolevSection.hasChartGluing_of_le_one`); it is the only input on the order `k` used
for the extension by zero `TauCeti.SobolevSection.extendLocalL` and the density of smooth
sections. -/
@[expose] def HasChartGluing : Prop :=
  ∀ U : Fin A.n → Set ℂ, (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ A.dom i ∧ A.chart i x ∈ U i) →
    ∀ s : ∀ x, V x, (∀ i, MemWkpLoc p (U i) k (A.coord i s)) →
      ∃ w : SobolevSection A volume p k, ∀ i,
        A.sectionChartData.chartValueL volume p k i w =ᵐ[volume.restrict (A.image i)] A.coord i s

variable {A p k}

/-- **Gluing at orders `k ≤ 1`.** This is
`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm` for the
charts and trivializations of `A`. -/
theorem hasChartGluing_of_le_one [IsManifold 𝓘(ℝ, ℂ) 1 M] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, ℂ)]
    (hk : k ≤ 1) : HasChartGluing A p k := fun U hU hcover s hs ↦
  exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm hk A.chart
    (fun _ ↦ IsManifold.chart_mem_maximalAtlas _) A.triv U hU
    (fun x ↦ let ⟨i, hi, hiU⟩ := hcover x
      ⟨i, A.dom_subset_chart_source i hi, A.dom_subset_baseSet i hi, hiU⟩)
    fun i ↦ by simpa only [funext (A.coord_def i s)] using hs i

variable (A) in
open Classical in
/-- The section whose coordinates in chart `i` are `G` on the domain of the chart, and which
vanishes off it. -/
private def chartSection (i : Fin A.n) (G : ℂ → F) : ∀ x, V x := fun x ↦
  if x ∈ A.dom i then (A.triv i).symmₗ ℝ x (G (A.chart i x)) else 0

omit [FiniteDimensional ℝ F] in
private theorem triv_chartSection {i : Fin A.n} (G : ℂ → F) {x : M} (hx : x ∈ A.dom i) :
    (A.triv i ⟨x, chartSection A i G x⟩).2 = G (A.chart i x) := by
  have hb := A.dom_subset_baseSet i hx
  simp only [chartSection, ite_eq_left hx, Trivialization.symmₗ_apply _ hb,
    Trivialization.apply_mk_symm _ hb]

omit [FiniteDimensional ℝ F] in
private theorem coord_chartSection {i : Fin A.n} (G : ℂ → F) {y : ℂ} (hy : y ∈ A.image i) :
    A.coord i (chartSection A i G) y = G y := by
  obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
  rw [A.coord_chart _ hx, triv_chartSection G hx]

omit [FiniteDimensional ℝ F] in
private theorem chartSection_eq_zero {i : Fin A.n} {G : ℂ → F} {x : M}
    (h : x ∈ A.dom i → G (A.chart i x) = 0) : chartSection A i G x = 0 := by
  by_cases hx : x ∈ A.dom i
  · simp only [chartSection, ite_eq_left hx, h hx, map_zero]
  · simp only [chartSection, ite_eq_right hx]

omit [FiniteDimensional ℝ F] in
/-- The coordinates of a section vanish at the points over which it vanishes. -/
private theorem coord_eq_zero {s : ∀ x, V x} {i : Fin A.n} {y : ℂ} (hy : y ∈ A.image i)
    (h : s ((A.chart i).symm y) = 0) : A.coord i s y = 0 := by
  rw [A.coord_def, h]
  simpa only [A.coord_def, Pi.zero_apply] using A.coord_zero i hy

section Extension

variable [IsManifold 𝓘(ℝ, ℂ) 1 M]

/-- An element supported in a subset `L` of the domain of chart `i` with vanishing chart-`i`
components vanishes: over `L` its components in every other chart are coordinate changes of its
chart-`i` components. -/
private theorem eq_zero_of_chartRestrictL_eq_zero {i : Fin A.n} {L : Set M} (hLi : L ⊆ A.dom i)
    {w : supportedIn A volume p k L} (hw : chartRestrictL A volume p k i L w = 0) : w = 0 := by
  have hC := A.aeTransition_sectionChartData volume
  have hslot : ((w : SobolevSection A volume p k) : A.sectionChartData.SobolevData volume p k) i =
      0 :=
    congrArg Subtype.val hw
  have hi : ∀ᵐ y ∂volume.restrict (A.image i),
      A.sectionChartData.chartValueL volume p k i w y = 0 := by
    filter_upwards [A.sectionChartData.chartValueL_apply_ae volume p k i w,
      Lp.coeFn_zero ℝ p ((volume : Measure ℂ).restrict (A.image i))] with y hy h0
    rw [hy]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hslot, Pi.zero_apply, ← Wkp.valueL_apply, map_zero]
    exact (congrArg (· • finBasis ℝ F j) h0).trans (zero_smul ℝ _)
  refine Subtype.ext (SobolevSection.eq_of_ae_eq_coord (s := 0) (fun i' ↦ ?_) fun i' ↦ ?_)
  · have hcomp := (A.sectionChartData.compatible_iff volume p k).1
      (A.sectionChartData.compatible_of_mem hC (w : SobolevSection A volume p k).2 i i')
    have htr := A.sectionChartData.aeTransition_iff.1 hC (i' := i') hi
    have hov : ∀ᵐ y ∂volume.restrict (A.image i'), y ∈ A.overlap i i' →
        A.sectionChartData.chartValueL volume p k i' w y = 0 := by
      have h' : ∀ᵐ y ∂volume.restrict (A.overlap i i'),
          A.sectionChartData.chartValueL volume p k i' w y = 0 := by
        filter_upwards [hcomp, htr] with y hy htr
        rw [hy, htr, map_zero]
      exact ae_restrict_of_ae ((ae_restrict_iff' (A.isOpen_overlap i i').measurableSet).1 h')
    filter_upwards [w.2 i', hov, ae_restrict_mem (A.image i').isOpen.measurableSet]
      with y hy hyo hyi
    rw [A.coord_zero i' hyi]
    by_cases hL : (A.chart i').symm y ∈ L
    · refine hyo ?_
      obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hyi
      rw [(A.chart i').left_inv (A.dom_subset_chart_source i' hx)] at hL
      exact A.chart_mem_overlap (hLi hL) hx
    · exact hy hL
  · simp only [ZeroMemClass.coe_zero, map_zero]
    filter_upwards [Lp.coeFn_zero F p ((volume : Measure ℂ).restrict (A.image i')),
      ae_restrict_mem (A.image i').isOpen.measurableSet] with y h0 hy
    rw [A.coord_zero i' hy]
    exact h0

omit [IsManifold 𝓘(ℝ, ℂ) 1 M] in
/-- Every chart-`i` tuple vanishing off a closed subset `L` of the domain of chart `i` consists of
the chart-`i` components of an element supported in `L`: extend the function it defines on the
chart by zero to a section. -/
private theorem exists_chartRestrictL_eq (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartSupportedIn A volume p k i L) :
    ∃ w, chartRestrictL A volume p k i L w = g := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : ℂ → F, ∀ y, G y = if (A.chart i).symm y ∈ L then
      ∑ j, Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j) y • finBasis ℝ F j
      else 0 := ⟨_, fun _ ↦ rfl⟩
  -- The section `t`, which vanishes off `L`.
  have ht : ∀ x ∉ L, chartSection A i G x = 0 := fun x hx ↦ chartSection_eq_zero fun hxi ↦ by
    rw [hG, ite_eq_right (by rwa [(A.chart i).left_inv (A.dom_subset_chart_source i hxi)])]
  have hcoord : ∀ i', ∀ y ∈ A.image i', (A.chart i').symm y ∉ L →
      A.coord i' (chartSection A i G) y = 0 := fun i' y hy hL ↦ coord_eq_zero hy (ht _ hL)
  -- Chart `i` near `L`, and every chart away from `L`.
  have hopen : ∀ i', IsOpen ((A.image i' : Set ℂ) ∩ (A.chart i').symm ⁻¹' Lᶜ) := fun i' ↦
    ((A.chart i').continuousOn_symm.mono ((A.image_subset_chart_image_closure_dom i').trans
      ((A.chart_image_closure_dom_subset i').trans inter_subset_left))).isOpen_inter_preimage
        (A.image i').isOpen hL.isOpen_compl
  let U : Fin A.n → Set ℂ := fun i' ↦
    if i' = i then A.image i else A.image i' ∩ (A.chart i').symm ⁻¹' Lᶜ
  have hU : ∀ i', IsOpen (U i') := fun i' ↦ by
    simp only [U]
    split_ifs
    · exact (A.image i).isOpen
    · exact hopen i'
  have hcover : ∀ x, ∃ i', x ∈ A.dom i' ∧ A.chart i' x ∈ U i' := fun x ↦ by
    by_cases hx : x ∈ L
    · refine ⟨i, hLi hx, ?_⟩
      simp only [U, ↓reduceIte]
      exact A.mem_image.2 ⟨x, hLi hx, rfl⟩
    · obtain ⟨i', hi'⟩ := A.exists_mem_dom x
      refine ⟨i', hi', ?_⟩
      simp only [U]
      split_ifs with hii
      · exact hii ▸ A.mem_image.2 ⟨x, hi', rfl⟩
      · exact ⟨A.mem_image.2 ⟨x, hi', rfl⟩, by
          rwa [mem_preimage, (A.chart i').left_inv (A.dom_subset_chart_source i' hi')]⟩
  have hmem : ∀ i', MemWkpLoc p (U i') k (A.coord i' (chartSection A i G)) := fun i' ↦ by
    simp only [U]
    split_ifs with hii
    · rw [hii]
      refine MemWkpLoc.congr_fun ?_ (fun y hy ↦ (coord_chartSection G hy).symm)
        (A.image i).isOpen.measurableSet
      refine (finBasis ℝ F).memWkpLoc_iff.2 fun j ↦ ?_
      refine (Wkp.memWkpLoc_value_of_ae_le (Opens.ext (A.image i).isOpen.interior_eq)
        (ae_subset.2 (by simp))
        ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j)).congr_ae ?_
      filter_upwards [g.2 j] with y hy
      rw [hG]
      split_ifs with hL'
      · rw [(finBasis ℝ F).repr_sum_self]
      · rw [hy hL', map_zero, Finsupp.coe_zero, Pi.zero_apply]
    · exact memWkpLoc_zero_fun.congr_fun (fun y hy ↦ (hcoord i' y hy.1 hy.2).symm)
        (hopen i').measurableSet
  obtain ⟨w, hw⟩ := h U hU hcover _ hmem
  have hwL : w ∈ supportedIn A volume p k L := fun i' ↦ by
    filter_upwards [hw i', ae_restrict_mem (A.image i').isOpen.measurableSet] with y hy hyi hL'
    rw [hy]
    exact hcoord i' y hyi hL'
  refine ⟨⟨w, hwL⟩, Subtype.ext <| funext fun j ↦ Wkp.ext k <| Lp.ext ?_⟩
  have hs : A.sectionChartData.chartValueL volume p k i w =ᵐ[volume.restrict (A.image i)]
      A.sectionChartData.coord i (chartSection A i G) :=
    (hw i).trans (A.sectionChartData_coord_ae_eq volume i _).symm
  rw [coe_chartRestrictL_apply]
  filter_upwards [SectionChartData.value_ae_eq_repr_coord hs j, g.2 j,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h1 h2 hy
  refine h1.trans ?_
  rw [A.sectionChartData_coord_of_mem _ hy, coord_chartSection G hy, hG]
  split_ifs with hL'
  · rw [(finBasis ℝ F).repr_sum_self]
  · rw [map_zero, Finsupp.coe_zero, Pi.zero_apply, h2 hL']

variable (A p k) in
/-- The chart-`i` components of the elements supported in a closed subset `L` of the domain of
chart `i`, as a linear equivalence onto the chart-`i` tuples vanishing off `L`. -/
private def chartRestrictEquiv (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) :
    supportedIn A volume p k L ≃ₗ[ℝ] chartSupportedIn A volume p k i L :=
  LinearEquiv.ofBijective (chartRestrictL A volume p k i L).toLinearMap
    ⟨(injective_iff_map_eq_zero _).2 fun _ hw ↦ eq_zero_of_chartRestrictL_eq_zero hLi hw,
      exists_chartRestrictL_eq h hL hLi⟩

private theorem chartRestrictL_chartRestrictEquiv_symm (h : HasChartGluing A p k) {i : Fin A.n}
    {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartSupportedIn A volume p k i L) :
    chartRestrictL A volume p k i L ((chartRestrictEquiv A p k h hL hLi).symm g) = g := by
  exact (chartRestrictEquiv A p k h hL hLi).apply_symm_apply g

private theorem chartRestrictEquiv_symm_chartRestrictL (h : HasChartGluing A p k) {i : Fin A.n}
    {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : supportedIn A volume p k L) :
    (chartRestrictEquiv A p k h hL hLi).symm (chartRestrictL A volume p k i L w) = w := by
  exact (chartRestrictEquiv A p k h hL hLi).symm_apply_apply w

/-- **Extension by zero.** Let `L` be a closed subset of the domain of chart `i`. A tuple of
chart-`i` Sobolev functions vanishing almost everywhere off `L` defines an element of
`W^{k,p}(V)`, supported in `L`, whose chart-`i` components are the given functions: the section
equal to the function they define on the chart and zero off it. This is a continuous linear map
from the closed subspace `TauCeti.SobolevSection.chartSupportedIn A volume p k i L` into
`W^{k,p}(V)`, by the closed graph theorem. -/
def extendLocalL (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : chartSupportedIn A volume p k i L →L[ℝ] SobolevSection A volume p k :=
  ContinuousLinearMap.ofSeqClosedGraph
    (g := (supportedIn A volume p k L).subtype ∘ₗ
      (chartRestrictEquiv A p k h hL hLi).symm.toLinearMap)
    fun u x y hu hy ↦ by
      set e := chartRestrictEquiv A p k h hL hLi
      -- The limit `y` is supported in `L`, and its chart-`i` components are the limit `x`.
      have hyL : y ∈ supportedIn A volume p k L :=
        (isClosed_supportedIn A volume p k L).mem_of_tendsto hy
          (Eventually.of_forall fun n ↦ (e.symm (u n)).2)
      have hconv : Tendsto (fun n ↦ e.symm (u n)) atTop (𝓝 ⟨y, hyL⟩) := tendsto_subtype_rng.2 hy
      have hx : chartRestrictL A volume p k i L ⟨y, hyL⟩ = x :=
        tendsto_nhds_unique (((chartRestrictL A volume p k i L).continuous.tendsto _).comp hconv)
          (hu.congr fun n ↦ (chartRestrictL_chartRestrictEquiv_symm h hL hLi (u n)).symm)
      rw [← hx, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        chartRestrictEquiv_symm_chartRestrictL, Submodule.subtype_apply]

theorem extendLocalL_mem_supportedIn (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartSupportedIn A volume p k i L) :
    extendLocalL h hL hLi g ∈ supportedIn A volume p k L :=
  ((chartRestrictEquiv A p k h hL hLi).symm g).2

/-- The chart-`i` components of the extension by zero are the given tuple. -/
theorem chartRestrictL_extendLocalL (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartSupportedIn A volume p k i L) :
    chartRestrictL A volume p k i L ⟨_, extendLocalL_mem_supportedIn h hL hLi g⟩ = g :=
  chartRestrictL_chartRestrictEquiv_symm h hL hLi g

/-- The chart-`i` components of the extension by zero are the given functions. -/
theorem coe_extendLocalL_apply (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartSupportedIn A volume p k i L) :
    ((extendLocalL h hL hLi g : SobolevSection A volume p k) :
      A.sectionChartData.SobolevData volume p k) i =
      (g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) :=
  congrArg Subtype.val (chartRestrictL_extendLocalL h hL hLi g)

/-- An element supported in `L` is the extension by zero of its chart-`i` components. -/
theorem extendLocalL_chartRestrictL (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : supportedIn A volume p k L) :
    extendLocalL h hL hLi (chartRestrictL A volume p k i L w) = w :=
  congrArg Subtype.val (chartRestrictEquiv_symm_chartRestrictL h hL hLi w)

end Extension

section Density

variable [IsManifold 𝓘(ℝ, ℂ) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

omit [FiniteDimensional ℝ F] in
/-- The product of a smooth function `ψ` supported in the domain of chart `i` with the section
equal in chart `i` to a function `G` smooth on the chart image is a smooth section. -/
private theorem contMDiff_smul_chartSection {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ) (hψi : tsupport ψ ⊆ A.dom i) {G : ℂ → F}
    (hG : ContDiffOn ℝ ∞ G (A.image i)) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞
      fun x ↦ TotalSpace.mk' F x (ψ x • chartSection A i G x) := by
  intro x₀
  by_cases hx₀ : x₀ ∈ A.dom i
  · rw [(A.triv i).contMDiffAt_section_iff (A.dom_subset_baseSet i hx₀)]
    have hev : (fun x ↦ ψ x • G (A.chart i x)) =ᶠ[𝓝 x₀]
        fun x ↦ (A.triv i ⟨x, ψ x • chartSection A i G x⟩).2 := by
      filter_upwards [(A.isOpen_dom i).mem_nhds hx₀] with x hx
      have hb := A.dom_subset_baseSet i hx
      rw [← (A.triv i).continuousLinearMapAt_apply_of_mem (R := ℝ) hb, map_smul,
        (A.triv i).continuousLinearMapAt_apply_of_mem (R := ℝ) hb, triv_chartSection G hx]
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev.symm
    have hc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (A.chart i) x₀ :=
      contMDiffOn_chart.contMDiffAt
        ((A.chart i).open_source.mem_nhds (A.dom_subset_chart_source i hx₀))
    have hGc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) ∞ G (A.chart i x₀) :=
      (hG.contDiffAt ((A.image i).isOpen.mem_nhds (A.mem_image.2 ⟨x₀, hx₀, rfl⟩))).contMDiffAt
    exact (hψ x₀).smul (hGc.comp x₀ hc)
  · have h0 : ψ =ᶠ[𝓝 x₀] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx₀ (hψi h)
    have hx₀b := mem_baseSet_trivializationAt F V x₀
    rw [(trivializationAt F V x₀).contMDiffAt_section_iff hx₀b]
    refine (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [h0, (trivializationAt F V x₀).open_baseSet.mem_nhds hx₀b] with x hx hxb
    rw [hx, Pi.zero_apply, zero_smul, ← (trivializationAt F V x₀).continuousLinearMapAt_apply_of_mem
      (R := ℝ) hxb, map_zero]

variable (k) in
/-- `C^∞` sections as `Cᵏ` sections. -/
private def ofLE : Cₛ^∞⟮𝓘(ℝ, ℂ); F, V⟯ →ₗ[ℝ] Cₛ^k⟮𝓘(ℝ, ℂ); F, V⟯ where
  toFun s := ⟨s, s.contMDiff.of_le (mod_cast le_top)⟩
  map_add' _ _ := ContMDiffSection.ext fun _ ↦ rfl
  map_smul' _ _ := ContMDiffSection.ext fun _ ↦ rfl

variable (A p k) in
/-- The elements of `W^{k,p}(V)` given by `C^∞` sections. -/
private def smoothRange : Submodule ℝ (SobolevSection A volume p k) :=
  LinearMap.range ((ofContMDiffSection A volume p k).comp (ofLE k))

private theorem mem_smoothRange_iff {w : SobolevSection A volume p k} :
    w ∈ smoothRange A p k ↔ ∃ s : Cₛ^∞⟮𝓘(ℝ, ℂ); F, V⟯, ∀ i,
      A.sectionChartData.chartValueL volume p k i w =ᵐ[volume.restrict (A.image i)]
        A.coord i s := by
  refine ⟨?_, fun ⟨s, hs⟩ ↦ ⟨s, eq_of_ae_eq_coord
    (chartValueL_ofContMDiffSection_ae A volume p k (ofLE k s)) hs⟩⟩
  rintro ⟨s, rfl⟩
  exact ⟨s, chartValueL_ofContMDiffSection_ae A volume p k (ofLE k s)⟩

/-- **The localized density step.** An element supported in a closed subset `L` of the domain of
chart `i` is a limit of elements given by `C^∞` sections. Take a smooth cutoff `ψ` equal to one on
`L` with support in the chart domain, approximate the chart-`i` components by functions smooth on
the chart image (Meyers–Serrin), and multiply them by `ψ`: these are the chart readings of smooth
sections supported in `tsupport ψ`, and extension by zero is continuous. -/
private theorem mem_topologicalClosure_smoothRange [T2Space M] [CompactSpace M] (hp : p ≠ ⊤)
    (h : HasChartGluing A p k) {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    {u : SobolevSection A volume p k} (hu : u ∈ supportedIn A volume p k L) :
    u ∈ (smoothRange A p k).topologicalClosure := by
  -- A smooth cutoff `ψ`, equal to one on `L`, with support in the domain of chart `i`.
  obtain ⟨O, hO, hLO, hOi⟩ := normal_exists_closure_subset hL (A.isOpen_dom i) hLi
  obtain ⟨ψ, hψ, -, hψO, hψL⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, ℂ) (n := ⊤) hO hL hLO
  have hψi : tsupport ψ ⊆ A.dom i := by rw [tsupport, hψO]; exact hOi
  have hLψ : L ⊆ tsupport ψ := fun x hx ↦ subset_tsupport ψ (by
    rw [Function.mem_support, (hψL x).1 hx]; exact one_ne_zero)
  have hu' := supportedIn_mono hLψ hu
  -- Multiplication by `ψ`, read in chart `i`, on the chart-`i` Sobolev functions.
  obtain ⟨T, -, hT⟩ : ∃ T : Wkp volume (A.image i) p k →L[ℝ] Wkp volume (A.image i) p k,
      (∀ (b : SobolevSection A volume p k) (j : Fin (finrank ℝ F)),
        (contMDiffSMulL A volume p k hψ b : A.sectionChartData.SobolevData volume p k) i j =
          T ((b : A.sectionChartData.SobolevData volume p k) i j)) ∧
      ∀ v, (Wkp.value k (T v) : ℂ → ℝ) =ᵐ[volume.restrict (A.image i)]
        fun y ↦ ψ ((A.chart i).symm y) * Wkp.value k v y :=
    ⟨_, fun b j ↦ contMDiffSMulL_apply hψ b i j, fun v ↦ Wkp.value_contDiffOnSMulL_ae _ _ _ k _ v⟩
  -- `T` fixes the chart-`i` components of `u`, since `ψ = 1` on `L`.
  set ui : Fin (finrank ℝ F) → Wkp volume (A.image i) p k :=
    ((u : SobolevSection A volume p k) : A.sectionChartData.SobolevData volume p k) i
  have hTu : ∀ j, T (ui j) = ui j := fun j ↦ Wkp.ext k <| Lp.ext <| by
    filter_upwards [hT (ui j), mem_chartSupportedIn_of_mem_supportedIn hu i j] with y h1 h2
    rw [h1]
    by_cases hy : (A.chart i).symm y ∈ L
    · rw [(hψL _).1 hy, one_mul]
    · rw [h2 hy, mul_zero]
  -- Meyers–Serrin approximations of the chart-`i` components.
  choose v f hf hvf hlim using fun j ↦ Wkp.exists_contDiffOn_approximation hp k (ui j)
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℂ → F, ∀ m y, G m y = ∑ j, f j m y • finBasis ℝ F j :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hGs : ∀ m, ContDiffOn ℝ ∞ (G m) (A.image i) := fun m ↦ by
    rw [funext (hG m)]
    exact ContDiffOn.sum fun j _ ↦ (hf j m).smul contDiffOn_const
  -- The smooth sections `ψ • G m` and their elements `a m`, supported in `tsupport ψ`.
  let s : ℕ → Cₛ^∞⟮𝓘(ℝ, ℂ); F, V⟯ := fun m ↦
    ⟨fun x ↦ ψ x • chartSection A i (G m) x, contMDiff_smul_chartSection hψ hψi (hGs m)⟩
  let a : ℕ → SobolevSection A volume p k := fun m ↦ ofContMDiffSection A volume p k (ofLE k (s m))
  have hs : ∀ m i', A.sectionChartData.chartValueL volume p k i' (a m)
      =ᵐ[volume.restrict (A.image i')] A.coord i' fun x ↦ ψ x • chartSection A i (G m) x :=
    fun m i' ↦ chartValueL_ofContMDiffSection_ae A volume p k (ofLE k (s m)) i'
  have ha : ∀ m, a m ∈ supportedIn A volume p k (tsupport ψ) := fun m i' ↦ by
    filter_upwards [hs m i', ae_restrict_mem (A.image i').isOpen.measurableSet] with y hy hyi hL'
    rw [hy, A.coord_fun_smul i' ψ _ hyi, image_eq_zero_of_notMem_tsupport hL', zero_smul]
  -- The chart-`i` components of `a m` are `T (v j m)`.
  have hcomp : ∀ m j, ((a m : SobolevSection A volume p k) :
      A.sectionChartData.SobolevData volume p k) i j = T (v j m) := fun m j ↦
    Wkp.ext k <| Lp.ext <| by
      have hs' : A.sectionChartData.chartValueL volume p k i (a m)
          =ᵐ[volume.restrict (A.image i)]
            A.sectionChartData.coord i fun x ↦ ψ x • chartSection A i (G m) x :=
        (hs m i).trans (A.sectionChartData_coord_ae_eq volume i _).symm
      filter_upwards [SectionChartData.value_ae_eq_repr_coord hs' j, hT (v j m), hvf j m,
        ae_restrict_mem (A.image i).isOpen.measurableSet] with y h1 h2 h3 hy
      refine h1.trans ?_
      rw [A.sectionChartData_coord_of_mem _ hy, A.coord_fun_smul i ψ _ hy,
        coord_chartSection (G m) hy, hG, map_smul, Finsupp.smul_apply,
        (finBasis ℝ F).repr_sum_self, smul_eq_mul, ← h3]
      exact h2.symm
  -- Convergence of the chart-`i` components, then of the extensions by zero.
  have hconv : Tendsto (fun m ↦ chartRestrictL A volume p k i (tsupport ψ) ⟨a m, ha m⟩) atTop
      (𝓝 (chartRestrictL A volume p k i (tsupport ψ) ⟨u, hu'⟩)) := by
    refine tendsto_subtype_rng.2 (tendsto_pi_nhds.2 fun j ↦ ?_)
    simp only [coe_chartRestrictL_apply, hcomp]
    have hT' := (T.continuous.tendsto _).comp (hlim j)
    rw [hTu j] at hT'
    exact hT'
  have hE := ((extendLocalL h (isClosed_tsupport ψ) hψi).continuous.tendsto _).comp hconv
  simp only [Function.comp_def, extendLocalL_chartRestrictL] at hE
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hE
    (Eventually.of_forall fun m ↦ Submodule.le_topologicalClosure _ ⟨s m, rfl⟩)

/-- **Density of smooth sections, assuming gluing at order `k`.** On a compact Hausdorff base, for
`1 ≤ p < ∞`, the elements of `W^{k,p}(V)` whose chart data are the coordinates of a `C^∞` section
are dense, provided sections with locally `W^{k,p}` chart readings define elements of
`W^{k,p}(V)` (`TauCeti.SobolevSection.HasChartGluing`). -/
theorem dense_setOf_ae_eq_coord_of_hasChartGluing [T2Space M] [CompactSpace M] (hp : p ≠ ⊤)
    (h : HasChartGluing A p k) :
    Dense {w : SobolevSection A volume p k | ∃ s : Cₛ^∞⟮𝓘(ℝ, ℂ); F, V⟯, ∀ i,
      A.sectionChartData.chartValueL volume p k i w =ᵐ[volume.restrict (A.image i)]
        A.coord i s} := by
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  intro w
  refine closure_mono (fun w' hw' ↦ mem_smoothRange_iff.1 hw') ?_
  rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe,
    ← sum_contMDiffSMulL (fun i ↦ (χ i).contMDiff)
      (fun x ↦ by simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)) w]
  exact Submodule.sum_mem _ fun i _ ↦ mem_topologicalClosure_smoothRange hp h
    (isClosed_tsupport _) (hχ i) (contMDiffSMulL_mem_supportedIn _ w)

/-- **Smooth sections are dense in `W^{k,p}(V)`** for `1 ≤ p < ∞` and `k ≤ 1`, on a compact
Hausdorff base: the elements of `W^{k,p}(V)` whose chart data are the coordinates of a `C^∞`
section are dense. -/
theorem dense_setOf_ae_eq_coord [T2Space M] [CompactSpace M] (hp : p ≠ ⊤) (hk : k ≤ 1) :
    Dense {w : SobolevSection A volume p k | ∃ s : Cₛ^∞⟮𝓘(ℝ, ℂ); F, V⟯, ∀ i,
      A.sectionChartData.chartValueL volume p k i w =ᵐ[volume.restrict (A.image i)]
        A.coord i s} :=
  dense_setOf_ae_eq_coord_of_hasChartGluing hp (hasChartGluing_of_le_one hk)

/-- **`Cᵏ` sections are dense in `W^{k,p}(V)`** for `1 ≤ p < ∞` and `k ≤ 1`, on a compact
Hausdorff base. In fact the `C^∞` sections are dense
(`TauCeti.SobolevSection.dense_setOf_ae_eq_coord`). -/
theorem denseRange_ofContMDiffSection [T2Space M] [CompactSpace M] (hp : p ≠ ⊤) (hk : k ≤ 1) :
    DenseRange (ofContMDiffSection A volume p k) := by
  refine (dense_setOf_ae_eq_coord hp hk).mono ?_
  rintro w ⟨s, hs⟩
  exact ⟨ofLE k s, eq_of_ae_eq_coord (chartValueL_ofContMDiffSection_ae A volume p k (ofLE k s)) hs⟩

end Density

end Chart

end SobolevSection

end TauCeti
