/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
import TauCeti.MeasureTheory.Function.Lp.Closed

/-!
# Sobolev sections vanishing off a set, and extension by zero from one chart

Let `M` be a manifold without boundary modelled on a finite-dimensional real inner product space
`E`, let `V → M` be a real vector bundle with finite-dimensional model fibre `F`, and let `A` be a
finite bundle atlas. For a set `L ⊆ M`, `TauCeti.SobolevSection.aeZeroOff A μ p k L` is the closed
subspace of `W^{k,p}(V)` of the elements whose chart data vanish almost everywhere over the
complement of `L`. When `L` is closed these are the elements supported in `L`; for a set `L` that
is not closed the condition is weaker (for instance it holds for every element when `Lᶜ` is a
point).

For `L` inside the domain of chart `i`, an element of `aeZeroOff A μ p k L` is determined by its
chart-`i` components (`TauCeti.SobolevSection.chartRestrictL_injective`), which lie in the closed
subspace `TauCeti.SobolevSection.chartAeZeroOff A μ p k i L` of chart-`i` tuples vanishing almost
everywhere off `L`. When, for closed `L`, every such tuple arises in this way (the property
`TauCeti.SobolevSection.HasExtensionByZero A μ p k`), the chart-`i` components form a linear
equivalence (`TauCeti.SobolevSection.chartRestrictEquiv`). Its inverse followed by the inclusion is
the extension by zero `TauCeti.SobolevSection.extendLocalL` from chart-`i` tuples to `W^{k,p}(V)`,
which is continuous by the closed graph theorem.

## Main definitions

* `TauCeti.SobolevSection.aeZeroOff`: the elements of `W^{k,p}(V)` vanishing almost everywhere
  off a set `L ⊆ M`.
* `TauCeti.SobolevSection.chartAeZeroOff`: the tuples of chart-`i` Sobolev functions vanishing
  almost everywhere off `L`.
* `TauCeti.SobolevSection.chartRestrictL`: the chart-`i` components of an element vanishing off
  `L`.
* `TauCeti.SobolevSection.HasExtensionByZero`: for closed `L` inside the domain of chart `i`,
  every chart-`i` tuple vanishing off `L` consists of the chart-`i` components of an element of
  `W^{k,p}(V)`.
* `TauCeti.SobolevSection.chartRestrictEquiv`, `TauCeti.SobolevSection.extendLocalL`: the
  resulting isomorphism, and extension by zero.

## Main results

* `TauCeti.SobolevSection.isClosed_aeZeroOff`, `TauCeti.SobolevSection.isClosed_chartAeZeroOff`:
  both subspaces are closed, hence complete.
* `TauCeti.SobolevSection.mem_aeZeroOff_of_ae_eq_coord`: an element given by a section vanishing
  off `L` vanishes off `L`.
* `TauCeti.SobolevSection.contMDiffSMulL_mem_aeZeroOff`: `φ • w` vanishes off `tsupport φ`.
* `TauCeti.SobolevSection.chartRestrictL_injective`: an element vanishing off a subset of the
  domain of chart `i` is determined by its chart-`i` components.
* `TauCeti.SobolevSection.chartRestrictL_extendLocalL`,
  `TauCeti.SobolevSection.extendLocalL_chartRestrictL`: extension by zero and the chart
  components are inverse to each other.

## References

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

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (k : ℕ)

/-- The elements of `W^{k,p}(V)` vanishing almost everywhere off a set `L ⊆ M`: in every chart
`i` the chart data vanish almost everywhere at the points of `A.image i` lying over the complement
of `L`. For closed `L` these are the elements supported in `L`. -/
def aeZeroOff (L : Set M) : Submodule ℝ (SobolevSection A μ p k) where
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
theorem mem_aeZeroOff {L : Set M} {w : SobolevSection A μ p k} :
    w ∈ aeZeroOff A μ p k L ↔ ∀ i, ∀ᵐ y ∂μ.restrict (A.image i),
      (A.chart i).symm y ∉ L → A.sectionChartData.chartValueL μ p k i w y = 0 :=
  Iff.rfl

variable {A μ p k} in
theorem aeZeroOff_mono {L L' : Set M} (h : L ⊆ L') :
    aeZeroOff A μ p k L ≤ aeZeroOff A μ p k L' := fun _ hw i ↦ by
  filter_upwards [hw i] with y hy hL using hy fun h' ↦ hL (h h')

/-- The elements of `W^{k,p}(V)` vanishing off `L` form a closed subspace. -/
theorem isClosed_aeZeroOff (L : Set M) :
    IsClosed (aeZeroOff A μ p k L : Set (SobolevSection A μ p k)) := by
  have : (aeZeroOff A μ p k L : Set (SobolevSection A μ p k)) = ⋂ i : Fin A.n,
      (fun w : SobolevSection A μ p k ↦ A.sectionChartData.chartValueL μ p k i w) ⁻¹'
        {f | ∀ᵐ y ∂μ.restrict (A.image i), (A.chart i).symm y ∉ L → f y = 0} := by
    ext w
    simp only [SetLike.mem_coe, mem_aeZeroOff, mem_iInter, mem_preimage, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((A.sectionChartData.chartValueL μ p k i).continuous.comp continuous_subtype_val)

instance aeZeroOff.instCompleteSpace [IsManifold 𝓘(ℝ, E) 1 M] (L : Set M) :
    CompleteSpace (aeZeroOff A μ p k L) :=
  (isClosed_aeZeroOff A μ p k L).completeSpace_coe

/-- The tuples of chart-`i` Sobolev functions, one for each vector of the basis
`Module.finBasis ℝ F`, vanishing almost everywhere at the points of `A.image i` lying over the
complement of `L ⊆ M`. -/
def chartAeZeroOff (i : Fin A.n) (L : Set M) :
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
theorem mem_chartAeZeroOff {i : Fin A.n} {L : Set M}
    {g : Fin (finrank ℝ F) → Wkp μ (A.image i) p k} :
    g ∈ chartAeZeroOff A μ p k i L ↔ ∀ j, ∀ᵐ y ∂μ.restrict (A.image i),
      (A.chart i).symm y ∉ L → Wkp.value k (g j) y = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- The chart-`i` tuples vanishing off `L` form a closed subspace. -/
theorem isClosed_chartAeZeroOff (i : Fin A.n) (L : Set M) :
    IsClosed (chartAeZeroOff A μ p k i L : Set (Fin (finrank ℝ F) → Wkp μ (A.image i) p k)) := by
  have : (chartAeZeroOff A μ p k i L : Set (Fin (finrank ℝ F) → Wkp μ (A.image i) p k)) =
      ⋂ j, (fun g : Fin (finrank ℝ F) → Wkp μ (A.image i) p k ↦ Wkp.valueL k (g j)) ⁻¹'
        {f | ∀ᵐ y ∂μ.restrict (A.image i), (A.chart i).symm y ∉ L → f y = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_chartAeZeroOff, mem_iInter, mem_preimage, mem_ofPred_eq,
      Wkp.valueL_apply]
  rw [this]
  exact isClosed_iInter fun j ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((Wkp.valueL k).continuous.comp (continuous_apply j))

instance chartAeZeroOff.instCompleteSpace (i : Fin A.n) (L : Set M) :
    CompleteSpace (chartAeZeroOff A μ p k i L) :=
  (isClosed_chartAeZeroOff A μ p k i L).completeSpace_coe

variable {A μ p k} in
/-- The chart-`i` components of an element vanishing off `L` vanish off `L`. -/
theorem mem_chartAeZeroOff_of_mem_aeZeroOff {L : Set M} {w : SobolevSection A μ p k}
    (hw : w ∈ aeZeroOff A μ p k L) (i : Fin A.n) :
    (w : A.sectionChartData.SobolevData μ p k) i ∈ chartAeZeroOff A μ p k i L := fun j ↦ by
  filter_upwards [hw i, A.sectionChartData.chartValueL_apply_ae μ p k i w] with y hy happ hL
  have h := congrArg (fun v ↦ (finBasis ℝ F).repr v j) ((happ.symm.trans (hy hL)))
  rwa [(finBasis ℝ F).repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h

/-- The chart-`i` components of the elements of `W^{k,p}(V)` vanishing off `L`, as a continuous
linear map into the chart-`i` tuples vanishing off `L`. -/
def chartRestrictL (i : Fin A.n) (L : Set M) :
    aeZeroOff A μ p k L →L[ℝ] chartAeZeroOff A μ p k i L :=
  ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun i : Fin A.n ↦ Fin (finrank ℝ F) → Wkp μ (A.image i) p k) i).comp
    ((A.sectionChartData.sobolevSections μ p k).subtypeL.comp
      (aeZeroOff A μ p k L).subtypeL)).codRestrict _
    fun w ↦ mem_chartAeZeroOff_of_mem_aeZeroOff w.2 i

@[simp]
theorem coe_chartRestrictL_apply (i : Fin A.n) (L : Set M) (w : aeZeroOff A μ p k L) :
    (chartRestrictL A μ p k i L w : Fin (finrank ℝ F) → Wkp μ (A.image i) p k) =
      ((w : SobolevSection A μ p k) : A.sectionChartData.SobolevData μ p k) i :=
  (rfl)

variable {A μ p k}

/-- If the chart data of `w` are the coordinates of a section `s`, then the chart-`i` components
of `w` are the coordinates of `A.coord i s` in the basis `Module.finBasis ℝ F`. -/
theorem value_ae_eq_repr_coord {w : SobolevSection A μ p k} {s : ∀ x, V x} {i : Fin A.n}
    (hs : A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((w : A.sectionChartData.SobolevData μ p k) i j) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (finBasis ℝ F).repr (A.coord i s y) j := by
  filter_upwards [SectionChartData.value_ae_eq_repr_coord
      (hs.trans (A.sectionChartData_coord_ae_eq μ i s).symm) j,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hy
  rw [h, A.sectionChartData_coord_of_mem _ hy]

/-- An element whose chart data are the coordinates of a section vanishing off `L` vanishes
almost everywhere off `L`. -/
theorem mem_aeZeroOff_of_ae_eq_coord {L : Set M} {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (hsL : ∀ x ∉ L, s x = 0) : w ∈ aeZeroOff A μ p k L := fun i ↦ by
  filter_upwards [hs i, ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hyi hL
  rw [hy]
  exact A.coord_eq_zero hyi (hsL _ hL)

/-- Multiplication by a smooth function `φ` takes values in the elements vanishing off
`tsupport φ`. -/
theorem contMDiffSMulL_mem_aeZeroOff [IsManifold 𝓘(ℝ, E) ∞ M] {φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection A μ p k) :
    contMDiffSMulL A μ p k hφ w ∈ aeZeroOff A μ p k (tsupport φ) := fun i ↦ by
  filter_upwards [chartValueL_contMDiffSMulL_ae hφ w i] with y hy hL
  rw [hy, image_eq_zero_of_notMem_tsupport hL, zero_smul]

/-- An element vanishing off a subset `L` of the domain of chart `i` is determined by its
chart-`i` components: over `L` its components in every other chart are coordinate changes of its
chart-`i` components. -/
theorem chartRestrictL_injective [IsManifold 𝓘(ℝ, E) 1 M] {i : Fin A.n} {L : Set M}
    (hLi : L ⊆ A.dom i) : Function.Injective (chartRestrictL A μ p k i L) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  have hC := A.aeTransition_sectionChartData μ
  have hslot : ((w : SobolevSection A μ p k) : A.sectionChartData.SobolevData μ p k) i = 0 := by
    rw [← coe_chartRestrictL_apply, hw]
    rfl
  have hi : ∀ᵐ y ∂μ.restrict (A.image i), A.sectionChartData.chartValueL μ p k i w y = 0 := by
    filter_upwards [A.sectionChartData.chartValueL_apply_ae μ p k i w,
      Lp.coeFn_zero ℝ p (μ.restrict (A.image i))] with y hy h0
    rw [hy]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hslot, Pi.zero_apply, ← Wkp.valueL_apply, map_zero]
    exact (congrArg (· • finBasis ℝ F j) h0).trans (zero_smul ℝ _)
  refine Subtype.ext (SobolevSection.eq_of_ae_eq_coord (s := 0) (fun i' ↦ ?_) fun i' ↦ ?_)
  · have hcomp := (A.sectionChartData.compatible_iff μ p k).1
      (A.sectionChartData.compatible_of_mem hC (w : SobolevSection A μ p k).2 i i')
    have htr := A.sectionChartData.aeTransition_iff.1 hC (i' := i') hi
    have hov : ∀ᵐ y ∂μ.restrict (A.image i'), y ∈ A.overlap i i' →
        A.sectionChartData.chartValueL μ p k i' w y = 0 := by
      have h' : ∀ᵐ y ∂μ.restrict (A.overlap i i'),
          A.sectionChartData.chartValueL μ p k i' w y = 0 := by
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
    filter_upwards [Lp.coeFn_zero F p (μ.restrict (A.image i')),
      ae_restrict_mem (A.image i').isOpen.measurableSet] with y h0 hy
    rw [A.coord_zero i' hy]
    exact h0

variable (A μ p k) in
/-- **Extension by zero at order `k`.** For every closed subset `L` of the domain of a chart `i`,
every tuple of chart-`i` Sobolev functions vanishing almost everywhere off `L` consists of the
chart-`i` components of an element of `W^{k,p}(V)` vanishing off `L`. Over surfaces this holds for
`k ≤ 1` (`TauCeti.SobolevSection.hasExtensionByZero_of_le_one`). -/
def HasExtensionByZero : Prop :=
  ∀ ⦃i : Fin A.n⦄ ⦃L : Set M⦄, IsClosed L → L ⊆ A.dom i →
    Function.Surjective (chartRestrictL A μ p k i L)

theorem hasExtensionByZero_iff : HasExtensionByZero A μ p k ↔
    ∀ ⦃i : Fin A.n⦄ ⦃L : Set M⦄, IsClosed L → L ⊆ A.dom i →
      Function.Surjective (chartRestrictL A μ p k i L) :=
  Iff.rfl

section Extension

variable [IsManifold 𝓘(ℝ, E) 1 M]

variable (A μ p k) in
/-- Under `TauCeti.SobolevSection.HasExtensionByZero`, the chart-`i` components of the elements
vanishing off a closed subset `L` of the domain of chart `i` form a linear equivalence onto the
chart-`i` tuples vanishing off `L`. -/
def chartRestrictEquiv (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) :
    aeZeroOff A μ p k L ≃ₗ[ℝ] chartAeZeroOff A μ p k i L :=
  LinearEquiv.ofBijective (chartRestrictL A μ p k i L).toLinearMap
    ⟨chartRestrictL_injective hLi, h hL hLi⟩

@[simp]
theorem chartRestrictEquiv_apply (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A μ p k L) :
    chartRestrictEquiv A μ p k h hL hLi w = chartRestrictL A μ p k i L w :=
  (rfl)

/-- **Extension by zero.** Let `L` be a closed subset of the domain of chart `i`. Under
`TauCeti.SobolevSection.HasExtensionByZero`, a tuple of chart-`i` Sobolev functions vanishing
almost everywhere off `L` defines an element of `W^{k,p}(V)`, vanishing off `L`, whose chart-`i`
components are the given functions. This is a continuous linear map from the closed subspace
`TauCeti.SobolevSection.chartAeZeroOff A μ p k i L` into `W^{k,p}(V)`, by the closed graph
theorem. -/
def extendLocalL (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : chartAeZeroOff A μ p k i L →L[ℝ] SobolevSection A μ p k :=
  ContinuousLinearMap.ofSeqClosedGraph
    (g := (aeZeroOff A μ p k L).subtype ∘ₗ (chartRestrictEquiv A μ p k h hL hLi).symm.toLinearMap)
    fun u x y hu hy ↦ by
      set e := chartRestrictEquiv A μ p k h hL hLi
      -- The limit `y` vanishes off `L`, and its chart-`i` components are the limit `x`.
      have hyL : y ∈ aeZeroOff A μ p k L :=
        (isClosed_aeZeroOff A μ p k L).mem_of_tendsto hy
          (Eventually.of_forall fun n ↦ (e.symm (u n)).2)
      have hconv : Tendsto (fun n ↦ e.symm (u n)) atTop (𝓝 ⟨y, hyL⟩) := tendsto_subtype_rng.2 hy
      have hx : chartRestrictL A μ p k i L ⟨y, hyL⟩ = x :=
        tendsto_nhds_unique (((chartRestrictL A μ p k i L).continuous.tendsto _).comp hconv)
          (hu.congr fun n ↦ by
            rw [Function.comp_apply, ← chartRestrictEquiv_apply h hL hLi, e.apply_symm_apply])
      rw [← hx, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        ← chartRestrictEquiv_apply h hL hLi, e.symm_apply_apply, Submodule.subtype_apply]

theorem extendLocalL_apply (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    extendLocalL h hL hLi g = (chartRestrictEquiv A μ p k h hL hLi).symm g := by
  rw [extendLocalL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Submodule.subtype_apply]

theorem extendLocalL_mem_aeZeroOff (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    extendLocalL h hL hLi g ∈ aeZeroOff A μ p k L := by
  rw [extendLocalL_apply]
  exact ((chartRestrictEquiv A μ p k h hL hLi).symm g).2

/-- The chart-`i` components of the extension by zero are the given tuple. -/
@[simp]
theorem chartRestrictL_extendLocalL (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    chartRestrictL A μ p k i L ⟨_, extendLocalL_mem_aeZeroOff h hL hLi g⟩ = g := by
  simp_rw [extendLocalL_apply, Subtype.coe_eta, ← chartRestrictEquiv_apply h hL hLi,
    LinearEquiv.apply_symm_apply]

/-- The chart-`i` components of the extension by zero are the given functions. -/
@[simp]
theorem extendLocalL_apply_self (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    ((extendLocalL h hL hLi g : SobolevSection A μ p k) :
      A.sectionChartData.SobolevData μ p k) i =
      (g : Fin (finrank ℝ F) → Wkp μ (A.image i) p k) := by
  rw [← coe_chartRestrictL_apply A μ p k i L ⟨_, extendLocalL_mem_aeZeroOff h hL hLi g⟩,
    chartRestrictL_extendLocalL]

/-- An element vanishing off `L` is the extension by zero of its chart-`i` components. -/
@[simp]
theorem extendLocalL_chartRestrictL (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A μ p k L) :
    extendLocalL h hL hLi (chartRestrictL A μ p k i L w) = w := by
  rw [extendLocalL_apply, ← chartRestrictEquiv_apply h hL hLi, LinearEquiv.symm_apply_apply]

end Extension

end SobolevSection

end TauCeti
