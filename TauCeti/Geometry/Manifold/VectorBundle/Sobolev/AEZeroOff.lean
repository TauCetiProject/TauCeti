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
the extension by zero `TauCeti.SobolevSection.extendByZeroL` from chart-`i` tuples to `W^{k,p}(V)`,
which is continuous by the closed graph theorem.

The construction is carried out for general chart data `C : TauCeti.SectionChartData E F S` and
sets `Z i ⊆ E`, one per chart, on which the chart data are to vanish
(`TauCeti.SectionChartData.aeZeroOn`, `TauCeti.SectionChartData.chartRestrictL`,
`TauCeti.SectionChartData.extendByZeroL`), so that it serves bases with boundary as well.

## Main definitions

* `TauCeti.SectionChartData.aeZeroOn`, `TauCeti.SectionChartData.chartAeZeroOn`: the Sobolev
  sections of chart data, and the chart-`i` tuples, vanishing on given sets.
* `TauCeti.SectionChartData.chartRestrictL`, `TauCeti.SectionChartData.extendByZeroL`: the
  chart-`i` components, and their inverse when they are bijective.

* `TauCeti.SobolevSection.aeZeroOff`: the elements of `W^{k,p}(V)` vanishing almost everywhere
  off a set `L ⊆ M`.
* `TauCeti.SobolevSection.chartAeZeroOff`: the tuples of chart-`i` Sobolev functions vanishing
  almost everywhere off `L`.
* `TauCeti.SobolevSection.chartRestrictL`: the chart-`i` components of an element vanishing off
  `L`.
* `TauCeti.SobolevSection.HasExtensionByZero`: for closed `L` inside the domain of chart `i`,
  every chart-`i` tuple vanishing off `L` consists of the chart-`i` components of an element of
  `W^{k,p}(V)`.
* `TauCeti.SobolevSection.chartRestrictEquiv`, `TauCeti.SobolevSection.extendByZeroL`: the
  resulting isomorphism, and extension by zero.

## Main results

* `TauCeti.SectionChartData.chartRestrictL_injective`: a Sobolev section vanishing on the sets
  `Z i` is determined by its chart-`i` components when every point of a chart image outside `Z`
  lies in the overlap with chart `i`.
* `TauCeti.SobolevSection.isClosed_aeZeroOff`, `TauCeti.SobolevSection.isClosed_chartAeZeroOff`:
  both subspaces are closed, hence complete.
* `TauCeti.SobolevSection.mem_aeZeroOff_of_ae_eq_coord`: an element given by a section vanishing
  off `L` vanishes off `L`.
* `TauCeti.SobolevSection.contMDiffSMulL_mem_aeZeroOff`: `φ • w` vanishes off `tsupport φ`.
* `TauCeti.SobolevSection.chartRestrictL_injective`: an element vanishing off a subset of the
  domain of chart `i` is determined by its chart-`i` components.
* `TauCeti.SobolevSection.chartRestrictL_extendByZeroL`,
  `TauCeti.SobolevSection.extendByZeroL_chartRestrictL`: extension by zero and the chart
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

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (k : ℕ)

/-- The Sobolev sections whose chart data vanish almost everywhere on given sets `Z i ⊆ E`, one
for each chart `i`. When `Z i` consists of the points of the image of chart `i` lying over the
complement of a set `L` in the base, these are the sections vanishing off `L`. -/
def aeZeroOn (Z : Fin C.n → Set E) : Submodule ℝ (C.sobolevSections μ p k) where
  carrier := {w | ∀ i, ∀ᵐ y ∂μ.restrict (C.image i), y ∈ Z i → C.chartValueL μ p k i w y = 0}
  add_mem' {w w'} hw hw' i := by
    filter_upwards [hw i, hw' i, Lp.coeFn_add (C.chartValueL μ p k i w)
      (C.chartValueL μ p k i w')] with y hy hy' hadd hZ
    rw [Submodule.coe_add, map_add, hadd, Pi.add_apply, hy hZ, hy' hZ, add_zero]
  zero_mem' i := by
    filter_upwards [Lp.coeFn_zero F p (μ.restrict (C.image i))] with y hy _
    rw [ZeroMemClass.coe_zero, map_zero]
    exact hy
  smul_mem' c w hw i := by
    filter_upwards [hw i, Lp.coeFn_smul c (C.chartValueL μ p k i w)] with y hy hsmul hZ
    rw [Submodule.coe_smul, map_smul, hsmul, Pi.smul_apply, hy hZ, smul_zero]

variable {C μ p k} in
theorem mem_aeZeroOn {Z : Fin C.n → Set E} {w : C.sobolevSections μ p k} :
    w ∈ C.aeZeroOn μ p k Z ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (C.image i), y ∈ Z i → C.chartValueL μ p k i w y = 0 :=
  Iff.rfl

variable {C μ p k} in
theorem aeZeroOn_mono {Z Z' : Fin C.n → Set E} (h : ∀ i, Z' i ⊆ Z i) :
    C.aeZeroOn μ p k Z ≤ C.aeZeroOn μ p k Z' := fun _ hw i ↦ by
  filter_upwards [hw i] with y hy hZ using hy (h i hZ)

/-- The Sobolev sections vanishing on the sets `Z i` form a closed subspace. -/
theorem isClosed_aeZeroOn (Z : Fin C.n → Set E) :
    IsClosed (C.aeZeroOn μ p k Z : Set (C.sobolevSections μ p k)) := by
  have : (C.aeZeroOn μ p k Z : Set (C.sobolevSections μ p k)) = ⋂ i : Fin C.n,
      (fun w : C.sobolevSections μ p k ↦ C.chartValueL μ p k i w) ⁻¹'
        {f | ∀ᵐ y ∂μ.restrict (C.image i), y ∈ Z i → f y = 0} := by
    ext w
    simp only [SetLike.mem_coe, mem_aeZeroOn, mem_iInter, mem_preimage, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((C.chartValueL μ p k i).continuous.comp continuous_subtypeVal)

instance aeZeroOn.instCompleteSpace [CompleteSpace (C.sobolevSections μ p k)]
    (Z : Fin C.n → Set E) : CompleteSpace (C.aeZeroOn μ p k Z) :=
  (C.isClosed_aeZeroOn μ p k Z).completeSpace_coe

omit [FiniteDimensional ℝ F] in
/-- The tuples of chart-`i` Sobolev functions, one for each vector of the basis
`Module.finBasis ℝ F`, vanishing almost everywhere on a set `Z ⊆ E`. -/
def chartAeZeroOn (i : Fin C.n) (Z : Set E) :
    Submodule ℝ (Fin (finrank ℝ F) → Wkp μ (C.image i) p k) where
  carrier := {g | ∀ j, ∀ᵐ y ∂μ.restrict (C.image i), y ∈ Z → Wkp.value k (g j) y = 0}
  add_mem' {g g'} hg hg' j := by
    filter_upwards [hg j, hg' j, Lp.coeFn_add (Wkp.value k (g j)) (Wkp.value k (g' j))]
      with y hy hy' hadd hZ
    rw [Pi.add_apply, Wkp.value_add, hadd, Pi.add_apply, hy hZ, hy' hZ, add_zero]
  zero_mem' j := by
    filter_upwards [Lp.coeFn_zero ℝ p (μ.restrict (C.image i))] with y hy _
    rw [Pi.zero_apply, ← Wkp.valueL_apply, map_zero, hy, Pi.zero_apply]
  smul_mem' c g hg j := by
    filter_upwards [hg j, Lp.coeFn_smul c (Wkp.value k (g j))] with y hy hsmul hZ
    rw [Pi.smul_apply, Wkp.value_smul, hsmul, Pi.smul_apply, hy hZ, smul_zero]

omit [FiniteDimensional ℝ F] in
variable {C μ p k} in
theorem mem_chartAeZeroOn {i : Fin C.n} {Z : Set E}
    {g : Fin (finrank ℝ F) → Wkp μ (C.image i) p k} :
    g ∈ C.chartAeZeroOn μ p k i Z ↔
      ∀ j, ∀ᵐ y ∂μ.restrict (C.image i), y ∈ Z → Wkp.value k (g j) y = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ F] in
/-- The chart-`i` tuples vanishing on `Z` form a closed subspace. -/
theorem isClosed_chartAeZeroOn (i : Fin C.n) (Z : Set E) :
    IsClosed (C.chartAeZeroOn μ p k i Z : Set (Fin (finrank ℝ F) → Wkp μ (C.image i) p k)) := by
  have : (C.chartAeZeroOn μ p k i Z : Set (Fin (finrank ℝ F) → Wkp μ (C.image i) p k)) =
      ⋂ j, (fun g : Fin (finrank ℝ F) → Wkp μ (C.image i) p k ↦ Wkp.valueL k (g j)) ⁻¹'
        {f | ∀ᵐ y ∂μ.restrict (C.image i), y ∈ Z → f y = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_chartAeZeroOn, mem_iInter, mem_preimage, mem_ofPred_eq,
      Wkp.valueL_apply]
  rw [this]
  exact isClosed_iInter fun j ↦ (isClosed_setOf_ae_imp_eq_zero p _).preimage
    ((Wkp.valueL k).continuous.comp (continuous_apply j))

omit [FiniteDimensional ℝ F] in
instance chartAeZeroOn.instCompleteSpace (i : Fin C.n) (Z : Set E) :
    CompleteSpace (C.chartAeZeroOn μ p k i Z) :=
  (C.isClosed_chartAeZeroOn μ p k i Z).completeSpace_coe

variable {C μ p k} in
/-- The chart-`i` components of a Sobolev section vanishing on the sets `Z i` vanish on `Z i`. -/
theorem mem_chartAeZeroOn_of_mem_aeZeroOn {Z : Fin C.n → Set E}
    {w : C.sobolevSections μ p k} (hw : w ∈ C.aeZeroOn μ p k Z) (i : Fin C.n) :
    (w : C.SobolevData μ p k) i ∈ C.chartAeZeroOn μ p k i (Z i) := fun j ↦ by
  filter_upwards [hw i, C.chartValueL_apply_ae μ p k i w] with y hy happ hZ
  have h := congrArg (fun v ↦ (finBasis ℝ F).repr v j) ((happ.symm.trans (hy hZ)))
  rwa [(finBasis ℝ F).repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h

/-- The chart-`i` components of the Sobolev sections vanishing on the sets `Z i`, as a continuous
linear map into the chart-`i` tuples vanishing on `Z i`. -/
def chartRestrictL (Z : Fin C.n → Set E) (i : Fin C.n) :
    C.aeZeroOn μ p k Z →L[ℝ] C.chartAeZeroOn μ p k i (Z i) :=
  ((C.componentsL μ p k i).comp (C.aeZeroOn μ p k Z).subtypeL).codRestrict _ fun w ↦ by
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, componentsL_apply]
    exact mem_chartAeZeroOn_of_mem_aeZeroOn w.property i

@[simp]
theorem coe_chartRestrictL_apply (Z : Fin C.n → Set E) (i : Fin C.n)
    (w : C.aeZeroOn μ p k Z) :
    (C.chartRestrictL μ p k Z i w : Fin (finrank ℝ F) → Wkp μ (C.image i) p k) =
      ((w : C.sobolevSections μ p k) : C.SobolevData μ p k) i := by
  rw [chartRestrictL, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, componentsL_apply]

variable {C μ p k}

/-- A Sobolev section vanishing on the sets `Z i` is determined by its chart-`i` components, as
soon as every point of the image of a chart `i'` outside `Z i'` lies in the overlap of charts `i`
and `i'`: there its chart-`i'` data are a coordinate change of its chart-`i` data. -/
theorem chartRestrictL_injective (hC : C.AETransition μ) {Z : Fin C.n → Set E}
    {i : Fin C.n} (hZ : ∀ i', ∀ y ∈ C.image i', y ∉ Z i' → y ∈ C.overlap i i') :
    Function.Injective (C.chartRestrictL μ p k Z i) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  have hslot : ((w : C.sobolevSections μ p k) : C.SobolevData μ p k) i = 0 := by
    rw [← coe_chartRestrictL_apply, hw, ZeroMemClass.coe_zero]
  have hi : ∀ᵐ y ∂μ.restrict (C.image i), C.chartValueL μ p k i w y = 0 := by
    filter_upwards [C.chartValueL_apply_ae μ p k i w,
      Lp.coeFn_zero ℝ p (μ.restrict (C.image i))] with y hy h0
    rw [hy]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hslot, Pi.zero_apply, ← Wkp.valueL_apply, map_zero]
    exact (congrArg (· • finBasis ℝ F j) h0).trans (zero_smul ℝ _)
  refine Subtype.ext (eq_of_ae_eq_coord (s := 0) (fun i' ↦ ?_) fun i' ↦ ?_)
  · have hcomp := (C.compatible_iff μ p k).1
      (compatible_of_mem hC (w : C.sobolevSections μ p k).property i i')
    have htr := C.aeTransition_iff.1 hC (i' := i') hi
    have hov : ∀ᵐ y ∂μ.restrict (C.image i'), y ∈ C.overlap i i' →
        C.chartValueL μ p k i' w y = 0 := by
      have h' : ∀ᵐ y ∂μ.restrict (C.overlap i i'), C.chartValueL μ p k i' w y = 0 := by
        filter_upwards [hcomp, htr] with y hy htr
        rw [hy, htr, map_zero]
      exact ae_restrict_of_ae ((ae_restrict_iff' (C.isOpen_overlap i i').measurableSet).1 h')
    filter_upwards [w.property i', hov, ae_restrict_mem (C.image i').isOpen.measurableSet]
      with y hy hyo hyi
    rw [C.coord_zero i' hyi]
    by_cases hy' : y ∈ Z i'
    exacts [hy hy', hyo (hZ i' y hyi hy')]
  · simp only [ZeroMemClass.coe_zero, map_zero]
    filter_upwards [Lp.coeFn_zero F p (μ.restrict (C.image i')),
      ae_restrict_mem (C.image i').isOpen.measurableSet] with y h0 hy
    rw [C.coord_zero i' hy]
    exact h0

section Extension

variable [CompleteSpace (C.sobolevSections μ p k)] {Z : Fin C.n → Set E} {i : Fin C.n}

variable (C μ p k) in
/-- When the chart-`i` components of the Sobolev sections vanishing on the sets `Z i` are a
bijection onto the chart-`i` tuples vanishing on `Z i`, they form a linear equivalence. -/
def chartRestrictEquiv (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i)) :
    C.aeZeroOn μ p k Z ≃ₗ[ℝ] C.chartAeZeroOn μ p k i (Z i) :=
  LinearEquiv.ofBijective (C.chartRestrictL μ p k Z i).toLinearMap ⟨hinj, hsurj⟩

omit [CompleteSpace (C.sobolevSections μ p k)] in
@[simp]
theorem chartRestrictEquiv_apply (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i)) (w : C.aeZeroOn μ p k Z) :
    C.chartRestrictEquiv μ p k hinj hsurj w = C.chartRestrictL μ p k Z i w :=
  LinearEquiv.ofBijective_apply _ w

variable (C μ p k) in
/-- **Extension by zero.** When the chart-`i` components of the Sobolev sections vanishing on the
sets `Z i` are a bijection onto the chart-`i` tuples vanishing on `Z i`, the inverse followed by
the inclusion is a continuous linear map from these tuples to the Sobolev sections, by the closed
graph theorem. -/
def extendByZeroL (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i)) :
    C.chartAeZeroOn μ p k i (Z i) →L[ℝ] C.sobolevSections μ p k :=
  -- `ContinuousLinearEquiv.ofBijective` would give the inverse directly, but it needs the module
  -- structure of the normed space `C.aeZeroOn μ p k Z`, which agrees with the submodule one only
  -- after unfolding `TauCeti.SectionChartData.sobolevSections`, not exposed to this module.
  ContinuousLinearMap.ofSeqClosedGraph
    (g := (C.aeZeroOn μ p k Z).subtype ∘ₗ (C.chartRestrictEquiv μ p k hinj hsurj).symm.toLinearMap)
    fun u x y hu hy ↦ by
      set e := C.chartRestrictEquiv μ p k hinj hsurj
      -- The limit `y` vanishes on the sets `Z i`, and its chart-`i` components are the limit `x`.
      have hyZ : y ∈ C.aeZeroOn μ p k Z := (C.isClosed_aeZeroOn μ p k Z).mem_of_tendsto hy
        (Eventually.of_forall fun n ↦ (e.symm (u n)).property)
      have hconv : Tendsto (fun n ↦ e.symm (u n)) atTop (𝓝 ⟨y, hyZ⟩) := tendsto_subtype_rng.2 hy
      have hx : C.chartRestrictL μ p k Z i ⟨y, hyZ⟩ = x :=
        tendsto_nhds_unique (((C.chartRestrictL μ p k Z i).continuous.tendsto _).comp hconv)
          (hu.congr fun n ↦ by
            rw [Function.comp_apply, ← chartRestrictEquiv_apply hinj hsurj, e.apply_symm_apply])
      rw [← hx, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        ← chartRestrictEquiv_apply hinj hsurj, e.symm_apply_apply, Submodule.subtype_apply]

theorem extendByZeroL_apply (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i))
    (g : C.chartAeZeroOn μ p k i (Z i)) :
    C.extendByZeroL μ p k hinj hsurj g = (C.chartRestrictEquiv μ p k hinj hsurj).symm g := by
  rw [extendByZeroL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Submodule.subtype_apply]

theorem extendByZeroL_mem_aeZeroOn (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i))
    (g : C.chartAeZeroOn μ p k i (Z i)) :
    C.extendByZeroL μ p k hinj hsurj g ∈ C.aeZeroOn μ p k Z := by
  rw [extendByZeroL_apply]
  exact ((C.chartRestrictEquiv μ p k hinj hsurj).symm g).property

/-- The chart-`i` components of the extension by zero are the given tuple. -/
@[simp]
theorem chartRestrictL_extendByZeroL (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i))
    (g : C.chartAeZeroOn μ p k i (Z i)) :
    C.chartRestrictL μ p k Z i ⟨_, C.extendByZeroL_mem_aeZeroOn hinj hsurj g⟩ = g := by
  simp_rw [extendByZeroL_apply, Subtype.coe_eta, ← chartRestrictEquiv_apply hinj hsurj,
    LinearEquiv.apply_symm_apply]

/-- The chart-`i` components of the extension by zero are the given functions. -/
@[simp]
theorem extendByZeroL_apply_self (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i))
    (g : C.chartAeZeroOn μ p k i (Z i)) :
    ((C.extendByZeroL μ p k hinj hsurj g : C.sobolevSections μ p k) : C.SobolevData μ p k) i =
      (g : Fin (finrank ℝ F) → Wkp μ (C.image i) p k) := by
  rw [← coe_chartRestrictL_apply C μ p k Z i ⟨_, C.extendByZeroL_mem_aeZeroOn hinj hsurj g⟩,
    chartRestrictL_extendByZeroL]

/-- A Sobolev section vanishing on the sets `Z i` is the extension by zero of its chart-`i`
components. -/
@[simp]
theorem extendByZeroL_chartRestrictL (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i)) (w : C.aeZeroOn μ p k Z) :
    C.extendByZeroL μ p k hinj hsurj (C.chartRestrictL μ p k Z i w) = w := by
  rw [extendByZeroL_apply, ← chartRestrictEquiv_apply hinj hsurj, LinearEquiv.symm_apply_apply]

/-- Sobolev sections vanishing on the sets `Z i` converge as soon as their chart-`i` components
converge, when the chart-`i` components are bijective: extension by zero is continuous. -/
theorem tendsto_of_tendsto_chartRestrictL (hinj : Function.Injective (C.chartRestrictL μ p k Z i))
    (hsurj : Function.Surjective (C.chartRestrictL μ p k Z i)) {ι : Type*} {l : Filter ι}
    {a : ι → C.aeZeroOn μ p k Z} {u : C.aeZeroOn μ p k Z}
    (h : Tendsto (fun m ↦ C.chartRestrictL μ p k Z i (a m)) l
      (𝓝 (C.chartRestrictL μ p k Z i u))) :
    Tendsto a l (𝓝 u) := by
  have hE := ((C.extendByZeroL μ p k hinj hsurj).continuous.tendsto _).comp h
  simp only [Function.comp_def, extendByZeroL_chartRestrictL] at hE
  exact tendsto_subtype_rng.2 hE

end Extension

end SectionChartData

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
abbrev aeZeroOff (L : Set M) : Submodule ℝ (SobolevSection A μ p k) :=
  A.sectionChartData.aeZeroOn μ p k fun i ↦ {y | (A.chart i).symm y ∉ L}

variable {A μ p k} in
theorem mem_aeZeroOff {L : Set M} {w : SobolevSection A μ p k} :
    w ∈ aeZeroOff A μ p k L ↔ ∀ i, ∀ᵐ y ∂μ.restrict (A.image i),
      (A.chart i).symm y ∉ L → A.sectionChartData.chartValueL μ p k i w y = 0 :=
  Iff.rfl

variable {A μ p k} in
theorem aeZeroOff_mono {L L' : Set M} (h : L ⊆ L') :
    aeZeroOff A μ p k L ≤ aeZeroOff A μ p k L' :=
  SectionChartData.aeZeroOn_mono fun _ _ hy h' ↦ hy (h h')

/-- The elements of `W^{k,p}(V)` vanishing off `L` form a closed subspace. -/
theorem isClosed_aeZeroOff (L : Set M) :
    IsClosed (aeZeroOff A μ p k L : Set (SobolevSection A μ p k)) :=
  A.sectionChartData.isClosed_aeZeroOn μ p k _

/-- The tuples of chart-`i` Sobolev functions, one for each vector of the basis
`Module.finBasis ℝ F`, vanishing almost everywhere at the points of `A.image i` lying over the
complement of `L ⊆ M`. -/
abbrev chartAeZeroOff (i : Fin A.n) (L : Set M) :
    Submodule ℝ (Fin (finrank ℝ F) → Wkp μ (A.image i) p k) :=
  A.sectionChartData.chartAeZeroOn μ p k i {y | (A.chart i).symm y ∉ L}

omit [FiniteDimensional ℝ F] in
variable {A μ p k} in
theorem mem_chartAeZeroOff {i : Fin A.n} {L : Set M}
    {g : Fin (finrank ℝ F) → Wkp μ (A.image i) p k} :
    g ∈ chartAeZeroOff A μ p k i L ↔ ∀ j, ∀ᵐ y ∂μ.restrict (A.image i),
      (A.chart i).symm y ∉ L → Wkp.value k (g j) y = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ F] in
/-- The chart-`i` tuples vanishing off `L` form a closed subspace. -/
theorem isClosed_chartAeZeroOff (i : Fin A.n) (L : Set M) :
    IsClosed (chartAeZeroOff A μ p k i L : Set (Fin (finrank ℝ F) → Wkp μ (A.image i) p k)) :=
  A.sectionChartData.isClosed_chartAeZeroOn μ p k i _

variable {A μ p k} in
/-- The chart-`i` components of an element vanishing off `L` vanish off `L`. -/
theorem mem_chartAeZeroOff_of_mem_aeZeroOff {L : Set M} {w : SobolevSection A μ p k}
    (hw : w ∈ aeZeroOff A μ p k L) (i : Fin A.n) :
    (w : A.sectionChartData.SobolevData μ p k) i ∈ chartAeZeroOff A μ p k i L :=
  SectionChartData.mem_chartAeZeroOn_of_mem_aeZeroOn hw i

/-- The chart-`i` components of the elements of `W^{k,p}(V)` vanishing off `L`, as a continuous
linear map into the chart-`i` tuples vanishing off `L`. -/
def chartRestrictL (i : Fin A.n) (L : Set M) :
    aeZeroOff A μ p k L →L[ℝ] chartAeZeroOff A μ p k i L :=
  A.sectionChartData.chartRestrictL μ p k _ i

@[simp]
theorem coe_chartRestrictL_apply (i : Fin A.n) (L : Set M) (w : aeZeroOff A μ p k L) :
    (chartRestrictL A μ p k i L w : Fin (finrank ℝ F) → Wkp μ (A.image i) p k) =
      ((w : SobolevSection A μ p k) : A.sectionChartData.SobolevData μ p k) i :=
  A.sectionChartData.coe_chartRestrictL_apply μ p k _ i w

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
    (hLi : L ⊆ A.dom i) : Function.Injective (chartRestrictL A μ p k i L) :=
  SectionChartData.chartRestrictL_injective (A.aeTransition_sectionChartData μ)
    fun i' y hy hL ↦ by
      obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
      rw [mem_ofPred_eq, not_not, (A.chart i').left_inv (A.dom_subset_chart_source i' hx)] at hL
      exact A.chart_mem_overlap (hLi hL) hx

variable (A μ p k) in
/-- **Extension by zero at order `k`.** For every closed subset `L` of the domain of a chart `i`,
every tuple of chart-`i` Sobolev functions vanishing almost everywhere off `L` consists of the
chart-`i` components of an element of `W^{k,p}(V)` vanishing off `L`. Over surfaces this holds for
`Cⁿ` bundles at orders `k ≤ n` with `k ≤ 1` or `p ≠ ∞` (`TauCeti.SobolevSection.hasExtensionByZero`
in `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density`). -/
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
vanishing off a closed subset `L` of the domain of chart `i` form an isomorphism onto the chart-`i`
tuples vanishing off `L`. -/
def chartRestrictEquiv (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) :
    aeZeroOff A μ p k L ≃ₗ[ℝ] chartAeZeroOff A μ p k i L :=
  A.sectionChartData.chartRestrictEquiv μ p k (chartRestrictL_injective hLi) (h hL hLi)

@[simp]
theorem chartRestrictEquiv_apply (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A μ p k L) :
    chartRestrictEquiv A μ p k h hL hLi w = chartRestrictL A μ p k i L w :=
  SectionChartData.chartRestrictEquiv_apply (chartRestrictL_injective hLi) (h hL hLi) w

/-- **Extension by zero.** Let `L` be a closed subset of the domain of chart `i`. Under
`TauCeti.SobolevSection.HasExtensionByZero`, a tuple of chart-`i` Sobolev functions vanishing
almost everywhere off `L` defines an element of `W^{k,p}(V)`, vanishing off `L`, whose chart-`i`
components are the given functions. This is a continuous linear map from the closed subspace
`TauCeti.SobolevSection.chartAeZeroOff A μ p k i L` into `W^{k,p}(V)`
(`TauCeti.SectionChartData.extendByZeroL`). -/
def extendByZeroL (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : chartAeZeroOff A μ p k i L →L[ℝ] SobolevSection A μ p k :=
  A.sectionChartData.extendByZeroL μ p k (chartRestrictL_injective hLi) (h hL hLi)

theorem extendByZeroL_apply (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    extendByZeroL h hL hLi g = (chartRestrictEquiv A μ p k h hL hLi).symm g :=
  SectionChartData.extendByZeroL_apply (chartRestrictL_injective hLi) (h hL hLi) g

theorem extendByZeroL_mem_aeZeroOff (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    extendByZeroL h hL hLi g ∈ aeZeroOff A μ p k L :=
  SectionChartData.extendByZeroL_mem_aeZeroOn (chartRestrictL_injective hLi) (h hL hLi) g

/-- The chart-`i` components of the extension by zero are the given tuple. -/
@[simp]
theorem chartRestrictL_extendByZeroL (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    chartRestrictL A μ p k i L ⟨_, extendByZeroL_mem_aeZeroOff h hL hLi g⟩ = g :=
  SectionChartData.chartRestrictL_extendByZeroL (chartRestrictL_injective hLi) (h hL hLi) g

/-- The chart-`i` components of the extension by zero are the given functions. -/
@[simp]
theorem extendByZeroL_apply_self (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A μ p k i L) :
    ((extendByZeroL h hL hLi g : SobolevSection A μ p k) :
      A.sectionChartData.SobolevData μ p k) i =
      (g : Fin (finrank ℝ F) → Wkp μ (A.image i) p k) :=
  SectionChartData.extendByZeroL_apply_self (chartRestrictL_injective hLi) (h hL hLi) g

/-- An element vanishing off `L` is the extension by zero of its chart-`i` components. -/
@[simp]
theorem extendByZeroL_chartRestrictL (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A μ p k L) :
    extendByZeroL h hL hLi (chartRestrictL A μ p k i L w) = w :=
  SectionChartData.extendByZeroL_chartRestrictL (chartRestrictL_injective hLi) (h hL hLi) w

/-- Elements vanishing off `L` converge as soon as their chart-`i` components converge, since
extension by zero is continuous. -/
theorem tendsto_of_tendsto_chartRestrictL (h : HasExtensionByZero A μ p k) {i : Fin A.n}
    {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i) {ι : Type*} {l : Filter ι}
    {a : ι → aeZeroOff A μ p k L} {u : aeZeroOff A μ p k L}
    (ha : Tendsto (fun m ↦ chartRestrictL A μ p k i L (a m)) l
      (𝓝 (chartRestrictL A μ p k i L u))) :
    Tendsto a l (𝓝 u) :=
  SectionChartData.tendsto_of_tendsto_chartRestrictL (chartRestrictL_injective hLi) (h hL hLi) ha

end Extension

end SobolevSection

end TauCeti
