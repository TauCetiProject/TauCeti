/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Function.SimpleFunc.Dense
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Indicator classes in `Lᵖ`

The class `MeasureTheory.indicatorConstLp p hs hμs c` of `s.indicator fun _ => c` is linear in the
constant `c`: Mathlib provides additivity, `MeasureTheory.indicatorConstLp_add`, and this file adds
compatibility with scalar multiplication. Together with the norm formula
`MeasureTheory.norm_indicatorConstLp`, this makes `c ↦ indicatorConstLp p hs hμs c` a bounded
linear map, so closed subspaces of `Lᵖ` can be tested on indicator classes of a dense set of
constants.

Indicator classes of pairwise disjoint sets of finite measure span a weighted finite `ℓ¹` space
inside `L¹`: the norm of `∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)` is
`∑ i, μ(s i) * ‖c i‖`. An `Lᵖ` class represented by `φ ∘ G` for a simple function `G` is the
sum of the indicator classes of the fibres of `G` with constants `φ w`.

In `L∞` the indicator of any measurable set is essentially bounded, whatever its measure. The
class `TauCeti.linftyIndicator μ s hs` of `1_s` in real `L∞(μ)` therefore needs no finiteness of
`μ s`, unlike `indicatorConstLp`. It is additive on disjoint sets, nonnegative, vanishes on null
sets, and equals the constant one at `univ`.

## Main declarations

* `TauCeti.indicatorConstLp_smul`: the indicator class of `a • c` is `a` times that of `c`.
* `TauCeti.norm_sum_indicatorConstLp_one`: the `L¹` norm of a sum of indicator classes of pairwise
  disjoint sets.
* `TauCeti.eq_sum_indicatorConstLp_fiber`: an `Lᵖ` class represented by `φ ∘ G`, for a simple
  function `G`, as a sum of indicator classes of the fibres of `G`.
* `TauCeti.linftyIndicator μ s hs`: the class in `L∞(μ)` of the indicator of a measurable set.
* `MeasureTheory.SimpleFunc.toLpTop_piecewise_const_zero`: the class of a simple function
  `c • 1_s` is `c • linftyIndicator μ s hs`.
* `LinearMap.ext_linftyIndicator`: a continuous linear map out of real `L∞` is determined by its
  values at the classes `linftyIndicator μ s hs`.
* `PositiveLinearMap.ext_linftyIndicator`: the same for positive linear functionals on real `L∞`,
  which are automatically continuous.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {s : Set α}

/-- A version of `Set.indicator_const_smul` for `MeasureTheory.indicatorConstLp`. -/
theorem indicatorConstLp_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (a : 𝕜) (c : E) :
    indicatorConstLp p hs hμs (a • c) = a • indicatorConstLp p hs hμs c := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := a • c),
    Lp.coeFn_smul a (indicatorConstLp p hs hμs c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

section Disjoint

variable {ι : Type*} [Fintype ι] {s : ι → Set α}

/-- The `L¹` norm of a sum of indicator classes of pairwise disjoint sets of finite measure is the
sum of the norms of the constants, weighted by the measures of the sets. -/
theorem norm_sum_indicatorConstLp_one (hs : ∀ i, MeasurableSet (s i)) (hμs : ∀ i, μ (s i) ≠ ∞)
    (hd : Pairwise (Function.onFun Disjoint s)) (c : ι → E) :
    ‖∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)‖ = ∑ i, μ.real (s i) * ‖c i‖ := by
  rw [L1.norm_eq_integral_norm]
  -- Almost everywhere, at most one of the indicator functions is nonzero.
  have hae : (fun x ↦ ‖(∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)) x‖) =ᵐ[μ]
      fun x ↦ ∑ i, (s i).indicator (fun _ ↦ ‖c i‖) x := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        fun i ↦ indicatorConstLp 1 (hs i) (hμs i) (c i),
      ae_all_iff.2 fun i ↦ indicatorConstLp_coeFn (p := 1) (hs := hs i) (hμs := hμs i)
        (c := c i)] with x h₁ h₂
    simp only [h₁, h₂]
    by_cases hx : ∃ k, x ∈ s k
    · obtain ⟨k, hk⟩ := hx
      have hne (i : ι) (hi : i ≠ k) : x ∉ s i := fun hxi ↦ Set.disjoint_left.1 (hd hi) hxi hk
      rw [Finset.sum_eq_single k (fun i _ hi ↦ by simp [hne i hi]) (by simp),
        Finset.sum_eq_single k (fun i _ hi ↦ by simp [hne i hi]) (by simp)]
      simp [hk]
    · simp only [not_exists] at hx
      simp [hx]
  rw [integral_congr_ae hae, integral_finsetSum _ fun i _ ↦
    (integrableOn_const (hμs i)).integrable_indicator (hs i)]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [integral_indicator_const _ (hs i), smul_eq_mul]

/-- An `Lᵖ` class that is almost everywhere `φ ∘ G`, for a simple function `G`, is the sum over a
finite set `S` of values of `G` of the indicator classes of the fibres `G ⁻¹' {w}` with constants
`φ w`, provided that `φ ∘ G` vanishes wherever `G` takes a value outside `S`. -/
theorem eq_sum_indicatorConstLp_fiber {F : Type*} {G : SimpleFunc α F} {φ : F → E}
    {S : Finset F} (hS : ∀ a, G a ∉ S → φ (G a) = 0) (hμS : ∀ w : S, μ (G ⁻¹' {w.1}) ≠ ∞)
    {x : Lp E p μ} (hx : x =ᵐ[μ] fun a ↦ φ (G a)) :
    x = ∑ w : S, indicatorConstLp p (G.measurableSet_fiber w.1) (hμS w) (φ w.1) := by
  refine Lp.ext ?_
  filter_upwards [hx, Lp.coeFn_fun_finsetSum Finset.univ
      fun w : S ↦ indicatorConstLp p (G.measurableSet_fiber w.1) (hμS w) (φ w.1),
    ae_all_iff.2 fun w : S ↦ indicatorConstLp_coeFn (p := p) (hs := G.measurableSet_fiber w.1)
      (hμs := hμS w) (c := φ w.1)] with a h₀ h₁ h₂
  simp only [h₀, h₁, h₂]
  by_cases h : G a ∈ S
  · rw [Finset.sum_eq_single (⟨G a, h⟩ : S)]
    · simp
    · intro w _ hw
      have hw' : a ∉ G ⁻¹' {w.1} := fun ha ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 ha).symm)
      simp [hw']
    · simp
  · refine (hS a h).trans (Finset.sum_eq_zero fun w _ ↦ ?_).symm
    have hw : a ∉ G ⁻¹' {w.1} := fun ha ↦ h ((Set.mem_singleton_iff.1 ha) ▸ w.2)
    simp [hw]

end Disjoint

section IndicatorContinuousOn

variable [TopologicalSpace α] [OpensMeasurableSpace α] [SecondCountableTopologyEither α E]

/-- A function that is continuous and bounded on a measurable set of finite measure, extended by
zero outside it, lies in every `L^p` space. -/
theorem memLp_indicator_of_continuousOn_of_norm_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {g : α → E} (hg : ContinuousOn g s) {M : ℝ} (hM : ∀ x ∈ s, ‖g x‖ ≤ M) :
    MemLp (s.indicator g) p μ := by
  have : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hμs.lt_top⟩
  refine (memLp_indicator_iff_restrict hs.nullMeasurableSet).2
    (MemLp.of_bound (hg.aestronglyMeasurable hs) M ?_)
  exact (ae_restrict_iff' hs).2 (ae_of_all _ hM)

end IndicatorContinuousOn

end TauCeti

noncomputable section

open Set
open scoped ENNReal

namespace TauCeti

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}

variable (μ) in
/-- The class in `L∞(μ)` of the indicator function of a measurable set. Unlike
`MeasureTheory.indicatorConstLp`, it needs no finiteness of `μ s`. -/
def linftyIndicator (s : Set α) (hs : MeasurableSet s) : Lp ℝ ∞ μ :=
  SimpleFunc.toLpTop μ ℝ (SimpleFunc.piecewise s hs (SimpleFunc.const α 1) 0)

/-- A constant multiple of an indicator, as a simple function, has class a multiple of
`TauCeti.linftyIndicator`. -/
@[simp]
theorem _root_.MeasureTheory.SimpleFunc.toLpTop_piecewise_const_zero (hs : MeasurableSet s)
    (c : ℝ) : SimpleFunc.toLpTop μ ℝ (SimpleFunc.piecewise s hs (SimpleFunc.const α c) 0) =
      c • linftyIndicator μ s hs := by
  rw [linftyIndicator, ← map_smul]
  congr 1
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- The class `TauCeti.linftyIndicator μ s hs` is almost everywhere the indicator of `s`. -/
theorem coeFn_linftyIndicator (hs : MeasurableSet s) :
    linftyIndicator μ s hs =ᵐ[μ] s.indicator 1 := by
  filter_upwards [SimpleFunc.coeFn_toLpTop (μ := μ) (𝕜 := ℝ)
    (SimpleFunc.piecewise s hs (SimpleFunc.const α (1 : ℝ)) 0)] with x hx
  rw [linftyIndicator, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The indicator of the empty set vanishes in `L∞`. -/
@[simp]
theorem linftyIndicator_empty : linftyIndicator μ ∅ MeasurableSet.empty = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) MeasurableSet.empty, Lp.coeFn_zero ℝ ∞ μ]
    with x h h0
  rw [h, h0, Set.indicator_empty, Pi.zero_apply]

/-- The indicator of the whole space is the constant one in `L∞`. -/
@[simp]
theorem linftyIndicator_univ : linftyIndicator μ univ MeasurableSet.univ = 1 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) MeasurableSet.univ,
    Lp.coeFn_one (E := ℝ) (μ := μ)] with x h h1
  rw [h, h1, Set.indicator_univ]

/-- Indicators of disjoint measurable sets add in `L∞`. -/
theorem linftyIndicator_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    linftyIndicator μ (s ∪ t) (hs.union ht) = linftyIndicator μ s hs + linftyIndicator μ t ht := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) (hs.union ht), coeFn_linftyIndicator (μ := μ) hs,
    coeFn_linftyIndicator (μ := μ) ht, Lp.coeFn_add (linftyIndicator μ s hs)
      (linftyIndicator μ t ht)] with x h hsx htx hadd
  rw [h, hadd, Pi.add_apply, hsx, htx, Set.indicator_union_of_disjoint hst]

/-- The indicator of a measurable set is nonnegative in `L∞`. -/
theorem linftyIndicator_nonneg (hs : MeasurableSet s) : 0 ≤ linftyIndicator μ s hs := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_linftyIndicator (μ := μ) hs] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- The indicator of a null set vanishes in `L∞`. -/
theorem linftyIndicator_of_measure_eq_zero (hs : MeasurableSet s) (h : μ s = 0) :
    linftyIndicator μ s hs = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) hs, Lp.coeFn_zero ℝ ∞ μ,
    measure_eq_zero_iff_ae_notMem.1 h] with x hx h0 hxs
  rw [hx, h0, Set.indicator_of_notMem hxs, Pi.zero_apply]

end TauCeti

namespace LinearMap

open MeasureTheory TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A continuous linear map out of real `L∞` is determined by its values at the indicators of
measurable sets. -/
theorem ext_linftyIndicator {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T2Space E] {f g : Lp ℝ ∞ μ →ₗ[ℝ] E} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ s (hs : MeasurableSet s), f (linftyIndicator μ s hs) = g (linftyIndicator μ s hs)) :
    f = g := by
  have hsimple : f ∘ₗ SimpleFunc.toLpTop μ ℝ = g ∘ₗ SimpleFunc.toLpTop μ ℝ := by
    ext φ
    induction φ using SimpleFunc.induction with
    | const c hs => simp [h]
    | add _ hφ hψ => simp_all
  exact LinearMap.coe_injective <|
    SimpleFunc.denseRange_toLpTop.equalizer hf hg (congrArg DFunLike.coe hsimple)

end LinearMap

namespace PositiveLinearMap

open MeasureTheory TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A positive linear functional on real `L∞` is determined by its values at the indicators of
measurable sets. -/
theorem ext_linftyIndicator {M N : Lp ℝ ∞ μ →ₚ[ℝ] ℝ}
    (h : ∀ s (hs : MeasurableSet s), M (linftyIndicator μ s hs) = N (linftyIndicator μ s hs)) :
    M = N := by
  have := LinearMap.ext_linftyIndicator (f := M.toLinearMap) (g := N.toLinearMap)
    M.continuous_lpTop N.continuous_lpTop h
  ext φ
  exact LinearMap.congr_fun this φ

end PositiveLinearMap

end
