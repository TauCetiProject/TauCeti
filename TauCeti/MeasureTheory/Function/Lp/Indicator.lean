/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Function.SimpleFunc.Dense
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Indicator classes in `Lᵖ`

The class `MeasureTheory.indicatorConstLp p hs hμs c` of `s.indicator fun _ => c` is linear in the
constant `c`: Mathlib provides additivity, `MeasureTheory.indicatorConstLp_add`, and this file adds
compatibility with scalar multiplication, bundling both as the linear map
`TauCeti.indicatorConstLpₗ`. Together with the norm formula
`MeasureTheory.norm_indicatorConstLp`, this makes `c ↦ indicatorConstLp p hs hμs c` a bounded
linear map, so closed subspaces of `Lᵖ` can be tested on indicator classes of a dense set of
constants.

Indicator classes of pairwise disjoint sets of finite measure span a weighted finite `ℓ¹` space
inside `L¹`: the norm of `∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)` is
`∑ i, μ(s i) * ‖c i‖`. An `Lᵖ` class represented by `φ ∘ G` for a simple function `G` is the
sum of the indicator classes of the fibres of `G` with constants `φ w`.

In `L∞` the indicator of any measurable set is essentially bounded, whatever its measure. The
class `TauCeti.linftyIndicator μ R s hs` of `1_s` in `Lp R ∞ μ` (for any normed additive group `R`
with `1`) therefore needs no finiteness of `μ s`, unlike `indicatorConstLp`. It is additive on
disjoint sets, nonnegative when `0 ≤ (1 : R)`, vanishes on null sets (and conversely when `1 ≠ 0`),
identifies sets up to almost-everywhere equality, and equals the constant one at `univ`. For any
scalar action on `Lᵖ`, multiplying by `linftyIndicator μ 𝕜 s hs` is the indicator cutoff, both
almost everywhere and as a `MemLp.toLp` class; on constant indicator classes it intersects the
supporting sets.

## Main declarations

* `TauCeti.indicatorConstLp_eq_zero_iff`: an `Lᵖ` constant indicator class vanishes if and only if
  the set has measure zero or the constant is zero.
* `TauCeti.indicatorConstLp_smul`: the indicator class of `a • c` is `a` times that of `c`.
* `TauCeti.indicatorConstLpₗ`: the indicator class `indicatorConstLp p hs hμs c` as a linear map
  in `c`.
* `TauCeti.norm_sum_indicatorConstLp_one`: the `L¹` norm of a sum of indicator classes of pairwise
  disjoint sets.
* `TauCeti.eq_sum_indicatorConstLp_fiber`: an `Lᵖ` class represented by `φ ∘ G`, for a simple
  function `G`, as a sum of indicator classes of the fibres of `G`.
* `MeasureTheory.SimpleFunc.memLp_indicator`, `MeasureTheory.SimpleFunc.integrable_indicator`: a
  simple function cut off to a measurable set of finite measure lies in every `Lᵖ`.
* `TauCeti.linftyIndicator μ R s hs`: the class in `Lp R ∞ μ` of the indicator of a measurable set.
* `MeasureTheory.SimpleFunc.toLpTop_piecewise_const_zero`: the class of a simple function
  `c • 1_s` is `c • linftyIndicator μ R s hs`.
* `ContinuousLinearMap.ext_indicatorConstLp`,
  `ContinuousLinearMap.eq_zero_of_apply_indicatorConstLp`: continuous semilinear maps out of `Lᵖ`,
  `p ≠ ∞`, are determined by their values on all finite-measure constant indicator classes.
* `ContinuousLinearMap.eq_zero_of_apply_indicatorConstLp_singleton`: a continuous linear map out of
  counting-measure `Lᵖ`, `p ≠ ∞`, that vanishes on singleton-supported vectors is zero.
* `LinearMap.ext_linftyIndicator`: a continuous linear map out of real `L∞` is determined by its
  values at the classes `linftyIndicator μ ℝ s hs`.
* `PositiveLinearMap.ext_linftyIndicator`: the same for positive linear functionals on real `L∞`,
  which are automatically continuous.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

section Zero

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [NormedAddCommGroup E]

/-- An `Lᵖ` constant indicator class vanishes if and only if either the set has measure zero or
the constant is zero. -/
@[simp]
theorem indicatorConstLp_eq_zero_iff {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E} :
    indicatorConstLp p hs hμs c = 0 ↔ μ s = 0 ∨ c = 0 := by
  by_cases hc : c = 0
  · simp only [hc, or_true, iff_true]
    refine Lp.ext ?_
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (0 : E)),
      Lp.coeFn_zero E p μ] with x h₁ h₂
    rw [h₁, h₂, Pi.zero_apply]
    simp
  · simp only [hc, or_false, ← indicatorConstLp_empty (p := p) (μ := μ) (c := c),
      indicatorConstLp_inj hs hμs .empty (by simp) hc, ae_eq_empty]

end Zero

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

variable (𝕜 p) in
/-- `MeasureTheory.indicatorConstLp` as a linear map in the constant. -/
@[expose, simps]
noncomputable def indicatorConstLpₗ (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    E →ₗ[𝕜] Lp E p μ where
  toFun := indicatorConstLp p hs hμs
  map_add' _ _ := indicatorConstLp_add.symm
  map_smul' := indicatorConstLp_smul hs hμs

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
    {S : Finset F} (hS : ∀ a, G a ∉ S → φ (G a) = 0) (hμS : ∀ w : S, μ (G ⁻¹' {w.val}) ≠ ∞)
    {x : Lp E p μ} (hx : x =ᵐ[μ] fun a ↦ φ (G a)) :
    x = ∑ w : S, indicatorConstLp p (G.measurableSet_fiber w.val) (hμS w) (φ w.val) := by
  refine Lp.ext ?_
  filter_upwards [hx, Lp.coeFn_fun_finsetSum Finset.univ
      fun w : S ↦ indicatorConstLp p (G.measurableSet_fiber w.val) (hμS w) (φ w.val),
    ae_all_iff.2 fun w : S ↦ indicatorConstLp_coeFn (p := p) (hs := G.measurableSet_fiber w.val)
      (hμs := hμS w) (c := φ w.val)] with a h₀ h₁ h₂
  simp only [h₀, h₁, h₂]
  by_cases h : G a ∈ S
  · rw [Finset.sum_eq_single (⟨G a, h⟩ : S)]
    · simp
    · intro w _ hw
      have hw' : a ∉ G ⁻¹' {w.val} := fun ha ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 ha).symm)
      simp [hw']
    · simp
  · refine (hS a h).trans (Finset.sum_eq_zero fun w _ ↦ ?_).symm
    have hw : a ∉ G ⁻¹' {w.val} := fun ha ↦ h ((Set.mem_singleton_iff.1 ha) ▸ w.property)
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

/-- A simple function cut off to a measurable set of finite measure lies in every `Lᵖ` space. -/
theorem _root_.MeasureTheory.SimpleFunc.memLp_indicator (g : SimpleFunc α E)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) : MemLp (s.indicator g) p μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs
  exact (memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (g.memLp_of_isFiniteMeasure p _)

/-- A simple function cut off to a measurable set of finite measure is integrable. -/
theorem _root_.MeasureTheory.SimpleFunc.integrable_indicator (g : SimpleFunc α E)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) : Integrable (s.indicator g) μ :=
  memLp_one_iff_integrable.1 (g.memLp_indicator hs hμs)

end TauCeti

noncomputable section

open Set
open scoped ENNReal

namespace TauCeti

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}

section LinftyIndicator

variable {R : Type*} [NormedAddCommGroup R] [One R]

variable (μ R) in
/-- The class in `Lp R ∞ μ` of the indicator function of a measurable set. Unlike
`MeasureTheory.indicatorConstLp`, it needs no finiteness of `μ s`. -/
def linftyIndicator (s : Set α) (hs : MeasurableSet s) : Lp R ∞ μ :=
  ((SimpleFunc.piecewise s hs (SimpleFunc.const α (1 : R)) 0).memLp_top μ).toLp _

/-- The class `TauCeti.linftyIndicator μ R s hs` is almost everywhere the indicator of `s`. -/
theorem coeFn_linftyIndicator (hs : MeasurableSet s) :
    linftyIndicator μ R s hs =ᵐ[μ] s.indicator 1 := by
  filter_upwards [MemLp.coeFn_toLp
    ((SimpleFunc.piecewise s hs (SimpleFunc.const α (1 : R)) 0).memLp_top μ)] with x hx
  rw [linftyIndicator, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- A constant multiple of an indicator, as a simple function, has class a multiple of
`TauCeti.linftyIndicator`. -/
@[simp]
theorem _root_.MeasureTheory.SimpleFunc.toLpTop_piecewise_const_zero
    {𝕜 R : Type*} [NormedRing 𝕜] [NormedRing R] [Module 𝕜 R] [IsBoundedSMul 𝕜 R]
    (hs : MeasurableSet s) (c : R) :
    SimpleFunc.toLpTop μ 𝕜 (SimpleFunc.piecewise s hs (SimpleFunc.const α c) 0) =
      c • linftyIndicator μ R s hs := by
  refine Lp.ext ?_
  filter_upwards [SimpleFunc.coeFn_toLpTop (μ := μ) (𝕜 := 𝕜)
      (SimpleFunc.piecewise s hs (SimpleFunc.const α c) 0),
    Lp.coeFn_smul c (linftyIndicator μ R s hs),
    coeFn_linftyIndicator (μ := μ) (R := R) hs] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

section SMul

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [MulActionWithZero 𝕜 E]
  [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞}

/-- Heterogeneous `L∞` scalar multiplication by an indicator is almost everywhere the indicator
cutoff. -/
theorem coeFn_linftyIndicator_smul (hs : MeasurableSet s) (f : Lp E p μ) :
    (linftyIndicator μ 𝕜 s hs • f : Lp E p μ) =ᵐ[μ] s.indicator f := by
  filter_upwards [Lp.coeFn_lpSMul (r := p) (linftyIndicator μ 𝕜 s hs) f,
    coeFn_linftyIndicator (μ := μ) (R := 𝕜) hs] with x hx hsx
  rw [hx, Pi.smul_apply', hsx]
  by_cases h : x ∈ s <;> simp [h]

/-- Heterogeneous `L∞` scalar multiplication by an indicator agrees with the `MemLp.toLp`
cutoff. -/
theorem linftyIndicator_smul_eq_toLp (hs : MeasurableSet s) (f : Lp E p μ) :
    (linftyIndicator μ 𝕜 s hs • f : Lp E p μ) =
      ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f) :=
  Lp.ext ((coeFn_linftyIndicator_smul hs f).trans
    ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp.symm)

/-- Cutting off a constant indicator class by `L∞` scalar multiplication intersects its supporting
set. -/
@[simp]
theorem linftyIndicator_smul_indicatorConstLp (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (c : E) :
    (linftyIndicator μ 𝕜 s hs • indicatorConstLp p ht hμt c : Lp E p μ) =
      indicatorConstLp p (hs.inter ht)
        (ne_top_of_le_ne_top hμt (measure_mono inter_subset_right)) c := by
  apply Lp.ext
  filter_upwards [coeFn_linftyIndicator_smul (𝕜 := 𝕜) hs (indicatorConstLp p ht hμt c),
    indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt) (c := c),
    indicatorConstLp_coeFn (p := p) (hs := hs.inter ht)
      (hμs := ne_top_of_le_ne_top hμt (measure_mono inter_subset_right)) (c := c)]
      with x hx ht hst
  rw [hx, hst]
  by_cases h : x ∈ s <;> by_cases h' : x ∈ t <;> simp [h, h', ht]

end SMul

section Holder

variable {p : ℝ≥0∞}

private theorem holder_mul_linftyIndicator_eq_smul (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    (ContinuousLinearMap.mul ℝ ℝ).holder p (linftyIndicator μ ℝ s hs) f =
      linftyIndicator μ ℝ s hs • f := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
      (r := p) (linftyIndicator μ ℝ s hs) f,
    Lp.coeFn_lpSMul (r := p) (linftyIndicator μ ℝ s hs) f] with x hx hy
  rw [hx, ContinuousLinearMap.mul_apply', hy, Pi.smul_apply', smul_eq_mul]

/-- Hölder multiplication by an `L∞` indicator is almost everywhere the indicator cutoff. -/
theorem coeFn_holder_mul_linftyIndicator (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    (ContinuousLinearMap.mul ℝ ℝ).holder p (linftyIndicator μ ℝ s hs) f =ᵐ[μ]
      s.indicator f := by
  rw [holder_mul_linftyIndicator_eq_smul]
  exact coeFn_linftyIndicator_smul hs f

/-- Hölder multiplication by an `L∞` indicator agrees with the `MemLp.toLp` cutoff. -/
theorem holder_mul_linftyIndicator_eq_toLp (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    (ContinuousLinearMap.mul ℝ ℝ).holder p (linftyIndicator μ ℝ s hs) f =
      ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f) := by
  rw [holder_mul_linftyIndicator_eq_smul]
  exact linftyIndicator_smul_eq_toLp hs f

/-- Cutting off a constant indicator class intersects its supporting set. -/
@[simp]
theorem holder_mul_linftyIndicator_indicatorConstLp (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (c : ℝ) :
    (ContinuousLinearMap.mul ℝ ℝ).holder p (linftyIndicator μ ℝ s hs)
        (indicatorConstLp p ht hμt c) =
      indicatorConstLp p (hs.inter ht)
        (ne_top_of_le_ne_top hμt (measure_mono inter_subset_right)) c := by
  rw [holder_mul_linftyIndicator_eq_smul]
  exact linftyIndicator_smul_indicatorConstLp hs ht hμt c

end Holder

/-- The indicator of the empty set vanishes in `L∞`. -/
@[simp]
theorem linftyIndicator_empty : linftyIndicator μ R ∅ MeasurableSet.empty = 0 := by
  simp [linftyIndicator]

/-- The indicator of the whole space is the constant one in `L∞`. -/
@[simp]
theorem linftyIndicator_univ : linftyIndicator μ R univ MeasurableSet.univ = 1 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) (R := R) MeasurableSet.univ,
    Lp.coeFn_one (E := R) (μ := μ)] with x h h1
  rw [h, h1, Set.indicator_univ]

/-- Indicators of disjoint measurable sets add in `L∞`. -/
theorem linftyIndicator_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    linftyIndicator μ R (s ∪ t) (hs.union ht) =
      linftyIndicator μ R s hs + linftyIndicator μ R t ht := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) (R := R) (hs.union ht),
    coeFn_linftyIndicator (μ := μ) (R := R) hs, coeFn_linftyIndicator (μ := μ) (R := R) ht,
    Lp.coeFn_add (linftyIndicator μ R s hs) (linftyIndicator μ R t ht)] with x h hsx htx hadd
  rw [h, hadd, Pi.add_apply, hsx, htx, Set.indicator_union_of_disjoint hst]

/-- The indicator of a measurable set is nonnegative in `L∞`. -/
theorem linftyIndicator_nonneg [PartialOrder R] [ZeroLEOneClass R] (hs : MeasurableSet s) :
    0 ≤ linftyIndicator μ R s hs := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_linftyIndicator (μ := μ) (R := R) hs] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- The indicator of a null set vanishes in `L∞`. -/
theorem linftyIndicator_of_measure_eq_zero (hs : MeasurableSet s) (h : μ s = 0) :
    linftyIndicator μ R s hs = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) (R := R) hs, Lp.coeFn_zero R ∞ μ,
    measure_eq_zero_iff_ae_notMem.1 h] with x hx h0 hxs
  rw [hx, h0, Set.indicator_of_notMem hxs, Pi.zero_apply]

/-- Two measurable-set unit indicators in `Lp R ∞ μ` agree if and only if their underlying sets
agree almost everywhere, provided `(1 : R) ≠ 0`. -/
theorem linftyIndicator_inj [NeZero (1 : R)] (hs : MeasurableSet s) (ht : MeasurableSet t) :
    linftyIndicator μ R s hs = linftyIndicator μ R t ht ↔ s =ᵐ[μ] t := by
  rw [Lp.ext_iff, ← Filter.indicator_const_eventuallyEq (one_ne_zero (α := R))]
  exact ⟨fun h ↦ (coeFn_linftyIndicator hs).symm.trans (h.trans (coeFn_linftyIndicator ht)),
    fun h ↦ (coeFn_linftyIndicator hs).trans (h.trans (coeFn_linftyIndicator ht).symm)⟩

/-- The unit indicator of a measurable set vanishes in `Lp R ∞ μ` if and only if the set is
`μ`-null, provided `(1 : R) ≠ 0`. -/
@[simp]
theorem linftyIndicator_eq_zero_iff [NeZero (1 : R)] (hs : MeasurableSet s) :
    linftyIndicator μ R s hs = 0 ↔ μ s = 0 := by
  rw [← linftyIndicator_empty (μ := μ) (R := R), linftyIndicator_inj hs MeasurableSet.empty,
    ae_eq_empty]

end LinftyIndicator

end TauCeti

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal

/-- Two continuous semilinear maps out of `Lᵖ`, `p ≠ ∞`, that agree on all finite-measure constant
indicator classes are equal. -/
theorem ext_indicatorConstLp
    {α 𝕜₁ 𝕜₂ E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedRing 𝕜₁] [Semiring 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
    [NormedAddCommGroup E] [Module 𝕜₁ E] [IsBoundedSMul 𝕜₁ E]
    [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜₂ F] [T2Space F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {S T : Lp E p μ →SL[σ₁₂] F}
    (h : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E),
      S (indicatorConstLp p hs hμs c) = T (indicatorConstLp p hs hμs c)) : S = T := by
  refine ContinuousLinearMap.ext fun f ↦ ?_
  refine Lp.induction (p := p) hp (fun f ↦ S f = T f) ?_ ?_
    (isClosed_eq S.continuous T.continuous) f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact h s hs hμs.ne c
  · intro f g _ _ _ hfg₁ hfg₂
    rw [map_add, map_add, hfg₁, hfg₂]

/-- A continuous semilinear map out of `Lᵖ`, `p ≠ ∞`, that vanishes on all finite-measure constant
indicator classes is zero. -/
theorem eq_zero_of_apply_indicatorConstLp
    {α 𝕜₁ 𝕜₂ E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedRing 𝕜₁] [Semiring 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
    [NormedAddCommGroup E] [Module 𝕜₁ E] [IsBoundedSMul 𝕜₁ E]
    [TopologicalSpace F] [AddCommMonoid F] [Module 𝕜₂ F] [T2Space F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : Lp E p μ →SL[σ₁₂] F)
    (h : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E),
      T (indicatorConstLp p hs hμs c) = 0) : T = 0 :=
  ext_indicatorConstLp hp fun s hs hμs c ↦ by
    rw [zero_apply]
    exact h s hs hμs c

/-- A continuous linear map out of counting-measure `Lᵖ`, `p ≠ ∞`, that vanishes on all
singleton-supported vectors is zero. No countability of the index space is needed. -/
theorem eq_zero_of_apply_indicatorConstLp_singleton
    {α 𝕜 E F : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : Lp E p (Measure.count : Measure α) →L[𝕜] F)
    (h : ∀ (i : α) (v : E),
      T (indicatorConstLp p (measurableSet_singleton i) (by simp) v) = 0) : T = 0 := by
  -- Finite sets are finite disjoint unions of singletons.
  have hfin (c : E) (t : Finset α) :
      T (indicatorConstLp p t.measurableSet (by simp [Measure.count_apply_finset]) c) = 0 := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
      have hd : Disjoint ({i} : Set α) (t : Set α) := by simpa using hi
      have := indicatorConstLp_disjoint_union (p := p) (μ := (Measure.count : Measure α))
        (measurableSet_singleton i) t.measurableSet (by simp)
        (by simp [Measure.count_apply_finset]) hd c
      simp only [Finset.coe_insert, ← Set.singleton_union] at *
      rw [this, map_add, h, ih, add_zero]
  refine eq_zero_of_apply_indicatorConstLp hp T fun s hs hμs c ↦ ?_
  obtain ⟨t, rfl⟩ := (Measure.count_apply_lt_top.mp hμs.lt_top).exists_finset_coe
  exact hfin c t

end ContinuousLinearMap

namespace LinearMap

open MeasureTheory TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A continuous linear map out of real `L∞` is determined by its values at the indicators of
measurable sets. -/
theorem ext_linftyIndicator {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T2Space E] {f g : Lp ℝ ∞ μ →ₗ[ℝ] E} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ s (hs : MeasurableSet s),
      f (linftyIndicator μ ℝ s hs) = g (linftyIndicator μ ℝ s hs)) :
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
    (h : ∀ s (hs : MeasurableSet s),
      M (linftyIndicator μ ℝ s hs) = N (linftyIndicator μ ℝ s hs)) :
    M = N := by
  have := LinearMap.ext_linftyIndicator (f := M.toLinearMap) (g := N.toLinearMap)
    M.continuous_lpTop N.continuous_lpTop h
  ext φ
  exact LinearMap.congr_fun this φ

end PositiveLinearMap

end
