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
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Indicator classes in `Lᵖ`

The class `MeasureTheory.indicatorConstLp p hs hμs c` of `s.indicator fun _ => c` is linear in the
constant `c`: Mathlib provides additivity, `MeasureTheory.indicatorConstLp_add`, and this file adds
compatibility with scalar multiplication, bundling both as the linear map
`TauCeti.indicatorConstLpₗ`. Together with the norm formula
`MeasureTheory.norm_indicatorConstLp`, this makes `c ↦ indicatorConstLp p hs hμs c` a bounded
linear map, so closed subspaces of `Lᵖ` can be tested on indicator classes of a dense set of
constants.

For finite exponents, the `Lᵖ` seminorm of a fixed `Lᵖ` function on sets whose measure tends to
zero tends to zero (`MeasureTheory.MemLp.tendsto_eLpNorm_restrict_of_tendsto_measure`), so cutting
the function off to varying sets is continuous when the measures of their symmetric differences
tend to zero (`MeasureTheory.MemLp.tendsto_toLp_indicator`). The ambient measure need not be
finite.

Indicator classes of pairwise disjoint sets of finite measure span a weighted finite `ℓ¹` space
inside `L¹`: the norm of `∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)` is
`∑ i, μ(s i) * ‖c i‖`. An `Lᵖ` class represented by `φ ∘ G` for a simple function `G` is the
sum of the indicator classes of the fibres of `G` with constants `φ w`.

For finite exponents, the indicator classes of the partial unions of a sequence of sets converge
to the indicator class of the union when the union has finite measure. Hence a closed additive
subgroup of `Lᵖ` containing the indicator classes of a pairwise disjoint sequence contains the
indicator class of its union.

In `L∞` the indicator of any measurable set is essentially bounded, whatever its measure. The
class `TauCeti.linftyIndicator μ s hs` of `1_s` in real `L∞(μ)` therefore needs no finiteness of
`μ s`, unlike `indicatorConstLp`. It is additive on disjoint sets, nonnegative, vanishes on null
sets, and equals the constant one at `univ`. Hölder multiplication by this class is the
indicator cutoff on real `Lᵖ`, both almost everywhere and as a `MemLp.toLp` class; on
constant indicator classes it intersects the supporting sets.

## Main declarations

* `TauCeti.indicatorConstLp_eq_zero_iff`: an `Lᵖ` constant indicator class vanishes if and only if
  the set has measure zero or the constant is zero.
* `TauCeti.indicatorConstLp_smul`: the indicator class of `a • c` is `a` times that of `c`.
* `TauCeti.indicatorConstLpₗ`: the indicator class `indicatorConstLp p hs hμs c` as a linear map
  in `c`.
* `TauCeti.indicatorConstLpL`: the same map `c ↦ indicatorConstLp p hs hμs c` as a continuous
  linear map.
* `TauCeti.norm_sum_indicatorConstLp_one`: the `L¹` norm of a sum of indicator classes of pairwise
  disjoint sets.
* `TauCeti.eq_sum_indicatorConstLp_fiber`: an `Lᵖ` class represented by `φ ∘ G`, for a simple
  function `G`, as a sum of indicator classes of the fibres of `G`.
* `TauCeti.tendsto_indicatorConstLp_accumulate`: for `p < ∞`, the indicator classes of the partial
  unions of a sequence of sets converge to that of the union, if the union has finite measure.
* `TauCeti.indicatorConstLp_iUnion_mem`: for `p < ∞`, a closed additive subgroup of `Lᵖ` containing
  the indicator classes of a pairwise disjoint sequence of sets contains that of their union.
* `MeasureTheory.SimpleFunc.memLp_indicator`, `MeasureTheory.SimpleFunc.integrable_indicator`: a
  simple function cut off to a measurable set of finite measure lies in every `Lᵖ`.
* `TauCeti.linftyIndicator μ s hs`: the class in `L∞(μ)` of the indicator of a measurable set.
* `MeasureTheory.SimpleFunc.toLpTop_piecewise_const_zero`: the class of a simple function
  `c • 1_s` is `c • linftyIndicator μ s hs`.
* `ContinuousLinearMap.compLp_indicatorConstLp`: postcomposition with a continuous linear map
  sends the indicator class of `c` to that of its image.
* `ContinuousLinearMap.eq_zero_of_apply_indicatorConstLp_singleton`: a continuous linear map out of
  counting-measure `Lᵖ`, `p ≠ ∞`, that vanishes on singleton-supported vectors is zero.
* `LinearMap.ext_linftyIndicator`: a continuous linear map out of real `L∞` is determined by its
  values at the classes `linftyIndicator μ s hs`.
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

variable (𝕜 p) in
/-- `TauCeti.indicatorConstLpₗ` as a continuous linear map from the constants to `Lᵖ`. Its norm
is at most `μ(s) ^ (1 / p)`, by `MeasureTheory.norm_indicatorConstLp_le`. -/
noncomputable def indicatorConstLpL [Fact (1 ≤ p)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    E →L[𝕜] Lp E p μ :=
  (indicatorConstLpₗ 𝕜 p hs hμs).mkContinuous (μ.real s ^ (1 / p.toReal)) fun c ↦
    (norm_indicatorConstLp_le (hs := hs) (hμs := hμs) (c := c)).trans_eq (mul_comm _ _)

/-- `TauCeti.indicatorConstLpL` sends a constant to its indicator class. -/
@[simp]
theorem indicatorConstLpL_apply [Fact (1 ≤ p)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    indicatorConstLpL 𝕜 p hs hμs c = indicatorConstLp p hs hμs c := by
  simp [indicatorConstLpL]

section NormedField

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [NormedAddCommGroup E]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] {s : Set α}

variable (𝕜 E) in
/-- The operator norm of `TauCeti.indicatorConstLpL` is at most `μ(s) ^ (1 / p)`. -/
theorem norm_indicatorConstLpL_le [Fact (1 ≤ p)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ‖(indicatorConstLpL 𝕜 p hs hμs : E →L[𝕜] Lp E p μ)‖ ≤ μ.real s ^ (1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg measureReal_nonneg _) _

end NormedField

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

section DisjointUnion

open Filter Set
open scoped symmDiff Topology

variable [Fact (1 ≤ p)] {f : ℕ → Set α} {c : E}

/-- For `p < ∞`, the indicator classes of the partial unions `accumulate f n` of a sequence of sets
converge in `Lᵖ` to the indicator class of the whole union, provided the union has finite
measure. -/
theorem tendsto_indicatorConstLp_accumulate {hU : MeasurableSet (⋃ i, f i)}
    {hμU : μ (⋃ i, f i) ≠ ∞} {hA : ∀ n, MeasurableSet (accumulate f n)}
    {hμA : ∀ n, μ (accumulate f n) ≠ ∞} (hp : p ≠ ∞) :
    Tendsto (fun n ↦ indicatorConstLp p (hA n) (hμA n) c) atTop
      (𝓝 (indicatorConstLp p hU hμU c)) := by
  refine tendsto_indicatorConstLp_set hp ?_
  simp_rw [symmDiff_of_le (accumulate_subset_iUnion _)]
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n ↦ (⋃ i, f i) \ accumulate f n)
    (fun n ↦ (hU.diff (hA n)).nullMeasurableSet)
    (fun i j hij ↦ sdiff_subset_sdiff_right (monotone_accumulate hij))
    ⟨0, measure_ne_top_of_subset sdiff_subset hμU⟩
  rwa [← sdiff_iUnion, iUnion_accumulate, Set.sdiff_self, measure_empty] at h

/-- If a closed additive subgroup of `Lᵖ`, `p < ∞`, contains the indicator classes of the members
of a pairwise disjoint sequence of measurable sets, it contains the indicator class of their union,
provided the union has finite measure. -/
theorem indicatorConstLp_iUnion_mem {V : AddSubgroup (Lp E p μ)}
    (hV : IsClosed (V : Set (Lp E p μ))) (hp : p ≠ ∞) (hfm : ∀ i, MeasurableSet (f i))
    (hfd : Pairwise (Function.onFun Disjoint f)) (hμ : μ (⋃ i, f i) ≠ ∞)
    (hf : ∀ i (hμi : μ (f i) ≠ ∞), indicatorConstLp p (hfm i) hμi c ∈ V) :
    indicatorConstLp p (MeasurableSet.iUnion hfm) hμ c ∈ V := by
  have hA : ∀ n, MeasurableSet (accumulate f n) := fun n ↦
    MeasurableSet.biUnion (to_countable _) fun i _ ↦ hfm i
  have hμA : ∀ n, μ (accumulate f n) ≠ ∞ := fun n ↦
    measure_ne_top_of_subset (accumulate_subset_iUnion n) hμ
  have hμf : ∀ i, μ (f i) ≠ ∞ := fun i ↦ measure_ne_top_of_subset (subset_iUnion f i) hμ
  -- the partial unions have indicator classes in `V`
  have hAV : ∀ n, indicatorConstLp p (hA n) (hμA n) c ∈ V := by
    intro n
    induction n with
    | zero =>
      convert hf 0 (hμf 0) using 2
      exact accumulate_zero_nat f
    | succ n ih =>
      convert V.add_mem ih (hf _ (hμf (n + 1))) using 1
      rw [← indicatorConstLp_disjoint_union (hA n) (hfm _) (hμA n) (hμf _)
        (disjoint_accumulate hfd n.lt_succ_self)]
      congr 1
      exact accumulate_succ f n
  exact hV.mem_of_tendsto (tendsto_indicatorConstLp_accumulate (hA := hA) (hμA := hμA) hp)
    (Eventually.of_forall hAV)

end DisjointUnion

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

namespace MeasureTheory.MemLp

open Filter Set
open scoped Topology ENNReal symmDiff

/-- The `Lᵖ` seminorm of a fixed `Lᵖ` function on sets whose measure tends to zero tends to zero,
for `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_restrict_of_tendsto_measure {α E ι : Type*} {_ : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} {f : α → E} (hf : MemLp f p μ)
    (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {l : Filter ι} {s : ι → Set α}
    (h : Tendsto (fun i ↦ μ (s i)) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm f p (μ.restrict (s i))) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((hf.tendsto_eLpNorm_restrict_zero hp_one hp_top).comp h)
    (Eventually.of_forall fun _ ↦ bot_le)
    (Eventually.of_forall fun i ↦ le_iSup_of_le (s i) (le_iSup_of_le le_rfl le_rfl))

/-- Cutting a fixed `Lᵖ` function off to sets converging in symmetric-difference measure
converges in `Lᵖ`, for `1 ≤ p < ∞`. Neither the ambient measure nor the sets need have
finite measure. -/
theorem tendsto_toLp_indicator {α E ι : Type*} {_ : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : α → E} (hf : MemLp f p μ) (hp : p ≠ ∞)
    {l : Filter ι} {s : ι → Set α} {t : Set α}
    (hs : ∀ i, NullMeasurableSet (s i) μ) (ht : NullMeasurableSet t μ)
    (h : Tendsto (fun i ↦ μ (s i ∆ t)) l (𝓝 0)) :
    Tendsto (fun i ↦ (hf.indicator (hs i)).toLp ((s i).indicator f))
      l (𝓝 ((hf.indicator ht).toLp (t.indicator f))) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  simp_rw [eLpNorm_indicator_sub_indicator f (hs _) ht,
    eLpNorm_indicator_eq_eLpNorm_restrict ((hs _).symmDiff ht)]
  exact hf.tendsto_eLpNorm_restrict_of_tendsto_measure Fact.out hp h

end MeasureTheory.MemLp

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

section Holder

variable {p : ℝ≥0∞}

/-- Hölder multiplication by an `L∞` indicator is almost everywhere the indicator cutoff. -/
theorem coeFn_holder_mul_linftyIndicator (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    (ContinuousLinearMap.mul ℝ ℝ).holder p (linftyIndicator μ s hs) f =ᵐ[μ]
      s.indicator f := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := p) (linftyIndicator μ s hs) f, coeFn_linftyIndicator (μ := μ) hs] with x hx hsx
  rw [hx, ContinuousLinearMap.mul_apply', hsx]
  by_cases h : x ∈ s <;> simp [h]

/-- Hölder multiplication by an `L∞` indicator agrees with the `MemLp.toLp` cutoff. -/
theorem holder_mul_linftyIndicator_eq_toLp (hs : MeasurableSet s) (f : Lp ℝ p μ) :
    (ContinuousLinearMap.mul ℝ ℝ).holder p (linftyIndicator μ s hs) f =
      ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f) :=
  Lp.ext ((coeFn_holder_mul_linftyIndicator hs f).trans
    ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp.symm)

/-- Cutting off a constant indicator class intersects its supporting set. -/
@[simp]
theorem holder_mul_linftyIndicator_indicatorConstLp (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (c : ℝ) :
    (ContinuousLinearMap.mul ℝ ℝ).holder p (linftyIndicator μ s hs)
        (indicatorConstLp p ht hμt c) =
      indicatorConstLp p (hs.inter ht)
        (ne_top_of_le_ne_top hμt (measure_mono inter_subset_right)) c := by
  apply Lp.ext
  filter_upwards [coeFn_holder_mul_linftyIndicator hs (indicatorConstLp p ht hμt c),
    indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt) (c := c),
    indicatorConstLp_coeFn (p := p) (hs := hs.inter ht)
      (hμs := ne_top_of_le_ne_top hμt (measure_mono inter_subset_right)) (c := c)]
      with x hx ht hst
  rw [hx, hst]
  by_cases h : x ∈ s <;> by_cases h' : x ∈ t <;> simp [h, h', ht]

end Holder

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

namespace ContinuousLinearMap

open MeasureTheory
open scoped ENNReal

/-- Postcomposition with a continuous (semi)linear map commutes with `indicatorConstLp`. -/
@[simp]
theorem compLp_indicatorConstLp {α 𝕜 𝕜' E F : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F] {σ : 𝕜 →+* 𝕜'}
    [RingHomIsometric σ] (L : E →SL[σ] F) {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : E) : L.compLp (indicatorConstLp p hs hμs c) = indicatorConstLp p hs hμs (L c) := by
  refine Lp.ext ?_
  filter_upwards [L.coeFn_compLp (indicatorConstLp p hs hμs c),
    (indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] _),
    (indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs (L c)) =ᵐ[μ] _)] with x hx₁ hx₂ hx₃
  rw [hx₁, hx₂, hx₃]
  exact (congrFun (Set.indicator_comp_of_zero (f := fun _ ↦ c) (map_zero L)) x).symm

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
  refine ContinuousLinearMap.ext fun f ↦ ?_
  refine Lp.induction (p := p) hp (fun f ↦ T f = 0) ?_ ?_
    (isClosed_eq T.continuous continuous_const) f
  · intro c s hs hμs
    obtain ⟨t, rfl⟩ := (Measure.count_apply_lt_top.mp hμs).exists_finset_coe
    exact hfin c t
  · intro f g hf hg _ hTf hTg
    rw [map_add, hTf, hTg, add_zero]

end ContinuousLinearMap

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
