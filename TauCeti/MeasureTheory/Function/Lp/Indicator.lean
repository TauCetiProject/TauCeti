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

In `L∞` the indicator of any measurable set is essentially bounded, whatever its measure. The
class `TauCeti.linftyIndicator μ s hs` of `1_s` in real `L∞(μ)` therefore needs no finiteness of
`μ s`, unlike `indicatorConstLp`. It is additive on disjoint sets, nonnegative, vanishes on null
sets, and equals the constant one at `univ`. Hölder multiplication by this class is the
indicator cutoff on real `Lᵖ`, both almost everywhere and as a `MemLp.toLp` class; on
constant indicator classes it intersects the supporting sets.

## Main declarations

* `TauCeti.indicatorConstLp_eq_zero_iff`: an `Lᵖ` constant indicator class vanishes if and only if
  the set has measure zero or the constant is zero.
* `TauCeti.memLp_indicator_const_iff`: for `0 < p < ∞`, the indicator of a set with a nonzero
  constant value is in `Lᵖ` if and only if the set has finite measure.
* `TauCeti.indicatorConstLp_smul`: the indicator class of `a • c` is `a` times that of `c`.
* `TauCeti.indicatorConstLpₗ`: the indicator class `indicatorConstLp p hs hμs c` as a linear map
  in `c`.
* `TauCeti.indicatorConstLpL`: the same map `c ↦ indicatorConstLp p hs hμs c` as a continuous
  linear map.
* `ContinuousLinearMap.norm_comp_indicatorConstLpL_le`: for a continuous linear map `T` on `Lᵖ`,
  the map `c ↦ T (1_s c)` has norm at most `‖T‖ μ(s) ^ (1 / p)`.
* `MeasureTheory.MemLp.toLp_indicator_eq_indicatorConstLp`: the cut-off to `s` of a function that is
  a.e. equal to a constant `c` on `s` is the indicator class of `c`.
* `TauCeti.norm_sum_indicatorConstLp_one`: the `L¹` norm of a sum of indicator classes of pairwise
  disjoint sets.
* `TauCeti.tendsto_indicatorConstLp_of_monotone`: for a finite exponent, the indicator classes of
  an increasing family of measurable sets converge to the class of their union of finite measure.
* `TauCeti.indicatorConstLp_sdiff`, `TauCeti.sum_indicatorConstLp`,
  `TauCeti.hasSum_indicatorConstLp`: indicator classes are subtractive, finitely additive, and for a
  finite exponent countably additive on pairwise disjoint sets whose union has finite measure.
* `TauCeti.eq_sum_indicatorConstLp_fiber`: an `Lᵖ` class represented by `φ ∘ G`, for a simple
  function `G`, as a sum of indicator classes of the fibres of `G`.
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

/-- For an exponent `0 < p < ∞`, the indicator of a set with a constant value is in `Lᵖ` if and
only if the constant is zero or the set has finite measure. -/
theorem memLp_indicator_const_iff {s : Set α} (hs : NullMeasurableSet s μ) (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {c : E} : MemLp (s.indicator fun _ ↦ c) p μ ↔ c = 0 ∨ μ s ≠ ∞ := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hc hμs ↦ ?_, memLp_indicator_const p hs c⟩
  have := h.eLpNorm_lt_top
  rw [eLpNorm_indicator_const hs hp0 hp, hμs,
    ENNReal.top_rpow_of_pos (by simp [ENNReal.toReal_pos hp0 hp]),
    ENNReal.mul_top (eNorm_ne_zero.2 hc)] at this
  exact lt_irrefl _ this

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

/-- For a continuous linear map `T` on `Lᵖ`, the map `c ↦ T (1_s c)` on the constants has norm at
most `‖T‖ μ(s) ^ (1 / p)`. On an atom `s` this is the bound of the discussion of atomic measure
spaces before Proposition 1.3.3 of Hytönen, van Neerven, Veraar and Weis, *Analysis in Banach
Spaces*, Vol. I, as corrected in the authors' Volume I errata, entry for p. 39
(<https://fa.ewi.tudelft.nl/~neerven/ABS/errata-vol1.pdf>). -/
theorem _root_.ContinuousLinearMap.norm_comp_indicatorConstLpL_le {F : Type*}
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Fact (1 ≤ p)] (T : Lp E p μ →L[𝕜] F)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ‖T.comp (indicatorConstLpL 𝕜 p hs hμs)‖ ≤ ‖T‖ * μ.real s ^ (1 / p.toReal) :=
  (T.opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_left (norm_indicatorConstLpL_le 𝕜 E hs hμs) (norm_nonneg T))

end NormedField

/-- The indicator class of a difference `s \ t` with `t ⊆ s` is the difference of the indicator
classes. -/
theorem indicatorConstLp_sdiff {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hts : t ⊆ s) (c : E) :
    indicatorConstLp p (hs.diff ht) (ne_top_of_le_ne_top hμs (measure_mono Set.sdiff_subset)) c =
      indicatorConstLp p hs hμs c -
        indicatorConstLp p ht (ne_top_of_le_ne_top hμs (measure_mono hts)) c := by
  rw [eq_sub_iff_add_eq, ← indicatorConstLp_disjoint_union _ _ _ _ Set.disjoint_sdiff_left]
  congr 1
  exact Set.sdiff_union_of_subset hts

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

section Countable

open Filter
open scoped symmDiff Topology

variable {ι : Type*} {s : ι → Set α}

/-- The indicator class of a finite union of pairwise disjoint sets of finite measure is the sum
of the indicator classes of the sets. -/
theorem sum_indicatorConstLp (t : Finset ι) (hs : ∀ i, MeasurableSet (s i))
    (hμs : ∀ i, μ (s i) ≠ ∞) (hd : (t : Set ι).PairwiseDisjoint s) (c : E) :
    ∑ i ∈ t, indicatorConstLp p (hs i) (hμs i) c =
      indicatorConstLp p (t.measurableSet_biUnion fun i _ ↦ hs i)
        (measure_biUnion_lt_top t.finite_toSet fun i _ ↦ (hμs i).lt_top).ne c := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact (indicatorConstLp_eq_zero_iff.2 (.inl (by simp))).symm
  | insert i t hi ih =>
    have hd' : (t : Set ι).PairwiseDisjoint s :=
      hd.subset (Finset.coe_subset.2 (Finset.subset_insert i t))
    rw [Finset.sum_insert hi, ih hd', ← indicatorConstLp_disjoint_union (hs i)
      (t.measurableSet_biUnion fun j _ ↦ hs j) (hμs i) _
      (Set.disjoint_iUnion₂_right.2 fun j hj ↦ hd (by simp) (by simp [hj])
        fun h ↦ hi (h ▸ hj))]
    congr 1
    rw [Finset.set_biUnion_insert]

/-- For a finite exponent, the indicator classes of an increasing family of measurable sets
converge to the indicator class of their union, provided the union has finite measure. -/
theorem tendsto_indicatorConstLp_of_monotone [Fact (1 ≤ p)] (hp : p ≠ ∞) [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {u : Set α} {hu : MeasurableSet u} {hμu : μ u ≠ ∞}
    {t : ι → Set α} (ht : ∀ i, MeasurableSet (t i)) (hmono : Monotone t) (htu : ⋃ i, t i = u)
    (c : E) :
    Tendsto (fun i ↦ indicatorConstLp p (ht i)
        (ne_top_of_le_ne_top hμu (measure_mono (htu ▸ Set.subset_iUnion t i))) c) atTop
      (𝓝 (indicatorConstLp p hu hμu c)) := by
  subst htu
  have hμt (i : ι) : μ (t i) ≠ ∞ := ne_top_of_le_ne_top hμu (measure_mono (Set.subset_iUnion t i))
  refine tendsto_indicatorConstLp_set hp ?_
  have hdiff (i : ι) : μ (t i ∆ ⋃ j, t j) = μ (⋃ j, t j) - μ (t i) := by
    rw [symmDiff_of_le (Set.subset_iUnion t i),
      measure_sdiff (Set.subset_iUnion t i) (ht i).nullMeasurableSet (hμt i)]
  simp_rw [hdiff]
  have := ENNReal.Tendsto.sub tendsto_const_nhds (tendsto_measure_iUnion_atTop (μ := μ) hmono)
    (.inl hμu)
  rwa [tsub_self] at this

/-- **Countable additivity of indicator classes.** For a finite exponent, the classes in `Lᵖ` of
the indicators of countably many pairwise disjoint measurable sets whose union has finite measure
sum to the class of the indicator of the union. -/
theorem hasSum_indicatorConstLp [Countable ι] [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Function.onFun Disjoint s))
    (hμ : μ (⋃ i, s i) ≠ ∞) (c : E) :
    HasSum (fun i ↦ indicatorConstLp p (hs i)
        (ne_top_of_le_ne_top hμ (measure_mono (Set.subset_iUnion s i))) c)
      (indicatorConstLp p (MeasurableSet.iUnion hs) hμ c) := by
  have hsum := fun t : Finset ι ↦ sum_indicatorConstLp t hs
    (fun i ↦ ne_top_of_le_ne_top hμ (measure_mono (Set.subset_iUnion s i)))
    (hd.set_pairwise (t : Set ι)) c (p := p)
  simp_rw [HasSum, hsum, SummationFilter.unconditional_filter]
  exact tendsto_indicatorConstLp_of_monotone hp
    (fun t : Finset ι ↦ t.measurableSet_biUnion fun i _ ↦ hs i)
    (fun t t' h ↦ Set.biUnion_subset_biUnion_left h) (Set.iUnion_eq_iUnion_finset s).symm c

end Countable

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

/-- On a set where `f` agrees almost everywhere with a constant `c`, the cut-off of `f` to the set
is the indicator class of `c` in `Lᵖ`. -/
theorem toLp_indicator_eq_indicatorConstLp {α E : Type*} {_ : MeasurableSpace α}
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} {f : α → E} (hf : MemLp f p μ)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {c : E}
    (hfc : f =ᵐ[μ.restrict s] fun _ ↦ c) :
    (hf.indicator hs.nullMeasurableSet).toLp (s.indicator f) = indicatorConstLp p hs hμs c :=
  Lp.ext <| (hf.indicator hs.nullMeasurableSet).coeFn_toLp.trans <|
    ((ae_eq_restrict_iff_indicator_ae_eq hs).1 hfc).trans indicatorConstLp_coeFn.symm

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
