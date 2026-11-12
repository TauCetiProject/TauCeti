/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Acceptance
public import TauCeti.Probability.PointProcess.Poisson.Count
public import TauCeti.Probability.PointProcess.Poisson.Independence
public import TauCeti.Probability.PointProcess.Poisson.IntegerValued
public import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Splitting two-colour temporal Poisson measures

For a Poisson random measure on `ℝ≥0 × Bool`, the two colour-count paths are independent
for the whole product sigma-algebra, not just at individual observation times. With locally
finite intensity, their sum agrees with the ground count simultaneously at every time.
All counts retain multiplicities and count `(0,t]`, excluding the origin.

Disjoint measurable mark families have mutually independent count paths. For product intensity
`r dt ⊗ Q` with s-finite `Q`, any measurable mark set of finite mass has independent increments
and Poisson increment laws of rate `r * Q A`. Bernoulli colour intensities give
the rates `p*r` and `(1-p)*r`, including `p = 0, 1` and zero ground rate. These statements start
from a coloured Poisson measure; they do not construct independent marks on a given uncoloured
realization.

The proofs consume the random-measure restriction, acceptance and count APIs. See G. Last
and M. Penrose, *Lectures on the Poisson Process* (2018), Chapters 5 and 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability.IsPoissonRandomMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Disjoint measurable mark families give mutually independent complete temporal count paths,
without product-intensity or local-finiteness assumptions. -/
theorem iIndepFun_nat_count_prod {E ι : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise fun i j ↦ Disjoint (A i) (A j)) :
    ProbabilityTheory.iIndepFun
      (fun i ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ A i)).toNNReal⌋₊) P := by
  let f (μ : Measure ℝ≥0) (t : ℝ≥0) := ⌊(μ (Ioc 0 t)).toNNReal⌋₊
  have hf : Measurable f := Measurable.of_eval fun t ↦
    (Measure.measurable_coe measurableSet_Ioc).ennreal_toNNReal.nat_floor
  simpa only [f, Function.comp_def, Measure.map_fst_restrict_univ_prod_apply _ _
    measurableSet_Ioc] using (h.iIndepFun_map_fst_restrict_prod hA hd).comp (fun _ ↦ f) (fun _ ↦ hf)

/-- A null mark region has identically zero count path on one full-measure event, including
all observation times simultaneously. No local finiteness is required. -/
theorem ae_nat_count_prod_eq_zero {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) {A : Set E} (hA : MeasurableSet A)
    (hΛ : Λ (univ ×ˢ A) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ = 0 := by
  have hz : ∀ᵐ ω ∂P, M ω (univ ×ˢ A) = 0 := by
    have hl := h.hasLaw (MeasurableSet.univ.prod hA) (by simp [hΛ])
    simp only [hΛ, ENNReal.toNNReal_zero, poissonMeasure_zero, Measure.map_dirac,
      Nat.cast_zero] at hl
    exact hl.ae_eq_of_dirac
  filter_upwards [hz] with ω hω t
  rw [measure_mono_null (prod_mono (subset_univ _) Subset.rfl) hω]
  simp

variable {M : Ω → Measure (ℝ≥0 × Bool)} {Λ : Measure (ℝ≥0 × Bool)}

/-- The complete paths of the two colour counts are independent, even for intensities
that are not product measures or locally finite. -/
theorem indepFun_nat_count_colors (h : IsPoissonRandomMeasure P M Λ) :
    IndepFun (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
      (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P := by
  exact (h.iIndepFun_nat_count_prod (A := fun b : Bool ↦ {b}) (by measurability)
    (by intro i j hij; simpa using hij)).indepFun (i := true) (j := false) (by decide)

/-- Each coordinate of a colour count path is measurable, for arbitrary intensity. -/
theorem measurable_nat_count_color (h : IsPoissonRandomMeasure P M Λ) (b : Bool) (t : ℝ≥0) :
    Measurable (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) :=
  ((Measure.measurable_coe (measurableSet_Ioc.prod (measurableSet_singleton b))).comp
    h.measurable).ennreal_toNNReal.nat_floor

/-- Colour count paths are monotone on one full-measure event when the intensity is locally
finite. -/
theorem ae_monotone_nat_count_color [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) (b : Bool) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) := by
  let := (Λ.restrict (univ ×ˢ {b})).isLocallyFiniteMeasure_map_fst
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    ((h.restrict (s := univ ×ˢ {b}) (by measurability)).map measurable_fst).ae_monotone_nat_count

/-- A colour count on a right-closed interval has Poisson law with its interval intensity,
including empty intervals. -/
theorem hasLaw_nat_count_color_Ioc [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) (b : Bool) (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ {b})).toNNReal) P := by
  let := (Λ.restrict (univ ×ˢ {b})).isLocallyFiniteMeasure_map_fst
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    ((h.restrict (s := univ ×ˢ {b}) (by measurability)).map measurable_fst).hasLaw_nat_count_Ioc s t

/-- The colour counts add to the ground count on a single full-measure event. This is a
simultaneous identity in time, rather than a separate almost-sure statement for each time. -/
theorem ae_nat_count_eq_add_colors [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ univ)).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
          ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ := by
  filter_upwards [h.ae_isIntegerValued, h.ae_isLocallyFiniteMeasure] with ω hi hf t
  let := hf
  have hfin (b : Bool) : M ω (Ioc 0 t ×ˢ {b}) < ∞ :=
    (measure_mono (prod_mono Ioc_subset_Icc_self (subset_univ _))).trans_lt
      ((isCompact_Icc.prod isCompact_univ).measure_lt_top)
  obtain ⟨a, ha⟩ := hi.exists_eq_natCast (measurableSet_Ioc.prod (measurableSet_singleton true))
    (hfin true)
  obtain ⟨b, hb⟩ := hi.exists_eq_natCast (measurableSet_Ioc.prod (measurableSet_singleton false))
    (hfin false)
  have hunion : (Ioc 0 t ×ˢ {true}) ∪ (Ioc 0 t ×ˢ {false}) =
      Ioc 0 t ×ˢ (univ : Set Bool) := by
    ext ⟨s, c⟩
    cases c <;> simp
  have hadd := measure_union (μ := M ω) (s₁ := Ioc 0 t ×ˢ {true})
    (s₂ := Ioc 0 t ×ˢ {false}) (by simp [disjoint_left])
    (measurableSet_Ioc.prod (measurableSet_singleton false))
  rw [hunion, ha, hb, ← Nat.cast_add] at hadd
  rw [hadd, ha, hb]
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast]

/-- Colour counts have independent increments for any locally finite intensity, without
requiring product structure or homogeneity. -/
theorem hasIndepIncrements_nat_count_color [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) (b : Bool) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) P := by
  let := (Λ.restrict (univ ×ˢ {b})).isLocallyFiniteMeasure_map_fst
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    ((h.restrict (s := univ ×ˢ {b}) (by measurability)).map
      measurable_fst).hasIndepIncrements_nat_count

/-- A colour-count increment has Poisson law with parameter equal to its interval intensity,
for any locally finite intensity. -/
theorem hasLaw_nat_count_color_sub [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ {b})).toNNReal) P := by
  let := (Λ.restrict (univ ×ˢ {b})).isLocallyFiniteMeasure_map_fst
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    ((h.restrict (s := univ ×ˢ {b}) (by measurability)).map measurable_fst).hasLaw_nat_count_sub hst

/-- Selecting a finite-mass mark set preserves independent temporal count increments for an
arbitrary locally finite ground intensity and s-finite mark measure. -/
theorem hasIndepIncrements_nat_count_prod {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) P := by
  let := ν.isLocallyFiniteMeasure_smul hQA
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    (h.acceptance_prod hA).hasIndepIncrements_nat_count

/-- For locally finite ground intensity, a finite-mass mark-count increment has Poisson law
with parameter equal to the ground interval intensity times the mark mass. -/
theorem hasLaw_nat_count_prod_sub {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) {s t : ℝ≥0} (hst : s ≤ t)
    (hQA : Q A ≠ ∞ := by finiteness) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure (ν.prod Q (Ioc s t ×ˢ A)).toNNReal) P := by
  let := ν.isLocallyFiniteMeasure_smul hQA
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc,
    smul_apply, smul_eq_mul, Measure.prod_prod, mul_comm] using
    (h.acceptance_prod hA).hasLaw_nat_count_sub hst

/-- A finite-mass mark selection from homogeneous product intensity is itself a Poisson
random measure, of rate `r * Q A`, including rate zero. -/
theorem acceptance_prod_smul_nnvolume {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Q : Measure E} [SFinite Q] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • nnvolume).prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ A)).map Prod.fst)
      (((r * (Q A).toNNReal : ℝ≥0) : ℝ≥0∞) • nnvolume) := by
  have hrate : Q A • (r : ℝ≥0∞) • nnvolume =
      ((r * (Q A).toNNReal : ℝ≥0) : ℝ≥0∞) • nnvolume := by
    rw [smul_smul, ENNReal.coe_mul, ENNReal.coe_toNNReal hQA, mul_comm]
  simpa only [hrate] using h.acceptance_prod hA

/-- A finite-mass mark-count increment has rate `r * Q A` under homogeneous product intensity.
Zero mark mass, zero ground rate and equal observation endpoints are allowed. -/
theorem hasLaw_nat_count_prod_sub_smul_nnvolume {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Q : Measure E} [SFinite Q] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • nnvolume).prod Q))
    {A : Set E} (hA : MeasurableSet A) {s t : ℝ≥0} (hst : s ≤ t)
    (hQA : Q A ≠ ∞ := by finiteness) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure ((r * (Q A).toNNReal) * (t - s))) P := by
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    (h.acceptance_prod_smul_nnvolume hA hQA).hasLaw_nat_count_sub_smul_nnvolume hst

/-- A zero-rate mark selection is the identically zero count path on a single event of full
probability. This covers zero ground rate and zero mark mass. -/
theorem ae_nat_count_prod_eq_zero_of_rate_eq_zero {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Q : Measure E} [SFinite Q] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • nnvolume).prod Q))
    {A : Set E} (hA : MeasurableSet A) (hzero : r * (Q A).toNNReal = 0)
    (hQA : Q A ≠ ∞ := by finiteness) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ = 0 := by
  apply h.ae_nat_count_prod_eq_zero hA
  have hr : (r : ℝ≥0∞) * Q A = 0 := by
    rw [← ENNReal.coe_toNNReal hQA, ← ENNReal.coe_mul, hzero, ENNReal.coe_zero]
  rw [Measure.prod_prod, smul_apply, smul_eq_mul, mul_right_comm, hr, zero_mul]

variable {r : ℝ≥0}

/-- Bernoulli colour intensities give Poisson colour projections of rates `r*p` and `r*(1-p)`,
including both endpoint parameters and zero ground rate. -/
theorem acceptance_prod_smul_nnvolume_bernoulliMeasure {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • nnvolume).prod (bernoulliMeasure true false p))) (b : Bool) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ {b})).map Prod.fst)
      (((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • nnvolume) := by
  have hb : ((bernoulliMeasure true false p) {b}).toNNReal =
      if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p := by
    cases b
    · simpa using eq_tsub_of_add_eq (unitInterval.toNNReal_symm_add_toNNReal p)
    · simp
  simpa only [hb] using h.acceptance_prod_smul_nnvolume (measurableSet_singleton b)

/-- Bernoulli colour intensities split the temporal rate into `r*p` and `r*(1-p)`.
The endpoint parameters produce a zero-rate colour, without any positive-rate assumption. -/
theorem hasLaw_nat_count_color_sub_of_bernoulliMeasure
    {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • nnvolume).prod (bernoulliMeasure true false p)))
    (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure ((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p) * (t - s))) P := by
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    (h.acceptance_prod_smul_nnvolume_bernoulliMeasure b).hasLaw_nat_count_sub_smul_nnvolume hst

end TauCeti.Probability.IsPoissonRandomMeasure
