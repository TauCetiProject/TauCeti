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
import Mathlib.MeasureTheory.Function.Floor

/-!
# Splitting marked temporal Poisson measures

Disjoint measurable mark families of a Poisson random measure on `ℝ≥0 × E` have independent
count paths for the whole product sigma-algebra, not just at individual observation times.
Finite intensity on each selected positive-time window `Ioc 0 t ×ˢ A` gives monotonicity,
independent increments, interval laws and simultaneous additivity for finite disjoint families,
without product structure. Singleton selections need only intensity finite on compact sets.
Cumulative counts retain multiplicities and count `(0,t]`, excluding the origin; interval
counts use `(s,t]`.

For product intensity `ν.prod Q` with locally finite `ν`, finite-mass measurable mark selections
have independent increments and simultaneous monotonicity and additivity. If `Q` is s-finite,
their Poisson parameters are ground interval intensity times mark mass. Homogeneous intensity
`r dt ⊗ Q` gives rate `r * Q A`. Bernoulli mark intensities give rates `p*r` and `(1-p)*r`,
including `p = 0, 1` and zero ground rate. These statements start from a marked Poisson measure;
they do not construct independent marks on a given uncoloured realization.

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
  simpa only [f, Function.comp_def, Measure.map_fst_restrict_prod_apply _ _ _
    measurableSet_Ioc, inter_univ] using
    (h.iIndepFun_map_fst_restrict_univ_prod hA hd).comp (fun _ ↦ f) (fun _ ↦ hf)

/-- Two disjoint measurable mark sets give independent complete temporal count paths,
without product-intensity or local-finiteness assumptions. -/
theorem indepFun_nat_count_prod {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) {A B : Set E}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B) :
    IndepFun (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊)
      (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊) P := by
  let f (μ : Measure ℝ≥0) (t : ℝ≥0) := ⌊(μ (Ioc 0 t)).toNNReal⌋₊
  have hf : Measurable f := Measurable.of_eval fun t ↦
    (Measure.measurable_coe measurableSet_Ioc).ennreal_toNNReal.nat_floor
  simpa only [f, Function.comp_def, Measure.map_fst_restrict_prod_apply _ _ _
    measurableSet_Ioc, inter_univ] using
    (h.indepFun_map_fst_restrict_univ_prod hA hB hd).comp hf hf

/-- A null mark region has identically zero count path on one full-measure event, including
all observation times simultaneously. No local finiteness is required. -/
theorem ae_nat_count_prod_eq_zero {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) {A : Set E}
    (hΛ : Λ (Ioi 0 ×ˢ A) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ = 0 := by
  obtain ⟨B, hAB, hBm, hΛB⟩ := exists_measurable_superset_of_null hΛ
  have hz : ∀ᵐ ω ∂P, M ω (Ioi 0 ×ˢ A) = 0 := by
    have hl := h.hasLaw hBm (by simp [hΛB])
    simp only [hΛB, ENNReal.toNNReal_zero, poissonMeasure_zero, Measure.map_dirac,
      Nat.cast_zero] at hl
    filter_upwards [hl.ae_eq_of_dirac] with ω hω
    exact measure_mono_null hAB hω
  filter_upwards [hz] with ω hω t
  rw [measure_mono_null (prod_mono Ioc_subset_Ioi_self Subset.rfl) hω]
  simp

/-- Every coordinate of a measurable mark-selection count path is measurable, without
finiteness or product-intensity assumptions. -/
theorem measurable_nat_count_prod {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) {A : Set E} (hA : MeasurableSet A) (t : ℝ≥0) :
    Measurable (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) :=
  ((Measure.measurable_coe (measurableSet_Ioc.prod hA)).comp
    h.measurable).ennreal_toNNReal.nat_floor

section MarkSelection

variable {E : Type*} [MeasurableSpace E]
  {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}

/-- A selected count path is simultaneously monotone if the selected intensity is finite
on each bounded positive-time window. The intensity need not be a product. -/
theorem ae_monotone_nat_count_prod_of_measure_Ioc_prod_lt_top
    (h : IsPoissonRandomMeasure P M Λ) {A : Set E} (hA : MeasurableSet A)
    (hfin : ∀ t : ℝ≥0, Λ (Ioc 0 t ×ˢ A) < ∞) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) := by
  let := Λ.isLocallyFiniteMeasure_map_fst_restrict_Ioi_prod 0 A hfin
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self] using
    ((h.restrict (s := Ioi 0 ×ˢ A)
      (measurableSet_Ioi.prod hA)).map measurable_fst).ae_monotone_nat_count

/-- A selected interval count has Poisson law if that interval has finite intensity,
including empty intervals and nonproduct intensities. -/
theorem hasLaw_nat_count_prod_Ioc_of_lt_top
    (h : IsPoissonRandomMeasure P M Λ) {A : Set E} (hA : MeasurableSet A)
    (s t : ℝ≥0) (hfin : Λ (Ioc s t ×ˢ A) < ∞) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ A)).toNNReal) P :=
  h.hasLaw_natFloor (measurableSet_Ioc.prod hA) hfin

/-- Selected counts have independent increments whenever the selected intensity is finite
on bounded positive-time windows, without product structure or a topology on the mark space. -/
theorem hasIndepIncrements_nat_count_prod_of_measure_Ioc_prod_lt_top
    (h : IsPoissonRandomMeasure P M Λ) {A : Set E} (hA : MeasurableSet A)
    (hfin : ∀ t : ℝ≥0, Λ (Ioc 0 t ×ˢ A) < ∞) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) P := by
  let := Λ.isLocallyFiniteMeasure_map_fst_restrict_Ioi_prod 0 A hfin
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self] using
    ((h.restrict (s := Ioi 0 ×ˢ A)
      (measurableSet_Ioi.prod hA)).map measurable_fst).hasIndepIncrements_nat_count

/-- A selected count increment has the Poisson law of its interval intensity if the selected
positive-time window up to the later endpoint has finite intensity. -/
theorem hasLaw_nat_count_prod_sub_of_measure_Ioc_prod_lt_top
    (h : IsPoissonRandomMeasure P M Λ) {A : Set E} (hA : MeasurableSet A)
    {s t : ℝ≥0} (hst : s ≤ t) (hfin : Λ (Ioc 0 t ×ˢ A) < ∞) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ A)).toNNReal) P := by
  have hsfin := (measure_mono (prod_mono (Ioc_subset_Ioc_right hst) Subset.rfl)).trans_lt hfin
  have hstfin : Λ (Ioc s t ×ˢ A) < ∞ :=
    (measure_mono (prod_mono (Ioc_subset_Ioc_left bot_le) Subset.rfl)).trans_lt hfin
  apply (h.hasLaw_nat_count_prod_Ioc_of_lt_top hA s t hstfin).congr
  filter_upwards [h.ae_natCast_natFloor_eq (measurableSet_Ioc.prod hA) hsfin,
    h.ae_natCast_natFloor_eq (measurableSet_Ioc.prod hA) hstfin] with ω hs ht
  have hadd := measure_union (μ := M ω) (s₁ := Ioc 0 s ×ˢ A) (s₂ := Ioc s t ×ˢ A)
    ((Ioc_disjoint_Ioc_of_le (le_refl s)).set_prod_left _ _) (measurableSet_Ioc.prod hA)
  rw [← union_prod, Ioc_union_Ioc_eq_Ioc (a := 0) bot_le hst,
    ← hs, ← ht, ← Nat.cast_add] at hadd
  rw [hadd]
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast, Nat.add_sub_cancel_left]

private theorem ae_nat_count_prod_cast (h : IsPoissonRandomMeasure P M Λ)
    {A : Set E} (hA : MeasurableSet A) (hfin : ∀ t : ℝ≥0, Λ (Ioc 0 t ×ˢ A) < ∞) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ : ℝ≥0∞) = M ω (Ioc 0 t ×ˢ A) := by
  let := Λ.isLocallyFiniteMeasure_map_fst_restrict_Ioi_prod 0 A hfin
  have hP := (h.restrict (s := Ioi 0 ×ˢ A) (measurableSet_Ioi.prod hA)).map measurable_fst
  filter_upwards [hP.ae_isIntegerValued, hP.ae_isLocallyFiniteMeasure] with ω hi hf t
  let := hf
  obtain ⟨n, hn⟩ := hi.exists_eq_natCast measurableSet_Ioc
    (measure_Ioc_lt_top (a := 0) (b := t))
  simp only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self] at hn
  simp [hn]

/-- Counts on a finite disjoint family of measurable mark sets add simultaneously at every
time if each selection has finite intensity on bounded positive-time windows. -/
theorem ae_nat_count_prod_biUnion_finset_eq_sum_of_measure_Ioc_prod_lt_top {ι : Type*}
    (h : IsPoissonRandomMeasure P M Λ) {s : Finset ι} {A : ι → Set E}
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hd : (↑s : Set ι).PairwiseDisjoint A)
    (hfin : ∀ i ∈ s, ∀ t : ℝ≥0, Λ (Ioc 0 t ×ˢ A i) < ∞) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ (⋃ i ∈ s, A i))).toNNReal⌋₊ =
        ∑ i ∈ s, ⌊(M ω (Ioc 0 t ×ˢ A i)).toNNReal⌋₊ := by
  filter_upwards [(ae_ball_iff s.countable_toSet).2
    (fun i hi ↦ h.ae_nat_count_prod_cast (hA i hi) (hfin i hi))] with ω hω t
  have hadd := measure_biUnion_finset (μ := M ω)
    (f := fun i ↦ Ioc 0 t ×ˢ A i)
    (fun i hi j hj hij ↦ (hd hi hj hij).set_prod_right _ _)
    (fun i hi ↦ measurableSet_Ioc.prod (hA i hi))
  simp only [← prod_iUnion] at hadd
  rw [hadd, ← Finset.sum_congr rfl (fun i hi ↦ hω i hi t),
    ← Nat.cast_sum (R := ℝ≥0∞)]
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast]

/-- Counts on two disjoint measurable mark sets add simultaneously at every time if each
selection has finite intensity on bounded positive-time windows. -/
theorem ae_nat_count_prod_union_eq_add_of_measure_Ioc_prod_lt_top
    (h : IsPoissonRandomMeasure P M Λ) {A B : Set E}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hfinA : ∀ t : ℝ≥0, Λ (Ioc 0 t ×ˢ A) < ∞)
    (hfinB : ∀ t : ℝ≥0, Λ (Ioc 0 t ×ˢ B) < ∞) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ (A ∪ B))).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ + ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ := by
  have hd' : (univ : Set Bool).PairwiseDisjoint (fun b ↦ if b then A else B) := by
    intro i _ j _ hij
    cases i <;> cases j <;> simp_all [Disjoint.symm]
  have hunion : (⋃ b : Bool, if b then A else B) = A ∪ B := by
    ext x
    simp [Bool.exists_bool, or_comm]
  simpa [hunion, Fintype.sum_bool] using
    h.ae_nat_count_prod_biUnion_finset_eq_sum_of_measure_Ioc_prod_lt_top
      (s := Finset.univ) (A := fun b : Bool ↦ if b then A else B)
      (by intro b _; cases b <;> assumption) (by simpa only [Finset.coe_univ] using hd')
      (by intro b _; cases b <;> assumption)

end MarkSelection

/-- All singleton-mark count paths are mutually independent, without finiteness assumptions. -/
theorem iIndepFun_nat_count_prod_singleton {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) :
    ProbabilityTheory.iIndepFun
      (fun b ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) P :=
  h.iIndepFun_nat_count_prod measurableSet_singleton (by simp [Pairwise])

/-- Distinct singleton marks give independent complete count paths for arbitrary intensity. -/
theorem indepFun_nat_count_prod_singleton {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) {a b : E} (hab : a ≠ b) :
    IndepFun (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {a})).toNNReal⌋₊)
      (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) P :=
  h.iIndepFun_nat_count_prod_singleton.indepFun hab

/-- For a finite mark space, singleton counts sum to the ground count simultaneously in time
when the intensity is finite on compact sets. -/
theorem ae_nat_count_prod_univ_eq_sum {E : Type*} [Fintype E] [TopologicalSpace E]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)} [IsFiniteMeasureOnCompacts Λ]
    (h : IsPoissonRandomMeasure P M Λ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ univ)).toNNReal⌋₊ =
        ∑ b : E, ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ := by
  simpa only [Finset.mem_univ, iUnion_true, iUnion_of_singleton] using
    h.ae_nat_count_prod_biUnion_finset_eq_sum_of_measure_Ioc_prod_lt_top
      (s := Finset.univ) (A := fun b : E ↦ {b}) (fun b _ ↦ measurableSet_singleton b)
      (by intro i _ j _ hij; exact disjoint_singleton.mpr hij)
      (fun b _ t ↦ Λ.measure_Ioc_prod_singleton_lt_top b 0 t)

variable {M : Ω → Measure (ℝ≥0 × Bool)} {Λ : Measure (ℝ≥0 × Bool)}

/-- The complete paths of the two colour counts are independent, even for intensities
that are not product measures or locally finite. -/
theorem indepFun_nat_count_prod_singleton_bool (h : IsPoissonRandomMeasure P M Λ) :
    IndepFun (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
      (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P := by
  exact h.indepFun_nat_count_prod_singleton (by decide)

/-- Each coordinate of a colour count path is measurable, for arbitrary intensity. -/
theorem measurable_nat_count_prod_singleton {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) (b : E) (t : ℝ≥0) :
    Measurable (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) :=
  h.measurable_nat_count_prod (measurableSet_singleton b) t

/-- A singleton-mark count path is monotone on a full-measure event when the intensity is
finite on compact sets. -/
theorem ae_monotone_nat_count_prod_singleton {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) := by
  exact h.ae_monotone_nat_count_prod_of_measure_Ioc_prod_lt_top (measurableSet_singleton b)
    (Λ.measure_Ioc_prod_singleton_lt_top b 0)

/-- A colour count on a right-closed interval has Poisson law with its interval intensity,
including empty intervals. -/
theorem hasLaw_nat_count_prod_singleton_Ioc {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E) (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ {b})).toNNReal) P := by
  exact h.hasLaw_nat_count_prod_Ioc_of_lt_top (measurableSet_singleton b) s t
    (Λ.measure_Ioc_prod_singleton_lt_top b s t)

/-- The colour counts add to the ground count on a single full-measure event. This is a
simultaneous identity in time, rather than a separate almost-sure statement for each time. -/
theorem ae_nat_count_prod_univ_eq_add_bool [IsFiniteMeasureOnCompacts Λ]
    (h : IsPoissonRandomMeasure P M Λ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ univ)).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
          ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ := by
  simpa only [Fintype.sum_bool] using h.ae_nat_count_prod_univ_eq_sum

/-- Singleton-mark counts have independent increments for any intensity finite on compact
sets, without requiring product structure or homogeneity. -/
theorem hasIndepIncrements_nat_count_prod_singleton {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) P := by
  exact h.hasIndepIncrements_nat_count_prod_of_measure_Ioc_prod_lt_top (measurableSet_singleton b)
    (Λ.measure_Ioc_prod_singleton_lt_top b 0)

/-- A singleton-mark count increment has Poisson law with parameter equal to its interval
intensity, for any intensity finite on compact sets. -/
theorem hasLaw_nat_count_prod_singleton_sub {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ {b})).toNNReal) P := by
  exact h.hasLaw_nat_count_prod_sub_of_measure_Ioc_prod_lt_top (measurableSet_singleton b) hst
    (Λ.measure_Ioc_prod_singleton_lt_top b 0 t)

/-- Selecting a finite-mass mark set preserves independent temporal count increments for an
arbitrary locally finite ground intensity and any mark measure. -/
theorem hasIndepIncrements_nat_count_prod {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) P := by
  exact h.hasIndepIncrements_nat_count_prod_of_measure_Ioc_prod_lt_top hA
    (ν.measure_Ioc_prod_lt_top Q hQA 0)

/-- For locally finite ground intensity, a finite-mass mark-count increment has Poisson law
with parameter equal to the ground interval intensity times the mark mass. -/
theorem hasLaw_nat_count_prod_sub {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) {s t : ℝ≥0} (hst : s ≤ t)
    (hQA : Q A ≠ ∞ := by finiteness) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure ((ν (Ioc s t)).toNNReal * (Q A).toNNReal)) P := by
  simpa only [Measure.prod_prod, ENNReal.toNNReal_mul] using
    h.hasLaw_nat_count_prod_sub_of_measure_Ioc_prod_lt_top hA hst
      (ν.measure_Ioc_prod_lt_top Q hQA 0 t)

/-- A finite-mass mark-selection path is simultaneously monotone in time for locally finite
ground intensity and any mark measure. -/
theorem ae_monotone_nat_count_prod {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) := by
  exact h.ae_monotone_nat_count_prod_of_measure_Ioc_prod_lt_top hA
    (ν.measure_Ioc_prod_lt_top Q hQA 0)

/-- A finite-mass selected interval count has Poisson parameter equal to the ground interval
intensity times the mark mass, including empty intervals. -/
theorem hasLaw_nat_count_prod_Ioc {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) (s t : ℝ≥0) (hQA : Q A ≠ ∞ := by finiteness) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure ((ν (Ioc s t)).toNNReal * (Q A).toNNReal)) P := by
  simpa only [Measure.prod_prod, ENNReal.toNNReal_mul] using
    h.hasLaw_nat_count_prod_Ioc_of_lt_top hA s t (ν.measure_Ioc_prod_lt_top Q hQA s t)

/-- Counts on a finite disjoint family of finite-mass mark sets add simultaneously in time
for locally finite ground intensity and any mark measure. -/
theorem ae_nat_count_prod_biUnion_finset_eq_sum {E ι : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {s : Finset ι} {A : ι → Set E} (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (↑s : Set ι).PairwiseDisjoint A) (hQA : ∀ i ∈ s, Q (A i) ≠ ∞ := by finiteness) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ (⋃ i ∈ s, A i))).toNNReal⌋₊ =
        ∑ i ∈ s, ⌊(M ω (Ioc 0 t ×ˢ A i)).toNNReal⌋₊ :=
  h.ae_nat_count_prod_biUnion_finset_eq_sum_of_measure_Ioc_prod_lt_top hA hd
    (fun i hi ↦ ν.measure_Ioc_prod_lt_top Q (hQA i hi) 0)

/-- Counts on two disjoint finite-mass mark sets add simultaneously at every time for
locally finite ground intensity and any mark measure. -/
theorem ae_nat_count_prod_union_eq_add {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hQA : Q A ≠ ∞ := by finiteness) (hQB : Q B ≠ ∞ := by finiteness) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ (A ∪ B))).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ + ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ := by
  exact h.ae_nat_count_prod_union_eq_add_of_measure_Ioc_prod_lt_top hA hB hd
    (ν.measure_Ioc_prod_lt_top Q hQA 0) (ν.measure_Ioc_prod_lt_top Q hQB 0)

/-- Under homogeneous product intensity, a selected interval count has parameter
`r * Q A` times elapsed time, including zero rates and empty intervals. -/
theorem hasLaw_nat_count_prod_Ioc_smul_nnvolume {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Q : Measure E} [SFinite Q] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • nnvolume).prod Q))
    {A : Set E} (hA : MeasurableSet A) (s t : ℝ≥0) (hQA : Q A ≠ ∞ := by finiteness) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure ((r * (Q A).toNNReal) * (t - s))) P := by
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ] using
    (h.acceptance_univ_prod_smul hA hQA).hasLaw_nat_count_Ioc_smul_nnvolume s t

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
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ] using
    (h.acceptance_univ_prod_smul hA hQA).hasLaw_nat_count_sub_smul_nnvolume hst

/-- A product-intensity selection with zero mass on positive times has identically zero
count path on a single full-measure event, without finiteness assumptions. -/
theorem ae_nat_count_prod_eq_zero_of_mul_eq_zero {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} {Q : Measure E}
    (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hzero : ν (Ioi 0) * Q A = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ = 0 := by
  exact h.ae_nat_count_prod_eq_zero (le_antisymm
    ((Measure.prod_prod_le ν Q _ _).trans_eq hzero) bot_le)

/-- A zero-rate mark selection is the identically zero count path on a single event of full
probability. This covers zero ground scale and zero mark mass, including infinite scales. -/
theorem ae_nat_count_prod_eq_zero_of_smul_prod_of_mul_eq_zero {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} {Q : Measure E} {r : ℝ≥0∞}
    (h : IsPoissonRandomMeasure P M ((r • ν).prod Q))
    {A : Set E} (hzero : r * Q A = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ = 0 := by
  apply h.ae_nat_count_prod_eq_zero_of_mul_eq_zero
  rw [smul_apply, smul_eq_mul, mul_right_comm, hzero, zero_mul]

variable {r : ℝ≥0}

/-- Bernoulli colour interval counts have parameters `r*p` and `r*(1-p)` times elapsed
time, including endpoint parameters, zero ground rate, and empty intervals. -/
theorem hasLaw_nat_count_prod_singleton_Ioc_of_bernoulliMeasure {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • nnvolume).prod (bernoulliMeasure true false p)))
    (b : Bool) (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure ((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p) * (t - s))) P := by
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ] using
    (h.acceptance_univ_prod_singleton_smul_of_bernoulliMeasure b).hasLaw_nat_count_Ioc_smul_nnvolume
      s t

/-- Bernoulli colour intensities split the temporal rate into `r*p` and `r*(1-p)`.
The endpoint parameters produce a zero-rate colour, without any positive-rate assumption. -/
theorem hasLaw_nat_count_prod_singleton_sub_of_bernoulliMeasure
    {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • nnvolume).prod (bernoulliMeasure true false p)))
    (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure ((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p) * (t - s))) P := by
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ] using
    (h.acceptance_univ_prod_singleton_smul_of_bernoulliMeasure b).hasLaw_nat_count_sub_smul_nnvolume
      hst

end TauCeti.Probability.IsPoissonRandomMeasure
