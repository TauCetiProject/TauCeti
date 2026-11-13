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
    measurableSet_Ioc] using
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
  simpa only [f, Function.comp_def, Measure.map_fst_restrict_univ_prod_apply _ _
    measurableSet_Ioc] using
    (h.indepFun_map_fst_restrict_univ_prod hA hB hd).comp hf hf

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
  (h : IsPoissonRandomMeasure P M Λ) {A : Set E} (hA : MeasurableSet A)
  (hfin : ∀ t : ℝ≥0, Λ (Iic t ×ˢ A) < ∞)

include h hA hfin

/-- A selected count path is simultaneously monotone if the selected intensity is finite
on each bounded initial interval. The intensity need not be a product. -/
theorem ae_monotone_nat_count_prod_of_measure_Iic_prod_lt_top :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) := by
  let := ((Λ.restrict (univ ×ˢ A)).map Prod.fst).isLocallyFiniteMeasure_of_measure_Iic_lt_top
    (by simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Iic] using hfin)
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    ((h.restrict (MeasurableSet.univ.prod hA)).map measurable_fst).ae_monotone_nat_count

/-- A selected interval count has Poisson law under finite bounded-window intensity,
including empty intervals and nonproduct intensities. -/
theorem hasLaw_nat_count_prod_Ioc_of_measure_Iic_prod_lt_top (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ A)).toNNReal) P :=
  h.hasLaw_natFloor (measurableSet_Ioc.prod hA)
    ((measure_mono (prod_mono Ioc_subset_Iic_self Subset.rfl)).trans_lt (hfin t))

/-- Selected counts have independent increments whenever the selected intensity is finite
on bounded initial intervals, without product structure or a topology on the mark space. -/
theorem hasIndepIncrements_nat_count_prod_of_measure_Iic_prod_lt_top :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) P := by
  let := ((Λ.restrict (univ ×ˢ A)).map Prod.fst).isLocallyFiniteMeasure_of_measure_Iic_lt_top
    (by simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Iic] using hfin)
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    ((h.restrict (MeasurableSet.univ.prod hA)).map measurable_fst).hasIndepIncrements_nat_count

/-- A selected count increment has the Poisson law of its interval intensity when selected
bounded windows have finite intensity. -/
theorem hasLaw_nat_count_prod_sub_of_measure_Iic_prod_lt_top {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ A)).toNNReal) P := by
  let := ((Λ.restrict (univ ×ˢ A)).map Prod.fst).isLocallyFiniteMeasure_of_measure_Iic_lt_top
    (by simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Iic] using hfin)
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    ((h.restrict (MeasurableSet.univ.prod hA)).map measurable_fst).hasLaw_nat_count_sub hst

omit hA hfin in
/-- Counts on two disjoint measurable mark sets add simultaneously at every time if each
selection has finite intensity on bounded initial intervals. -/
theorem ae_nat_count_prod_union_eq_add_of_measure_Iic_prod_lt_top {B : Set E}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hfinA : ∀ t : ℝ≥0, Λ (Iic t ×ˢ A) < ∞)
    (hfinB : ∀ t : ℝ≥0, Λ (Iic t ×ˢ B) < ∞) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ (A ∪ B))).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ + ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ := by
  let := ((Λ.restrict (univ ×ˢ A)).map Prod.fst).isLocallyFiniteMeasure_of_measure_Iic_lt_top
    (by simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Iic] using hfinA)
  let := ((Λ.restrict (univ ×ˢ B)).map Prod.fst).isLocallyFiniteMeasure_of_measure_Iic_lt_top
    (by simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Iic] using hfinB)
  have hPA := (h.restrict (MeasurableSet.univ.prod hA)).map measurable_fst
  have hPB := (h.restrict (MeasurableSet.univ.prod hB)).map measurable_fst
  filter_upwards [hPA.ae_isIntegerValued, hPA.ae_isLocallyFiniteMeasure,
    hPB.ae_isIntegerValued, hPB.ae_isLocallyFiniteMeasure] with ω hiA hfA hiB hfB t
  let := hfA
  let := hfB
  have hcountA := hiA.exists_eq_natCast measurableSet_Ioc
    (measure_Ioc_lt_top (a := 0) (b := t))
  have hcountB := hiB.exists_eq_natCast measurableSet_Ioc
    (measure_Ioc_lt_top (a := 0) (b := t))
  simp only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] at hcountA hcountB
  obtain ⟨a, ha⟩ := hcountA
  obtain ⟨b, hb⟩ := hcountB
  have hadd := measure_union (μ := M ω) (s₁ := Ioc 0 t ×ˢ A) (s₂ := Ioc 0 t ×ˢ B)
    (hd.set_prod_right _ _) (measurableSet_Ioc.prod hB)
  rw [← prod_union, ha, hb, ← Nat.cast_add] at hadd
  rw [hadd, ha, hb]
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast]

end MarkSelection

variable {M : Ω → Measure (ℝ≥0 × Bool)} {Λ : Measure (ℝ≥0 × Bool)}

/-- The complete paths of the two colour counts are independent, even for intensities
that are not product measures or locally finite. -/
theorem indepFun_nat_count_colors (h : IsPoissonRandomMeasure P M Λ) :
    IndepFun (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
      (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P := by
  exact h.indepFun_nat_count_prod (measurableSet_singleton true)
    (measurableSet_singleton false) (by simp)

/-- Each coordinate of a colour count path is measurable, for arbitrary intensity. -/
theorem measurable_nat_count_color {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    (h : IsPoissonRandomMeasure P M Λ) (b : E) (t : ℝ≥0) :
    Measurable (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) :=
  h.measurable_nat_count_prod (measurableSet_singleton b) t

/-- Colour count paths are monotone on one full-measure event when the intensity is locally
finite. -/
theorem ae_monotone_nat_count_color {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsLocallyFiniteMeasure Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) := by
  exact h.ae_monotone_nat_count_prod_of_measure_Iic_prod_lt_top (measurableSet_singleton b)
    (fun t ↦ by simpa only [Icc_bot] using
      ((isCompact_Icc (a := (⊥ : ℝ≥0)) (b := t)).prod
        (isCompact_singleton (x := b))).measure_lt_top)

/-- A colour count on a right-closed interval has Poisson law with its interval intensity,
including empty intervals. -/
theorem hasLaw_nat_count_color_Ioc {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsLocallyFiniteMeasure Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E) (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ {b})).toNNReal) P := by
  exact h.hasLaw_nat_count_prod_Ioc_of_measure_Iic_prod_lt_top (measurableSet_singleton b)
    (fun u ↦ by simpa only [Icc_bot] using
      ((isCompact_Icc (a := (⊥ : ℝ≥0)) (b := u)).prod
        (isCompact_singleton (x := b))).measure_lt_top) s t

/-- The colour counts add to the ground count on a single full-measure event. This is a
simultaneous identity in time, rather than a separate almost-sure statement for each time. -/
theorem ae_nat_count_eq_add_colors [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P M Λ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ univ)).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
          ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ := by
  have hunion : ({true} : Set Bool) ∪ {false} = univ := by
    ext b
    cases b <;> simp
  simpa only [hunion] using h.ae_nat_count_prod_union_eq_add_of_measure_Iic_prod_lt_top
    (measurableSet_singleton true) (measurableSet_singleton false) (by simp)
    (fun t ↦ by simpa only [Icc_bot] using
      ((isCompact_Icc (a := (⊥ : ℝ≥0)) (b := t)).prod
        (isCompact_singleton (x := true))).measure_lt_top)
    (fun t ↦ by simpa only [Icc_bot] using
      ((isCompact_Icc (a := (⊥ : ℝ≥0)) (b := t)).prod
        (isCompact_singleton (x := false))).measure_lt_top)

/-- Colour counts have independent increments for any locally finite intensity, without
requiring product structure or homogeneity. -/
theorem hasIndepIncrements_nat_count_color {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsLocallyFiniteMeasure Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) P := by
  exact h.hasIndepIncrements_nat_count_prod_of_measure_Iic_prod_lt_top (measurableSet_singleton b)
    (fun t ↦ by simpa only [Icc_bot] using
      ((isCompact_Icc (a := (⊥ : ℝ≥0)) (b := t)).prod
        (isCompact_singleton (x := b))).measure_lt_top)

/-- A colour-count increment has Poisson law with parameter equal to its interval intensity,
for any locally finite intensity. -/
theorem hasLaw_nat_count_color_sub {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {M : Ω → Measure (ℝ≥0 × E)} {Λ : Measure (ℝ≥0 × E)}
    [IsLocallyFiniteMeasure Λ] (h : IsPoissonRandomMeasure P M Λ) (b : E)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (Λ (Ioc s t ×ˢ {b})).toNNReal) P := by
  exact h.hasLaw_nat_count_prod_sub_of_measure_Iic_prod_lt_top (measurableSet_singleton b)
    (fun t ↦ by simpa only [Icc_bot] using
      ((isCompact_Icc (a := (⊥ : ℝ≥0)) (b := t)).prod
        (isCompact_singleton (x := b))).measure_lt_top) hst

/-- Selecting a finite-mass mark set preserves independent temporal count increments for an
arbitrary locally finite ground intensity and s-finite mark measure. -/
theorem hasIndepIncrements_nat_count_prod {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) P := by
  exact h.hasIndepIncrements_nat_count_prod_of_measure_Iic_prod_lt_top hA (fun t ↦ by
    simpa only [Measure.prod_prod, Icc_bot] using
      ENNReal.mul_lt_top (measure_Icc_lt_top (μ := ν) (a := ⊥) (b := t)) hQA.lt_top)

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
    h.hasLaw_nat_count_prod_sub_of_measure_Iic_prod_lt_top hA (fun t ↦ by
      simpa only [Measure.prod_prod, Icc_bot] using
        ENNReal.mul_lt_top (measure_Icc_lt_top (μ := ν) (a := ⊥) (b := t)) hQA.lt_top) hst

/-- Finite-mass mark-selection paths are simultaneously monotone for locally finite ground
intensity and s-finite mark measure. -/
theorem ae_monotone_nat_count_prod {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 ↦ ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊) := by
  exact h.ae_monotone_nat_count_prod_of_measure_Iic_prod_lt_top hA (fun t ↦ by
    simpa only [Measure.prod_prod, Icc_bot] using
      ENNReal.mul_lt_top (measure_Icc_lt_top (μ := ν) (a := ⊥) (b := t)) hQA.lt_top)

/-- A finite-mass selected interval count has Poisson parameter equal to the ground interval
intensity times the mark mass, including empty intervals. -/
theorem hasLaw_nat_count_prod_Ioc {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A : Set E} (hA : MeasurableSet A) (s t : ℝ≥0) (hQA : Q A ≠ ∞ := by finiteness) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure ((ν (Ioc s t)).toNNReal * (Q A).toNNReal)) P := by
  simpa only [Measure.prod_prod, ENNReal.toNNReal_mul] using
    h.hasLaw_nat_count_prod_Ioc_of_measure_Iic_prod_lt_top hA (fun u ↦ by
      simpa only [Measure.prod_prod, Icc_bot] using
        ENNReal.mul_lt_top (measure_Icc_lt_top (μ := ν) (a := ⊥) (b := u)) hQA.lt_top) s t

/-- Counts on two disjoint finite-mass mark sets add simultaneously at every time for
locally finite ground intensity and s-finite mark measure. -/
theorem ae_nat_count_prod_union_eq_add {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} [IsLocallyFiniteMeasure ν]
    {Q : Measure E} [SFinite Q] (h : IsPoissonRandomMeasure P M (ν.prod Q))
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hQA : Q A ≠ ∞ := by finiteness) (hQB : Q B ≠ ∞ := by finiteness) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(M ω (Ioc 0 t ×ˢ (A ∪ B))).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ + ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ := by
  exact h.ae_nat_count_prod_union_eq_add_of_measure_Iic_prod_lt_top hA hB hd
    (fun t ↦ by
      simpa only [Measure.prod_prod, Icc_bot] using
        ENNReal.mul_lt_top (measure_Icc_lt_top (μ := ν) (a := ⊥) (b := t)) hQA.lt_top)
    (fun t ↦ by
      simpa only [Measure.prod_prod, Icc_bot] using
        ENNReal.mul_lt_top (measure_Icc_lt_top (μ := ν) (a := ⊥) (b := t)) hQB.lt_top)

/-- Under homogeneous product intensity, a selected interval count has parameter
`r * Q A` times elapsed time, including zero rates and empty intervals. -/
theorem hasLaw_nat_count_prod_Ioc_smul_nnvolume {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {Q : Measure E} [SFinite Q] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • nnvolume).prod Q))
    {A : Set E} (hA : MeasurableSet A) (s t : ℝ≥0) (hQA : Q A ≠ ∞ := by finiteness) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ A)).toNNReal⌋₊)
      (poissonMeasure ((r * (Q A).toNNReal) * (t - s))) P := by
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
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
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    (h.acceptance_univ_prod_smul hA hQA).hasLaw_nat_count_sub_smul_nnvolume hst

/-- A zero-rate mark selection is the identically zero count path on a single event of full
probability. This covers zero ground rate and zero mark mass. -/
theorem ae_nat_count_prod_eq_zero_of_smul_prod_of_mul_eq_zero {E : Type*} [MeasurableSpace E]
    {M : Ω → Measure (ℝ≥0 × E)} {ν : Measure ℝ≥0} {Q : Measure E} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • ν).prod Q))
    {A : Set E} (hA : MeasurableSet A) (hzero : (r : ℝ≥0∞) * Q A = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ A)).toNNReal⌋₊ = 0 := by
  apply h.ae_nat_count_prod_eq_zero hA
  by_cases hQ : SFinite Q
  · let := hQ
    rw [Measure.prod_prod, smul_apply, smul_eq_mul, mul_right_comm, hzero, zero_mul]
  · simp [Measure.prod_eq_zero_of_not_sfinite hQ]

variable {r : ℝ≥0}

/-- Bernoulli colour interval counts have parameters `r*p` and `r*(1-p)` times elapsed
time, including endpoint parameters, zero ground rate, and empty intervals. -/
theorem hasLaw_nat_count_color_Ioc_of_bernoulliMeasure {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • nnvolume).prod (bernoulliMeasure true false p)))
    (b : Bool) (s t : ℝ≥0) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc s t ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure ((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p) * (t - s))) P := by
  simpa only [Measure.map_fst_restrict_univ_prod_apply _ _ measurableSet_Ioc] using
    (h.acceptance_univ_prod_singleton_smul_of_bernoulliMeasure b).hasLaw_nat_count_Ioc_smul_nnvolume
      s t

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
    (h.acceptance_univ_prod_singleton_smul_of_bernoulliMeasure b).hasLaw_nat_count_sub_smul_nnvolume
      hst

end TauCeti.Probability.IsPoissonRandomMeasure
