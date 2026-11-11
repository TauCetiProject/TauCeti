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

For product intensity `r dt ⊗ Q` with a finite colour measure `Q`, each colour has independent
increments and Poisson increment laws of rate `r * Q {b}`. Bernoulli colour intensities give
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
  {M : Ω → Measure (ℝ≥0 × Bool)} {Λ : Measure (ℝ≥0 × Bool)}

/-- The complete paths of the two colour counts are independent, even for intensities
that are not product measures or locally finite. -/
theorem indepFun_nat_count_colors (h : IsPoissonRandomMeasure P M Λ) :
    IndepFun (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
      (fun ω (t : ℝ≥0) ↦ ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P := by
  have hi := h.indepFun_restrict
    (s := univ ×ˢ {true}) (t := univ ×ˢ {false}) (by measurability)
    (by measurability) (by simp [disjoint_left])
  let f (μ : Measure (ℝ≥0 × Bool)) (t : ℝ≥0) :=
    ⌊(μ (Ioc 0 t ×ˢ univ)).toNNReal⌋₊
  have hf : Measurable f := Measurable.of_eval fun t ↦
    (Measure.measurable_coe (measurableSet_Ioc.prod MeasurableSet.univ)).ennreal_toNNReal.nat_floor
  simpa only [f, Function.comp_def, Measure.restrict_apply (measurableSet_Ioc.prod
    MeasurableSet.univ), prod_inter_prod, inter_univ, univ_inter] using hi.comp hf hf

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

variable {Q : Measure Bool} [IsFiniteMeasure Q] {r : ℝ≥0}

/-- A colour of a homogeneous product-intensity Poisson measure has independent count
increments. No pathwise assumptions on the input realizations are needed. -/
theorem hasIndepIncrements_nat_count_color
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • nnvolume).prod Q)) (b : Bool) :
    HasIndepIncrements (fun t ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) P := by
  have hc := h.acceptance (A := univ ×ˢ {b}) (by measurability)
  simp only [mk_preimage_prod_right (mem_univ _), withDensity_const] at hc
  rw [smul_smul] at hc
  let := nnvolume.isLocallyFiniteMeasure_smul (c := Q {b} * (r : ℝ≥0∞))
    (ENNReal.mul_ne_top (measure_ne_top Q _) ENNReal.coe_ne_top)
  simpa only [Measure.map_apply measurable_fst measurableSet_Ioc, ← prod_univ,
    Measure.restrict_apply (measurableSet_Ioc.prod MeasurableSet.univ),
    prod_inter_prod, inter_univ, univ_inter] using hc.hasIndepIncrements_nat_count

/-- A colour-count increment has rate `r * Q {b}` under product intensity. The formula
allows zero colour mass, zero ground rate and equal observation endpoints. -/
theorem hasLaw_nat_count_color_sub
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • nnvolume).prod Q))
    (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure ((r * (Q {b}).toNNReal) * (t - s))) P := by
  have hc := h.acceptance (A := univ ×ˢ {b}) (by measurability)
  simp only [mk_preimage_prod_right (mem_univ _), withDensity_const] at hc
  have hrate : Q {b} • (r : ℝ≥0∞) • nnvolume =
      ((r * (Q {b}).toNNReal : ℝ≥0) : ℝ≥0∞) • nnvolume := by
    rw [smul_smul, ENNReal.coe_mul, ENNReal.coe_toNNReal (measure_ne_top _ _), mul_comm]
  rw [hrate] at hc
  simpa only [Measure.map_apply measurable_fst measurableSet_Ioc, ← prod_univ,
    Measure.restrict_apply (measurableSet_Ioc.prod MeasurableSet.univ),
    prod_inter_prod, inter_univ, univ_inter] using hc.hasLaw_nat_count_sub_smul_nnvolume hst

/-- Bernoulli colour intensities split the temporal rate into `r*p` and `r*(1-p)`.
The endpoint parameters produce a zero-rate colour, without any positive-rate assumption. -/
theorem hasLaw_nat_count_color_sub_bernoulli
    {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • nnvolume).prod (bernoulliMeasure true false p)))
    (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure ((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p) * (t - s))) P := by
  have hb : ((bernoulliMeasure true false p) {b}).toNNReal =
      if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p := by
    cases b
    · simpa using eq_tsub_of_add_eq (unitInterval.toNNReal_symm_add_toNNReal p)
    · simp
  simpa only [hb] using h.hasLaw_nat_count_color_sub b hst

end TauCeti.Probability.IsPoissonRandomMeasure
