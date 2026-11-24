/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convex combinations of probability measures

Probability measures are closed under convex combinations: for nonnegative extended-real weights
`a + b = 1`, the measure `a • P + b • Q` again has total mass one.
`ProbabilityMeasure.convexComb` bundles this measure, allowing affinity of maps between
probability measures to be stated without rebuilding the probability-measure structure.

## Main results

* `TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul` proves that the underlying measure
  has total mass one.
* `TauCeti.isProbabilityMeasure_inv_natCast_smul_sum` proves that a uniform finite mixture of
  probability measures is a probability measure.
* `TauCeti.MeasureTheory.exists_mem_eq_smul_sum`: a set of probability measures closed under
  binary mixtures contains the uniform mixture of any finitely many of its members.
* `MeasureTheory.ProbabilityMeasure.toMeasure_convexComb` identifies the underlying measure.
* `MeasureTheory.ProbabilityMeasure.convexComb_apply` evaluates the combination on any set.
* `MeasureTheory.ProbabilityMeasure.convexComb_zero_left`,
  `MeasureTheory.ProbabilityMeasure.convexComb_zero_right`, and
  `MeasureTheory.ProbabilityMeasure.convexComb_self` simplify degenerate combinations.
* `MeasureTheory.ProbabilityMeasure.convexComb_comm` exchanges the measures and their weights.
* `MeasureTheory.ProbabilityMeasure.map_convexComb`: push-forward along a measurable map is affine.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal

namespace TauCeti

/-- The uniform mixture `(q : ℝ≥0∞)⁻¹ • ∑ r : Fin q, (μr r : Measure α)` of `q > 0` probability
measures is a probability measure. -/
theorem isProbabilityMeasure_inv_natCast_smul_sum {α : Type*} [MeasurableSpace α] {q : ℕ}
    (hq : 0 < q) (μr : Fin q → ProbabilityMeasure α) :
    IsProbabilityMeasure ((q : ℝ≥0∞)⁻¹ • ∑ r : Fin q, (μr r : Measure α)) := ⟨by
  simp [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hq.ne') (ENNReal.natCast_ne_top q)]⟩

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **A convex combination of probability measures is a probability measure.** The weights are
arbitrary elements of `ℝ≥0∞` summing to `1`; no separate nonnegativity condition is needed, since
`ℝ≥0∞` has none to impose. -/
theorem isProbabilityMeasure_smul_add_smul {a b : ℝ≥0∞} (hab : a + b = 1) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (a • μ + b • ν) :=
  ⟨by simp [hab]⟩

/-- **Uniform finite mixtures.** In a set `C` of probability measures closed under binary
mixtures `a • P + (1 - a) • Q`, `0 ≤ a ≤ 1`, the uniform mixture `(#s)⁻¹ • ∑ i ∈ s, Q i` of finitely
many members `Q i`, `i ∈ s`, is (the underlying measure of) a member. -/
theorem exists_mem_eq_smul_sum {C : Set (ProbabilityMeasure α)}
    (hconv : ∀ P ∈ C, ∀ Q ∈ C, ∀ a : ℝ≥0, a ≤ 1 →
      ∃ R ∈ C, (R : Measure α) = (a : ℝ≥0∞) • (P : Measure α) +
        ((1 - a : ℝ≥0) : ℝ≥0∞) • (Q : Measure α))
    {ι : Type*} {Q : ι → ProbabilityMeasure α} {s : Finset ι} (hQ : ∀ i ∈ s, Q i ∈ C)
    (hs : s.Nonempty) :
    ∃ R ∈ C, (R : Measure α) = (s.card : ℝ≥0)⁻¹ • ∑ i ∈ s, (Q i : Measure α) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨Q a, hQ a (Finset.mem_singleton_self a), by simp⟩
  | cons a s ha hs ih =>
    obtain ⟨R, hR, hReq⟩ := ih fun i hi ↦ hQ i (Finset.mem_cons_of_mem hi)
    have hk : (s.card : ℝ≥0) ≠ 0 := by simpa using hs.ne_empty
    have hw : ((s.card : ℝ≥0) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ le_add_self
    obtain ⟨R', hR', hR'eq⟩ := hconv (Q a) (hQ a (Finset.mem_cons_self a s)) R hR _ hw
    refine ⟨R', hR', ?_⟩
    have hcoef : (1 - ((s.card : ℝ≥0) + 1)⁻¹) * (s.card : ℝ≥0)⁻¹ = ((s.card : ℝ≥0) + 1)⁻¹ := by
      have hk' : (s.card : ℝ) ≠ 0 := by exact_mod_cast hk
      rw [← NNReal.coe_inj]
      push_cast [NNReal.coe_sub hw]
      field_simp
      ring
    rw [hR'eq, hReq, Finset.card_cons, Nat.cast_succ, Finset.sum_cons, ← ENNReal.smul_def,
      ← ENNReal.smul_def, smul_smul, hcoef, smul_add]

end MeasureTheory

end TauCeti

namespace MeasureTheory

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α]

/-- The **convex combination** `a • P + b • Q` of two probability measures, for weights summing
to `1`, bundled as a `ProbabilityMeasure`. Its underlying measure is `toMeasure_convexComb`. -/
def convexComb {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    ProbabilityMeasure α :=
  ⟨a • (P : Measure α) + b • (Q : Measure α),
    TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul hab _ _⟩

/-- The underlying measure of a convex combination is the combination of the underlying
measures. -/
@[simp]
theorem toMeasure_convexComb {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    (convexComb hab P Q : Measure α) = a • (P : Measure α) + b • (Q : Measure α) :=
  (rfl)

/-- Evaluation of a convex combination on an arbitrary set, with values in `ℝ≥0`. -/
@[simp]
theorem convexComb_apply {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α)
    (s : Set α) : convexComb hab P Q s = a.toNNReal * P s + b.toNNReal * Q s := by
  have ha : a ≠ ∞ := (ENNReal.add_ne_top.mp (hab ▸ ENNReal.one_ne_top)).1
  have hb : b ≠ ∞ := (ENNReal.add_ne_top.mp (hab ▸ ENNReal.one_ne_top)).2
  apply ENNReal.coe_injective
  simp [ENNReal.coe_toNNReal ha, ENNReal.coe_toNNReal hb]

/-- A combination with zero weight on the first measure is the second measure. -/
@[simp]
theorem convexComb_zero_left {b : ℝ≥0∞} (hb : 0 + b = 1) (P Q : ProbabilityMeasure α) :
    convexComb hb P Q = Q := by
  have hb' : b = 1 := by simpa using hb
  apply toMeasure_injective
  simp [hb']

/-- A combination with zero weight on the second measure is the first measure. -/
@[simp]
theorem convexComb_zero_right {a : ℝ≥0∞} (ha : a + 0 = 1) (P Q : ProbabilityMeasure α) :
    convexComb ha P Q = P := by
  have ha' : a = 1 := by simpa using ha
  apply toMeasure_injective
  simp [ha']

/-- A convex combination of a probability measure with itself is that measure. -/
@[simp]
theorem convexComb_self {a b : ℝ≥0∞} (hab : a + b = 1) (P : ProbabilityMeasure α) :
    convexComb hab P P = P := by
  apply toMeasure_injective
  simp [← add_smul, hab]

/-- Exchanging both the measures and their weights preserves a convex combination. -/
theorem convexComb_comm {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    convexComb hab P Q = convexComb ((add_comm b a).trans hab) Q P := by
  apply toMeasure_injective
  simp [add_comm]

/-- **Push-forward is affine.** The push-forward of a convex combination of probability measures
along a measurable map is the convex combination of the push-forwards. -/
@[simp]
theorem map_convexComb {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    (convexComb hab P Q).map f = convexComb hab (P.map f) (Q.map f) := by
  apply toMeasure_injective
  simp [Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable]

end ProbabilityMeasure

end MeasureTheory
