/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Bernoulli

import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import TauCeti.InformationTheory.KullbackLeibler.Convex
import TauCeti.InformationTheory.KullbackLeibler.Finite

/-!
# The binary Kullback–Leibler divergence

The binary divergence `klBin a b = a log (a / b) + (1 - a) log ((1 - a) / (1 - b))` is the
relative entropy of the Bernoulli law with mass `a` at one point from the Bernoulli law with
mass `b` there, for `a ∈ [0, 1]` and `b ∈ (0, 1)`. Outside `b ∈ (0, 1)` it takes the junk value
coming from `Real.log 0 = 0` where the divergence is infinite.

It is jointly convex on `[0, 1] × (0, 1)`: the Bernoulli law is affine in its parameter, and
relative entropy is jointly convex (`TauCeti.klDiv_smul_add_smul_smul_add_smul_le`). Data
processing to the indicator of an event bounds `klBin` of the masses of the event by the
divergence of the two laws, and the binary entropy bound `h(a) ≤ log 2` gives the lower bound
`klBin a b ≥ a log (1 / b) - log 2` used in Fano's inequality.

## Main definitions and statements

* `TauCeti.klBin`: the binary Kullback–Leibler divergence, as a real number.
* `TauCeti.klDiv_bernoulliMeasure`: `klBin a b` is the divergence of `Ber(x, y, a)` from
  `Ber(x, y, b)` for `x ≠ y`, `a ∈ [0, 1]` and `b ∈ (0, 1)`.
* `TauCeti.convexOn_klBin`: joint convexity on `[0, 1] × (0, 1)`.
* `TauCeti.neg_mul_log_sub_log_two_le_klBin`, `TauCeti.mul_log_sub_log_two_le_klBin`:
  `-a log b - log 2 ≤ klBin a b`, in particular `a log M - log 2 ≤ klBin a (1 / M)`.
* `TauCeti.ofReal_klBin_le_klDiv`: data processing to an event,
  `klBin (P.real A) (Q.real A) ≤ klDiv P Q` for probability measures `P`, `Q` and any set `A`.

## References

* R. J. Samworth and R. D. Shah, *Modern Statistical Methods for Data Science* (lecture
  notes), proof of Theorem 8.11 and (8.10), p. 235.

The formula for the divergence of two Bernoulli laws and the event bound are adapted from the
lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), files
`CKSD/Inference/Divergence/Basic.lean` (`klDiv_bernoulliMeasure_eq_bernoulliKullbackLeibler`,
`bernoulliKullbackLeibler_eq_neg_binEntropy_sub`) and
`CKSD/Nonparametric/LowerBounds/Testing.lean` (`measureReal_mul_neg_log_sub_log_two_le_klDiv`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Set Real unitInterval
open scoped ENNReal NNReal

namespace TauCeti

/-- The binary Kullback–Leibler divergence `a log (a / b) + (1 - a) log ((1 - a) / (1 - b))`.
For `a ∈ [0, 1]` and `b ∈ (0, 1)` it is the divergence of the Bernoulli law with parameter `a`
from that with parameter `b` (`TauCeti.klDiv_bernoulliMeasure`); at `b ∈ {0, 1}` it takes the
junk value given by `Real.log 0 = 0`. -/
noncomputable def klBin (a b : ℝ) : ℝ :=
  a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b))

/-- The binary divergence as the `klFun` form of relative entropy, weighted by the reference
masses `b` and `1 - b`. -/
theorem klBin_eq_mul_klFun_add_mul_klFun {a b : ℝ} (hb₀ : b ≠ 0) (hb₁ : b ≠ 1) :
    klBin a b = b * klFun (a / b) + (1 - b) * klFun ((1 - a) / (1 - b)) := by
  have : 1 - b ≠ 0 := sub_ne_zero.mpr hb₁.symm
  simp only [klBin, klFun]
  field_simp
  ring

/-- The binary divergence is nonnegative for `a ∈ [0, 1]` and `b ∈ (0, 1)`. -/
theorem klBin_nonneg {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Ioo 0 1) : 0 ≤ klBin a b := by
  rw [klBin_eq_mul_klFun_add_mul_klFun hb.1.ne' hb.2.ne]
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  exact add_nonneg (mul_nonneg hb.1.le (klFun_nonneg (div_nonneg ha.1 hb.1.le)))
    (mul_nonneg hb'.le (klFun_nonneg (div_nonneg (sub_nonneg.mpr ha.2) hb'.le)))

/-- `x log (x / y) = x log x - x log y` for `y ≠ 0`, including `x = 0`. -/
private theorem mul_log_div_eq {x y : ℝ} (hy : y ≠ 0) :
    x * log (x / y) = x * log x - x * log y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [log_div hx hy, mul_sub]

/-- The binary divergence in terms of the binary entropy, for `b ∉ {0, 1}`. -/
theorem klBin_eq_neg_binEntropy_sub {a b : ℝ} (hb₀ : b ≠ 0) (hb₁ : b ≠ 1) :
    klBin a b = -binEntropy a - a * log b - (1 - a) * log (1 - b) := by
  rw [klBin, mul_log_div_eq hb₀, mul_log_div_eq (sub_ne_zero.mpr hb₁.symm),
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [negMulLog]
  ring

/-- The lower bound `-a log b - log 2 ≤ klBin a b` for `a, b ∈ [0, 1]`, from the binary
entropy bound `h(a) ≤ log 2`. -/
theorem neg_mul_log_sub_log_two_le_klBin {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    -(a * log b) - log 2 ≤ klBin a b := by
  have hh : -a * log a + -(1 - a) * log (1 - a) ≤ log 2 := by
    simpa [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog] using
      binEntropy_le_log_two (p := a)
  have h₀ : 0 ≤ -a * log a := negMulLog_nonneg ha.1 ha.2
  have h₁ : 0 ≤ -(1 - a) * log (1 - a) :=
    negMulLog_nonneg (sub_nonneg.mpr ha.2) (sub_le_self 1 ha.1)
  rcases hb.1.eq_or_lt with rfl | hb₀
  · simp only [klBin, div_zero, log_zero, mul_zero, sub_zero, div_one, zero_add, neg_zero]
    linarith
  rcases hb.2.eq_or_lt with rfl | hb₁
  · simp only [klBin, div_one, sub_self, div_zero, log_zero, mul_zero, add_zero, log_one]
    linarith
  rw [klBin_eq_neg_binEntropy_sub hb₀.ne' hb₁.ne, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [negMulLog]
  have : (1 - a) * log (1 - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha.2)
      (log_nonpos (sub_nonneg.mpr hb₁.le) (sub_le_self 1 hb₀.le))
  linarith

/-- **Fano's lower bound for `klBin`**: `a log M - log 2 ≤ klBin a (1 / M)` for `a ∈ [0, 1]`. -/
theorem mul_log_sub_log_two_le_klBin {a : ℝ} (ha : a ∈ Icc 0 1) (M : ℕ) :
    a * log M - log 2 ≤ klBin a (1 / M) := by
  have hM : (1 / M : ℝ) ∈ Icc 0 1 := by
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · exact div_le_one_of_le₀ (Nat.one_le_cast.mpr hM) (Nat.cast_nonneg M)
  simpa [one_div, log_inv] using neg_mul_log_sub_log_two_le_klBin ha hM

section Bernoulli

variable {X : Type*} [MeasurableSpace X]

/-- On `Bool`, the binary divergence is the divergence of the Bernoulli laws. -/
private theorem klDiv_bernoulliMeasure_bool {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Ioo 0 1) :
    klDiv (bernoulliMeasure true false ⟨a, ha⟩)
        (bernoulliMeasure true false ⟨b, Ioo_subset_Icc_self hb⟩) =
      ENNReal.ofReal (klBin a b) := by
  have hν : ∀ c : Bool, bernoulliMeasure true false ⟨b, Ioo_subset_Icc_self hb⟩ {c} ≠ 0 := by
    rintro (_ | _) <;>
      simp [← NNReal.coe_eq_zero, hb.1.ne', sub_eq_zero, hb.2.ne']
  rw [klDiv_eq_ofReal_sum_log_singleton hν, Fintype.sum_bool]
  simp [klBin, add_comm]

/-- The Bernoulli law is affine in its parameter. -/
private theorem bernoulliMeasure_eq_smul_add_smul (x y : X) {p q r : I} {s t : ℝ≥0}
    (hst : s + t = 1) (hr : (r : ℝ) = s * p + t * q) :
    bernoulliMeasure x y r = s • bernoulliMeasure x y p + t • bernoulliMeasure x y q := by
  have hst' : (s : ℝ) + t = 1 := by exact_mod_cast hst
  have h₁ : unitInterval.toNNReal r = s * unitInterval.toNNReal p + t * unitInterval.toNNReal q :=
    by ext; simp [hr]
  have h₂ : unitInterval.toNNReal (σ r) =
      s * unitInterval.toNNReal (σ p) + t * unitInterval.toNNReal (σ q) := by
    ext
    simp only [unitInterval.coe_toNNReal, coe_symm_eq, hr, NNReal.coe_add, NNReal.coe_mul]
    linear_combination -hst'
  simp only [bernoulliMeasure_def, h₁, h₂, add_smul, mul_smul, smul_add]
  abel

/-- **Divergence of Bernoulli laws.** For `x ≠ y`, `a ∈ [0, 1]` and `b ∈ (0, 1)`, the
divergence of `Ber(x, y, a)` from `Ber(x, y, b)` (the laws with mass `a` and `b` at `x`) is
`klBin a b`. -/
theorem klDiv_bernoulliMeasure [MeasurableSingletonClass X] {x y : X} (hxy : x ≠ y) {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Ioo 0 1) :
    klDiv (bernoulliMeasure x y ⟨a, ha⟩) (bernoulliMeasure x y ⟨b, Ioo_subset_Icc_self hb⟩) =
      ENNReal.ofReal (klBin a b) := by
  classical
  rw [← klDiv_bernoulliMeasure_bool ha hb]
  set f : Bool → X := fun c ↦ cond c x y
  set g : X → Bool := fun z ↦ decide (z = x)
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable g := measurable_to_bool <| by
    simp [g, Set.preimage, Set.ofPred_eq_eq_singleton]
  have hfp (p : I) : (bernoulliMeasure true false p).map f = bernoulliMeasure x y p :=
    map_bernoulliMeasure' _ _ hf p
  have hgp (p : I) : (bernoulliMeasure x y p).map g = bernoulliMeasure true false p := by
    rw [map_bernoulliMeasure' _ _ hg p]
    simp [g, hxy.symm]
  refine le_antisymm ?_ ?_
  · simpa only [hfp] using klDiv_map_le (μ := bernoulliMeasure true false ⟨a, ha⟩)
      (ν := bernoulliMeasure true false ⟨b, Ioo_subset_Icc_self hb⟩) hf
  · simpa only [hgp] using klDiv_map_le (μ := bernoulliMeasure x y ⟨a, ha⟩)
      (ν := bernoulliMeasure x y ⟨b, Ioo_subset_Icc_self hb⟩) hg

end Bernoulli

/-- **Joint convexity** of the binary divergence on `[0, 1] × (0, 1)`. -/
theorem convexOn_klBin : ConvexOn ℝ (Icc 0 1 ×ˢ Ioo 0 1) fun p : ℝ × ℝ ↦ klBin p.1 p.2 := by
  have hconv : Convex ℝ (Icc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := (convex_Icc 0 1).prod (convex_Ioo 0 1)
  refine ⟨hconv, ?_⟩
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ s t hs ht hst
  obtain ⟨ha, hb⟩ := hconv ⟨ha₁, hb₁⟩ ⟨ha₂, hb₂⟩ hs ht hst
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at ha hb ⊢
  lift s to ℝ≥0 using hs
  lift t to ℝ≥0 using ht
  have hst' : s + t = 1 := by exact_mod_cast hst
  have htf : true ≠ false := by decide
  have key := klDiv_smul_add_smul_smul_add_smul_le
    (μ₁ := bernoulliMeasure true false ⟨a₁, ha₁⟩) (μ₂ := bernoulliMeasure true false ⟨a₂, ha₂⟩)
    (ν₁ := bernoulliMeasure true false ⟨b₁, Ioo_subset_Icc_self hb₁⟩)
    (ν₂ := bernoulliMeasure true false ⟨b₂, Ioo_subset_Icc_self hb₂⟩) s t
  rw [← bernoulliMeasure_eq_smul_add_smul _ _ (r := ⟨_, ha⟩) hst' rfl,
    ← bernoulliMeasure_eq_smul_add_smul _ _ (r := ⟨_, Ioo_subset_Icc_self hb⟩) hst' rfl,
    klDiv_bernoulliMeasure htf ha hb, klDiv_bernoulliMeasure htf ha₁ hb₁,
    klDiv_bernoulliMeasure htf ha₂ hb₂, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul s.coe_nonneg, ← ENNReal.ofReal_mul t.coe_nonneg,
    ← ENNReal.ofReal_add (mul_nonneg s.coe_nonneg (klBin_nonneg ha₁ hb₁))
      (mul_nonneg t.coe_nonneg (klBin_nonneg ha₂ hb₂)),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg s.coe_nonneg (klBin_nonneg ha₁ hb₁))
      (mul_nonneg t.coe_nonneg (klBin_nonneg ha₂ hb₂)))] at key
  exact key

/-- **Data processing to an event.** For probability measures `P`, `Q` and any set `A`, the
binary divergence of the masses of `A` is at most the divergence of `P` from `Q`. The set need
not be measurable: its masses are those of a common measurable hull for `P + Q`. Where
`Q.real A ∈ {0, 1}` and `P.real A` differs from it, `klBin` takes a junk value at most `0`,
and the inequality still holds. -/
theorem ofReal_klBin_le_klDiv {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (A : Set X) :
    ENNReal.ofReal (klBin (P.real A) (Q.real A)) ≤ klDiv P Q := by
  set H := toMeasurable (P + Q) A
  have hH : MeasurableSet H := measurableSet_toMeasurable _ _
  have hfin : (P + Q) A ≠ ∞ := measure_ne_top _ _
  have hP : P.real A = P.real H := by
    simp only [Measure.real, H]
    rw [← inter_univ (toMeasurable _ _), Measure.measure_toMeasurable_add_inter_left .univ hfin,
      inter_univ]
  have hQ : Q.real A = Q.real H := by
    simp only [Measure.real, H]
    rw [← inter_univ (toMeasurable _ _), Measure.measure_toMeasurable_add_inter_right .univ hfin,
      inter_univ]
  rw [hP, hQ]
  set p := P.real H
  set q := Q.real H
  have hp : p ∈ Icc 0 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  rcases (show 0 ≤ q from measureReal_nonneg).eq_or_lt with hq₀ | hq₀
  · refine le_of_eq_of_le (ENNReal.ofReal_of_nonpos ?_) zero_le
    have : 0 ≤ -(1 - p) * log (1 - p) := negMulLog_nonneg (sub_nonneg.mpr hp.2) (sub_le_self 1 hp.1)
    simp only [klBin, ← hq₀, div_zero, log_zero, mul_zero, sub_zero, div_one, zero_add]
    linarith
  rcases (show q ≤ 1 from measureReal_le_one).eq_or_lt with hq₁ | hq₁
  · refine le_of_eq_of_le (ENNReal.ofReal_of_nonpos ?_) zero_le
    have : 0 ≤ -p * log p := negMulLog_nonneg hp.1 hp.2
    simp only [klBin, hq₁, div_one, sub_self, div_zero, log_zero, mul_zero, add_zero]
    linarith
  have hlaw (R : Measure X) [IsProbabilityMeasure R] :=
    (hasLaw_indicator_one_bernoulliMeasure (M := ℝ) (P := R) hH.nullMeasurableSet).map_eq
  have hmeas : Measurable (H.indicator (1 : X → ℝ)) := measurable_one.indicator hH
  have hle := klDiv_map_le (μ := P) (ν := Q) hmeas
  rwa [hlaw P, hlaw Q, klDiv_bernoulliMeasure (one_ne_zero : (1 : ℝ) ≠ 0) hp ⟨hq₀, hq₁⟩] at hle

end TauCeti
