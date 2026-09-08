/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import TauCeti.Probability.Distributions.Multinomial.Basic

/-!
# Coordinate marginals of the multinomial distribution

Each coordinate of a multinomial count vector has the binomial distribution with success
probability equal to the corresponding cell probability.  This file proves that statement at the
level of measures.

## Main definitions and results

* `TauCeti.Probability.multinomialCellProbability`: a cell weight as a unit-interval parameter.
* `TauCeti.Probability.map_eval_multinomialMeasure`: a coordinate marginal is binomial.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*}

/-- The probability of one cell of a multinomial parameter, regarded as a binomial parameter. -/
def multinomialCellProbability (p : StdSimplex NNReal ι) (i : ι) : unitInterval :=
  ⟨(p.weights i : ℝ), by positivity, by exact_mod_cast p.weights_apply_le_one i⟩

/-- A multinomial cell probability has the value of the corresponding simplex weight. -/
@[simp]
theorem coe_multinomialCellProbability (p : StdSimplex NNReal ι) (i : ι) :
    (multinomialCellProbability p i : ℝ) = p.weights i := (rfl)

variable [Fintype ι]

open Classical in
private lemma multinomialWeight_add_apply (w : ι → NNReal) (i : ι) (m q : ℕ)
    (g : ι → ℕ) (hg : g ∈ Finset.piAntidiag (Finset.univ.erase i) q) :
    multinomialWeight w ((addRightEmbedding fun j ↦ if j = i then m else 0) g) =
      ((m + q).choose m : ℝ≥0∞) * (w i : ℝ≥0∞) ^ m *
        ((Nat.multinomial (Finset.univ.erase i) g : ℝ≥0∞) *
          ∏ j ∈ Finset.univ.erase i, (w j : ℝ≥0∞) ^ g j) := by
  have hi : i ∉ Finset.univ.erase i := Finset.notMem_erase i Finset.univ
  have hgi : g i = 0 := by
    by_contra h
    exact hi ((Finset.mem_piAntidiag.mp hg).2 i h)
  have hsum : ∑ j ∈ Finset.univ.erase i, g j = q :=
    (Finset.mem_piAntidiag.mp hg).1
  have huniv : (Finset.univ.erase i).cons i hi = Finset.univ := by ext; simp
  rw [multinomialWeight_eq, ← huniv, Nat.multinomial_cons, Finset.prod_cons]
  simp only [addRightEmbedding_apply, Pi.add_apply, hgi, zero_add]
  have hsum_add : ∑ j ∈ Finset.univ.erase i, (g j + if j = i then m else 0) = q := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, g j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [(Finset.mem_erase.mp hj).1]
      _ = q := hsum
  have hmultinomial :
      Nat.multinomial (Finset.univ.erase i) (g + fun j ↦ if j = i then m else 0) =
        Nat.multinomial (Finset.univ.erase i) g := by
    apply Nat.multinomial_congr
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  have hprod :
      (∏ j ∈ Finset.univ.erase i, (w j : ℝ≥0∞) ^ (g j + if j = i then m else 0)) =
        ∏ j ∈ Finset.univ.erase i, (w j : ℝ≥0∞) ^ g j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  have herase : ((Finset.univ.erase i).cons i hi).erase i = Finset.univ.erase i := by
    ext
    simp
  rw [hsum_add, hmultinomial, hprod, herase]
  push_cast
  ring

open Classical in
private lemma sum_multinomialWeight_eq_apply (w : ι → NNReal) (n m : ℕ) (i : ι) :
    (∑ k ∈ Finset.piAntidiag Finset.univ n,
        if k i = m then multinomialWeight w k else 0) =
      (n.choose m : ℝ≥0∞) * (w i : ℝ≥0∞) ^ m *
        (∑ j ∈ Finset.univ.erase i, (w j : ℝ≥0∞)) ^ (n - m) := by
  have huniv : (Finset.univ.erase i).cons i (Finset.notMem_erase i Finset.univ) =
      Finset.univ := by ext; simp
  conv_lhs =>
    rw [← huniv, Finset.piAntidiag_cons, Finset.sum_disjiUnion]
  simp only [Finset.sum_map]
  by_cases hmn : m ≤ n
  · rw [Finset.sum_eq_single (m, n - m)]
    · calc
        (∑ g ∈ Finset.piAntidiag (Finset.univ.erase i) (n - m),
            if (addRightEmbedding fun j ↦ if j = i then m else 0) g i = m then
              multinomialWeight w ((addRightEmbedding fun j ↦ if j = i then m else 0) g)
            else 0) =
            ∑ g ∈ Finset.piAntidiag (Finset.univ.erase i) (n - m),
              multinomialWeight w
                ((addRightEmbedding fun j ↦ if j = i then m else 0) g) := by
          apply Finset.sum_congr rfl
          intro g hg
          have hgi : g i = 0 := by
            by_contra h
            exact Finset.notMem_erase i Finset.univ
              ((Finset.mem_piAntidiag.mp hg).2 i h)
          simp [addRightEmbedding_apply, hgi]
        _ = (n.choose m : ℝ≥0∞) * (w i : ℝ≥0∞) ^ m *
            ∑ g ∈ Finset.piAntidiag (Finset.univ.erase i) (n - m),
              (Nat.multinomial (Finset.univ.erase i) g : ℝ≥0∞) *
                ∏ j ∈ Finset.univ.erase i, (w j : ℝ≥0∞) ^ g j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g hg
          rw [multinomialWeight_add_apply w i m (n - m) g hg,
            Nat.add_sub_of_le hmn]
        _ = _ := by
          rw [← Finset.sum_pow_eq_sum_piAntidiag]
    · rintro ⟨a, b⟩ hab hpne
      have ha : a ≠ m := by
        intro ham
        apply hpne
        ext
        · exact ham
        · have hab' := Finset.mem_antidiagonal.mp hab
          omega
      apply Finset.sum_eq_zero
      intro g hg
      have hgi : g i = 0 := by
        by_contra h
        exact Finset.notMem_erase i Finset.univ
          ((Finset.mem_piAntidiag.mp hg).2 i h)
      simp [addRightEmbedding_apply, hgi, ha]
    · intro hnot
      exact (hnot (by simp [Finset.mem_antidiagonal, Nat.add_sub_of_le hmn])).elim
  · have hnm : n < m := Nat.lt_of_not_ge hmn
    rw [Finset.sum_eq_zero]
    · simp [Nat.choose_eq_zero_of_lt hnm]
    · rintro ⟨a, b⟩ hab
      apply Finset.sum_eq_zero
      intro g hg
      have ha : a ≠ m := by
        have han : a ≤ n := by
          have := Finset.mem_antidiagonal.mp hab
          omega
        omega
      have hgi : g i = 0 := by
        by_contra h
        exact Finset.notMem_erase i Finset.univ
          ((Finset.mem_piAntidiag.mp hg).2 i h)
      simp [addRightEmbedding_apply, hgi, ha]

/-- The count in a fixed cell of a multinomial random vector is binomial, with success probability
equal to that cell's weight. -/
theorem map_eval_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι) (i : ι) :
    (multinomialMeasure n p).map (fun k ↦ k i) =
      Bin(n, multinomialCellProbability p i) := by
  classical
  apply Measure.ext_of_singleton
  intro m
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton m),
    multinomialMeasure_eq_sum_dirac, Measure.finsetSum_apply, binomial_singleton]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator, Pi.one_apply,
    Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_multinomialWeight_eq_apply]
  have hsum : p.weights i + ∑ j ∈ Finset.univ.erase i, p.weights j = 1 := by
    rw [← Finset.sum_insert (Finset.notMem_erase i Finset.univ),
      Finset.insert_erase (Finset.mem_univ i)]
    exact p.total_of_fintype
  have hrestNNReal : ∑ j ∈ Finset.univ.erase i, p.weights j = 1 - p.weights i := by
    apply eq_tsub_of_add_eq
    simpa [add_comm] using hsum
  have hrest : ∑ j ∈ Finset.univ.erase i, (p.weights j : ℝ≥0∞) =
      ENNReal.ofReal (1 - (p.weights i : ℝ)) := by
    rw [← ENNReal.toReal_eq_toReal_iff'
        (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.coe_ne_top) (by finiteness),
      ENNReal.toReal_sum (by simp), ENNReal.toReal_ofReal]
    · calc
        (∑ j ∈ Finset.univ.erase i, ((p.weights j : ℝ≥0∞).toReal)) =
            ((∑ j ∈ Finset.univ.erase i, p.weights j : NNReal) : ℝ) := by simp
        _ = ((1 - p.weights i : NNReal) : ℝ) := by rw [hrestNNReal]
        _ = 1 - (p.weights i : ℝ) :=
          NNReal.coe_sub (p.weights_apply_le_one i)
    · exact sub_nonneg.mpr (by exact_mod_cast p.weights_apply_le_one i)
  rw [hrest, ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  have hcomp : 0 ≤ 1 - (p.weights i : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast p.weights_apply_le_one i)
  rw [ENNReal.toReal_ofReal]
  · simp
  · rw [coe_multinomialCellProbability]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hcomp _)

end TauCeti.Probability
