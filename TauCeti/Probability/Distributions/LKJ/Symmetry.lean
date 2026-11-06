/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
public import TauCeti.Probability.Distributions.Beta.Symmetric
public import TauCeti.Probability.Distributions.Beta.Reflection
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Analysis.Matrix.MeasurableSpace
import TauCeti.Analysis.Matrix.PosSemidef.Basic

/-!
# Sign symmetry of partial-correlation Gram laws

Independent symmetric partial correlations give a Gram law invariant under conjugation by
any diagonal sign matrix. This holds for arbitrary symmetric marginal laws; for centered
symmetric Beta marginals, entries have all finite moments, the mean is the identity, and
distinct strictly lower entries have covariance zero. Zero covariance does not assert
independence of correlation entries.

The proofs use `partialCorrelationGram_signChange`, the coordinatewise product pushforward,
and reflection symmetry of Beta laws. These results apply to the independent-Beta construction
of random correlation matrices without requiring a density change of variables.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise ENNReal

namespace TauCeti.Probability

variable {p : ℕ}

/-- Independent negation-invariant partial correlations give a Gram law invariant under
conjugation by a diagonal sign matrix. The marginals need only be sigma-finite. -/
theorem map_signChange_map_partialCorrelationGram_pi
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, SigmaFinite (μ ij)]
    [∀ ij, (μ ij).IsNegInvariant] {s : Fin p → ℝ} (hs : ∀ i, |s i| = 1) :
    ((Measure.pi μ).map partialCorrelationGram).map
        (fun R : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.of fun i j ↦ s i * R i j * s j) =
      (Measure.pi μ).map partialCorrelationGram := by
  have hmap (ij : strictLowerTriangle p) :
      (μ ij).map (fun x ↦ s ij.1.1 * s ij.1.2 * x) = μ ij := by
    have habs : |s ij.1.1 * s ij.1.2| = 1 := by simp [abs_mul, hs]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 habs with h | h
    · simp [h]
    · simp [h]
  have (ij : strictLowerTriangle p) : SigmaFinite
      ((μ ij).map (fun x ↦ s ij.1.1 * s ij.1.2 * x)) := by
    rw [hmap]
    infer_instance
  have hpi : (Measure.pi μ).map
      (fun z ij ↦ s ij.1.1 * s ij.1.2 * z ij) = Measure.pi μ := by
    rw [Measure.pi_map_pi (fun _ ↦ by fun_prop)]
    simp_rw [hmap]
  have hcomp :
      (fun R : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.of fun i j ↦ s i * R i j * s j) ∘
        partialCorrelationGram = partialCorrelationGram ∘
          (fun z ij ↦ s ij.1.1 * s ij.1.2 * z ij) := by
    funext z i j
    exact (partialCorrelationGram_signChange z hs i j).symm
  rw [Measure.map_map (by fun_prop) continuous_partialCorrelationGram.measurable, hcomp,
    ← Measure.map_map (g := partialCorrelationGram (p := p))
      continuous_partialCorrelationGram.measurable (by fun_prop), hpi]

/-- Every entry of the independent-Beta Gram construction belongs to every `Lᵠ`, including
`L∞`. This supplies absolute integrability for its moment and covariance formulas. -/
theorem memLp_apply_map_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i j : Fin p) (q : ℝ≥0∞) :
    MemLp (fun R : Matrix (Fin p) (Fin p) ℝ ↦ R i j) q
      ((Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map
        (fun x ↦ -1 + 2 * x)).map partialCorrelationGram) := by
  rw [memLp_map_measure_iff Matrix.measurable_apply.aestronglyMeasurable
    continuous_partialCorrelationGram.measurable.aemeasurable]
  have (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  refine MemLp.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_abs_le_one_pi_centered_betaMeasure ha] with z hz
  exact (posSemidef_partialCorrelationGram z).norm_le_one_of_apply_self_eq_one
    (partialCorrelationGram_apply_self hz i) (partialCorrelationGram_apply_self hz j)

/-- The entrywise mean of the independent centered symmetric Beta Gram law is the identity.
The shapes may vary independently across all strictly lower positions. -/
@[simp]
theorem integral_apply_map_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i j : Fin p) :
    ∫ R : Matrix (Fin p) (Fin p) ℝ, R i j
      ∂((Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map
        (fun x ↦ -1 + 2 * x)).map partialCorrelationGram) = if i = j then 1 else 0 := by
  have (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  by_cases hij : i = j
  · subst j
    rw [integral_map continuous_partialCorrelationGram.measurable.aemeasurable
      Matrix.measurable_apply.aestronglyMeasurable]
    simp only [ite_true]
    calc
      _ = ∫ _, (1 : ℝ) ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map
          (fun x ↦ -1 + 2 * x)) := integral_congr_ae <|
        (ae_abs_le_one_pi_centered_betaMeasure ha).mono fun z hz ↦
          partialCorrelationGram_apply_self hz i
      _ = 1 := by simp
  · let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
    have hs : ∀ k, |s k| = 1 := by intro k; simp [s]; split_ifs <;> norm_num
    have h := congrArg (fun ν : Measure (Matrix (Fin p) (Fin p) ℝ) ↦ ∫ R, R i j ∂ν)
      (map_signChange_map_partialCorrelationGram_pi
        (fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) hs)
    rw [integral_map
      (by fun_prop : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦
        Matrix.of fun i j ↦ s i * R i j * s j)).aemeasurable
      Matrix.measurable_apply.aestronglyMeasurable] at h
    simp only [Matrix.of_apply] at h
    simp only [s, ite_true, ite_eq_right (Ne.symm hij), neg_one_mul, mul_one, integral_neg] at h
    rw [ite_eq_right hij]
    linarith

/-- Distinct strictly lower entries of the independent-Beta Gram law have covariance zero.
Their squares are integrable; the conclusion does not assert independence. -/
@[simp]
theorem covariance_apply_map_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    {ij kl : strictLowerTriangle p} (hne : ij ≠ kl) :
    cov[fun R : Matrix (Fin p) (Fin p) ℝ ↦ R ij.1.1 ij.1.2,
        fun R : Matrix (Fin p) (Fin p) ℝ ↦ R kl.1.1 kl.1.2;
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map
        (fun x ↦ -1 + 2 * x)).map partialCorrelationGram] = 0 := by
  have (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  have hp : ij.1 ≠ kl.1 := Subtype.coe_injective.ne hne
  have hij := ij.2
  have hkl := kl.2
  obtain ⟨v, hv, hvk, hvl⟩ : ∃ v : Fin p,
      (v = ij.1.1 ∨ v = ij.1.2) ∧ v ≠ kl.1.1 ∧ v ≠ kl.1.2 := by
    by_cases h : ij.1.1 = kl.1.1 ∨ ij.1.1 = kl.1.2
    · refine ⟨ij.1.2, Or.inr rfl, ?_, ?_⟩
      all_goals rcases h with h | h
      all_goals intro h'
      all_goals first | exact hp (Prod.ext h h') | omega
    · exact ⟨ij.1.1, Or.inl rfl, fun h' ↦ h (Or.inl h'), fun h' ↦ h (Or.inr h')⟩
  let s : Fin p → ℝ := fun k ↦ if k = v then -1 else 1
  have hs : ∀ k, |s k| = 1 := by intro k; simp [s]; split_ifs <;> norm_num
  have hsign : s ij.1.1 * s ij.1.2 = -1 := by
    rcases hv with rfl | rfl <;> simp [s, hij.ne, hij.ne']
  have h := congrArg (fun ν : Measure (Matrix (Fin p) (Fin p) ℝ) ↦
      ∫ R, R ij.1.1 ij.1.2 * R kl.1.1 kl.1.2 ∂ν)
    (map_signChange_map_partialCorrelationGram_pi
      (fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) hs)
  rw [integral_map (f := fun R : Matrix (Fin p) (Fin p) ℝ ↦
      R ij.1.1 ij.1.2 * R kl.1.1 kl.1.2)
    (by fun_prop : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦
      Matrix.of fun i j ↦ s i * R i j * s j)).aemeasurable
    (Matrix.measurable_apply.mul Matrix.measurable_apply).aestronglyMeasurable] at h
  simp only [Matrix.of_apply] at h
  have he : ∀ R : Matrix (Fin p) (Fin p) ℝ,
      (s ij.1.1 * R ij.1.1 ij.1.2 * s ij.1.2) *
        (s kl.1.1 * R kl.1.1 kl.1.2 * s kl.1.2) =
          -(R ij.1.1 ij.1.2 * R kl.1.1 kl.1.2) := by
    intro R
    rw [mul_right_comm (s ij.1.1), hsign]
    simp [s, Ne.symm hvk, Ne.symm hvl]
  simp_rw [he, integral_neg] at h
  simp only [covariance, integral_apply_map_partialCorrelationGram_pi_betaMeasure ha,
    ite_eq_right hij.ne', ite_eq_right hkl.ne', sub_zero]
  linarith

end TauCeti.Probability
