/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Probability.Distributions.LKJ.Cholesky.Moments
import Mathlib.Probability.Moments.Basic
import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.Probability.Distributions.LKJ.Marginal
import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
import TauCeti.Probability.Distributions.LKJ.PrincipalBlock
import TauCeti.Probability.Distributions.LKJ.Symmetry

/-!
# Mixed entry moments of LKJ correlation matrices

Every natural monomial in the entries of an LKJ correlation matrix belongs to every `Lᵖ`,
including `L∞`, and is therefore integrable; this covers repeated symmetric entries, diagonal
powers, the empty matrix, and nonpositive shapes where `lkjMeasure` is the zero measure.

For positive shape, representing the correlation matrix as `partialCorrelationGram z = L * Lᵀ`
of independent centered symmetric Beta partial correlations expands any entry monomial into a
finite multinomial sum of products of natural powers of `z ij` and nonnegative half-integer powers
of `1 - z ij ^ 2`, which evaluate to finite products of Beta quotients.

Every mixed moment in which some coordinate axis has odd total degree vanishes for all dimensions
and real shapes. Specializations give closed single-Beta-quotient formulas for arbitrary natural
powers of a single entry and evaluate the joint third moment `E[R i j * R i k * R j k]` of any
three pairwise distinct indices to `1 / (2 * η + p - 1) ^ 2`, witnessing non-independence of
off-diagonal correlation entries despite their zero pairwise covariances.

## Main results

* `TauCeti.Probability.memLp_prod_pow_partialCorrelationGram_pi_betaMeasure`,
  `TauCeti.Probability.integrable_prod_pow_partialCorrelationGram_pi_betaMeasure`,
  `TauCeti.Probability.prod_pow_partialCorrelationGram_ae_eq_sum_prod_pi_betaMeasure`, and
  `TauCeti.Probability.integral_prod_pow_partialCorrelationGram_pi_betaMeasure`: `Lᵖ` membership,
  coordinatewise expansion, and finite multinomial Beta-quotient evaluation of mixed entry moments
  for arbitrary independent centered symmetric Beta partial correlations.
* `TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure`,
  `TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure`, and
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure`: `Lᵖ` membership, integrability,
  and finite multinomial Beta-quotient evaluation of arbitrary natural mixed entry moments under
  `TauCeti.Probability.lkjMeasure`.
* `TauCeti.Probability.integral_prod_pow_partialCorrelationGram_pi_eq_zero_of_odd` and
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd`: vanishing of mixed
  moments whenever some coordinate axis has odd total degree.
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_of_diag` and
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_of_le_one`: diagonal-only and
  low-dimensional mixed moments equal one.
* `TauCeti.Probability.integral_pow_coe_apply_lkjMeasure_of_ne`,
  `TauCeti.Probability.integral_pow_coe_apply_self_lkjMeasure`, and
  `TauCeti.Probability.integral_mul_mul_coe_apply_lkjMeasure`: closed-form single-entry natural
  moments and the positive joint 3-cycle moment `1 / (2 * η + p - 1) ^ 2`.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace TauCeti.Probability

/-! ### Partial-correlation Gram mixed moments -/

/-- Under independent centered symmetric Beta partial correlations with positive shapes, every
natural monomial in the entries of `partialCorrelationGram` belongs to every `Lᵠ`, including
`L∞`. -/
theorem memLp_prod_pow_partialCorrelationGram_pi_betaMeasure {p : ℕ}
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun z ↦ ∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab) q
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  have hm : Measurable fun z : strictLowerTriangle p → ℝ ↦
      ∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab :=
    Finset.measurable_fun_prod _ fun ab _ ↦
      (((continuous_apply ab.2).comp ((continuous_apply ab.1).comp
        continuous_partialCorrelationGram)).measurable.pow_const (n ab))
  refine MemLp.of_bound hm.aestronglyMeasurable 1 ?_
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  have hz' : ∀ ij, |z ij| ≤ 1 := fun ij ↦ (hz ij).le
  rw [Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun ab _ ↦ ?_
  rw [abs_pow]
  refine pow_le_one₀ (abs_nonneg _) ?_
  simpa only [Real.norm_eq_abs] using
    (posSemidef_partialCorrelationGram z).norm_le_one_of_apply_self_eq_one
      (partialCorrelationGram_apply_self hz' ab.1) (partialCorrelationGram_apply_self hz' ab.2)

/-- Under independent centered symmetric Beta partial correlations with positive shapes, every
natural monomial in the entries of `partialCorrelationGram` is integrable. -/
theorem integrable_prod_pow_partialCorrelationGram_pi_betaMeasure {p : ℕ}
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun z ↦ ∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) :=
  memLp_one_iff_integrable.mp (memLp_prod_pow_partialCorrelationGram_pi_betaMeasure ha n 1)

/-- Almost everywhere under independent centered symmetric Beta laws, a natural monomial in the
entries of `partialCorrelationGram` equals a finite multinomial sum of coordinatewise products of
natural partial-correlation powers and nonnegative half-integer powers of `1 - z ij ^ 2`. -/
theorem prod_pow_partialCorrelationGram_ae_eq_sum_prod_pi_betaMeasure {p : ℕ}
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    (fun z ↦ ∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab) =ᵐ[
      Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)]
      fun z ↦
        ∑ K ∈ Fintype.piFinset (fun ab : Fin p × Fin p ↦
            Finset.piAntidiag (Finset.Iic (min ab.1 ab.2)) (n ab)),
          (∏ ab, (Nat.multinomial Finset.univ (K ab) : ℝ)) *
            ∏ ij : strictLowerTriangle p,
              z ij ^ partialCorrelationGramCholeskyPower K ij.1 *
                (1 - z ij ^ 2) ^
                  partialCorrelationCholeskyMonomialResidualPower
                    (partialCorrelationGramCholeskyPower K) ij := by
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  exact prod_pow_partialCorrelationGram_eq_sum_prod (fun ij ↦ (hz ij).le) n

/-- Natural mixed entry moments of `partialCorrelationGram` under independent centered symmetric
Beta partial correlations with positive shapes. Each multinomial summand factors into weighted
one-dimensional Beta quotients and vanishes whenever any induced strict-lower coordinate power is
odd. -/
theorem integral_prod_pow_partialCorrelationGram_pi_betaMeasure {p : ℕ}
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    ∫ z, ∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      ∑ K ∈ Fintype.piFinset (fun ab : Fin p × Fin p ↦
          Finset.piAntidiag (Finset.Iic (min ab.1 ab.2)) (n ab)),
        (∏ ab, (Nat.multinomial Finset.univ (K ab) : ℝ)) *
          ∏ ij : strictLowerTriangle p,
            if Even (partialCorrelationGramCholeskyPower K ij.1) then
              beta (((partialCorrelationGramCholeskyPower K ij.1 : ℝ) + 1) / 2)
                  (a ij + partialCorrelationCholeskyMonomialResidualPower
                    (partialCorrelationGramCholeskyPower K) ij) /
                beta (1 / 2) (a ij)
            else 0 := by
  simp_rw [prod_pow_partialCorrelationGram_eq_sum_prod_pow_partialCorrelationCholesky]
  rw [integral_finsetSum _ fun K _ ↦
    (integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha _).const_mul _]
  refine Finset.sum_congr rfl fun K hK ↦ ?_
  rw [integral_const_mul, integral_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha,
    ite_eq_left fun _ ↦ partialCorrelationGramCholeskyPower_le_of_mem_piFinset hK]

/-! ### Integrability and evaluation of LKJ mixed entry moments -/

/-- Every natural monomial in the entries of an LKJ matrix belongs to every `Lᵖ`, including
`L∞`. The exponent is indexed by all ordered pairs; this permits arbitrary mixed moments while
retaining the matrix-shaped API used by callers. -/
theorem memLp_prod_pow_coe_apply_lkjMeasure (p : ℕ) (η : ℝ)
    (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) q (lkjMeasure p η) := by
  classical
  by_cases hη : 0 < η
  · let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
    refine MemLp.of_bound (Finset.measurable_fun_prod _ fun ij _ ↦
      ((selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const (n ij))).aestronglyMeasurable 1 ?_
    filter_upwards [ae_posDef_lkjMeasure p η, ae_diag_eq_one_lkjMeasure p η] with R hR hdiag
    rw [Real.norm_eq_abs, Finset.abs_prod]
    apply Finset.prod_le_one₀
    · intro ij _
      positivity
    · intro ij _
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hR.posSemidef.norm_le_one_of_apply_self_eq_one
        (hdiag ij.1) (hdiag ij.2))
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- Every natural mixed entry moment of an LKJ matrix is integrable. This includes the zeroth
mixed moment and all invalid nonpositive shapes, where the measure is zero. -/
theorem integrable_prod_pow_coe_apply_lkjMeasure (p : ℕ) (η : ℝ)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) (lkjMeasure p η) :=
  memLp_one_iff_integrable.mp (memLp_prod_pow_coe_apply_lkjMeasure p η n 1)

/-- **Natural mixed entry moments of the LKJ law.** For `0 < η` and any ordered-pair exponent
multi-index `n`, the mixed entry moment `E[∏ ab, R ab.1 ab.2 ^ n ab]` under `lkjMeasure p η` is a
finite multinomial sum of products of Beta quotients at the column-dependent partial-correlation
shapes `lkjPartialCorrelationShape p η`. -/
theorem integral_prod_pow_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂lkjMeasure p η =
      ∑ K ∈ Fintype.piFinset (fun ab : Fin p × Fin p ↦
          Finset.piAntidiag (Finset.Iic (min ab.1 ab.2)) (n ab)),
        (∏ ab, (Nat.multinomial Finset.univ (K ab) : ℝ)) *
          ∏ ij : strictLowerTriangle p,
            if Even (partialCorrelationGramCholeskyPower K ij.1) then
              beta (((partialCorrelationGramCholeskyPower K ij.1 : ℝ) + 1) / 2)
                  (lkjPartialCorrelationShape p η ij +
                    partialCorrelationCholeskyMonomialResidualPower
                      (partialCorrelationGramCholeskyPower K) ij) /
                beta (1 / 2) (lkjPartialCorrelationShape p η ij)
            else 0 := by
  have hm : Measurable fun M : Matrix (Fin p) (Fin p) ℝ ↦ ∏ ab, M ab.1 ab.2 ^ n ab :=
    Finset.measurable_fun_prod _ fun ab _ ↦ Matrix.measurable_apply.pow_const (n ab)
  rw [← integral_map (f := fun M : Matrix (Fin p) (Fin p) ℝ ↦ ∏ ab, M ab.1 ab.2 ^ n ab)
      measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable,
    map_coe_lkjMeasure hη,
    integral_map continuous_partialCorrelationGram.measurable.aemeasurable hm.aestronglyMeasurable]
  exact integral_prod_pow_partialCorrelationGram_pi_betaMeasure (lkjPartialCorrelationShape_pos hη)
    n

/-! ### Parity vanishing and diagonal / low-dimensional reductions -/

private theorem prod_pow_sign_mul {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (s : Fin p → ℝ)
    (n : Fin p × Fin p → ℕ) :
    (∏ ab : Fin p × Fin p, (s ab.1 * M ab.1 ab.2 * s ab.2) ^ n ab) =
      (∏ a : Fin p, s a ^ ∑ b : Fin p, (n (a, b) + n (b, a))) *
        ∏ ab : Fin p × Fin p, M ab.1 ab.2 ^ n ab := by
  have heq (ab : Fin p × Fin p) :
      (s ab.1 * M ab.1 ab.2 * s ab.2) ^ n ab =
        (s ab.1 ^ n ab * s ab.2 ^ n ab) * M ab.1 ab.2 ^ n ab := by
    ring
  simp_rw [heq, Finset.prod_mul_distrib]
  congr 1
  have h1 :
      (∏ ab : Fin p × Fin p, s ab.1 ^ n ab) = ∏ a : Fin p, s a ^ ∑ b : Fin p, n (a, b) := by
    rw [Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun a _ ↦
      Finset.prod_pow_eq_pow_sum Finset.univ (fun b ↦ n (a, b)) (s a)
  have h2 :
      (∏ ab : Fin p × Fin p, s ab.2 ^ n ab) = ∏ a : Fin p, s a ^ ∑ b : Fin p, n (b, a) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    exact Finset.prod_congr rfl fun a _ ↦
      Finset.prod_pow_eq_pow_sum Finset.univ (fun b ↦ n (b, a)) (s a)
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [← pow_add, Finset.sum_add_distrib]

private theorem prod_pow_sign_single_odd {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    {n : Fin p × Fin p → ℕ} {i : Fin p} (hodd : Odd (∑ j, (n (i, j) + n (j, i)))) :
    (∏ ab : Fin p × Fin p,
        ((if ab.1 = i then (-1 : ℝ) else 1) * M ab.1 ab.2 *
          (if ab.2 = i then (-1 : ℝ) else 1)) ^ n ab) =
      -(∏ ab : Fin p × Fin p, M ab.1 ab.2 ^ n ab) := by
  rw [prod_pow_sign_mul M (fun k ↦ if k = i then (-1 : ℝ) else 1) n]
  have hsign :
      (∏ a : Fin p, (if a = i then (-1 : ℝ) else 1) ^ ∑ b : Fin p, (n (a, b) + n (b, a))) =
        -1 := by
    rw [Fintype.prod_eq_single i]
    · simp [hodd.neg_one_pow]
    · intro a ha
      simp [ha]
  rw [hsign, neg_one_mul]

/-- Under arbitrary sigma-finite negation-invariant partial-correlation marginals, any entry
monomial of `partialCorrelationGram` in which some coordinate axis `i` has odd total degree
`∑ j, (n (i, j) + n (j, i))` has zero integral (using totalized Bochner integrals when not
integrable). -/
theorem integral_prod_pow_partialCorrelationGram_pi_eq_zero_of_odd {p : ℕ}
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, SigmaFinite (μ ij)]
    [∀ ij, (μ ij).IsNegInvariant] {n : Fin p × Fin p → ℕ} {i : Fin p}
    (hodd : Odd (∑ j, (n (i, j) + n (j, i)))) :
    ∫ z, ∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab ∂Measure.pi μ = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by by_cases hk : k = i <;> simp [s, hk]
  have hm : Measurable fun M : Matrix (Fin p) (Fin p) ℝ ↦ ∏ ab, M ab.1 ab.2 ^ n ab :=
    Finset.measurable_fun_prod _ fun ab _ ↦ Matrix.measurable_apply.pow_const (n ab)
  have hsign : Measurable fun R : Matrix (Fin p) (Fin p) ℝ ↦
      Matrix.of fun a b ↦ s a * R a b * s b := by fun_prop
  have h := congrArg (fun ν : Measure (Matrix (Fin p) (Fin p) ℝ) ↦
      ∫ R, ∏ ab, R ab.1 ab.2 ^ n ab ∂ν) (map_signChange_map_partialCorrelationGram_pi μ hs)
  rw [integral_map hsign.aemeasurable hm.aestronglyMeasurable] at h
  simp only [Matrix.of_apply, s, prod_pow_sign_single_odd _ hodd, integral_neg] at h
  have hzero : ∫ R, ∏ ab, R ab.1 ab.2 ^ n ab ∂((Measure.pi μ).map partialCorrelationGram) = 0 := by
    linarith
  rwa [integral_map continuous_partialCorrelationGram.measurable.aemeasurable
    hm.aestronglyMeasurable] at hzero

/-- **Parity vanishing of LKJ mixed moments.** Whenever some coordinate axis `i` has odd total
degree `∑ j, (n (i, j) + n (j, i))`, the corresponding mixed entry moment under `lkjMeasure p η`
vanishes. This holds for all dimensions and all real shapes `η`, including nonpositive shapes. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd {p : ℕ} {η : ℝ}
    {n : Fin p × Fin p → ℕ} {i : Fin p} (hodd : Odd (∑ j, (n (i, j) + n (j, i)))) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂lkjMeasure p η = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by by_cases hk : k = i <;> simp [s, hk]
  have hm : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab :=
    Finset.measurable_fun_prod _ fun ab _ ↦
      (selfAdjoint.measurable_coe_apply ab.1 ab.2).pow_const (n ab)
  have h := congrArg (fun ν : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ↦
      ∫ R, ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂ν)
    (map_symmetricCongruenceLinearMap_diagonal_lkjMeasure p η hs)
  rw [integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
    hm.aestronglyMeasurable] at h
  simp only [Matrix.coe_symmetricCongruenceLinearMap_diagonal_apply, s,
    prod_pow_sign_single_odd _ hodd, integral_neg] at h
  linarith

/-- At positive shape, any mixed entry moment supported on the diagonal equals one. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_of_diag {p : ℕ} {η : ℝ} (hη : 0 < η)
    {n : Fin p × Fin p → ℕ} (hdiag : ∀ ab, n ab ≠ 0 → ab.1 = ab.2) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂lkjMeasure p η = 1 := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  have hae :
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab) =ᵐ[lkjMeasure p η]
      fun _ ↦ 1 := by
    filter_upwards [ae_diag_eq_one_lkjMeasure p η] with R hR
    refine Finset.prod_eq_one fun ab _ ↦ ?_
    by_cases hab : n ab = 0
    · simp [hab]
    · rw [hdiag ab hab, hR ab.2, one_pow]
  rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]

/-- In dimensions zero and one, every natural mixed entry moment under a positive-shape LKJ law
equals one. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_of_le_one {p : ℕ} (hp : p ≤ 1) {η : ℝ}
    (hη : 0 < η) (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂lkjMeasure p η = 1 := by
  have : Subsingleton (Fin p) := Fin.subsingleton_iff_le_one.mpr hp
  exact integral_prod_pow_coe_apply_lkjMeasure_of_diag hη fun ab _ ↦ Subsingleton.elim ab.1 ab.2

/-! ### Closed-form single-entry and three-entry mixed moments -/

/-- **Natural moments of an off-diagonal LKJ entry.** For `0 < η` and `i ≠ j`, the `k`-th moment of
`R i j` under `lkjMeasure p η` vanishes at odd `k` and equals a single Beta quotient at even `k`,
with shape `η + (p - 2) / 2`. -/
theorem integral_pow_coe_apply_lkjMeasure_of_ne {p : ℕ} {η : ℝ} (hη : 0 < η)
    {i j : Fin p} (hij : i ≠ j) (k : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ^ k ∂lkjMeasure p η =
      if Even k then
        beta (((k : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  have hf : Function.Injective ![j, i] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (by simpa using Fintype.card_le_of_injective _ hf : 2 ≤ p)
  have hα : 0 < η + ((p : ℝ) - 2) / 2 := by linarith
  rw [← integral_map (f := fun x : ℝ ↦ x ^ k)
      (selfAdjoint.measurable_coe_apply i j).aemeasurable (by fun_prop),
    map_coe_apply_lkjMeasure_of_ne hη hij]
  simpa only [Real.rpow_zero, mul_one, add_zero] using
    integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure (r := 0) hα (by linarith) k

/-- For `0 < η`, every natural power of a diagonal entry under `lkjMeasure p η` has expectation
one. -/
theorem integral_pow_coe_apply_self_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (i : Fin p) (k : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i i ^ k ∂lkjMeasure p η = 1 := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  have hae :
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ) i i ^ k) =ᵐ[lkjMeasure p η] fun _ ↦ 1 := by
    filter_upwards [ae_diag_eq_one_lkjMeasure p η] with R hR
    rw [hR i, one_pow]
  rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]

private theorem integral_sq_map_centered_betaMeasure {a : ℝ} (ha : 0 < a) :
    ∫ x, x ^ 2 ∂((betaMeasure a a).map (fun t ↦ -1 + 2 * t)) = 1 / (2 * a + 1) := by
  have h := integral_id_betaMeasure (by norm_num : (0 : ℝ) < 1 / 2) ha
  rw [← betaMeasure_map_centered_sq, integral_map (by fun_prop) (by fun_prop)] at h
  rw [integral_map (by fun_prop) (by fun_prop)]
  convert h using 1
  field_simp
  ring

private theorem partialCorrelationCholesky_apply_zero_of_pos {p : ℕ}
    (z : strictLowerTriangle (p + 1) → ℝ) {i : Fin (p + 1)} (hi : 0 < i) :
    partialCorrelationCholesky z i 0 = z ⟨(i, 0), hi⟩ := by
  rw [partialCorrelationCholesky_apply_of_gt z hi]
  have hempty :
      (Finset.univ.filter fun ij : strictLowerTriangle (p + 1) ↦ ij.1.1 = i ∧ ij.1.2 < 0) = ∅ := by
    ext ij
    simp
  rw [hempty, Finset.prod_empty, mul_one]

private theorem prod_triangle_first_term (z : strictLowerTriangle 3 → ℝ) :
    partialCorrelationCholesky z 2 0 ^ 2 * partialCorrelationCholesky z 1 0 ^ 2 =
      ∏ ij : strictLowerTriangle 3,
        if ij = ⟨(2, 1), by decide⟩ then 1 else z ij ^ 2 := by
  have huniv :
      (Finset.univ : Finset (strictLowerTriangle 3)) =
        {⟨(1, 0), by decide⟩, ⟨(2, 0), by decide⟩, ⟨(2, 1), by decide⟩} := by
    ext ⟨⟨a, b⟩, hab⟩
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
  rw [partialCorrelationCholesky_apply_zero_of_pos z (by decide : (0 : Fin 3) < 2),
    partialCorrelationCholesky_apply_zero_of_pos z (by decide : (0 : Fin 3) < 1),
    huniv, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have hne10 : (⟨(1, 0), by decide⟩ : strictLowerTriangle 3) ≠ ⟨(2, 1), by decide⟩ := by decide
  have hne20 : (⟨(2, 0), by decide⟩ : strictLowerTriangle 3) ≠ ⟨(2, 1), by decide⟩ := by decide
  simp only [hne10, hne20, ↓reduceIte, mul_one]
  ring

private theorem prod_triangle_second_term (z : strictLowerTriangle 3 → ℝ) :
    partialCorrelationCholesky z 2 1 * partialCorrelationCholesky z 1 1 *
        partialCorrelationCholesky z 2 0 * partialCorrelationCholesky z 1 0 =
      ∏ q : Fin 3 × Fin 3,
        partialCorrelationCholesky z q.1 q.2 ^
          (if q = (2, 1) ∨ q = (1, 1) ∨ q = (2, 0) ∨ q = (1, 0) then 1 else 0) := by
  let s : Finset (Fin 3 × Fin 3) := {(2, 1), (1, 1), (2, 0), (1, 0)}
  have hsub :
      (∏ q : Fin 3 × Fin 3,
          partialCorrelationCholesky z q.1 q.2 ^
            (if q = (2, 1) ∨ q = (1, 1) ∨ q = (2, 0) ∨ q = (1, 0) then 1 else 0)) =
        ∏ q ∈ s,
          partialCorrelationCholesky z q.1 q.2 ^
            (if q = (2, 1) ∨ q = (1, 1) ∨ q = (2, 0) ∨ q = (1, 0) then 1 else 0) := by
    symm
    refine Finset.prod_subset (Finset.subset_univ _) fun q _ hq ↦ ?_
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hq
    rw [ite_eq_right hq, pow_zero]
  rw [hsub]
  dsimp only [s]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [true_or, or_true, ↓reduceIte, pow_one]
  ring

private theorem partialCorrelationGram_triangle_three_eq (z : strictLowerTriangle 3 → ℝ) :
    partialCorrelationGram z 2 1 * partialCorrelationGram z 2 0 *
        partialCorrelationGram z 1 0 =
      (∏ ij : strictLowerTriangle 3, if ij = ⟨(2, 1), by decide⟩ then 1 else z ij ^ 2) +
        ∏ q : Fin 3 × Fin 3,
          partialCorrelationCholesky z q.1 q.2 ^
            (if q = (2, 1) ∨ q = (1, 1) ∨ q = (2, 0) ∨ q = (1, 0) then 1 else 0) := by
  have hIic : (Finset.Iic (1 : Fin 3)) = {0, 1} := by decide
  have h21 : partialCorrelationGram z 2 1 =
      partialCorrelationCholesky z 2 0 * partialCorrelationCholesky z 1 0 +
        partialCorrelationCholesky z 2 1 * partialCorrelationCholesky z 1 1 := by
    rw [partialCorrelationGram_apply_eq_sum_Iic, hIic, Finset.sum_insert (by decide),
      Finset.sum_singleton]
  have h20 : partialCorrelationGram z 2 0 = partialCorrelationCholesky z 2 0 :=
    (partialCorrelationGram_apply_zero_of_pos z (by decide : (0 : Fin 3) < 2)).trans
      (partialCorrelationCholesky_apply_zero_of_pos z (by decide : (0 : Fin 3) < 2)).symm
  have h10 : partialCorrelationGram z 1 0 = partialCorrelationCholesky z 1 0 :=
    (partialCorrelationGram_apply_zero_of_pos z (by decide : (0 : Fin 3) < 1)).trans
      (partialCorrelationCholesky_apply_zero_of_pos z (by decide : (0 : Fin 3) < 1)).symm
  rw [h21, h20, h10, ← prod_triangle_first_term z, ← prod_triangle_second_term z]
  ring

private theorem integral_triangle_first_term_three {η : ℝ} (hη : 0 < η) :
    ∫ z : strictLowerTriangle 3 → ℝ,
        (∏ ij : strictLowerTriangle 3, if ij = ⟨(2, 1), by decide⟩ then 1 else z ij ^ 2)
      ∂(Measure.pi fun ij : strictLowerTriangle 3 ↦
        (betaMeasure (lkjPartialCorrelationShape 3 η ij)
          (lkjPartialCorrelationShape 3 η ij)).map (fun x ↦ -1 + 2 * x)) =
      1 / (2 * η + 2) ^ 2 := by
  let _ (ij : strictLowerTriangle 3) : IsProbabilityMeasure
      ((betaMeasure (lkjPartialCorrelationShape 3 η ij)
        (lkjPartialCorrelationShape 3 η ij)).map (fun x ↦ -1 + 2 * x)) := by
    let _ := isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
    infer_instance
  let u₂₁ : strictLowerTriangle 3 := ⟨(2, 1), by decide⟩
  rw [integral_fintype_prod_eq_prod
    (f := fun (ij : strictLowerTriangle 3) (x : ℝ) ↦ if ij = u₂₁ then 1 else x ^ 2)]
  have huniv :
      (Finset.univ : Finset (strictLowerTriangle 3)) =
        {⟨(1, 0), by decide⟩, ⟨(2, 0), by decide⟩, u₂₁} := by
    ext ⟨⟨a, b⟩, hab⟩
    fin_cases a <;> fin_cases b <;> simp [u₂₁] at hab ⊢
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have hne10 : (⟨(1, 0), by decide⟩ : strictLowerTriangle 3) ≠ u₂₁ := by decide
  have hne20 : (⟨(2, 0), by decide⟩ : strictLowerTriangle 3) ≠ u₂₁ := by decide
  simp only [hne10, hne20, ↓reduceIte, integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [integral_sq_map_centered_betaMeasure
      (lkjPartialCorrelationShape_pos hη ⟨(1, 0), by decide⟩),
    integral_sq_map_centered_betaMeasure
      (lkjPartialCorrelationShape_pos hη ⟨(2, 0), by decide⟩)]
  simp only [lkjPartialCorrelationShape_eq, Fin.val_zero]
  norm_num
  field_simp
  ring

private theorem integral_triangle_lkjMeasure_three {η : ℝ} (hη : 0 < η) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ),
        (R : Matrix (Fin 3) (Fin 3) ℝ) 2 1 * (R : Matrix (Fin 3) (Fin 3) ℝ) 2 0 *
          (R : Matrix (Fin 3) (Fin 3) ℝ) 1 0 ∂lkjMeasure 3 η =
      1 / (2 * η + 2) ^ 2 := by
  let μ : strictLowerTriangle 3 → Measure ℝ := fun ij ↦
    (betaMeasure (lkjPartialCorrelationShape 3 η ij)
      (lkjPartialCorrelationShape 3 η ij)).map (fun x ↦ -1 + 2 * x)
  let _ (ij : strictLowerTriangle 3) : IsProbabilityMeasure (μ ij) := by
    let _ := isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
      (lkjPartialCorrelationShape_pos hη ij)
    infer_instance
  let u₂₁ : strictLowerTriangle 3 := ⟨(2, 1), by decide⟩
  let m₂ : Fin 3 × Fin 3 → ℕ :=
    fun q ↦ if q = (2, 1) ∨ q = (1, 1) ∨ q = (2, 0) ∨ q = (1, 0) then 1 else 0
  have hm : Measurable fun M : Matrix (Fin 3) (Fin 3) ℝ ↦ M 2 1 * M 2 0 * M 1 0 :=
    (Matrix.measurable_apply.mul Matrix.measurable_apply).mul Matrix.measurable_apply
  rw [← integral_map (f := fun M : Matrix (Fin 3) (Fin 3) ℝ ↦ M 2 1 * M 2 0 * M 1 0)
      measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable,
    map_coe_lkjMeasure hη,
    integral_map continuous_partialCorrelationGram.measurable.aemeasurable hm.aestronglyMeasurable]
  simp_rw [partialCorrelationGram_triangle_three_eq]
  have hint1 : Integrable
      (fun z : strictLowerTriangle 3 → ℝ ↦
        ∏ ij : strictLowerTriangle 3, if ij = u₂₁ then 1 else z ij ^ 2)
      (Measure.pi μ) := by
    refine Integrable.fintype_prod
      (f := fun (ij : strictLowerTriangle 3) (x : ℝ) ↦ if ij = u₂₁ then 1 else x ^ 2) fun ij ↦ ?_
    by_cases hij : ij = u₂₁
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      have ha := lkjPartialCorrelationShape_pos (p := 3) hη ij
      exact ((integrable_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure_iff (r := 0) ha 2).2
        (by linarith)).congr (by simp)
  have hint2 : Integrable
      (fun z : strictLowerTriangle 3 → ℝ ↦
        ∏ q : Fin 3 × Fin 3, partialCorrelationCholesky z q.1 q.2 ^ m₂ q) (Measure.pi μ) :=
    integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure
      (lkjPartialCorrelationShape_pos hη) m₂
  rw [integral_add hint1 hint2]
  have hzero :
      (∫ z, ∏ q : Fin 3 × Fin 3, partialCorrelationCholesky z q.1 q.2 ^ m₂ q ∂Measure.pi μ) =
        0 := by
    rw [integral_prod_pow_partialCorrelationCholesky_pi_betaMeasure
      (lkjPartialCorrelationShape_pos hη) m₂]
    split_ifs with hle
    · refine Finset.prod_eq_zero (Finset.mem_univ u₂₁) ?_
      simp [u₂₁, m₂]
    · rfl
  rw [hzero, add_zero]
  exact integral_triangle_first_term_three hη

/-- **Joint three-entry triangle moment of the LKJ law.** For `0 < η` and pairwise distinct indices
`i, j, k : Fin p`, the mixed moment `E[R i j * R i k * R j k]` equals `1 / (2 * η + p - 1) ^ 2`.
In particular, although distinct off-diagonal correlation entries have covariance zero, any three
entries forming a triangle have strictly positive joint third moment. -/
theorem integral_mul_mul_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    {i j k : Fin p} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j * (R : Matrix (Fin p) (Fin p) ℝ) i k *
          (R : Matrix (Fin p) (Fin p) ℝ) j k ∂lkjMeasure p η =
      1 / (2 * η + p - 1) ^ 2 := by
  have hf : Function.Injective ![k, j, i] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hp3 : (3 : ℝ) ≤ p := by
    exact_mod_cast (by simpa using Fintype.card_le_of_injective _ hf : 3 ≤ p)
  have hη' : 0 < η + ((p : ℝ) - 3) / 2 := by linarith
  have hm3 : Measurable fun B : selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) ↦
      (B : Matrix (Fin 3) (Fin 3) ℝ) 2 1 * (B : Matrix (Fin 3) (Fin 3) ℝ) 2 0 *
        (B : Matrix (Fin 3) (Fin 3) ℝ) 1 0 :=
    ((selfAdjoint.measurable_coe_apply 2 1).mul (selfAdjoint.measurable_coe_apply 2 0)).mul
      (selfAdjoint.measurable_coe_apply 1 0)
  let S := Matrix.symmetricCongruenceLinearMap
    ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix ![k, j, i] id)
  have hcomp (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      (R : Matrix (Fin p) (Fin p) ℝ) i j * (R : Matrix (Fin p) (Fin p) ℝ) i k *
          (R : Matrix (Fin p) (Fin p) ℝ) j k =
        (S R : Matrix (Fin 3) (Fin 3) ℝ) 2 1 * (S R : Matrix (Fin 3) (Fin 3) ℝ) 2 0 *
          (S R : Matrix (Fin 3) (Fin 3) ℝ) 1 0 := by
    simp only [S, Matrix.coe_symmetricCongruenceLinearMap_apply,
      Matrix.transpose_submatrix, Matrix.transpose_one,
      Matrix.submatrix_one_mul_mul_submatrix_one]
    simp
  simp_rw [hcomp]
  rw [← integral_map (f := fun B : selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) ↦
        (B : Matrix (Fin 3) (Fin 3) ℝ) 2 1 * (B : Matrix (Fin 3) (Fin 3) ℝ) 2 0 *
          (B : Matrix (Fin 3) (Fin 3) ℝ) 1 0)
      (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hm3.aestronglyMeasurable,
    map_symmetricCongruenceLinearMap_submatrix_one_lkjMeasure ![k, j, i] hf hη]
  -- `![k, j, i]` has block dimension elaborated as `Nat.succ (Nat.succ (Nat.succ 0))`.
  have h3 : (Nat.succ (Nat.succ (Nat.succ 0)) : ℝ) = 3 := by norm_num
  rw [h3, integral_triangle_lkjMeasure_three hη']
  congr 2
  ring

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ} {η : ℝ}
  {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- Every natural entry monomial of a random matrix with LKJ law belongs to every `Lᵠ`, including
`L∞`. -/
theorem memLp_prod_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (lkjMeasure p η) P) (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun ω ↦ ∏ ab, (X ω : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab) q P := by
  have hm : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab :=
    Finset.measurable_fun_prod _ fun ab _ ↦
      (selfAdjoint.measurable_coe_apply ab.1 ab.2).pow_const (n ab)
  refine (memLp_map_measure_iff hm.aestronglyMeasurable hX.aemeasurable).mp ?_
  rw [hX.map_eq]
  exact TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure p η n q

/-- Every natural mixed entry moment of a random matrix with LKJ law is integrable. -/
theorem integrable_prod_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (lkjMeasure p η) P) (n : Fin p × Fin p → ℕ) :
    Integrable (fun ω ↦ ∏ ab, (X ω : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure p η n)

/-- Natural mixed entry moments of a random matrix with positive-shape LKJ law. -/
theorem integral_prod_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (lkjMeasure p η) P) (hη : 0 < η) (n : Fin p × Fin p → ℕ) :
    ∫ ω, ∏ ab, (X ω : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂P =
      ∑ K ∈ Fintype.piFinset (fun ab : Fin p × Fin p ↦
          Finset.piAntidiag (Finset.Iic (min ab.1 ab.2)) (n ab)),
        (∏ ab, (Nat.multinomial Finset.univ (K ab) : ℝ)) *
          ∏ ij : strictLowerTriangle p,
            if Even (partialCorrelationGramCholeskyPower K ij.1) then
              beta (((partialCorrelationGramCholeskyPower K ij.1 : ℝ) + 1) / 2)
                  (lkjPartialCorrelationShape p η ij +
                    partialCorrelationCholeskyMonomialResidualPower
                      (partialCorrelationGramCholeskyPower K) ij) /
                beta (1 / 2) (lkjPartialCorrelationShape p η ij)
            else 0 := by
  have hm : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab :=
    Finset.measurable_fun_prod _ fun ab _ ↦
      (selfAdjoint.measurable_coe_apply ab.1 ab.2).pow_const (n ab)
  rw [← Function.comp_def
      (f := fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab),
    hX.integral_comp hm.aestronglyMeasurable,
    TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure hη n]

/-- For a random matrix with LKJ law, any mixed entry moment in which some coordinate axis has odd
total degree vanishes. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd
    (hX : HasLaw X (lkjMeasure p η) P) {n : Fin p × Fin p → ℕ} {i : Fin p}
    (hodd : Odd (∑ j, (n (i, j) + n (j, i)))) :
    ∫ ω, ∏ ab, (X ω : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂P = 0 := by
  have hm : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab :=
    Finset.measurable_fun_prod _ fun ab _ ↦
      (selfAdjoint.measurable_coe_apply ab.1 ab.2).pow_const (n ab)
  rw [← Function.comp_def
      (f := fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab),
    hX.integral_comp hm.aestronglyMeasurable,
    TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd hodd]

end ProbabilityTheory.HasLaw
