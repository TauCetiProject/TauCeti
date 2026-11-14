/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Probability.Distributions.LKJ.CoordinateIntegral
public import TauCeti.Analysis.Matrix.PartialCorrelation.Powers
public import TauCeti.Probability.Distributions.Beta.Reflection
public import Mathlib.Probability.Distributions.Beta
import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.Probability.Distributions.Beta.Symmetric
import TauCeti.Probability.Distributions.LKJ.Cholesky.Moments
import TauCeti.Probability.Distributions.LKJ.Marginal
import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
import TauCeti.Probability.Distributions.LKJ.Symmetry

/-!
# Mixed entry moments of LKJ correlation matrices

Every natural monomial `∏ q, R q.1 q.2 ^ n q` in the entries of an LKJ correlation matrix belongs
to every `Lᵖ`, including `L∞`, because positive-semidefiniteness and unit diagonal bound every
matrix entry in absolute value by one. For positive shape `η`, representing the LKJ law as the
Gram pushforward `partialCorrelationGram` of independent centered symmetric Beta partial
correlations (`TauCeti.Probability.map_coe_lkjMeasure`) and expanding `R = L * Lᵀ` through
`TauCeti.prod_pow_partialCorrelationGram_eq_sum` evaluates every mixed entry moment as a finite
multinomial sum of products of Beta quotients.

The expansion covers repeated symmetric entries, diagonal powers, and dimensions zero and one.
Diagonal exponents leave mixed moments unchanged, relabelling rows and columns by a permutation
preserves mixed moments, and any vertex `i` of odd symmetric degree `∑ j, (n (i, j) + n (j, i))`
forces the mixed moment to vanish by diagonal sign invariance. Specializing to a single entry gives
closed Beta-quotient moments of all natural orders.

## Main results

* `TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure` and
  `TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure`: `Lᵖ` membership and integrability
  of all natural mixed entry monomials under `lkjMeasure p η`;
* `TauCeti.Probability.integral_prod_pow_partialCorrelationGram_pi_betaMeasure`: mixed entry
  moments of `partialCorrelationGram` under independent centered symmetric Beta partial
  correlations with arbitrary positive shapes;
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure`: closed finite multinomial
  Beta-quotient evaluation of all natural mixed entry moments under `lkjMeasure p η` for `0 < η`;
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_prod_ne`,
  `TauCeti.Probability.integral_prod_pow_coe_apply_perm_lkjMeasure`, and
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd`: diagonal-exponent
  invariance, permutation invariance, and odd-degree vanishing of mixed moments;
* `TauCeti.Probability.integral_pow_coe_apply_lkjMeasure_of_ne` and
  `TauCeti.Probability.integral_pow_coe_apply_lkjMeasure`: single-entry moments of all natural
  orders;
* `ProbabilityTheory.HasLaw.integral_prod_pow_coe_apply_lkjMeasure` and companions: transfers to
  random matrices with LKJ law.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Matrix

namespace TauCeti.Probability

/-! ### Integrability and `Lᵖ` bounds -/

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

/-- Every natural power of a single entry of an LKJ matrix belongs to every `Lᵖ`, including
`L∞`. -/
theorem memLp_pow_coe_apply_lkjMeasure {p : ℕ} (η : ℝ) (i j : Fin p) (m : ℕ) (q : ℝ≥0∞) :
    MemLp (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m) q (lkjMeasure p η) := by
  classical
  have hsingle (M : Matrix (Fin p) (Fin p) ℝ) :
      (∏ ij : Fin p × Fin p, M ij.1 ij.2 ^ Pi.single (i, j) m ij) = M i j ^ m := by
    conv_rhs => rw [← Pi.single_eq_same (M := fun _ : Fin p × Fin p ↦ ℕ) (i, j) m]
    exact Fintype.prod_eq_single (i, j) fun ij hij ↦ by simp [Pi.single_eq_of_ne hij]
  simpa only [hsingle] using
    memLp_prod_pow_coe_apply_lkjMeasure p η (Pi.single (i, j) m) q

/-- Every natural power of a single entry of an LKJ matrix is integrable. -/
theorem integrable_pow_coe_apply_lkjMeasure {p : ℕ} (η : ℝ) (i j : Fin p) (m : ℕ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m) (lkjMeasure p η) :=
  memLp_one_iff_integrable.mp (memLp_pow_coe_apply_lkjMeasure η i j m 1)

/-! ### Independent centered-Beta Gram mixed moments -/

section PartialCorrelationGram

variable {p : ℕ}

/-- Every natural mixed entry monomial of `partialCorrelationGram` belongs to every `Lᵖ` (including
`L∞`) under independent centered symmetric Beta partial correlations with positive shapes. -/
theorem memLp_prod_pow_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun z ↦ ∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij) q
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  refine MemLp.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  have hz' : ∀ ij, |z ij| ≤ 1 := fun ij ↦ (hz ij).le
  rw [Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun ij _ ↦ ?_
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _)
    ((posSemidef_partialCorrelationGram z).norm_le_one_of_apply_self_eq_one
      (partialCorrelationGram_apply_self hz' ij.1) (partialCorrelationGram_apply_self hz' ij.2))

/-- Every natural mixed entry monomial of `partialCorrelationGram` is integrable under independent
centered symmetric Beta partial correlations with positive shapes. -/
theorem integrable_prod_pow_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun z ↦ ∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) :=
  memLp_one_iff_integrable.mp
    (memLp_prod_pow_partialCorrelationGram_pi_betaMeasure ha n 1)

/-- Under independent centered symmetric Beta partial correlations, a mixed natural monomial in
`partialCorrelationGram` agrees almost everywhere with its multinomial expansion into coordinate
and residual powers. -/
theorem prod_pow_partialCorrelationGram_ae_eq_sum_prod_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    (fun z ↦ ∏ q, partialCorrelationGram z q.1 q.2 ^ n q) =ᵐ[
      Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)]
      fun z ↦ ∑ c ∈ Fintype.piFinset
          (fun q : Fin p × Fin p ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij, z ij ^ gramFactorMultiIndex c ij.1 *
            (1 - z ij ^ 2) ^
              partialCorrelationCholeskyMonomialResidualPower (gramFactorMultiIndex c) ij := by
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  exact prod_pow_partialCorrelationGram_eq_sum_prod (fun ij ↦ (hz ij).le) n

/-- **Mixed entry moments of the independent centered-Beta Gram construction.** Expanding
`partialCorrelationGram z = L * Lᵀ` over column compositions supported on `Finset.Iic (min q.1 q.2)`
and integrating each Cholesky monomial coordinatewise evaluates every natural mixed entry moment as
a finite multinomial sum of products of Beta quotients. -/
theorem integral_prod_pow_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    ∫ z, (∏ q, partialCorrelationGram z q.1 q.2 ^ n q)
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      ∑ c ∈ Fintype.piFinset
          (fun q : Fin p × Fin p ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij, if Even (gramFactorMultiIndex c ij.1) then
            beta (((gramFactorMultiIndex c ij.1 : ℝ) + 1) / 2)
                (a ij + partialCorrelationCholeskyMonomialResidualPower
                  (gramFactorMultiIndex c) ij) /
              beta (1 / 2) (a ij)
          else 0 := by
  simp_rw [prod_pow_partialCorrelationGram_eq_sum]
  rw [integral_finsetSum _ fun c _ ↦
    (integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha
      (gramFactorMultiIndex c)).const_mul _]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [integral_const_mul, integral_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha,
    ite_eq_left fun _ ↦ le_of_gramFactorMultiIndex_ne_zero hc]

/-- For a Gram law built from independent sigma-finite negation-invariant partial correlations,
any vertex `i` whose symmetric exponent sum `∑ j, (n (i, j) + n (j, i))` is odd forces the mixed
entry moment `∫ R, (∏ q, R q.1 q.2 ^ n q)` to vanish. -/
theorem integral_prod_pow_apply_map_partialCorrelationGram_pi_eq_zero_of_odd
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, SigmaFinite (μ ij)]
    [∀ ij, (μ ij).IsNegInvariant] {n : Fin p × Fin p → ℕ} {i : Fin p}
    (hi : Odd (∑ j : Fin p, (n (i, j) + n (j, i)))) :
    ∫ R : Matrix (Fin p) (Fin p) ℝ, (∏ q, R q.1 q.2 ^ n q)
      ∂((Measure.pi μ).map partialCorrelationGram) = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by by_cases hk : k = i <;> simp [s, hk]
  have hmeas : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦ ∏ q, R q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦
      (Matrix.measurable_apply (i := q.1) (j := q.2)).pow_const _
  have h := congrArg (fun ν : Measure (Matrix (Fin p) (Fin p) ℝ) ↦ ∫ R, (∏ q, R q.1 q.2 ^ n q) ∂ν)
    (map_signChange_map_partialCorrelationGram_pi μ hs)
  rw [integral_map
    (by fun_prop : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦
      Matrix.of fun i j ↦ s i * R i j * s j)).aemeasurable
    hmeas.aestronglyMeasurable] at h
  have hsign (R : Matrix (Fin p) (Fin p) ℝ) :
      (∏ q : Fin p × Fin p,
        (Matrix.of (fun a b ↦ s a * R a b * s b)) q.1 q.2 ^ n q) =
        -(∏ q, R q.1 q.2 ^ n q) := by
    simp only [Matrix.of_apply]
    rw [Matrix.prod_pow_mul_apply_mul R s n]
    have hprod : (∏ r : Fin p, s r ^ ∑ j : Fin p, (n (r, j) + n (j, r))) = -1 := by
      rw [Fintype.prod_eq_single i]
      · simp [s, hi.neg_one_pow]
      · intro r hr
        simp [s, hr]
    rw [hprod, neg_one_mul]
  simp_rw [hsign, integral_neg] at h
  linarith

end PartialCorrelationGram

/-! ### Mixed and single-entry moments of `lkjMeasure` -/

/-- **Mixed entry moments of an LKJ correlation matrix.** For positive shape `η`, every natural
mixed entry moment `∫ R, (∏ q, R q.1 q.2 ^ n q) ∂lkjMeasure p η` equals the finite multinomial sum
over lower-triangular column compositions of products of Beta quotients at the LKJ
partial-correlation shapes `lkjPartialCorrelationShape p η`. This includes repeated entries,
diagonal powers, and dimensions zero and one. -/
theorem integral_prod_pow_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η =
      ∑ c ∈ Fintype.piFinset
          (fun q : Fin p × Fin p ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij : strictLowerTriangle p, if Even (gramFactorMultiIndex c ij.1) then
            beta (((gramFactorMultiIndex c ij.1 : ℝ) + 1) / 2)
                (lkjPartialCorrelationShape p η ij +
                  partialCorrelationCholeskyMonomialResidualPower (gramFactorMultiIndex c) ij) /
              beta (1 / 2) (lkjPartialCorrelationShape p η ij)
          else 0 := by
  let g : Matrix (Fin p) (Fin p) ℝ → ℝ := fun M ↦ ∏ q, M q.1 q.2 ^ n q
  have hg : Continuous g := by fun_prop
  rw [← integral_map (f := g) measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable,
    map_coe_lkjMeasure hη,
    integral_map continuous_partialCorrelationGram.measurable.aemeasurable hg.aestronglyMeasurable]
  exact integral_prod_pow_partialCorrelationGram_pi_betaMeasure
    (lkjPartialCorrelationShape_pos hη) n

/-- Diagonal exponents do not change mixed entry moments under `lkjMeasure`, since diagonal entries
are almost surely one (and for nonpositive shapes the measure is zero). -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_prod_ne {p : ℕ} (η : ℝ)
    (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η =
      ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q with q.1 ≠ q.2, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q)
          ∂lkjMeasure p η := by
  by_cases hη : 0 < η
  · refine integral_congr_ae ?_
    filter_upwards [ae_diag_eq_one_lkjMeasure p η] with R hdiag
    symm
    refine Finset.prod_subset (Finset.subset_univ _) fun q _ hq ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff] at hq
    rw [hq, hdiag q.2, one_pow]
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- Mixed entry moments of an LKJ matrix are invariant under simultaneous row-and-column
permutations. -/
theorem integral_prod_pow_coe_apply_perm_lkjMeasure {p : ℕ} (η : ℝ)
    (σ : Equiv.Perm (Fin p)) (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) (σ q.1) (σ q.2) ^ n q) ∂lkjMeasure p η =
      ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η := by
  have hmeas : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦
      (selfAdjoint.measurable_coe_apply q.1 q.2).pow_const (n q)
  have h := congrArg
    (fun ν : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ↦
      ∫ R, (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂ν)
    (map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure p η σ)
  rw [integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
    hmeas.aestronglyMeasurable] at h
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply,
    Matrix.submatrix_apply] using h

/-- **Parity vanishing of LKJ mixed entry moments.** Whenever some index `i` has odd symmetric
degree `∑ j, (n (i, j) + n (j, i))`, flipping the sign of axis `i` negates the monomial while
preserving `lkjMeasure p η`, so the mixed entry moment vanishes. Because `2 * n (i, i)` is even,
only off-diagonal exponents incident to `i` affect the parity. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd {p : ℕ} (η : ℝ)
    {n : Fin p × Fin p → ℕ} {i : Fin p}
    (hi : Odd (∑ j : Fin p, (n (i, j) + n (j, i)))) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by by_cases hk : k = i <;> simp [s, hk]
  have hmeas : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦
      (selfAdjoint.measurable_coe_apply q.1 q.2).pow_const (n q)
  have h := congrArg
    (fun ν : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ↦
      ∫ R, (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂ν)
    (map_symmetricCongruenceLinearMap_diagonal_lkjMeasure p η hs)
  rw [integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
    hmeas.aestronglyMeasurable] at h
  have hsign (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      (∏ q : Fin p × Fin p,
        (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s) R :
          Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) =
        -(∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) := by
    simp only [Matrix.coe_symmetricCongruenceLinearMap_diagonal_apply]
    rw [Matrix.prod_pow_mul_apply_mul (R : Matrix (Fin p) (Fin p) ℝ) s n]
    have hprod : (∏ r : Fin p, s r ^ ∑ j : Fin p, (n (r, j) + n (j, r))) = -1 := by
      rw [Fintype.prod_eq_single i]
      · simp [s, hi.neg_one_pow]
      · intro r hr
        simp [s, hr]
    rw [hprod, neg_one_mul]
  simp_rw [hsign, integral_neg] at h
  linarith

/-- Every natural moment of a diagonal entry of an LKJ matrix of positive shape equals one. -/
@[simp]
theorem integral_pow_coe_apply_self_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (i : Fin p) (m : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i i ^ m ∂lkjMeasure p η = 1 := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  rw [integral_congr_ae (g := fun _ ↦ (1 : ℝ))
    ((ae_diag_eq_one_lkjMeasure p η).mono fun R hR ↦ by simp [hR i])]
  simp

/-- **Natural moments of an off-diagonal LKJ entry.** For `η > 0` and `i ≠ j`, odd moments of
`R i j` vanish and even moments equal `B((m + 1) / 2, α) / B(1 / 2, α)` with
`α = η + (p - 2) / 2`. -/
theorem integral_pow_coe_apply_lkjMeasure_of_ne {p : ℕ} {η : ℝ} (hη : 0 < η)
    {i j : Fin p} (hij : i ≠ j) (m : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m ∂lkjMeasure p η =
      if Even m then
        beta (((m : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  have hp2 : (2 : ℝ) ≤ p := by
    have : 2 ≤ p := by
      have := i.isLt
      have := j.isLt
      omega
    exact_mod_cast this
  have hα : 0 < η + ((p : ℝ) - 2) / 2 := by linarith
  rw [← integral_map (f := fun x : ℝ ↦ x ^ m)
      (selfAdjoint.measurable_coe_apply i j).aemeasurable (by fun_prop),
    map_coe_apply_lkjMeasure_of_ne hη hij]
  simpa using integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
    (r := 0) hα (by simpa using hα) m

/-- Natural moments of an arbitrary entry `R i j` of an LKJ matrix of positive shape `η`. -/
theorem integral_pow_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (i j : Fin p) (m : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m ∂lkjMeasure p η =
      if i = j then 1
      else if Even m then
        beta (((m : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  by_cases hij : i = j
  · subst j
    simp [integral_pow_coe_apply_self_lkjMeasure hη]
  · simp [hij, integral_pow_coe_apply_lkjMeasure_of_ne hη hij]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ} {η : ℝ}
  {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- Every natural mixed entry monomial of a random matrix with LKJ law belongs to every `Lᵖ`,
including `L∞`. -/
theorem memLp_prod_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun ω ↦ ∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) q P := by
  have hg : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) :=
    Finset.measurable_fun_prod _ fun ij _ ↦
      (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const (n ij)
  exact (memLp_map_measure_iff hg.aestronglyMeasurable hX.aemeasurable).mp
    (hX.map_eq.symm ▸ TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure p η n q)

/-- Every natural mixed entry monomial of a random matrix with LKJ law is integrable. -/
theorem integrable_prod_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun ω ↦ ∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) P :=
  memLp_one_iff_integrable.mp (hX.memLp_prod_pow_coe_apply_lkjMeasure n 1)

/-- Mixed entry moments of a random matrix with positive-shape LKJ law. -/
theorem integral_prod_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) (n : Fin p × Fin p → ℕ) :
    ∫ ω, (∏ q, (X ω : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂P =
      ∑ c ∈ Fintype.piFinset
          (fun q : Fin p × Fin p ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij : strictLowerTriangle p, if Even (gramFactorMultiIndex c ij.1) then
            beta (((gramFactorMultiIndex c ij.1 : ℝ) + 1) / 2)
                (lkjPartialCorrelationShape p η ij +
                  partialCorrelationCholeskyMonomialResidualPower (gramFactorMultiIndex c) ij) /
              beta (1 / 2) (lkjPartialCorrelationShape p η ij)
          else 0 := by
  have hg : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦
      (selfAdjoint.measurable_coe_apply q.1 q.2).pow_const (n q)
  exact (hX.integral_comp hg.aestronglyMeasurable).trans
    (TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure hη n)

/-- Mixed entry moments of a random matrix with LKJ law vanish whenever some vertex has odd
symmetric degree. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd (hX : HasLaw X (lkjMeasure p η) P)
    {n : Fin p × Fin p → ℕ} {i : Fin p}
    (hi : Odd (∑ j : Fin p, (n (i, j) + n (j, i)))) :
    ∫ ω, (∏ q, (X ω : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂P = 0 := by
  have hg : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦
      (selfAdjoint.measurable_coe_apply q.1 q.2).pow_const (n q)
  exact (hX.integral_comp hg.aestronglyMeasurable).trans
    (TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd η hi)

/-- Natural moments of an off-diagonal entry of a random matrix with positive-shape LKJ law. -/
theorem integral_pow_coe_apply_lkjMeasure_of_ne (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) (m : ℕ) :
    ∫ ω, (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ m ∂P =
      if Even m then
        beta (((m : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  have hg : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m) :=
    (selfAdjoint.measurable_coe_apply i j).pow_const m
  exact (hX.integral_comp hg.aestronglyMeasurable).trans
    (TauCeti.Probability.integral_pow_coe_apply_lkjMeasure_of_ne hη hij m)

/-- Natural moments of an arbitrary entry of a random matrix with positive-shape LKJ law. -/
theorem integral_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) (i j : Fin p) (m : ℕ) :
    ∫ ω, (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ m ∂P =
      if i = j then 1
      else if Even m then
        beta (((m : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  have hg : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m) :=
    (selfAdjoint.measurable_coe_apply i j).pow_const m
  exact (hX.integral_comp hg.aestronglyMeasurable).trans
    (TauCeti.Probability.integral_pow_coe_apply_lkjMeasure hη i j m)

end ProbabilityTheory.HasLaw
