/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.Symmetry
public import TauCeti.Probability.Distributions.LKJ.CoordinateIntegral
public import TauCeti.Analysis.Matrix.PartialCorrelation.GramPowers
public import Mathlib.Probability.Distributions.Beta
import TauCeti.Algebra.BigOperators.Pi
import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.Probability.Distributions.Beta.Symmetric
import TauCeti.Probability.Distributions.LKJ.Cholesky.Moments
import TauCeti.Probability.Distributions.LKJ.Marginal
import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
import TauCeti.Probability.Distributions.LKJ.PrincipalBlock

/-!
# Mixed entry moments of LKJ correlation matrices

Every natural monomial `∏ q, R q.1 q.2 ^ n q` in the entries of an LKJ correlation matrix belongs
to every `Lᵖ`, including `L∞`, because positive-semidefiniteness and unit diagonal bound every
matrix entry in absolute value by one. For positive shape `η`, representing the LKJ law as the
Gram pushforward `partialCorrelationGram` of independent centered symmetric Beta partial
correlations (`TauCeti.Probability.map_coe_lkjMeasure`) and expanding `R = L * Lᵀ` through
`TauCeti.prod_pow_partialCorrelationGram_eq_sum` evaluates every mixed entry moment as a finite
sum, over the column choices of the Cholesky expansion, of products of Beta quotients.

The expansion covers repeated symmetric entries, diagonal powers, and dimensions zero and one.
Diagonal exponents leave mixed moments unchanged, relabelling rows and columns by a permutation
preserves mixed moments, and any vertex `i` of odd symmetric degree `∑ j, (n (i, j) + n (j, i))`
forces the mixed moment to vanish by diagonal sign invariance. Specializing to a single entry gives
closed Beta-quotient moments of all natural orders, and evaluating a three-entry cycle gives the
joint third moment `E[R i j * R i k * R j k] = 1 / (2 * η + p - 1) ^ 2` for pairwise distinct
indices, witnessing non-independence of off-diagonal correlation entries despite zero pairwise
covariances between distinct strict-lower-triangle entries.

## Main results

* `TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure` and
  `TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure`: `Lᵖ` membership and integrability
  of all natural mixed entry monomials under `lkjMeasure p η`;
* `TauCeti.Probability.integral_prod_pow_partialCorrelationGram_pi_betaMeasure`: mixed entry
  moments of `partialCorrelationGram` under independent centered symmetric Beta partial
  correlations with arbitrary positive shapes;
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure`: closed finite
  Beta-quotient evaluation of all natural mixed entry moments under `lkjMeasure p η` for `0 < η`;
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_integral_prod_filter_ne`,
  `TauCeti.Probability.integral_prod_pow_coe_apply_perm_lkjMeasure`,
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd`, and
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_of_diag`: diagonal-exponent
  invariance, permutation invariance, odd-degree vanishing, and diagonal-supported unit
  evaluations of mixed moments;
* `TauCeti.Probability.integral_pow_coe_apply_lkjMeasure_of_ne` and
  `TauCeti.Probability.integral_pow_coe_apply_lkjMeasure`: single-entry moments of all natural
  orders (with unexponentiated first moments re-exported from
  `TauCeti.Probability.Distributions.LKJ.Symmetry`);
* `TauCeti.Probability.integral_mul_mul_coe_apply_lkjMeasure`: the joint three-entry triangle
  moment `1 / (2 * η + p - 1) ^ 2`;
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
theorem memLp_prod_pow_coe_apply_lkjMeasure {p : ℕ} (η : ℝ)
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
theorem integrable_prod_pow_coe_apply_lkjMeasure {p : ℕ} (η : ℝ)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) (lkjMeasure p η) :=
  memLp_one_iff_integrable.mp (memLp_prod_pow_coe_apply_lkjMeasure η n 1)

/-- Every natural power of a single entry of an LKJ matrix belongs to every `Lᵖ`, including
`L∞`. -/
theorem memLp_pow_coe_apply_lkjMeasure {p : ℕ} (η : ℝ) (i j : Fin p) (m : ℕ) (q : ℝ≥0∞) :
    MemLp (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m) q (lkjMeasure p η) := by
  classical
  have hsingle (M : Matrix (Fin p) (Fin p) ℝ) :
      (∏ ij : Fin p × Fin p, M ij.1 ij.2 ^ Pi.single (i, j) m ij) = M i j ^ m :=
    Fintype.prod_pow_pi_single (fun ij : Fin p × Fin p ↦ M ij.1 ij.2) (i, j) m
  simpa only [hsingle] using
    memLp_prod_pow_coe_apply_lkjMeasure η (Pi.single (i, j) m) q

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
`partialCorrelationGram` agrees almost everywhere with its expansion into coordinate and residual
powers. -/
theorem prod_pow_partialCorrelationGram_ae_eq_sum_prod_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    (fun z ↦ ∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij) =ᵐ[
      Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)]
      fun z ↦ ∑ c : mulTransposeExpansionChoice n,
        ∏ ij, z ij ^ mulTransposeExpansionPower c ij.val *
          (1 - z ij ^ 2) ^
            partialCorrelationCholeskyMonomialResidualPower (mulTransposeExpansionPower c) ij := by
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  exact prod_pow_partialCorrelationGram_eq_sum_prod (fun ij ↦ (hz ij).le) n

/-- The expectation of every natural monomial in the entries of the Gram matrix of independent
centered symmetric Beta partial correlations with positive shapes is a finite sum of products of
Beta quotients. The sum runs over the column choices of the Cholesky expansion; a term vanishes
when its Cholesky multi-index has an odd coordinate exponent. -/
theorem integral_prod_pow_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (n : Fin p × Fin p → ℕ) :
    ∫ z, ∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      ∑ c : mulTransposeExpansionChoice n,
        ∏ ij, if Even (mulTransposeExpansionPower c ij.val) then
          beta (((mulTransposeExpansionPower c ij.val : ℝ) + 1) / 2)
              (a ij + partialCorrelationCholeskyMonomialResidualPower
                (mulTransposeExpansionPower c) ij) /
            beta (1 / 2) (a ij)
        else 0 := by
  simp_rw [prod_pow_partialCorrelationGram_eq_sum]
  rw [integral_finsetSum _ fun c _ ↦
    integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha
      (mulTransposeExpansionPower c)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [integral_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha, ite_eq_left]
  exact fun q hq ↦ not_lt.mp fun h ↦ hq (mulTransposeExpansionPower_of_lt c h)

/-- Under the pushforward of a product of independent sigma-finite negation-invariant marginals
by `partialCorrelationGram`, any vertex `i` whose symmetric exponent sum
`∑ j, (n (i, j) + n (j, i))` is odd forces the Bochner integral `∫ R, (∏ q, R q.1 q.2 ^ n q)`
to vanish. Nonintegrable integrals are totalized to zero, so this does not assert integrability. -/
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

/-- **Exact mixed entry moments of the LKJ law.** At positive shape, the expectation of every
natural monomial in the matrix entries is a finite sum of products of Beta quotients. The sum runs
over the column choices of the Cholesky expansion; a term vanishes when its Cholesky multi-index
has an odd coordinate exponent. -/
theorem integral_prod_pow_coe_apply_lkjMeasure (p : ℕ) {η : ℝ} (hη : 0 < η)
    (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij ∂(lkjMeasure p η) =
      ∑ c : mulTransposeExpansionChoice n,
        ∏ ij, if Even (mulTransposeExpansionPower c ij.val) then
          beta (((mulTransposeExpansionPower c ij.val : ℝ) + 1) / 2)
              (lkjPartialCorrelationShape p η ij +
                partialCorrelationCholeskyMonomialResidualPower
                  (mulTransposeExpansionPower c) ij) /
            beta (1 / 2) (lkjPartialCorrelationShape p η ij)
        else 0 := by
  let f := fun R : Matrix (Fin p) (Fin p) ℝ ↦ ∏ ij, R ij.1 ij.2 ^ n ij
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  calc
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij ∂(lkjMeasure p η) =
        ∫ R, f R ∂((lkjMeasure p η).map Subtype.val) := by
          rw [integral_map measurable_subtypeVal.aemeasurable hf.aestronglyMeasurable]
    _ = ∫ z, f (partialCorrelationGram z) ∂(Measure.pi fun ij : strictLowerTriangle p ↦
          (betaMeasure (lkjPartialCorrelationShape p η ij)
            (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) := by
      rw [map_coe_lkjMeasure hη, integral_map
        continuous_partialCorrelationGram.measurable.aemeasurable hf.aestronglyMeasurable]
    _ = _ := integral_prod_pow_partialCorrelationGram_pi_betaMeasure
      (lkjPartialCorrelationShape_pos hη) n

/-- Diagonal exponents do not change mixed entry moments under `lkjMeasure`, since diagonal entries
are almost surely one (and for nonpositive shapes the measure is zero). -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_integral_prod_filter_ne {p : ℕ} (η : ℝ)
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
  rcases le_or_gt η 0 with hη | hη
  · simp [lkjMeasure_of_nonpos hη]
  · let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)) :=
      isProbabilityMeasureBeta (lkjPartialCorrelationShape_pos hη ij)
        (lkjPartialCorrelationShape_pos hη ij)
    let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure
        ((betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) :=
      (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
    let g : Matrix (Fin p) (Fin p) ℝ → ℝ := fun M ↦ ∏ q, M q.1 q.2 ^ n q
    have hg : Continuous g := by fun_prop
    rw [← integral_map (f := g) measurable_subtypeVal.aemeasurable hg.aestronglyMeasurable,
      map_coe_lkjMeasure hη]
    exact integral_prod_pow_apply_map_partialCorrelationGram_pi_eq_zero_of_odd _ hi

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

/-- At positive shape, any mixed entry moment supported on the diagonal equals one. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_of_diag {p : ℕ} {η : ℝ} (hη : 0 < η)
    {n : Fin p × Fin p → ℕ} (hdiag : ∀ ab, n ab ≠ 0 → ab.1 = ab.2) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ab, (R : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab ∂lkjMeasure p η = 1 := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  rw [integral_prod_pow_coe_apply_lkjMeasure_eq_integral_prod_filter_ne]
  have hprod (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      (∏ q with q.1 ≠ q.2, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) = 1 := by
    refine Finset.prod_eq_one fun q hq ↦ ?_
    have h0 : n q = 0 := not_not.mp fun hn ↦ (Finset.mem_filter.mp hq).2 (hdiag q hn)
    simp [h0]
  simp [hprod]

/-! ### Joint three-entry triangle moment of `lkjMeasure` -/

private theorem integral_triangle_lkjMeasure_three {η : ℝ} (hη : 0 < η) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ),
        (R : Matrix (Fin 3) (Fin 3) ℝ) 2 1 * (R : Matrix (Fin 3) (Fin 3) ℝ) 2 0 *
          (R : Matrix (Fin 3) (Fin 3) ℝ) 1 0 ∂lkjMeasure 3 η =
      1 / (2 * η + 2) ^ 2 := by
  let n : Fin 3 × Fin 3 → ℕ :=
    Pi.single ((2 : Fin 3), (1 : Fin 3)) 1 +
      Pi.single ((2 : Fin 3), (0 : Fin 3)) 1 +
      Pi.single ((1 : Fin 3), (0 : Fin 3)) 1
  have hprod (R : selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ)) :
      (R : Matrix (Fin 3) (Fin 3) ℝ) 2 1 * (R : Matrix (Fin 3) (Fin 3) ℝ) 2 0 *
          (R : Matrix (Fin 3) (Fin 3) ℝ) 1 0 =
        ∏ ij : Fin 3 × Fin 3, (R : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 ^ n ij := by
    simp only [n, Pi.add_apply, pow_add, Finset.prod_mul_distrib,
      Fintype.prod_pow_pi_single (fun ij : Fin 3 × Fin 3 ↦
        (R : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2), pow_one]
  simp_rw [hprod]
  rw [integral_prod_pow_coe_apply_lkjMeasure 3 hη n]
  let c₀ : mulTransposeExpansionChoice n := fun _ _ ↦ ⟨0, Fin.zero_le _⟩
  have hsum_pow (c : mulTransposeExpansionChoice n) (q : Fin 3 × Fin 3) :
      mulTransposeExpansionPower c q =
        ((if ((2 : Fin 3), (c (2, 1) ⟨0, by decide⟩ : Fin 3)) = q then 1 else 0) +
          if ((1 : Fin 3), (c (2, 1) ⟨0, by decide⟩ : Fin 3)) = q then 1 else 0) +
        ((if ((2 : Fin 3), (0 : Fin 3)) = q then 1 else 0) +
          if ((0 : Fin 3), (0 : Fin 3)) = q then 1 else 0) +
        ((if ((1 : Fin 3), (0 : Fin 3)) = q then 1 else 0) +
          if ((0 : Fin 3), (0 : Fin 3)) = q then 1 else 0) := by
    have hc20 : (c (2, 0) ⟨0, by decide⟩ : Fin 3) = 0 :=
      Fin.le_zero_iff.mp (c (2, 0) ⟨0, by decide⟩).property
    have hc10 : (c (1, 0) ⟨0, by decide⟩ : Fin 3) = 0 :=
      Fin.le_zero_iff.mp (c (1, 0) ⟨0, by decide⟩).property
    rw [mulTransposeExpansionPower_eq_sum, Fintype.sum_prod_type, Fin.sum_univ_three,
      Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    have h0 (ij : Fin 3 × Fin 3) (hn : n ij = 0) :
        (∑ r : Fin (n ij), ((if (ij.1, (c ij r : Fin 3)) = q then 1 else 0) +
          if (ij.2, (c ij r : Fin 3)) = q then 1 else 0)) = 0 := by
      simp [hn]
    have h1 (ij : Fin 3 × Fin 3) (hn : n ij = 1) :
        (∑ r : Fin (n ij), ((if (ij.1, (c ij r : Fin 3)) = q then 1 else 0) +
          if (ij.2, (c ij r : Fin 3)) = q then 1 else 0)) =
          ((if (ij.1, (c ij ⟨0, by omega⟩ : Fin 3)) = q then 1 else 0) +
            if (ij.2, (c ij ⟨0, by omega⟩ : Fin 3)) = q then 1 else 0) := by
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · intro r _ hr
        exfalso
        exact hr (Fin.ext (by omega))
      · simp
    rw [h0 (0, 0) (by decide), h0 (0, 1) (by decide), h0 (0, 2) (by decide),
      h1 (1, 0) (by decide), h0 (1, 1) (by decide), h0 (1, 2) (by decide),
      h1 (2, 0) (by decide), h1 (2, 1) (by decide), h0 (2, 2) (by decide),
      hc20, hc10]
    simp only [zero_add, add_zero]
    abel
  rw [Finset.sum_eq_single c₀]
  · have hres (ij : strictLowerTriangle 3) :
        partialCorrelationCholeskyMonomialResidualPower (mulTransposeExpansionPower c₀) ij = 0 := by
      rw [partialCorrelationCholeskyMonomialResidualPower_eq_sum_Ioi]
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      rw [hsum_pow]
      have hk' : ij.val.2 < k := Finset.mem_Ioi.mp hk
      have hk0 : (0 : Fin 3) ≠ k := (lt_of_le_of_lt (Fin.zero_le _) hk').ne
      simp [c₀, hk0]
    let z10 : strictLowerTriangle 3 := ⟨(1, 0), by decide⟩
    let z20 : strictLowerTriangle 3 := ⟨(2, 0), by decide⟩
    let z21 : strictLowerTriangle 3 := ⟨(2, 1), by decide⟩
    have huniv : (Finset.univ : Finset (strictLowerTriangle 3)) = {z10, z20, z21} := by decide
    have hp10 : mulTransposeExpansionPower c₀ z10.val = 2 := by simp [hsum_pow, c₀, z10]
    have hp20 : mulTransposeExpansionPower c₀ z20.val = 2 := by simp [hsum_pow, c₀, z20]
    have hp21 : mulTransposeExpansionPower c₀ z21.val = 0 := by simp [hsum_pow, c₀, z21]
    simp_rw [hres, add_zero]
    rw [huniv, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton, hp10, hp20, hp21]
    have h10pos := lkjPartialCorrelationShape_pos hη z10
    have h20pos := lkjPartialCorrelationShape_pos hη z20
    have h21pos := lkjPartialCorrelationShape_pos hη z21
    have hbeta (a : ℝ) (ha : 0 < a) :
        beta (((2 : ℕ) + 1) / 2) a / beta (1 / 2) a = 1 / (2 * a + 1) := by
      have hb : beta (1 / 2) a ≠ 0 := (beta_pos (by norm_num) ha).ne'
      rw [show (((2 : ℕ) : ℝ) + 1) / 2 = (1 / 2 : ℝ) + 1 by norm_num,
        beta_add_one_left (by norm_num) (by positivity), mul_div_cancel_right₀ _ hb]
      field_simp
      ring
    simp only [show Even 2 by decide, show Even 0 by decide, ↓reduceIte, Nat.cast_zero, zero_add]
    rw [hbeta _ h10pos, hbeta _ h20pos, div_self (beta_pos (by norm_num) h21pos).ne',
      lkjPartialCorrelationShape_eq, lkjPartialCorrelationShape_eq]
    norm_num [z10, z20]
    field_simp
    ring
  · intro c _ hc
    have h21 : (c (2, 1) ⟨0, by decide⟩ : Fin 3) = 1 := by
      by_contra hne
      apply hc
      ext ij r
      have hn1 : ij = (2, 1) ∨ ij = (2, 0) ∨ ij = (1, 0) := by
        by_contra hnot
        have hzero : n ij = 0 := by
          simp only [n, Pi.add_apply, Pi.single_apply]
          aesop
        exact absurd r.isLt (by omega)
      rcases hn1 with rfl | rfl | rfl
      · have hn21 : n (2, 1) = 1 := by decide
        have hr0 : r = ⟨0, by decide⟩ := Fin.ext (by have := r.isLt; omega)
        subst hr0
        have hle : ((c (2, 1) ⟨0, by decide⟩ : Fin 3) : ℕ) ≤ 1 :=
          (c (2, 1) ⟨0, by decide⟩).property
        have hne' : ((c (2, 1) ⟨0, by decide⟩ : Fin 3) : ℕ) ≠ 1 := fun h ↦ hne (Fin.ext h)
        simp only [c₀]
        omega
      · exact congrArg Fin.val (Fin.le_zero_iff.mp (c (2, 0) r).property)
      · exact congrArg Fin.val (Fin.le_zero_iff.mp (c (1, 0) r).property)
    have hpow21 : mulTransposeExpansionPower c (2, 1) = 1 := by
      rw [hsum_pow, h21]
      decide
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨(2, 1), by decide⟩ : strictLowerTriangle 3))
      (by simp [hpow21])
  · simp

/-- **Joint three-entry triangle moment of the LKJ law.** For `0 < η` and pairwise distinct indices
`i, j, k : Fin p`, the mixed moment `E[R i j * R i k * R j k]` equals `1 / (2 * η + p - 1) ^ 2`.
In particular, although distinct strict-lower-triangle correlation entries have covariance zero, any
three entries forming a triangle have strictly positive joint third moment. -/
theorem integral_mul_mul_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    {i j k : Fin p} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j * (R : Matrix (Fin p) (Fin p) ℝ) i k *
          (R : Matrix (Fin p) (Fin p) ℝ) j k ∂lkjMeasure p η =
      1 / (2 * η + p - 1) ^ 2 := by
  have hf : Function.Injective ![k, j, i] := by
    simp only [Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Set.range_eq_empty,
      Set.mem_insert_iff, Set.mem_empty_iff_false, or_false, not_or, not_false_eq_true, true_and]
    exact ⟨⟨hjk.symm, hik.symm⟩, hij.symm, Function.injective_of_subsingleton _⟩
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

/-- Every natural mixed entry monomial of a random matrix with LKJ law belongs to every `Lᵖ`,
including `L∞`. -/
theorem memLp_prod_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun ω ↦ ∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) q P :=
  hX.memLp_fun_comp (TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure η n q)

/-- Every natural mixed entry monomial of a random matrix with LKJ law is integrable. -/
theorem integrable_prod_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun ω ↦ ∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η n)

/-- Every natural power of a single entry of a random matrix with LKJ law belongs to every `Lᵖ`,
including `L∞`. -/
theorem memLp_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (i j : Fin p) (m : ℕ) (q : ℝ≥0∞) :
    MemLp (fun ω ↦ (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ m) q P :=
  hX.memLp_fun_comp (TauCeti.Probability.memLp_pow_coe_apply_lkjMeasure η i j m q)

/-- Every natural power of a single entry of a random matrix with LKJ law is integrable. -/
theorem integrable_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (i j : Fin p) (m : ℕ) :
    Integrable (fun ω ↦ (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ m) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_pow_coe_apply_lkjMeasure η i j m)

/-- Mixed entry moments of a random matrix with positive-shape LKJ law. -/
theorem integral_prod_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) (n : Fin p × Fin p → ℕ) :
    ∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂P =
      ∑ c : mulTransposeExpansionChoice n,
        ∏ ij, if Even (mulTransposeExpansionPower c ij.val) then
          beta (((mulTransposeExpansionPower c ij.val : ℝ) + 1) / 2)
              (lkjPartialCorrelationShape p η ij +
                partialCorrelationCholeskyMonomialResidualPower
                  (mulTransposeExpansionPower c) ij) /
            beta (1 / 2) (lkjPartialCorrelationShape p η ij)
        else 0 :=
  (hX.integral_comp
    (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η n).aestronglyMeasurable).trans
    (TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure p hη n)

/-- Diagonal exponents do not change mixed entry moments of a random matrix with LKJ law. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_integral_prod_filter_ne
    (hX : HasLaw X (lkjMeasure p η) P) (n : Fin p × Fin p → ℕ) :
    ∫ ω, (∏ q, (X ω : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂P =
      ∫ ω, (∏ q with q.1 ≠ q.2, (X ω : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂P := by
  have hfilter (M : Matrix (Fin p) (Fin p) ℝ) :
      (∏ q with q.1 ≠ q.2, M q.1 q.2 ^ n q) =
        ∏ q, M q.1 q.2 ^ (if q.1 ≠ q.2 then n q else 0) := by
    rw [Finset.prod_filter]
    exact Finset.prod_congr rfl fun q _ ↦ by split_ifs <;> simp
  have hrhs : AEStronglyMeasurable
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ∏ q with q.1 ≠ q.2, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q)
      (lkjMeasure p η) := by
    simp_rw [hfilter]
    exact (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η _).aestronglyMeasurable
  exact (hX.integral_comp
    (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η n).aestronglyMeasurable).trans
    ((TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_integral_prod_filter_ne η
      n).trans (hX.integral_comp hrhs).symm)

/-- Mixed entry moments of a random matrix with LKJ law are invariant under simultaneous
row-and-column permutations. -/
theorem integral_prod_pow_coe_apply_perm_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (σ : Equiv.Perm (Fin p)) (n : Fin p × Fin p → ℕ) :
    ∫ ω, (∏ q, (X ω : Matrix (Fin p) (Fin p) ℝ) (σ q.1) (σ q.2) ^ n q) ∂P =
      ∫ ω, (∏ q, (X ω : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂P := by
  have hperm (M : Matrix (Fin p) (Fin p) ℝ) :
      (∏ q : Fin p × Fin p, M (σ q.1) (σ q.2) ^ n q) =
        ∏ q : Fin p × Fin p, M q.1 q.2 ^ n (σ.symm q.1, σ.symm q.2) := by
    simpa using (Equiv.prodCongr σ σ).prod_comp
      fun q : Fin p × Fin p ↦ M q.1 q.2 ^ n (σ.symm q.1, σ.symm q.2)
  have hlhs : AEStronglyMeasurable
      (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ∏ q, (R : Matrix (Fin p) (Fin p) ℝ) (σ q.1) (σ q.2) ^ n q)
      (lkjMeasure p η) := by
    simp_rw [hperm]
    exact (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η _).aestronglyMeasurable
  exact (hX.integral_comp hlhs).trans
    ((TauCeti.Probability.integral_prod_pow_coe_apply_perm_lkjMeasure η σ n).trans
      (hX.integral_comp
        (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η
          n).aestronglyMeasurable).symm)

/-- Mixed entry moments of a random matrix with LKJ law vanish whenever some vertex has odd
symmetric degree. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd (hX : HasLaw X (lkjMeasure p η) P)
    {n : Fin p × Fin p → ℕ} {i : Fin p}
    (hi : Odd (∑ j : Fin p, (n (i, j) + n (j, i)))) :
    ∫ ω, (∏ q, (X ω : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂P = 0 :=
  (hX.integral_comp
    (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η n).aestronglyMeasurable).trans
    (TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd η hi)

/-- Every natural moment of a diagonal entry of a random matrix with positive-shape LKJ law equals
one. -/
theorem integral_pow_coe_apply_self_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) (i : Fin p) (m : ℕ) :
    ∫ ω, (X ω : Matrix (Fin p) (Fin p) ℝ) i i ^ m ∂P = 1 :=
  (hX.integral_comp
    (TauCeti.Probability.integrable_pow_coe_apply_lkjMeasure η i i m).aestronglyMeasurable).trans
    (TauCeti.Probability.integral_pow_coe_apply_self_lkjMeasure hη i m)

/-- Natural moments of an off-diagonal entry of a random matrix with positive-shape LKJ law. -/
theorem integral_pow_coe_apply_lkjMeasure_of_ne (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) {i j : Fin p} (hij : i ≠ j) (m : ℕ) :
    ∫ ω, (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ m ∂P =
      if Even m then
        beta (((m : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 :=
  (hX.integral_comp
    (TauCeti.Probability.integrable_pow_coe_apply_lkjMeasure η i j m).aestronglyMeasurable).trans
    (TauCeti.Probability.integral_pow_coe_apply_lkjMeasure_of_ne hη hij m)

/-- Natural moments of an arbitrary entry of a random matrix with positive-shape LKJ law. -/
theorem integral_pow_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) (i j : Fin p) (m : ℕ) :
    ∫ ω, (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ m ∂P =
      if i = j then 1
      else if Even m then
        beta (((m : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 :=
  (hX.integral_comp
    (TauCeti.Probability.integrable_pow_coe_apply_lkjMeasure η i j m).aestronglyMeasurable).trans
    (TauCeti.Probability.integral_pow_coe_apply_lkjMeasure hη i j m)

/-- At positive shape, any mixed entry moment of a random matrix with LKJ law equals one when all
off-diagonal exponents vanish. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_of_diag (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) {n : Fin p × Fin p → ℕ} (hdiag : ∀ ab, n ab ≠ 0 → ab.1 = ab.2) :
    ∫ ω, (∏ ab, (X ω : Matrix (Fin p) (Fin p) ℝ) ab.1 ab.2 ^ n ab) ∂P = 1 :=
  (hX.integral_comp
    (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure η n).aestronglyMeasurable).trans
    (TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_of_diag hη hdiag)

/-- Joint three-entry triangle moment of a random matrix with positive-shape LKJ law. -/
theorem integral_mul_mul_coe_apply_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P)
    (hη : 0 < η) {i j k : Fin p} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∫ ω, (X ω : Matrix (Fin p) (Fin p) ℝ) i j * (X ω : Matrix (Fin p) (Fin p) ℝ) i k *
        (X ω : Matrix (Fin p) (Fin p) ℝ) j k ∂P =
      1 / (2 * η + p - 1) ^ 2 :=
  (hX.integral_comp
    (((selfAdjoint.measurable_coe_apply i j).mul (selfAdjoint.measurable_coe_apply i k)).mul
      (selfAdjoint.measurable_coe_apply j k)).aestronglyMeasurable).trans
    (TauCeti.Probability.integral_mul_mul_coe_apply_lkjMeasure hη hij hik hjk)

end ProbabilityTheory.HasLaw
