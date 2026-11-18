/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.GramPowers
public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Probability.Distributions.LKJ.Cholesky.Moments
public import TauCeti.Probability.Distributions.LKJ.CoordinateIntegral
import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.Probability.Distributions.LKJ.PartialCorrelation

/-!
# Mixed entry moments of the LKJ law

Every natural monomial in the entries of an LKJ correlation matrix is integrable. In fact, it
belongs to every `Lᵖ`, including `L∞`, because positive-semidefiniteness and unit diagonal bound
every matrix entry in absolute value by one. The result includes repeated symmetric entries,
diagonal powers, the empty matrix, and nonpositive shapes, where `lkjMeasure` is the zero measure.

Expanding the partial-correlation Gram representation also gives an exact finite sum for every
mixed moment at positive shape. Each summand is the Beta-product moment of one Cholesky monomial.
The evaluation holds for the Gram matrix of independent centered symmetric Beta partial
correlations with arbitrary positive shapes; the LKJ law is the case of the LKJ shapes.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti.Probability

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

/-- Every natural monomial in the entries of the Gram matrix of independent centered symmetric
Beta partial correlations with positive shapes is integrable. -/
theorem integrable_prod_pow_partialCorrelationGram_pi_betaMeasure {p : ℕ}
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (n : Fin p × Fin p → ℕ) :
    Integrable (fun z ↦ ∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  simp_rw [prod_pow_partialCorrelationGram_eq_sum]
  exact integrable_finsetSum _ fun c _ ↦
    integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha
      (mulTransposeExpansionPower c)

/-- The expectation of every natural monomial in the entries of the Gram matrix of independent
centered symmetric Beta partial correlations with positive shapes is a finite sum of products of
Beta quotients. The sum runs over the column choices of the Cholesky expansion; a term vanishes
when its Cholesky multi-index has an odd coordinate exponent. -/
theorem integral_prod_pow_partialCorrelationGram_pi_betaMeasure {p : ℕ}
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (n : Fin p × Fin p → ℕ) :
    ∫ z, ∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      ∑ c : mulTransposeExpansionChoice n,
        ∏ ij, if Even (mulTransposeExpansionPower c ij.1) then
          beta (((mulTransposeExpansionPower c ij.1 : ℝ) + 1) / 2)
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

/-- **Exact mixed entry moments of the LKJ law.** At positive shape, the expectation of every
natural monomial in the matrix entries is a finite sum of products of Beta quotients. The sum runs
over the column choices of the Cholesky expansion; a term vanishes when its Cholesky multi-index
has an odd coordinate exponent. -/
theorem integral_prod_pow_coe_apply_lkjMeasure (p : ℕ) {η : ℝ} (hη : 0 < η)
    (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij ∂(lkjMeasure p η) =
      ∑ c : mulTransposeExpansionChoice n,
        ∏ ij, if Even (mulTransposeExpansionPower c ij.1) then
          beta (((mulTransposeExpansionPower c ij.1 : ℝ) + 1) / 2)
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
          rw [integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]
    _ = ∫ z, f (partialCorrelationGram z) ∂(Measure.pi fun ij : strictLowerTriangle p ↦
          (betaMeasure (lkjPartialCorrelationShape p η ij)
            (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) := by
      rw [map_coe_lkjMeasure hη, integral_map
        continuous_partialCorrelationGram.measurable.aemeasurable hf.aestronglyMeasurable]
    _ = _ := integral_prod_pow_partialCorrelationGram_pi_betaMeasure
      (lkjPartialCorrelationShape_pos hη) n

end TauCeti.Probability
