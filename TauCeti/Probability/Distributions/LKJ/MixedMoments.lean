/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Probability.Distributions.LKJ.Cholesky.Moments
import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.Probability.Distributions.LKJ.Marginal

/-!
# Mixed entry moments of the LKJ distribution

Every natural monomial in the entries of an LKJ correlation matrix belongs to every `Lᵖ`,
including `L∞`, because positive-semidefiniteness and unit diagonal bound every matrix entry in
absolute value by one. Expanding `partialCorrelationGram z` through
`partialCorrelationCholesky z * (partialCorrelationCholesky z)ᵀ` expresses each correlation-entry
monomial as a finite multinomial sum of lower-triangular Cholesky monomials, whose expectations
under independent centered symmetric Beta partial correlations evaluate to finite products of Beta
quotients.

Through `TauCeti.Probability.map_coe_lkjMeasure`, this yields an explicit finite Beta-product sum
for all natural mixed entry moments of `TauCeti.Probability.lkjMeasure` at positive shapes.
Symmetry and unit diagonal reduce arbitrary ordered-pair multi-indices to the strict lower
triangle, any odd total degree incident to a coordinate axis forces the mixed moment to vanish by
diagonal sign invariance, and single-entry natural moments collapse to a single Beta quotient off
the diagonal and to one on the diagonal.

## Main results

* `TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure` and
  `TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure`: `Lᵖ` membership and
  integrability of all natural mixed entry moments of `lkjMeasure`.
* `TauCeti.Probability.memLp_prod_pow_partialCorrelationGram_pi_betaMeasure`,
  `TauCeti.Probability.integrable_prod_pow_partialCorrelationGram_pi_betaMeasure`, and
  `TauCeti.Probability.integral_prod_pow_partialCorrelationGram_pi_betaMeasure`: `Lᵖ` membership,
  integrability, and Beta-product formula for mixed entry moments of `partialCorrelationGram` under
  independent centered symmetric Beta coordinates with arbitrary positive shapes.
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure`: finite multinomial Beta-product
  formula for all natural mixed entry moments of `lkjMeasure` at positive shape.
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_prod_strictLowerTriangle`,
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_of_offDiag_eq_zero`, and
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_of_le_one`: reductions using symmetry
  and unit diagonal.
* `TauCeti.Probability.integral_prod_pow_apply_map_partialCorrelationGram_pi_eq_zero_of_odd` and
  `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd`: vanishing of mixed
  entry moments with an odd incident degree at some coordinate axis.
* `TauCeti.Probability.memLp_pow_coe_apply_lkjMeasure`,
  `TauCeti.Probability.integrable_pow_coe_apply_lkjMeasure`, and
  `TauCeti.Probability.integral_pow_coe_apply_lkjMeasure`: `Lᵖ` membership, integrability, and
  closed-form single-entry natural moments of `lkjMeasure`.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Matrix

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

section PartialCorrelationGram

variable {p : ℕ}

/-- Every natural mixed entry monomial of the independent-Beta partial-correlation Gram
construction belongs to every `Lᵠ`, including `L∞`. -/
theorem memLp_prod_pow_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun z ↦ ∏ r, partialCorrelationGram z r.1 r.2 ^ n r) q
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  refine MemLp.of_bound (Finset.measurable_fun_prod _ fun r _ ↦
    ((Matrix.measurable_apply.comp continuous_partialCorrelationGram.measurable).pow_const
      (n r))).aestronglyMeasurable 1 ?_
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  have hz' : ∀ ij, |z ij| ≤ 1 := fun ij ↦ (hz ij).le
  rw [Real.norm_eq_abs, Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro _ _
    positivity
  · intro r _
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _)
      ((posSemidef_partialCorrelationGram z).norm_le_one_of_apply_self_eq_one
        (partialCorrelationGram_apply_self hz' r.1) (partialCorrelationGram_apply_self hz' r.2))

/-- Every natural mixed entry moment of the independent-Beta partial-correlation Gram construction
is integrable. -/
theorem integrable_prod_pow_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun z ↦ ∏ r, partialCorrelationGram z r.1 r.2 ^ n r)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) :=
  memLp_one_iff_integrable.mp (memLp_prod_pow_partialCorrelationGram_pi_betaMeasure ha n 1)

/-- **Natural mixed entry moments of the independent-Beta partial-correlation Gram construction.**
Expanding `partialCorrelationGram z` through its lower-triangular Cholesky factor expresses every
mixed entry moment as a multinomial sum over lower-triangular column decompositions of finite
products of Beta quotients. -/
theorem integral_prod_pow_partialCorrelationGram_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (n : Fin p × Fin p → ℕ) :
    ∫ z, (∏ q, partialCorrelationGram z q.1 q.2 ^ n q)
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij, if Even (gramMonomialExponent c ij.1) then
            beta (((gramMonomialExponent c ij.1 : ℝ) + 1) / 2)
                (a ij + partialCorrelationCholeskyMonomialResidualPower
                  (gramMonomialExponent c) ij) /
              beta (1 / 2) (a ij)
          else 0 := by
  simp_rw [prod_pow_partialCorrelationGram_eq_sum_prod_pow_partialCorrelationCholesky]
  rw [integral_finsetSum _ fun c _ ↦
    (integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha
      (gramMonomialExponent c)).const_mul _]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [integral_const_mul,
    integral_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha (gramMonomialExponent c),
    ite_eq_left fun _ hr ↦ le_of_gramMonomialExponent_ne_zero_of_mem_piFinset_piAntidiag_Iic hc hr]

/-- Under a partial-correlation Gram law with independent negation-invariant sigma-finite
marginals, any mixed entry moment in which some coordinate axis `i` has odd total incident degree
vanishes. Nonintegrable integrals are totalized to zero. -/
theorem integral_prod_pow_apply_map_partialCorrelationGram_pi_eq_zero_of_odd
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, SigmaFinite (μ ij)]
    [∀ ij, (μ ij).IsNegInvariant] (n : Fin p × Fin p → ℕ) {i : Fin p}
    (hodd : Odd (∑ j : Fin p, (n (i, j) + n (j, i)))) :
    ∫ R : Matrix (Fin p) (Fin p) ℝ, (∏ q, R q.1 q.2 ^ n q)
      ∂((Measure.pi μ).map partialCorrelationGram) = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by
    dsimp only [s]
    split_ifs <;> norm_num
  have hm : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦ ∏ q, R q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦ Matrix.measurable_apply.pow_const (n q)
  have h := congrArg (fun ν : Measure (Matrix (Fin p) (Fin p) ℝ) ↦
      ∫ R, (∏ q, R q.1 q.2 ^ n q) ∂ν)
    (map_signChange_map_partialCorrelationGram_pi μ hs)
  rw [integral_map
    (by fun_prop : Measurable (fun R : Matrix (Fin p) (Fin p) ℝ ↦
      Matrix.of fun a b ↦ s a * R a b * s b)).aemeasurable
    hm.aestronglyMeasurable] at h
  simp only [Matrix.of_apply, s] at h
  simp_rw [Matrix.prod_pow_signFlip_mul_apply, hodd.neg_one_pow, neg_one_mul, integral_neg] at h
  linarith

end PartialCorrelationGram

section LKJ

variable {p : ℕ} {η : ℝ}

/-- **Natural mixed entry moments of the LKJ distribution.** For `η > 0`, the expectation of any
natural monomial `∏ q, R q.1 q.2 ^ n q` under `lkjMeasure p η` is the multinomial sum over
lower-triangular column decompositions of finite products of Beta quotients at the column-dependent
partial-correlation shapes `lkjPartialCorrelationShape p η`. This includes repeated symmetric
entries, diagonal powers, the zeroth moment, and dimensions zero and one. -/
theorem integral_prod_pow_coe_apply_lkjMeasure (hη : 0 < η) (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij, if Even (gramMonomialExponent c ij.1) then
            beta (((gramMonomialExponent c ij.1 : ℝ) + 1) / 2)
                (lkjPartialCorrelationShape p η ij +
                  partialCorrelationCholeskyMonomialResidualPower
                    (gramMonomialExponent c) ij) /
              beta (1 / 2) (lkjPartialCorrelationShape p η ij)
          else 0 := by
  have hm : Measurable (fun M : Matrix (Fin p) (Fin p) ℝ ↦ ∏ q, M q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦ Matrix.measurable_apply.pow_const (n q)
  rw [← integral_map (f := fun M : Matrix (Fin p) (Fin p) ℝ ↦ ∏ q, M q.1 q.2 ^ n q)
      measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable,
    map_coe_lkjMeasure hη,
    integral_map continuous_partialCorrelationGram.measurable.aemeasurable
      hm.aestronglyMeasurable]
  exact integral_prod_pow_partialCorrelationGram_pi_betaMeasure
    (lkjPartialCorrelationShape_pos hη) n

/-- Symmetry and unit diagonal reduce any natural mixed entry moment of `lkjMeasure` to the strict
lower triangle, summing symmetric off-diagonal exponents and dropping diagonal ones. This holds for
all real shapes `η`, including nonpositive shapes where `lkjMeasure` is the zero measure. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_prod_strictLowerTriangle
    (p : ℕ) (η : ℝ) (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η =
      ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij : strictLowerTriangle p,
          (R : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 ^ (n ij.1 + n ij.1.swap))
          ∂lkjMeasure p η := by
  apply integral_congr_ae
  filter_upwards [ae_diag_eq_one_lkjMeasure p η] with R hdiag
  have hsymm : (R : Matrix (Fin p) (Fin p) ℝ).IsSymm := by
    have hstar := R.2.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hstar
  exact hsymm.prod_pow_apply_of_diag_eq_one hdiag n

/-- A natural mixed entry moment supported on the diagonal equals one under a positive-shape LKJ
law. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_of_offDiag_eq_zero (hη : 0 < η)
    {n : Fin p × Fin p → ℕ} (hn : ∀ q, q.1 ≠ q.2 → n q = 0) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η = 1 := by
  let _ := isProbabilityMeasure_lkjMeasure (p := p) hη
  rw [integral_prod_pow_coe_apply_lkjMeasure_eq_prod_strictLowerTriangle]
  have hzero (ij : strictLowerTriangle p) : n ij.1 + n ij.1.swap = 0 := by
    rw [hn ij.1 ij.2.ne', hn ij.1.swap ij.2.ne, add_zero]
  simp [hzero]

/-- In dimensions zero and one, every natural mixed entry moment under a positive-shape LKJ law
equals one. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_of_le_one (hp : p ≤ 1) (hη : 0 < η)
    (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η = 1 :=
  integral_prod_pow_coe_apply_lkjMeasure_of_offDiag_eq_zero hη fun q hne ↦
    (hne (Fin.ext (by omega))).elim

/-- Any natural mixed entry moment of `lkjMeasure` in which some coordinate axis `i` has odd total
incident degree vanishes. This holds for all real shapes `η`. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd
    (p : ℕ) (η : ℝ) (n : Fin p × Fin p → ℕ) {i : Fin p}
    (hodd : Odd (∑ j : Fin p, (n (i, j) + n (j, i)))) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂lkjMeasure p η = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by
    dsimp only [s]
    split_ifs <;> norm_num
  have hm : Measurable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) :=
    Finset.measurable_fun_prod _ fun q _ ↦
      (selfAdjoint.measurable_coe_apply q.1 q.2).pow_const (n q)
  have h := congrArg
    (fun ν : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ↦
      ∫ R, (∏ q, (R : Matrix (Fin p) (Fin p) ℝ) q.1 q.2 ^ n q) ∂ν)
    (map_symmetricCongruenceLinearMap_diagonal_lkjMeasure p η hs)
  rw [integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
    hm.aestronglyMeasurable] at h
  simp only [Matrix.coe_symmetricCongruenceLinearMap_diagonal_apply, s] at h
  simp_rw [Matrix.prod_pow_signFlip_mul_apply, hodd.neg_one_pow, neg_one_mul, integral_neg] at h
  linarith

/-- Every natural power of a single entry of an LKJ matrix belongs to every `Lᵠ`, including `L∞`. -/
theorem memLp_pow_coe_apply_lkjMeasure (p : ℕ) (η : ℝ) (i j : Fin p) (m : ℕ) (q : ℝ≥0∞) :
    MemLp (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m) q (lkjMeasure p η) := by
  simpa only [Matrix.prod_pow_single_apply] using
    memLp_prod_pow_coe_apply_lkjMeasure p η (Pi.single (i, j) m) q

/-- Every natural power of a single entry of an LKJ matrix is integrable, including at nonpositive
shapes where `lkjMeasure` is the zero measure. -/
theorem integrable_pow_coe_apply_lkjMeasure (p : ℕ) (η : ℝ) (i j : Fin p) (m : ℕ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m) (lkjMeasure p η) :=
  memLp_one_iff_integrable.mp (memLp_pow_coe_apply_lkjMeasure p η i j m 1)

/-- **Single-entry natural moments of the LKJ distribution.** For `η > 0`, diagonal entry powers
have expectation one, while off-diagonal entry powers have expectation
`B((m + 1) / 2, η + (p - 2) / 2) / B(1 / 2, η + (p - 2) / 2)` at even orders and zero at odd
orders. -/
theorem integral_pow_coe_apply_lkjMeasure (hη : 0 < η) (i j : Fin p) (m : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ^ m ∂lkjMeasure p η =
      if i = j then 1
      else if Even m then
        beta (((m : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, ← integral_prod_pow_coe_apply_lkjMeasure_of_offDiag_eq_zero hη
      (n := Pi.single (i, i) m) fun q hne ↦ by
        simp only [Pi.single_apply, Prod.ext_iff, ite_eq_right_iff, and_imp]
        rintro rfl hq
        exact (hne hq.symm).elim]
    simp_rw [Matrix.prod_pow_single_apply]
  · rw [ite_eq_right hij]
    have hp : (2 : ℝ) ≤ p := by
      have hi := i.isLt
      have hj := j.isLt
      have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
      exact_mod_cast (by omega : 2 ≤ p)
    have hα : 0 < η + ((p : ℝ) - 2) / 2 := by linarith
    rw [← integral_map (f := fun x : ℝ ↦ x ^ m)
        (selfAdjoint.measurable_coe_apply i j).aemeasurable
        (measurable_id.pow_const m).aestronglyMeasurable,
      map_coe_apply_lkjMeasure_of_ne hη hij]
    simpa only [Real.rpow_zero, mul_one, add_zero] using
      integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
        (r := 0) hα (by rwa [add_zero]) m

end LKJ

end TauCeti.Probability
