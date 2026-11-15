/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Antigravity
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import TauCeti.Probability.Distributions.LKJ.Cholesky.Moments
import TauCeti.Algebra.BigOperators.Pi
import TauCeti.Probability.Distributions.LKJ.Marginal
import TauCeti.Analysis.Matrix.PosSemidef.Basic

/-!
# Mixed entry moments of the LKJ law

Every natural monomial in the entries of an LKJ correlation matrix belongs to every `Lᵖ`,
including `L∞`, and is therefore integrable (`memLp_prod_pow_coe_apply_lkjMeasure` and
`integrable_prod_pow_coe_apply_lkjMeasure`). Positive-semidefiniteness and unit diagonal bound
every matrix entry in absolute value by one; nonpositive shapes give the zero measure.

At positive shape `η`, pushing forward through the independent centered-Beta partial-correlation
Gram representation `R = L Lᵀ` expands any natural entry monomial into a finite multinomial sum of
lower-triangular Cholesky monomials, each of which factors over the strictly lower coordinates into
natural powers of `z ij` and nonnegative half-integer powers of `1 - z ij ^ 2`. Independence and
symmetric-Beta integration then evaluate every mixed entry moment as a finite sum of products of
Beta quotients (`integral_prod_pow_coe_apply_lkjMeasure`).

## Main results

* `TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure` and
  `TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure`: all natural entry monomials lie
  in every `Lᵖ` and are integrable.
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure`: closed finite Beta-quotient
  evaluation of arbitrary natural mixed entry moments at `η > 0`.
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_congr_add_swap` and
  `TauCeti.Probability.integral_prod_pow_coe_apply_perm_lkjMeasure`: invariance under symmetrized
  off-diagonal exponent redistribution (including diagonal changes and transposition) and under
  coordinate permutations.
* `TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd`: vanishing whenever
  any coordinate index has odd total incident degree.
* `TauCeti.Probability.integral_pow_coe_apply_lkjMeasure`: closed natural moments of any single
  entry.
* `ProbabilityTheory.HasLaw` companions for random matrices with an LKJ law.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

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

/-- **Mixed entry moments of the LKJ law.** For `η > 0`, expanding `R = L Lᵀ` in the independent
centered-Beta partial-correlation representation expresses the expectation of any natural monomial
`∏ ij, R ij.1 ij.2 ^ n ij` as a finite multinomial sum of products of Beta quotients. -/
theorem integral_prod_pow_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂lkjMeasure p η =
      ∑ c ∈ Fintype.piFinset (fun q ↦ (Finset.Iic (min q.1 q.2)).piAntidiag (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij, if Even (gramMonomialExponent c ij.1) then
            beta (((gramMonomialExponent c ij.1 : ℝ) + 1) / 2)
                (lkjPartialCorrelationShape p η ij +
                  partialCorrelationCholeskyMonomialResidualPower
                    (gramMonomialExponent c) ij) /
              beta (1 / 2) (lkjPartialCorrelationShape p η ij)
          else 0 := by
  have hshape (ij : strictLowerTriangle p) : 0 < lkjPartialCorrelationShape p η ij :=
    lkjPartialCorrelationShape_pos hη ij
  let _ (ij : strictLowerTriangle p) :
      IsProbabilityMeasure (betaMeasure (lkjPartialCorrelationShape p η ij)
        (lkjPartialCorrelationShape p η ij)) :=
    isProbabilityMeasureBeta (hshape ij) (hshape ij)
  let g : Matrix (Fin p) (Fin p) ℝ → ℝ := fun M ↦ ∏ ij, M ij.1 ij.2 ^ n ij
  have hg : Measurable g := Finset.measurable_fun_prod _ fun ij _ ↦
    Matrix.measurable_apply.pow_const (n ij)
  refine (integral_map (f := g) measurable_subtype_coe.aemeasurable
    hg.aestronglyMeasurable).symm.trans ?_
  rw [map_coe_lkjMeasure hη,
    integral_map continuous_partialCorrelationGram.measurable.aemeasurable
      hg.aestronglyMeasurable]
  exact integral_prod_pow_partialCorrelationGram_pi_betaMeasure hshape n

/-- In dimensions zero and one, every natural mixed entry moment under a positive-shape LKJ law
equals one. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_of_le_one {p : ℕ} {η : ℝ}
    (hp : p ≤ 1) (hη : 0 < η) (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂lkjMeasure p η = 1 := by
  rw [lkjMeasure_of_le_one hp hη, integral_dirac]
  apply Finset.prod_eq_one
  intro ij _
  have hij : ij.1 = ij.2 := by
    have := ij.1.isLt
    have := ij.2.isLt
    exact Fin.ext (by omega)
  rw [Submodule.coe_mk (p := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) 1
    (IsSelfAdjoint.one _), hij, Matrix.one_apply_eq, one_pow]

/-- **Symmetric-exponent invariance of LKJ mixed moments.** Because an LKJ matrix is symmetric and
has unit diagonal almost surely, a mixed entry moment depends only on the unordered off-diagonal
exponent sums `m (i, j) + m (j, i)` for `i ≠ j`. This also holds at nonpositive shapes, where the
measure is zero. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_congr_add_swap (p : ℕ) (η : ℝ)
    {m n : Fin p × Fin p → ℕ}
    (hmn : ∀ i j, i ≠ j → m (i, j) + m (j, i) = n (i, j) + n (j, i)) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ m ij) ∂lkjMeasure p η =
      ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂lkjMeasure p η := by
  by_cases hη : 0 < η
  · refine integral_congr_ae ((ae_diag_eq_one_lkjMeasure p η).mono fun R hdiag ↦ ?_)
    have hsymm : (R : Matrix (Fin p) (Fin p) ℝ).IsSymm :=
      Matrix.isHermitian_iff_isSymm.1 (selfAdjoint.isHermitian_coe R)
    refine (hsymm.prod_pow_apply_eq_prod_strictLowerTriangle hdiag m).trans
      ((Finset.prod_congr rfl fun ij _ ↦ ?_).trans
        (hsymm.prod_pow_apply_eq_prod_strictLowerTriangle hdiag n).symm)
    rw [Prod.swap_prod_mk, hmn ij.1.1 ij.1.2 (ne_of_gt ij.2)]
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- Because diagonal entries of an LKJ matrix equal one almost surely, changing only diagonal
exponents does not alter any mixed entry moment. This also holds at nonpositive shapes, where the
measure is zero. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_congr_offDiag (p : ℕ) (η : ℝ)
    {m n : Fin p × Fin p → ℕ} (hmn : ∀ i j, i ≠ j → m (i, j) = n (i, j)) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ m ij) ∂lkjMeasure p η =
      ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂lkjMeasure p η :=
  integral_prod_pow_coe_apply_lkjMeasure_congr_add_swap p η fun i j hij ↦ by
    rw [hmn i j hij, hmn j i hij.symm]

/-- **Permutation invariance of LKJ mixed moments.** Relabelling coordinate indices by a
permutation `σ` preserves every mixed entry moment of `lkjMeasure p η`. -/
theorem integral_prod_pow_coe_apply_perm_lkjMeasure (p : ℕ) (η : ℝ)
    (σ : Equiv.Perm (Fin p)) (n : Fin p × Fin p → ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) (σ ij.1) (σ ij.2) ^ n ij) ∂lkjMeasure p η =
      ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂lkjMeasure p η := by
  have hlaw : HasLaw (Matrix.symmetricCongruenceLinearMap (σ.permMatrix ℝ))
      (lkjMeasure p η) (lkjMeasure p η) :=
    ⟨(LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable,
      map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure p η σ⟩
  let f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ := fun R ↦
    ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij
  have hf : Measurable f := Finset.measurable_fun_prod _ fun ij _ ↦
    (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const (n ij)
  simpa only [Function.comp_apply, f, Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply,
    Matrix.submatrix_apply] using hlaw.integral_comp hf.aestronglyMeasurable

private theorem prod_pow_sign_mul {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (n : Fin p × Fin p → ℕ) (v : Fin p) :
    (∏ ij : Fin p × Fin p,
        ((if ij.1 = v then (-1 : ℝ) else 1) * M ij.1 ij.2 *
          (if ij.2 = v then (-1 : ℝ) else 1)) ^ n ij) =
      (-1 : ℝ) ^ ((∑ j, n (v, j)) + ∑ i, n (i, v)) *
        ∏ ij : Fin p × Fin p, M ij.1 ij.2 ^ n ij := by
  simp_rw [mul_right_comm _ (M _ _), mul_pow, Finset.prod_mul_distrib, pow_add]
  congr 1
  congr 1
  · rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp [Finset.prod_pow_eq_pow_sum]
  · simp [Fintype.prod_prod_type, Finset.prod_pow_eq_pow_sum]

/-- **Odd-degree vanishing of LKJ mixed moments.** If any coordinate index `v` has odd total
exponent `(∑ j, n (v, j)) + ∑ i, n (i, v)` in a matrix monomial, then its expectation under
`lkjMeasure p η` vanishes. Flipping the sign of axis `v` preserves the law and negates the
monomial. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd (p : ℕ) (η : ℝ)
    (n : Fin p × Fin p → ℕ) {v : Fin p}
    (hv : Odd ((∑ j, n (v, j)) + ∑ i, n (i, v))) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂lkjMeasure p η = 0 := by
  let s : Fin p → ℝ := fun k ↦ if k = v then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by by_cases hk : k = v <;> simp [s, hk]
  have hlaw : HasLaw (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s))
      (lkjMeasure p η) (lkjMeasure p η) :=
    ⟨(LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable,
      map_symmetricCongruenceLinearMap_diagonal_lkjMeasure p η hs⟩
  let f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ := fun R ↦
    ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij
  have hf : Measurable f := Finset.measurable_fun_prod _ fun ij _ ↦
    (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const (n ij)
  have hcomp := hlaw.integral_comp hf.aestronglyMeasurable
  have hneg : f ∘ Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s) = -f := by
    funext R
    simp only [Function.comp_apply, Pi.neg_apply, f,
      Matrix.coe_symmetricCongruenceLinearMap_diagonal_apply, s]
    rw [prod_pow_sign_mul, hv.neg_one_pow, neg_one_mul]
  rw [hneg, Pi.neg_def, integral_neg] at hcomp
  linarith

/-- Every natural power of a single entry of an LKJ matrix belongs to every `Lᵖ`, including
`L∞`. -/
theorem memLp_pow_coe_apply_lkjMeasure (p : ℕ) (η : ℝ) (i j : Fin p) (k : ℕ) (q : ℝ≥0∞) :
    MemLp (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ k) q (lkjMeasure p η) := by
  have hsingle (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    Fintype.prod_pow_pi_single
      (fun ij : Fin p × Fin p ↦ (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2) (i, j) k
  simpa only [hsingle] using memLp_prod_pow_coe_apply_lkjMeasure p η (Pi.single (i, j) k) q

/-- Every natural power of a single entry of an LKJ matrix is integrable. -/
theorem integrable_pow_coe_apply_lkjMeasure (p : ℕ) (η : ℝ) (i j : Fin p) (k : ℕ) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j ^ k) (lkjMeasure p η) :=
  memLp_one_iff_integrable.mp (memLp_pow_coe_apply_lkjMeasure p η i j k 1)

/-- At positive shape, every natural power of a diagonal entry of an LKJ matrix has expectation
one. -/
theorem integral_pow_coe_apply_self_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (i : Fin p) (k : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i i ^ k ∂lkjMeasure p η = 1 := by
  refine (integral_map (f := fun x : ℝ ↦ x ^ k)
    (selfAdjoint.measurable_coe_apply i i).aemeasurable (by fun_prop)).symm.trans ?_
  rw [map_coe_apply_self_lkjMeasure hη i, integral_dirac, one_pow]

/-- **Natural moments of an off-diagonal LKJ entry.** For `η > 0` and `i ≠ j`, the `k`-th moment
of `R i j` under `lkjMeasure p η` vanishes for odd `k` and equals the Beta quotient
`beta ((k + 1) / 2) α / beta (1 / 2) α` with `α = η + (p - 2) / 2` for even `k`. -/
theorem integral_pow_coe_apply_lkjMeasure_of_ne {p : ℕ} {η : ℝ} (hη : 0 < η)
    {i j : Fin p} (hij : i ≠ j) (k : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ^ k ∂lkjMeasure p η =
      if Even k then
        beta (((k : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  have hp2 : 2 ≤ p := by
    have := i.isLt
    have := j.isLt
    have := Fin.val_ne_of_ne hij
    omega
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hα : 0 < η + ((p : ℝ) - 2) / 2 := by linarith
  refine (integral_map (f := fun x : ℝ ↦ x ^ k)
    (selfAdjoint.measurable_coe_apply i j).aemeasurable (by fun_prop)).symm.trans ?_
  rw [map_coe_apply_lkjMeasure_of_ne hη hij]
  simpa using integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
    (r := 0) hα (by simpa using hα) k

/-- **Natural moments of any single entry of an LKJ matrix.** At positive shape `η`, diagonal
entries have moments equal to one and off-diagonal entries have the symmetric-Beta moments of
shape `η + (p - 2) / 2`. -/
theorem integral_pow_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (i j : Fin p) (k : ℕ) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ^ k ∂lkjMeasure p η =
      if i = j then 1
      else if Even k then
        beta (((k : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, integral_pow_coe_apply_self_lkjMeasure hη i k]
  · rw [ite_eq_right hij, integral_pow_coe_apply_lkjMeasure_of_ne hη hij k]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ} {η : ℝ}
  {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- Every natural monomial in the entries of a random matrix with an LKJ law belongs to every
`Lᵖ`, including `L∞`. -/
theorem memLp_prod_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P)
    (n : Fin p × Fin p → ℕ) (q : ℝ≥0∞) :
    MemLp (fun ω ↦ ∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) q P :=
  hX.memLp_fun_comp (TauCeti.Probability.memLp_prod_pow_coe_apply_lkjMeasure p η n q)

/-- Every natural mixed entry moment of a random matrix with an LKJ law is integrable. -/
theorem integrable_prod_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P)
    (n : Fin p × Fin p → ℕ) :
    Integrable (fun ω ↦ ∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_prod_pow_coe_apply_lkjMeasure p η n)

/-- **Mixed entry moments of a random LKJ matrix.** -/
theorem integral_prod_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P) (hη : 0 < η)
    (n : Fin p × Fin p → ℕ) :
    (∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂P) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ (Finset.Iic (min q.1 q.2)).piAntidiag (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : ℝ)) *
          ∏ ij, if Even (TauCeti.gramMonomialExponent c ij.1) then
            beta (((TauCeti.gramMonomialExponent c ij.1 : ℝ) + 1) / 2)
                (TauCeti.Probability.lkjPartialCorrelationShape p η ij +
                  TauCeti.partialCorrelationCholeskyMonomialResidualPower
                    (TauCeti.gramMonomialExponent c) ij) /
              beta (1 / 2) (TauCeti.Probability.lkjPartialCorrelationShape p η ij)
          else 0 := by
  let f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ := fun R ↦
    ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij
  have hf : Measurable f := Finset.measurable_fun_prod _ fun ij _ ↦
    (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const (n ij)
  exact (hX.integral_comp (f := f) hf.aestronglyMeasurable).trans
    (TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure hη n)

/-- **Symmetric-exponent invariance of mixed moments of a random LKJ matrix.** -/
theorem integral_prod_pow_coe_apply_lkjMeasure_congr_add_swap
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P) {m n : Fin p × Fin p → ℕ}
    (hmn : ∀ i j, i ≠ j → m (i, j) + m (j, i) = n (i, j) + n (j, i)) :
    (∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ m ij) ∂P) =
      ∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂P := by
  have hm : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ m ij :=
    Finset.measurable_fun_prod _ fun ij _ ↦ (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const _
  have hn : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij :=
    Finset.measurable_fun_prod _ fun ij _ ↦ (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const _
  exact (hX.integral_comp hm.aestronglyMeasurable).trans
    ((TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_congr_add_swap p η hmn).trans
      (hX.integral_comp hn.aestronglyMeasurable).symm)

/-- Changing only diagonal exponents does not alter any mixed entry moment of a random LKJ
matrix. -/
theorem integral_prod_pow_coe_apply_lkjMeasure_congr_offDiag
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P) {m n : Fin p × Fin p → ℕ}
    (hmn : ∀ i j, i ≠ j → m (i, j) = n (i, j)) :
    (∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ m ij) ∂P) =
      ∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂P :=
  hX.integral_prod_pow_coe_apply_lkjMeasure_congr_add_swap fun i j hij ↦ by
    rw [hmn i j hij, hmn j i hij.symm]

/-- **Permutation invariance of mixed moments of a random LKJ matrix.** -/
theorem integral_prod_pow_coe_apply_perm_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P)
    (σ : Equiv.Perm (Fin p)) (n : Fin p × Fin p → ℕ) :
    (∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) (σ ij.1) (σ ij.2) ^ n ij) ∂P) =
      ∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂P := by
  have hσ : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) (σ ij.1) (σ ij.2) ^ n ij :=
    Finset.measurable_fun_prod _ fun ij _ ↦
      (selfAdjoint.measurable_coe_apply (σ ij.1) (σ ij.2)).pow_const _
  have hn : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij :=
    Finset.measurable_fun_prod _ fun ij _ ↦ (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const _
  exact (hX.integral_comp hσ.aestronglyMeasurable).trans
    ((TauCeti.Probability.integral_prod_pow_coe_apply_perm_lkjMeasure p η σ n).trans
      (hX.integral_comp hn.aestronglyMeasurable).symm)

/-- **Odd-degree vanishing of mixed moments of a random LKJ matrix.** -/
theorem integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P)
    (n : Fin p × Fin p → ℕ) {v : Fin p}
    (hv : Odd ((∑ j, n (v, j)) + ∑ i, n (i, v))) :
    (∫ ω, (∏ ij, (X ω : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij) ∂P) = 0 := by
  have hn : Measurable fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ∏ ij, (R : Matrix (Fin p) (Fin p) ℝ) ij.1 ij.2 ^ n ij :=
    Finset.measurable_fun_prod _ fun ij _ ↦ (selfAdjoint.measurable_coe_apply ij.1 ij.2).pow_const _
  exact (hX.integral_comp hn.aestronglyMeasurable).trans
    (TauCeti.Probability.integral_prod_pow_coe_apply_lkjMeasure_eq_zero_of_odd p η n hv)

/-- Every natural power of a single entry of a random matrix with an LKJ law belongs to every
`Lᵖ`, including `L∞`. -/
theorem memLp_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P)
    (i j : Fin p) (k : ℕ) (q : ℝ≥0∞) :
    MemLp (fun ω ↦ (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ k) q P :=
  hX.memLp_fun_comp (TauCeti.Probability.memLp_pow_coe_apply_lkjMeasure p η i j k q)

/-- Every natural power of a single entry of a random matrix with an LKJ law is integrable. -/
theorem integrable_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P)
    (i j : Fin p) (k : ℕ) :
    Integrable (fun ω ↦ (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ k) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_pow_coe_apply_lkjMeasure p η i j k)

/-- **Natural moments of a single entry of a random LKJ matrix.** -/
theorem integral_pow_coe_apply_lkjMeasure
    (hX : HasLaw X (TauCeti.Probability.lkjMeasure p η) P) (hη : 0 < η)
    (i j : Fin p) (k : ℕ) :
    (∫ ω, (X ω : Matrix (Fin p) (Fin p) ℝ) i j ^ k ∂P) =
      if i = j then 1
      else if Even k then
        beta (((k : ℝ) + 1) / 2) (η + ((p : ℝ) - 2) / 2) /
          beta (1 / 2) (η + ((p : ℝ) - 2) / 2)
      else 0 := by
  let f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ := fun R ↦
    (R : Matrix (Fin p) (Fin p) ℝ) i j ^ k
  have hf : Measurable f := (selfAdjoint.measurable_coe_apply i j).pow_const k
  exact (hX.integral_comp (f := f) hf.aestronglyMeasurable).trans
    (TauCeti.Probability.integral_pow_coe_apply_lkjMeasure hη i j k)

end ProbabilityTheory.HasLaw
