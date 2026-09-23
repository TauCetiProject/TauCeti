/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Marginal
public import TauCeti.Probability.Moments.Covariance

/-!
# Mean and covariance of the Dirichlet distribution

A Dirichlet law with positive concentration parameters on a nonempty coordinate type is carried by
the standard simplex, so it has moments of every order and its elementary moments can be read off
its block marginals.  For invalid parameters or an empty coordinate type, `dirichletMeasure a = 0`,
so the support, `MemLp`, integrability, and exponential-moment conclusions below are vacuous.
Writing `a₀ = ∑ j, a j` for the total concentration, the total of a nonempty block of
coordinates whose complement is also nonempty is a Beta variable with parameters the block
concentration and its complement, whence the mean
`a i / a₀` of a coordinate, the variance `a i * (a₀ - a i) / (a₀ ^ 2 * (a₀ + 1))`, and, by
polarization on a two-element block, the covariance `-(a i * a j) / (a₀ ^ 2 * (a₀ + 1))` of two
distinct coordinates.

The two degenerate blocks are not Beta but constant, and the block variance is stated for an
arbitrary block anyway: the total over the empty block is constantly `0` and the total over the
whole index type is almost surely `1`, and in both cases the complementary concentration factor
makes the stated value vanish.

## Main results

* `TauCeti.Probability.memLp_id_dirichletMeasure` — the valid Dirichlet law has moments of every
  order, while the other parameter cases reduce to the zero measure.
* `TauCeti.Probability.integral_id_dirichletMeasure` — the Bochner mean is the normalized
  concentration vector.
* `TauCeti.Probability.variance_sum_dirichletMeasure` — the variance of the total of a block of
  coordinates, with `TauCeti.Probability.variance_eval_dirichletMeasure` the one-coordinate case.
* `TauCeti.Probability.covariance_eval_dirichletMeasure_of_ne` — the covariance of two distinct
  coordinates.
* `TauCeti.Probability.integrableExpSet_inner_dirichletMeasure` — every directional exponential
  moment is finite.
* `TauCeti.Probability.covMatrix_dirichletMeasure` and
  `TauCeti.Probability.covarianceBilin_dirichletMeasure` — the matrix and bilinear-form packagings
  of the same data.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal RealInnerProductSpace

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι] {a : ι → ℝ}

/-! ### Moments of every order -/

omit [Nonempty ι] in
/-- With positive parameters on a nonempty coordinate type, a Dirichlet vector almost surely lies
in the closed unit ball. Otherwise `dirichletMeasure a = 0`, so the conclusion is vacuous. -/
theorem ae_norm_le_one_dirichletMeasure :
    ∀ᵐ x ∂dirichletMeasure a, ‖x‖ ≤ 1 := by
  by_cases h : Nonempty ι ∧ ∀ i, 0 < a i
  · let : Nonempty ι := h.1
    filter_upwards [ae_pos_dirichletMeasure h.2, ae_sum_eq_one_dirichletMeasure h.2]
      with x hpos hsum
    have hle : ∀ i, x i ≤ 1 := fun i ↦ hsum ▸
      Finset.single_le_sum (fun j _ ↦ (hpos j).le) (Finset.mem_univ i)
    have hsq : ∑ i, ‖x i‖ ^ 2 ≤ 1 := by
      rw [← hsum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [Real.norm_eq_abs, abs_of_pos (hpos i), sq]
      nlinarith [hpos i, hle i]
    rw [EuclideanSpace.norm_eq]
    simpa using Real.sqrt_le_sqrt hsq
  · rw [dirichletMeasure_eq_zero_of_invalid h]
    simp

omit [Nonempty ι] in
/-- With positive parameters on a nonempty coordinate type, the simplex-supported Dirichlet law has
moments of every order. Otherwise `dirichletMeasure a = 0`, so the `MemLp` conclusion is vacuous. -/
theorem memLp_id_dirichletMeasure (p : ℝ≥0∞) :
    MemLp id p (dirichletMeasure a) := by
  by_cases h : Nonempty ι ∧ ∀ i, 0 < a i
  · let : Nonempty ι := h.1
    have : IsProbabilityMeasure (dirichletMeasure a) := isProbabilityMeasure_dirichletMeasure h.2
    exact MemLp.of_bound aestronglyMeasurable_id 1 ae_norm_le_one_dirichletMeasure
  · rw [dirichletMeasure_eq_zero_of_invalid h]
    simp

omit [Nonempty ι] in
/-- Every coordinate of the valid Dirichlet law has moments of every order. For invalid parameters,
`dirichletMeasure a = 0`, so the `MemLp` conclusion is vacuous. -/
theorem memLp_eval_dirichletMeasure (i : ι) (p : ℝ≥0∞) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) p (dirichletMeasure a) :=
  (memLp_id_dirichletMeasure p).eval_piLp i

omit [Nonempty ι] in
/-- The identity is integrable for the simplex-supported Dirichlet law. For invalid parameters or
an empty coordinate type, `dirichletMeasure a = 0`, so the conclusion is vacuous. -/
theorem integrable_id_dirichletMeasure :
    Integrable id (dirichletMeasure a) :=
  memLp_one_iff_integrable.mp (memLp_id_dirichletMeasure 1)

/-! ### The mean -/

omit [Nonempty ι] in
/-- The mean of a Dirichlet coordinate is its share of the total concentration. -/
@[simp]
theorem integral_eval_dirichletMeasure (ha : ∀ i, 0 < a i) (i : ι) :
    ∫ x, x i ∂dirichletMeasure a = a i / ∑ j, a j := by
  classical
  rcases subsingleton_or_nontrivial ι with _ | _
  · have hcard : Fintype.card ι = 1 := Fintype.card_eq_one_iff.2 ⟨i, fun j ↦ Subsingleton.elim j i⟩
    rw [dirichletMeasure_eq_dirac_of_card_eq_one ha hcard, integral_dirac,
      Fintype.sum_subsingleton a i, div_self (ha i).ne']
    simp
  · have hβ : 0 < ∑ j with j ≠ i, a j := by
      obtain ⟨j, hj⟩ := exists_ne i
      exact Finset.sum_pos (fun k _ ↦ ha k) ⟨j, by simpa using hj⟩
    rw [← integral_map (f := fun x : ℝ ↦ x) (by fun_prop) aestronglyMeasurable_id,
      map_eval_dirichletMeasure ha i, integral_id_betaMeasure (ha i) hβ, Finset.filter_ne',
      Finset.add_sum_erase _ a (Finset.mem_univ i)]

omit [Nonempty ι] in
/-- The Bochner mean of a Dirichlet law is the normalized concentration vector. -/
@[simp]
theorem integral_id_dirichletMeasure (ha : ∀ i, 0 < a i) :
    ∫ x, x ∂dirichletMeasure a = (EuclideanSpace.equiv ι ℝ).symm fun i ↦ a i / ∑ j, a j := by
  refine (EuclideanSpace.equiv ι ℝ).injective ?_
  ext i
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (integrable_id_dirichletMeasure (a := a))
  simp only [EuclideanSpace.coe_proj, id_eq] at h
  simpa [← h] using integral_eval_dirichletMeasure ha i

/-! ### Variances and covariances -/

/-- The total of a block of Dirichlet coordinates has the variance of the Beta law of the block
and complementary concentrations.

Both degenerate blocks are included: the total over the empty block is constantly `0` and the
total over the whole index type is almost surely `1`, and in either case the stated value
vanishes. -/
theorem variance_sum_dirichletMeasure [DecidableEq ι] (ha : ∀ i, 0 < a i) (s : Finset ι) :
    Var[fun x ↦ ∑ i ∈ s, x i; dirichletMeasure a] =
      (∑ i ∈ s, a i) * (∑ i ∈ sᶜ, a i) / ((∑ i, a i) ^ 2 * ((∑ i, a i) + 1)) := by
  have _ : IsProbabilityMeasure (dirichletMeasure a) := isProbabilityMeasure_dirichletMeasure ha
  have hconst : ∀ c : ℝ, Var[fun _ : EuclideanSpace ℝ ι ↦ c; dirichletMeasure a] = 0 := by
    intro c
    rw [variance_eq_integral aemeasurable_const]
    simp
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa only [Finset.sum_empty, zero_mul, zero_div] using hconst 0
  rcases sᶜ.eq_empty_or_nonempty with hsc | hsc
  · have hsuniv : s = Finset.univ := by rwa [Finset.compl_eq_empty_iff] at hsc
    subst hsuniv
    rw [hsc, Finset.sum_empty, mul_zero, zero_div,
      variance_congr (ae_sum_eq_one_dirichletMeasure ha)]
    exact hconst 1
  · have hα : 0 < ∑ i ∈ s, a i := Finset.sum_pos (fun j _ ↦ ha j) hs
    have hβ : 0 < ∑ i ∈ sᶜ, a i := Finset.sum_pos (fun j _ ↦ ha j) hsc
    have hmeas : AEMeasurable (fun x : EuclideanSpace ℝ ι ↦ ∑ i ∈ s, x i) (dirichletMeasure a) := by
      fun_prop
    have hvar := variance_map (X := id) (Y := fun x : EuclideanSpace ℝ ι ↦ ∑ i ∈ s, x i)
      (by fun_prop) hmeas
    simp only [Function.comp_def, id_eq] at hvar
    rw [← hvar, map_sum_dirichletMeasure ha hs hsc, variance_id_betaMeasure hα hβ,
      Finset.sum_add_sum_compl]

/-- The variance of a Dirichlet coordinate. -/
@[simp]
theorem variance_eval_dirichletMeasure (ha : ∀ i, 0 < a i) (i : ι) :
    Var[fun x ↦ x i; dirichletMeasure a] =
      a i * ((∑ j, a j) - a i) / ((∑ j, a j) ^ 2 * ((∑ j, a j) + 1)) := by
  classical
  have hcompl : ∑ j ∈ ({i} : Finset ι)ᶜ, a j = (∑ j, a j) - a i := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_singleton (f := a) (a := i), Finset.sum_compl_add_sum]
  simpa only [Finset.sum_singleton, hcompl] using variance_sum_dirichletMeasure ha {i}

/-- The covariance of two distinct Dirichlet coordinates.  It is negative: the coordinates
compete for a fixed total. -/
@[simp]
theorem covariance_eval_dirichletMeasure_of_ne (ha : ∀ i, 0 < a i) {i j : ι}
    (hij : i ≠ j) :
    cov[fun x ↦ x i, fun x ↦ x j; dirichletMeasure a] =
      -(a i * a j) / ((∑ k, a k) ^ 2 * ((∑ k, a k) + 1)) := by
  classical
  have _ : IsProbabilityMeasure (dirichletMeasure a) := isProbabilityMeasure_dirichletMeasure ha
  have hT : 0 < ∑ k, a k := Finset.sum_pos (fun k _ ↦ ha k) Finset.univ_nonempty
  have hcompl : ∑ k ∈ ({i, j} : Finset ι)ᶜ, a k = (∑ k, a k) - a i - a j := by
    rw [sub_sub, eq_sub_iff_add_eq, ← Finset.sum_pair (f := a) hij, Finset.sum_compl_add_sum]
  have hpair := variance_sum_dirichletMeasure ha {i, j}
  simp only [Finset.sum_pair hij, hcompl] at hpair
  rw [variance_fun_add (memLp_eval_dirichletMeasure i 2) (memLp_eval_dirichletMeasure j 2),
    variance_eval_dirichletMeasure ha i, variance_eval_dirichletMeasure ha j] at hpair
  have hD : (∑ k, a k) ^ 2 * ((∑ k, a k) + 1) ≠ 0 := by positivity
  field_simp at hpair ⊢
  linarith

open scoped Classical in
/-- The covariance matrix of a Dirichlet law: the concentration-weighted diagonal minus the outer
square of the concentration vector, normalized by `a₀ ^ 2 * (a₀ + 1)`. -/
@[simp]
theorem covMatrix_dirichletMeasure (ha : ∀ i, 0 < a i) :
    covMatrix (dirichletMeasure a) =
      ((∑ k, a k) ^ 2 * ((∑ k, a k) + 1))⁻¹ •
        ((∑ k, a k) • Matrix.diagonal a - Matrix.vecMulVec a a) := by
  have hT : 0 < ∑ k, a k := Finset.sum_pos (fun k _ ↦ ha k) Finset.univ_nonempty
  have hD : (∑ k, a k) ^ 2 * ((∑ k, a k) + 1) ≠ 0 := by positivity
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · rw [covMatrix_apply, covariance_self (by fun_prop), variance_eval_dirichletMeasure ha i]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Matrix.vecMulVec_apply, smul_eq_mul]
    field_simp
  · rw [covMatrix_apply, covariance_eval_dirichletMeasure_of_ne ha hij]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.vecMulVec_apply, smul_eq_mul]
    field_simp
    ring

open scoped Classical in
/-- The covariance bilinear form of a Dirichlet law, read off its covariance matrix. -/
@[simp]
theorem covarianceBilin_dirichletMeasure (ha : ∀ i, 0 < a i)
    (x y : EuclideanSpace ℝ ι) :
    covarianceBilin (dirichletMeasure a) x y =
      ⟪x, (((∑ k, a k) ^ 2 * ((∑ k, a k) + 1))⁻¹ •
        ((∑ k, a k) • Matrix.diagonal a - Matrix.vecMulVec a a)).toEuclideanLin y⟫ := by
  have _ : IsProbabilityMeasure (dirichletMeasure a) := isProbabilityMeasure_dirichletMeasure ha
  rw [← covMatrix_dirichletMeasure ha]
  exact covarianceBilin_eq_covMatrix _ (memLp_id_dirichletMeasure 2) x y

/-! ### Exponential moments -/

omit [Nonempty ι] in
/-- With positive parameters on a nonempty coordinate type, every directional exponential moment
of the Dirichlet law is finite because the law is carried by the bounded standard simplex.
Otherwise `dirichletMeasure a = 0`, so the conclusion is vacuous. -/
theorem integrableExpSet_inner_dirichletMeasure (θ : EuclideanSpace ℝ ι) :
    integrableExpSet (fun x ↦ ⟪θ, x⟫) (dirichletMeasure a) = Set.univ := by
  by_cases h : Nonempty ι ∧ ∀ i, 0 < a i
  · let : Nonempty ι := h.1
    have _ : IsProbabilityMeasure (dirichletMeasure a) := isProbabilityMeasure_dirichletMeasure h.2
    ext t
    simp only [Set.mem_univ, iff_true, integrableExpSet, Set.mem_ofPred_eq]
    refine Integrable.mono' (integrable_const (Real.exp (|t| * ‖θ‖))) (by fun_prop) ?_
    filter_upwards [ae_norm_le_one_dirichletMeasure] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc t * ⟪θ, x⟫ ≤ |t * ⟪θ, x⟫| := le_abs_self _
      _ = |t| * |⟪θ, x⟫| := abs_mul _ _
      _ ≤ |t| * (‖θ‖ * ‖x‖) := by gcongr; exact abs_real_inner_le_norm θ x
      _ ≤ |t| * (‖θ‖ * 1) := by gcongr
      _ = |t| * ‖θ‖ := by ring
  · rw [dirichletMeasure_eq_zero_of_invalid h]
    simp [integrableExpSet]

end Probability

end TauCeti
