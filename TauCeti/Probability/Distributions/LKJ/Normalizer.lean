/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Probability.Distributions.Beta.Measurability

/-!
# The LKJ normalizing constant

The density of the LKJ law of shape `η` on `p × p` correlation matrices is proportional to
`det R ^ (η - 1)`.  In partial-correlation coordinates its normalizing constant is a finite
product of Euler beta functions.  This file defines that product and records the algebraic API
needed to normalize the density.

We index the factors by `k = p - j`, where `j` is the one-based column index in the usual
partial-correlation formula.  Thus

`lkjNormalizer p η = ∏ k ∈ Finset.Ico 1 p, beta (1 / 2) (η + (k - 1) / 2) ^ k`.

The reflected-index theorem gives the equivalent column-indexed form.  Legendre's duplication
formula also rewrites every factor as the normalizer of a symmetric beta law; this is the form
used by the independent-beta construction of LKJ partial correlations.

## Main declarations

* `TauCeti.Probability.lkjNormalizer` — the LKJ normalizing constant.
* `TauCeti.Probability.lkjNormalizer_eq_prod_columns` — the conventional one-based
  column-indexed formula.
* `TauCeti.Probability.lkjNormalizer_succ` — the recurrence in the matrix dimension.
* `TauCeti.Probability.lkjNormalizer_eq_prod_beta_self` — the symmetric-beta form of the
  product.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti.Probability

/-- The normalizing constant for the `p × p` LKJ correlation-matrix law of shape `η`.

The factor indexed by `k` occurs once for each of the `k` partial correlations in the
corresponding column of the triangular parametrization.  The intended parameter range is
`0 < η`; the formula is left total outside that range. -/
def lkjNormalizer (p : ℕ) (η : ℝ) : ℝ :=
  ∏ k ∈ Finset.Ico 1 p,
    ProbabilityTheory.beta (1 / 2) (η + ((k : ℝ) - 1) / 2) ^ k

/-- The defining row-indexed beta product for the LKJ normalizing constant. -/
theorem lkjNormalizer_def (p : ℕ) (η : ℝ) :
    lkjNormalizer p η =
      ∏ k ∈ Finset.Ico 1 p,
        ProbabilityTheory.beta (1 / 2) (η + ((k : ℝ) - 1) / 2) ^ k := by
  rw [lkjNormalizer]

/-- The LKJ normalizer in the conventional one-based column indexing.  The column `j` contributes
`p - j` partial correlations, each with second beta parameter
`η + (p - j - 1) / 2`. -/
theorem lkjNormalizer_eq_prod_columns (p : ℕ) (η : ℝ) :
    lkjNormalizer p η =
      ∏ j ∈ Finset.Ico 1 p,
        ProbabilityTheory.beta (1 / 2)
          (η + (((p - j : ℕ) : ℝ) - 1) / 2) ^ (p - j) := by
  simpa [lkjNormalizer] using (Finset.prod_Ico_reflect
    (fun k : ℕ ↦ ProbabilityTheory.beta (1 / 2)
      (η + ((k : ℝ) - 1) / 2) ^ k) 1 (m := p) (n := p) p.le_succ).symm

/-- In dimensions zero and one the LKJ normalizing constant is the empty product. -/
@[simp]
theorem lkjNormalizer_zero (η : ℝ) : lkjNormalizer 0 η = 1 := by
  simp [lkjNormalizer]

/-- In dimension one the LKJ normalizing constant is one. -/
@[simp]
theorem lkjNormalizer_one (η : ℝ) : lkjNormalizer 1 η = 1 := by
  simp [lkjNormalizer]

/-- In dimension two the single free correlation has beta normalizer `B(1/2, η)`. -/
@[simp]
theorem lkjNormalizer_two (η : ℝ) :
    lkjNormalizer 2 η = ProbabilityTheory.beta (1 / 2) η := by
  norm_num [lkjNormalizer]

/-- Increasing the matrix dimension appends the `k = p` product factor, corresponding after
reindexing to the first column in dimension `p + 1`. -/
theorem lkjNormalizer_succ (p : ℕ) (η : ℝ) :
    lkjNormalizer (p + 1) η = lkjNormalizer p η *
      ProbabilityTheory.beta (1 / 2) (η + ((p : ℝ) - 1) / 2) ^ p := by
  rcases p with _ | p
  · simp
  · exact Finset.prod_Ico_succ_top (Nat.succ_pos p) _

/-- Every beta parameter in the LKJ normalizer is positive when the shape is positive. -/
private theorem lkj_betaParameter_pos {η : ℝ} (hη : 0 < η) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 p) :
    0 < η + ((k : ℝ) - 1) / 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
  positivity

/-- The LKJ normalizing constant is strictly positive on its parameter domain. -/
theorem lkjNormalizer_pos {p : ℕ} {η : ℝ} (hη : 0 < η) : 0 < lkjNormalizer p η := by
  rw [lkjNormalizer]
  exact Finset.prod_pos fun k hk ↦ pow_pos
    (ProbabilityTheory.beta_pos (by norm_num) (lkj_betaParameter_pos hη hk)) k

/-- The LKJ normalizing constant does not vanish on its parameter domain. -/
theorem lkjNormalizer_ne_zero {p : ℕ} {η : ℝ} (hη : 0 < η) :
    lkjNormalizer p η ≠ 0 :=
  (lkjNormalizer_pos hη).ne'

/-- The LKJ normalizer is Borel measurable as a function of its shape parameter. -/
@[fun_prop]
theorem measurable_lkjNormalizer (p : ℕ) : Measurable (lkjNormalizer p) := by
  unfold lkjNormalizer
  refine Finset.measurable_prod _ fun k _ ↦ ?_
  have hk : Measurable fun η : ℝ ↦ η + ((k : ℝ) - 1) / 2 := by fun_prop
  exact (measurable_beta.comp (measurable_const.prodMk hk)).pow_const k

/-- Legendre's duplication formula rewrites the LKJ normalizer as a product of symmetric-beta
normalizers.  This is the factorization used when partial correlations are constructed from
independent symmetric beta variables on `(0, 1)`. -/
theorem lkjNormalizer_eq_prod_beta_self {p : ℕ} {η : ℝ} (hη : 0 < η) :
    lkjNormalizer p η =
      ∏ k ∈ Finset.Ico 1 p,
        ((2 : ℝ) ^ (2 * (η + ((k : ℝ) - 1) / 2) - 1) *
          ProbabilityTheory.beta (η + ((k : ℝ) - 1) / 2)
            (η + ((k : ℝ) - 1) / 2)) ^ k := by
  rw [lkjNormalizer]
  apply Finset.prod_congr rfl
  intro k hk
  rw [ProbabilityTheory.beta_one_half_left_eq_two_rpow_mul_beta_self
    (lkj_betaParameter_pos hη hk)]

end TauCeti.Probability
