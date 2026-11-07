/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
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
* `TauCeti.Probability.lkjNormalizer_eq_prod_strictLowerTriangle` — one factor for each partial
  correlation.

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

/-- The strictly lower positions in zero-based column `j` are the rows below it, so there are
`p - 1 - j` of them. -/
private theorem card_filter_strictLowerTriangle_snd_eq (j : Fin p) :
    (Finset.univ.filter fun ij : strictLowerTriangle p ↦ ij.1.2 = j).card = p - 1 - j := by
  rw [← Fin.card_Ioi j]
  refine Finset.card_bij (fun ij _ ↦ ij.1.1) (fun ij hij ↦ ?_) (fun ij hij kl hkl h ↦ ?_)
    fun i hi ↦ ⟨⟨(i, j), Finset.mem_Ioi.1 hi⟩, by simp, rfl⟩
  · rw [(Finset.mem_filter.1 hij).2.symm]
    exact Finset.mem_Ioi.2 ij.2
  · exact Subtype.ext
      (Prod.ext h ((Finset.mem_filter.1 hij).2.trans (Finset.mem_filter.1 hkl).2.symm))

/-- The LKJ normalizer has one beta factor for each partial correlation: the coordinate in
zero-based column `j` contributes `B(1 / 2, η + (p - j - 2) / 2)`. Dimensions are cast to the
reals before subtraction and division. -/
theorem lkjNormalizer_eq_prod_strictLowerTriangle (p : ℕ) (η : ℝ) :
    lkjNormalizer p η = ∏ ij : strictLowerTriangle p,
      ProbabilityTheory.beta (1 / 2) (η + ((p : ℝ) - ij.1.2.val - 2) / 2) := by
  set f : ℕ → ℝ := fun j ↦ ProbabilityTheory.beta (1 / 2) (η + ((p : ℝ) - j - 2) / 2)
  calc
    _ = ∏ j ∈ Finset.range p, f j ^ (p - 1 - j) := by
      rcases p with _ | p
      · simp
      rw [Finset.prod_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one,
        lkjNormalizer_eq_prod_columns, Finset.prod_Ico_eq_prod_range]
      refine Finset.prod_congr (by simp) fun j hj ↦ ?_
      have hj : j < p := Finset.mem_range.1 hj
      rw [show p + 1 - (1 + j) = p - j by omega]
      congr 3
      push_cast [Nat.cast_sub hj.le]
      ring
    _ = ∏ j : Fin p, ∏ ij : strictLowerTriangle p with ij.1.2 = j, f ij.1.2 := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [Finset.prod_congr rfl fun ij hij ↦ by rw [(Finset.mem_filter.1 hij).2],
        Finset.prod_const, card_filter_strictLowerTriangle_snd_eq]
    _ = _ := Finset.prod_fiberwise _ _ _

end TauCeti.Probability
