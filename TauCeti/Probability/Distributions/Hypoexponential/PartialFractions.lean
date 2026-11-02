/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import TauCeti.Algebra.Polynomial.BigOperators
import TauCeti.Analysis.Calculus.Deriv.Polynomial

/-!
# Partial fractions for the hypoexponential Laplace transform

For positive rates `λ i`, indexed by a nonempty finite type, the Laplace transform of the
hypoexponential law is the rational function `∏ i, λ i / (z + λ i)`. Group the rates by their
distinct values `ρ`, with multiplicities `m ρ`. For arbitrary real rates, this rational function
is the sum of its principal parts at the points `-ρ`:

`∏ i, λ i / (z + λ i) = ∑ ρ, ∑ k ∈ [1, m ρ], A ρ k / (z + ρ) ^ k`.

The coefficient `A ρ k` is the Taylor coefficient of order `m ρ - k` at `-ρ` of the function
obtained by removing the factors with rate `ρ`. It may be negative.

Evaluating at `z = 0` shows that, for nonzero rates, the numbers `A ρ k / ρ ^ k` sum to one.
When all rates are positive, each term `A ρ k / (z + ρ) ^ k` is the Laplace transform of
`A ρ k / ρ ^ k` times the Erlang law of shape `k` and rate `ρ`, so the expansion writes the
hypoexponential density and cdf as combinations of Erlang densities and cdfs, with these numbers
as the weights.

The identity holds for `z` in any field over `ℝ`, so it applies both to the real Laplace
transform and, at `z = -i t`, to the characteristic function.

## Main definitions

* `TauCeti.Probability.hypoexponentialCoeff r ρ k`: the coefficient `A ρ k`.

## Main results

* `TauCeti.Probability.prod_div_add_eq_sum_hypoexponentialCoeff`: the partial-fraction expansion.
* `TauCeti.Probability.hypoexponentialCoeff_def`: the iterated-derivative characterization of the
  coefficient.
* `TauCeti.Probability.hypoexponentialCoeff_card`: the coefficient of highest order at a pole is
  the value there of the remaining factors.
* `TauCeti.Probability.sum_hypoexponentialCoeff_div_pow`: for nonzero rates, the numbers
  `A ρ k / ρ ^ k` sum to one.
-/

public section

noncomputable section

open Finset Nat Polynomial

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The partial-fraction coefficient of `∏ i, r i / (z + r i)` at the pole `-ρ` and order `k`.
With `m = #{i | r i = ρ}`, it is the Taylor coefficient of order `m - k` at `-ρ` of
`z ↦ (∏ i, r i) / ∏ i with r i ≠ ρ, (z + r i)`; grouping the factors by rate, this denominator is
`∏ q, (z + q) ^ m q` over the distinct rates `q ≠ ρ`. Only the orders `1 ≤ k ≤ m` enter the
expansion `prod_div_add_eq_sum_hypoexponentialCoeff`. -/
def hypoexponentialCoeff (r : ι → ℝ) (ρ : ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv (#{i | r i = ρ} - k)
      (fun z ↦ (∏ i, r i) / ∏ i with r i ≠ ρ, (z + r i)) (-ρ) / (#{i | r i = ρ} - k)!

/-- The defining iterated-derivative formula for a hypoexponential partial-fraction coefficient. -/
theorem hypoexponentialCoeff_def (r : ι → ℝ) (ρ : ℝ) (k : ℕ) :
    hypoexponentialCoeff r ρ k =
      iteratedDeriv (#{i | r i = ρ} - k)
        (fun z ↦ (∏ i, r i) / ∏ i with r i ≠ ρ, (z + r i)) (-ρ) /
          (#{i | r i = ρ} - k)! := by
  rw [hypoexponentialCoeff]

/-- The coefficient of the highest-order term `(z + ρ) ^ (-m)` at the pole `-ρ` of multiplicity
`m` is the value at `-ρ` of the remaining factors. For a simple pole this is the whole principal
part. -/
@[simp]
theorem hypoexponentialCoeff_card (r : ι → ℝ) (ρ : ℝ) :
    hypoexponentialCoeff r ρ #{i | r i = ρ} = (∏ i, r i) / ∏ i with r i ≠ ρ, (r i - ρ) := by
  simp [hypoexponentialCoeff, neg_add_eq_sub]

/-- The factors of `∏ i, (X + r i)` whose rate differs from `ρ`. -/
private abbrev otherFactors (r : ι → ℝ) (ρ : ℝ) : ℝ[X] := ∏ i with r i ≠ ρ, (X + C (r i))

/-- The Taylor polynomial at `-ρ` of `(∏ i, r i) / otherFactors r ρ`, of order the multiplicity
of `ρ`, written in powers of `X + ρ`. -/
private abbrev principalNumerator (r : ι → ℝ) (ρ : ℝ) : ℝ[X] :=
  ∑ j ∈ range #{i | r i = ρ}, C (hypoexponentialCoeff r ρ (#{i | r i = ρ} - j)) * (X + C ρ) ^ j

private theorem natDegree_principalNumerator_mul_le (r : ι → ℝ) {ρ : ℝ} (hρ : ρ ∈ univ.image r) :
    (principalNumerator r ρ * otherFactors r ρ).natDegree ≤ Fintype.card ι - 1 := by
  have hm : 0 < #{i | r i = ρ} := by
    obtain ⟨i, -, hi⟩ := mem_image.1 hρ
    exact card_pos.2 ⟨i, by simp [hi]⟩
  have hcard := card_filter_add_card_filter_not (s := univ) (fun i ↦ r i = ρ)
  rw [Finset.card_univ] at hcard
  have hT : (principalNumerator r ρ).natDegree ≤ #{i | r i = ρ} - 1 :=
    natDegree_sum_le_of_forall_le _ _ fun j hj ↦ natDegree_C_mul_le _ _ |>.trans <|
      natDegree_pow_le.trans <| by simpa using Nat.le_sub_one_of_lt (mem_range.1 hj)
  have hQ : (otherFactors r ρ).natDegree ≤ #{i | ¬r i = ρ} :=
    (natDegree_prod_le _ _).trans <| by simp
  exact natDegree_mul_le.trans (by omega)

/-- The polynomial form of the partial-fraction expansion, after clearing denominators. -/
private theorem C_prod_eq_sum_principalNumerator_mul [Nonempty ι] (r : ι → ℝ) :
    C (∏ i, r i) = ∑ ρ ∈ univ.image r, principalNumerator r ρ * otherFactors r ρ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_dvd_of_natDegree_lt (p := ∏ i, (X + C (r i))) ?_ ?_
  · rw [Finset.prod_comp (fun ρ ↦ X + C ρ) r]
    refine prod_dvd_of_coprime (fun ρ _ ρ' _ h ↦ ?_) fun ρ hρ ↦ ?_
    · have := isCoprime_X_sub_C_of_isUnit_sub (R := ℝ) (a := -ρ) (b := -ρ')
        (sub_ne_zero.2 (neg_injective.ne h)).isUnit
      simp only [map_neg, sub_neg_eq_add] at this
      exact this.pow
    -- Up to a multiple of `(X + ρ) ^ m`, the difference is the Taylor remainder at `-ρ`.
    rw [← sum_erase_add _ _ hρ, sub_add_eq_sub_sub_swap]
    refine dvd_sub ?_ (dvd_sum fun ρ' hρ' ↦ dvd_mul_of_dvd_right ?_ _)
    · have hQ : (otherFactors r ρ).eval (-ρ) ≠ 0 := by
        simp only [eval_prod, eval_add, eval_X, eval_C]
        exact prod_ne_zero_iff.2 fun i hi ↦ by
          rw [neg_add_eq_sub, sub_ne_zero]; exact (mem_filter.1 hi).2
      have h := X_sub_C_pow_dvd_sub_sum_iteratedDeriv_mul (P := C (∏ i, r i)) hQ
        #{i | r i = ρ}
      simp only [eval_C, otherFactors, eval_prod, eval_add, eval_X, map_neg,
        sub_neg_eq_add] at h
      have hT : principalNumerator r ρ = ∑ j ∈ range #{i | r i = ρ},
          C (iteratedDeriv j (fun x ↦ (∏ i, r i) / ∏ i with r i ≠ ρ, (x + r i)) (-ρ) / j !) *
            (X + C ρ) ^ j :=
        sum_congr rfl fun j hj ↦ by
          rw [hypoexponentialCoeff, Nat.sub_sub_self (mem_range.1 hj).le]
      rwa [hT]
    · rw [pow_card_filter_eq_prod_X_add_C]
      refine prod_dvd_prod_of_subset _ _ _ fun i hi ↦ ?_
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      rw [hi]
      exact (ne_of_mem_erase hρ').symm
  · rw [natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_add_C _]
    simp only [natDegree_X_add_C, sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    have := Fintype.card_pos (α := ι)
    refine (natDegree_sub_le _ _).trans_lt (max_lt (by rwa [natDegree_C]) ?_)
    exact (natDegree_sum_le_of_forall_le _ _ fun ρ hρ ↦
      natDegree_principalNumerator_mul_le r hρ).trans_lt (by omega)

/-- Reindexing the Taylor coefficients by pole order turns the Taylor polynomial at `-ρ`,
divided by `(z + ρ) ^ m`, into the principal part at `-ρ`. -/
private theorem aeval_principalNumerator_div {K : Type*} [Field K] [Algebra ℝ K] (r : ι → ℝ)
    (ρ : ℝ) {z : K} (hz : z + algebraMap ℝ K ρ ≠ 0) :
    aeval z (principalNumerator r ρ) / (z + algebraMap ℝ K ρ) ^ #{i | r i = ρ} =
      ∑ k ∈ Icc 1 #{i | r i = ρ},
        algebraMap ℝ K (hypoexponentialCoeff r ρ k) / (z + algebraMap ℝ K ρ) ^ k := by
  simp only [principalNumerator, map_sum, map_mul, aeval_C, map_pow, map_add, aeval_X,
    Finset.sum_div]
  generalize #{i | r i = ρ} = m
  refine sum_nbij' (fun j ↦ m - j) (fun k ↦ m - k) (fun j hj ↦ ?_) (fun k hk ↦ ?_)
    (fun j hj ↦ ?_) (fun k hk ↦ ?_) fun j hj ↦ ?_
  any_goals simp only [mem_range, mem_Icc] at hj ⊢
  any_goals simp only [mem_range, mem_Icc] at hk ⊢
  any_goals omega
  · rw [← pow_mul_pow_sub (z + algebraMap ℝ K ρ) hj.le]
    field_simp

/-- **Partial fractions for the hypoexponential Laplace transform.** For real rates `r` indexed by
a nonempty finite type and any `z` in a field over `ℝ` away from the poles,
`∏ i, r i / (z + r i)` is the sum over the distinct rates `ρ` of the principal parts
`∑ k ∈ [1, m ρ], A ρ k / (z + ρ) ^ k`, where `m ρ` is the multiplicity of `ρ`. -/
theorem prod_div_add_eq_sum_hypoexponentialCoeff [Nonempty ι] {K : Type*} [Field K] [Algebra ℝ K]
    (r : ι → ℝ) {z : K} (hz : ∀ i, z + algebraMap ℝ K (r i) ≠ 0) :
    ∏ i, algebraMap ℝ K (r i) / (z + algebraMap ℝ K (r i)) =
      ∑ ρ ∈ univ.image r, ∑ k ∈ Icc 1 #{i | r i = ρ},
        algebraMap ℝ K (hypoexponentialCoeff r ρ k) / (z + algebraMap ℝ K ρ) ^ k := by
  have h := congrArg (aeval z) (C_prod_eq_sum_principalNumerator_mul r)
  rw [prod_div_distrib, ← map_prod, ← aeval_C (R := ℝ) z, h, map_sum, Finset.sum_div]
  refine sum_congr rfl fun ρ hρ ↦ ?_
  have hden : ∏ i, (z + algebraMap ℝ K (r i)) =
      (z + algebraMap ℝ K ρ) ^ #{i | r i = ρ} * aeval z (otherFactors r ρ) := by
    simpa [otherFactors] using congrArg (aeval z)
      (prod_X_add_C_eq_pow_card_filter_mul_prod_filter_ne r ρ)
  have hden0 : ∏ i, (z + algebraMap ℝ K (r i)) ≠ 0 := prod_ne_zero_iff.2 fun i _ ↦ hz i
  obtain ⟨i, -, rfl⟩ := mem_image.1 hρ
  rw [hden, map_mul, mul_div_mul_right _ _ (right_ne_zero_of_mul (hden ▸ hden0)),
    aeval_principalNumerator_div r _ (hz i)]

/-- For nonzero rates, the numbers `A ρ k / ρ ^ k` sum to one: this is the partial-fraction
expansion at `z = 0`. When all rates are positive, they are the weights of the Erlang laws in the
expansion of the hypoexponential law. -/
theorem sum_hypoexponentialCoeff_div_pow [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, r i ≠ 0) :
    ∑ ρ ∈ univ.image r, ∑ k ∈ Icc 1 #{i | r i = ρ}, hypoexponentialCoeff r ρ k / ρ ^ k = 1 := by
  have h := prod_div_add_eq_sum_hypoexponentialCoeff (K := ℝ) r (z := 0) (by simpa using hr)
  simp only [Algebra.algebraMap_self, RingHom.id_apply, zero_add] at h
  rw [← h, prod_eq_one fun i _ ↦ div_self (hr i)]

end TauCeti.Probability
