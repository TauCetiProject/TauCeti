/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Basic
public import Mathlib.Analysis.Real.Sqrt
import TauCeti.Algebra.Order.GroupWithZero.Pow
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Combinatorics.TraceWord.Coding

/-!
# Füredi–Komlós enumeration of bipartite words

The moment method for the largest eigenvalue of a sample covariance matrix `X Xᴴ / n`, with `X`
of size `p × n`, counts the closed bipartite words `u 0, v 0, u 1, v 1, …, v (k - 1), u 0`
(`TauCeti.bipartiteEdge`) of growing half-length `k` that read each of their positions at least
twice. Such a word visits at most `k + 1` row and column indices, and the words attaining this
bound are the double traversals of trees. Weighted by `n⁻ᵏ`, these leading words with `p` rows and
`n` columns contribute `p` times the `k`-th moment of the Marchenko–Pastur law of ratio `p / n`,
up to a factor that tends to `1` for fixed `k` as `p` and `n` tend to infinity. That moment is at
most `(1 + √(p / n)) ^ (2 * k)`, the `k`-th power of the upper edge. For growing `k` the other
words must be counted as well, so the enumeration below bounds the total weight of all words,
uniformly in `k`.

This file proves a weighted form of this enumeration with this sharp base. A word visiting `t` row
and column indices is weighted by `√(p * n) ^ (-t)` and damped by the factor
`γ ^ (2 * (2 * k + 2 - 2 * t))`, for `0 ≤ γ ≤ 1`. The total weight is at most
`√(p / n) * ((√(n / p) + 1 + 2 * k * γ) * (√(p / n) + 1 + 2 * k * γ)) ^ k`. At `γ = 0` the
base `(√(n / p) + 1) * (√(p / n) + 1)` is `(1 + √(p / n)) ^ 2 / √(p / n)`.

The bound is the weighted Füredi–Komlós enumeration
`TauCeti.sum_piFinset_pow_div_pow_card_image_le_of_no_singleton_edge`, applied to the cyclic words
`TauCeti.bipartiteWord` on `α ⊕ β`, which visit rows at even times and columns at odd times.
Each new index has the common weight `√(p * n)⁻¹`. So the discoveries of a column, from a row,
have total weight `n / √(p * n) = √(n / p)`, and the discoveries of a row have total weight
`√(p / n)`.

## Main results

* `TauCeti.sum_pow_div_sqrt_mul_pow_le_of_no_singleton_edge`: the weighted enumeration of
  bipartite words.
* `TauCeti.pow_card_bipartiteEdge_mul_pow_le_of_no_singleton_edge`: the bound on the product of
  entry moment bounds for a single word.

## References

* Z. Füredi and J. Komlós, *The eigenvalues of random symmetric matrices*, Combinatorica 1
  (1981), 233–241.
* Y. Q. Yin, Z. D. Bai, P. R. Krishnaiah, *On the limit of the largest eigenvalue of the large
  dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988), 509–521.
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.2.2.
-/

public section

open Finset

namespace TauCeti

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Füredi–Komlós enumeration of bipartite words.** Let `α` and `β` be finite types of
cardinalities `p` and `n`, let `k ≠ 0` and `0 ≤ γ ≤ 1`. Over the bipartite words `u : Fin k → α`,
`v : Fin k → β` reading each of their positions at least twice, the sum of
`γ ^ (2 * (2 * k + 2 - 2 * t)) / √(p * n) ^ t`, where `t = #(image u) + #(image v)` is the
number of row and column indices visited, is at most
`√(p / n) * ((√(n / p) + 1 + 2 * k * γ) * (√(p / n) + 1 + 2 * k * γ)) ^ k`. -/
theorem sum_pow_div_sqrt_mul_pow_le_of_no_singleton_edge {k : ℕ} (hk : k ≠ 0) {γ : ℝ}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    ∑ u : Fin k → α, ∑ v : Fin k → β with
        ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a,
      γ ^ (2 * (2 * k + 2 - 2 * (#(univ.image u) + #(univ.image v)))) /
        √(Fintype.card α * Fintype.card β) ^ (#(univ.image u) + #(univ.image v)) ≤
      √(Fintype.card α / Fintype.card β) *
        ((√(Fintype.card β / Fintype.card α) + 1 + 2 * k * γ) *
          (√(Fintype.card α / Fintype.card β) + 1 + 2 * k * γ)) ^ k := by
  have : NeZero (2 * k) := ⟨by omega⟩
  let e := finSumFinInterleaveEquiv k
  let A (s : Fin (2 * k)) : Finset (α ⊕ β) := bipartiteVertexFinset s.val
  let g (w : Fin (2 * k) → α ⊕ β) : ℝ :=
    γ ^ (2 * (2 * k + 2 - 2 * #(univ.image w))) /
      √(Fintype.card α * Fintype.card β) ^ #(univ.image w)
  have key := sum_piFinset_pow_div_pow_card_image_le_of_no_singleton_edge hγ₀ hγ₁
    (Real.sqrt_nonneg ((Fintype.card α : ℝ) * Fintype.card β)) A
  calc _ = ∑ x : (Fin k → α) × (Fin k → β) with
          ∀ a, ∃ b ≠ a, bipartiteEdge x.1 x.2 b = bipartiteEdge x.1 x.2 a,
        g (bipartiteWord x.1 x.2) := by
        simp only [g, card_image_bipartiteWord]
        rw [sum_filter, ← univ_product_univ, sum_product]
        simp only [sum_filter]
    _ = ∑ w ∈ (univ.filter fun x : (Fin k → α) × (Fin k → β) ↦
          ∀ a, ∃ b ≠ a, bipartiteEdge x.1 x.2 b = bipartiteEdge x.1 x.2 a).image
          (fun x ↦ bipartiteWord x.1 x.2), g w :=
        (sum_image fun x _ y _ h ↦ Prod.ext_iff.mpr (bipartiteWord_inj.mp h)).symm
    _ ≤ ∑ w ∈ Fintype.piFinset A with
          ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * k) s)) = s(w t, w (finRotate (2 * k) t)),
        g w := by
        refine sum_le_sum_of_subset_of_nonneg (fun w hw ↦ ?_) fun w _ _ ↦ by positivity
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hw
        exact mem_filter.mpr
          ⟨Fintype.mem_piFinset.mpr (bipartiteWord_mem_bipartiteVertexFinset x.1 x.2),
            bipartiteWord_no_singleton_edge (mem_filter.mp hx).2⟩
    _ ≤ _ := key
    _ = _ := by
      -- Steps from rows discover columns, and steps from columns discover rows.
      have h0 : (0 : Fin (2 * k)) = e (.inl ⟨0, Nat.pos_of_ne_zero hk⟩) := Fin.ext (by simp [e])
      have hrow (t : Fin k) : #(A (finSumFinInterleaveEquiv k (.inl t))) = Fintype.card α := by
        simp [A]
      have hcol (t : Fin k) : #(A (finSumFinInterleaveEquiv k (.inr t))) = Fintype.card β := by
        simp [A]
      rw [← e.prod_comp, Fintype.prod_sum_type, h0]
      simp only [e, finRotate_finSumFinInterleaveEquiv_inl, finRotate_finSumFinInterleaveEquiv_inr,
        hrow, hcol, prod_const, card_univ, Fintype.card_fin, ← mul_pow]
      -- `√(a * b) = a * √(b / a)`, so `a / √(a * b) = (√(b / a))⁻¹ = √(a / b)`.
      have hdiv {a b : ℝ} (ha : 0 ≤ a) : a / √(a * b) = √(a / b) := by
        rcases ha.eq_or_lt with rfl | ha
        · simp
        rw [mul_comm, Real.sqrt_mul_eq_mul_sqrt_div b ha.le, div_mul_cancel_left₀ ha.ne',
          ← Real.sqrt_inv, inv_div]
      rw [hdiv (Nat.cast_nonneg _), mul_comm (Fintype.card α : ℝ), hdiv (Nat.cast_nonneg _)]
      push_cast
      ring

/-- For a nonempty bipartite trace word of length `2 * k` reading every entry position at least
twice, the product of entry moment bounds is at most its Füredi–Komlós weight times
`(c * d) ^ k * d`, where `d = √(p * n)` for `p` row and `n` column labels.
Here `c` bounds the second moments and `b ^ 2 ≤ c * d * γ ^ 4` controls the entry bound. -/
theorem pow_card_bipartiteEdge_mul_pow_le_of_no_singleton_edge {k : ℕ} (hk : k ≠ 0)
    {u : Fin k → α} {v : Fin k → β}
    (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a)
    {b c γ : ℝ} (hc : 0 ≤ c)
    (hbc : b ^ 2 ≤ c * √(Fintype.card α * Fintype.card β) * γ ^ 4) :
    let d : ℝ := √(Fintype.card α * Fintype.card β)
    let e := #(univ.image (bipartiteEdge u v))
    let t := #(univ.image u) + #(univ.image v)
    min c (b ^ 2) ^ e * b ^ (2 * k - 2 * e) ≤
      ((c * d) ^ k * d) * (γ ^ (2 * (2 * k + 2 - 2 * t)) / d ^ t) := by
  intro d e t
  let i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  have : Nonempty α := ⟨u i⟩
  have : Nonempty β := ⟨v i⟩
  have hd : 0 < d := Real.sqrt_pos.mpr
    (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos))
  have hsq : √(c * d) ^ 2 = c * d := Real.sq_sqrt (mul_nonneg hc hd.le)
  have habs : |b| ≤ √(c * d) * γ ^ 2 := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) ?_
    rwa [sq_abs, mul_pow, hsq, ← pow_mul]
  have hmin : min c (b ^ 2) ≤ √(c * d) ^ 2 / d := by
    rw [hsq, mul_div_cancel_right₀ _ hd.ne']
    exact min_le_left _ _
  have hcb : min c (b ^ 2) ≤ |b| ^ 2 := by rw [sq_abs]; exact min_le_right _ _
  have ht : 1 ≤ t :=
    (card_pos.mpr ⟨u i, mem_image_of_mem _ (mem_univ i)⟩).trans_le le_self_add
  have hweight := pow_mul_pow_sub_le_mul_pow_div_pow (abs_nonneg b) (le_min hc (sq_nonneg _))
    hcb hmin habs hd ht (card_image_add_card_image_le_card_image_bipartiteEdge_add_one u v)
    (Nat.mul_le_mul_left 2 (card_image_bipartiteEdge_le_of_no_singleton_edge h))
  simpa only [← Nat.mul_sub_left_distrib, pow_abs_two_mul, pow_mul (√(c * d)) 2 k, hsq,
    mul_comm d ((c * d) ^ k)] using hweight

end TauCeti
