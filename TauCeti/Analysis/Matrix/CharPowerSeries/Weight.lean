/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Basic
import TauCeti.Algebra.Order.BigOperators.Antitone

/-!
# Fredholm coefficients from weighted entry bounds

Let `A` be a matrix over an ultrametric seminormed commutative ring, indexed by a type `ι`, and
let `det (1 - T A) = ∑ cₙ Tⁿ` be its principal-minor series. If the principal minors are bounded
by products `∏ i ∈ s, r i`, then `‖cₙ‖` is at most the largest such product over `n` indices.
When `ι` is enumerated by `e : ℕ ≃ ι` so that `r ∘ e` is antitone, this largest product is the
product over the first `n` indices of the enumeration:

`‖cₙ‖ ≤ ∏ k < n, r (e k)` (`Matrix.norm_charCoeff_le_prod_range_of_antitone`).

For `σ ≤ 1` this has a form in terms of weights. For `0 ≤ σ`, a row bound
`‖A i j‖ ≤ σ ^ w i` with `w ∘ e` monotone gives `‖cₙ‖ ≤ σ ^ (∑ k < n, w (e k))`
(`Matrix.norm_charCoeff_le_pow_sum_range`). For `0 < σ`, a two-sided bound
`‖A i j‖ ≤ σ ^ (w i - w' j)` with `k ↦ w (e k) - w' (e k)` monotone gives the same bound with
the integer weight differences (`Matrix.norm_charCoeff_le_zpow_sum_range`). The differences
may be negative; monotonicity in a block enumeration is what identifies the minimal sum over
`n` indices.

Two weightings are computed explicitly. On `ℕ`, the weight `w i = i` gives
`‖cₙ‖ ≤ σ ^ (n choose 2)`, that is, the exponent `n (n - 1) / 2`
(`Matrix.norm_charCoeff_le_pow_choose_two`). This is sharp: for `diag (pⁱ)` over `ℚ_p`, with
`σ = p⁻¹`, the coefficient `cₙ` has valuation exactly `n (n - 1) / 2` by the dominant-minor
criterion `Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one`. On `J × ℕ` with `J`
finite and nonempty, the weight `w (j, k) = k` gives the exponent `∑ i < n, ⌊i / #J⌋`, since
the enumeration of `J × ℕ` by blocks `J × {k}` has nondecreasing weights
(`Matrix.norm_charCoeff_le_pow_sum_range_div`).
For empty `J` the matrix is empty, its series is `1`, and the stated bound is `‖cₙ‖ ≤ 1`.

For row bounds the first estimate is the case of
`Matrix.norm_charCoeff_le_prod_decreasingRearrangement` in which an enumeration already lists
`r` in decreasing order; the enumeration form also covers two-sided bounds, which have no row
majorant, and needs no hypothesis `BddAbove (Set.range r)`, since an antitone `r ∘ e` is bounded
by `r (e 0)`.

## Main results

* `Matrix.norm_charCoeff_le_prod_range_of_antitone`: product majorants decreasing along an
  enumeration bound `cₙ` by the product over the first `n` indices.
* `Matrix.norm_charCoeff_le_pow_sum_range`, `Matrix.norm_charCoeff_le_zpow_sum_range`: the
  one-sided and two-sided weighted forms.
* `Matrix.norm_charCoeff_le_pow_choose_two`, `Matrix.norm_charCoeff_le_pow_sum_range_div`: the
  weights `i` on `ℕ` and `k` on `J × ℕ`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
* K. S. Kedlaya, *A little p-adic numerical analysis*, MIT 18.787 notes (2007), §3.
-/

public section

open Finset

namespace Matrix

variable {ι R : Type*} [DecidableEq ι]

section ProductMajorants

variable [SeminormedCommRing R] [IsUltrametricDist R]

/-- **Product majorants along an enumeration.** If the principal minors of `A` are bounded by
products `∏ i ∈ s, r i`, and `r` is antitone along an enumeration `e : ℕ ≃ ι`, then the `n`-th
principal-minor coefficient is bounded by the product of `r` over the first `n` indices
`e 0, …, e (n - 1)`. -/
theorem norm_charCoeff_le_prod_range_of_antitone {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ s : Finset ι, ‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i) (e : ℕ ≃ ι)
    (he : Antitone (r ∘ e)) (n : ℕ) :
    ‖A.charCoeff n‖ ≤ ∏ k ∈ range n, r (e k) := by
  have hr₀ (i : ι) : 0 ≤ r i := by
    simpa only [prod_singleton] using (norm_nonneg _).trans (hA {i})
  refine norm_charCoeff_le_of_principalMinor_le (prod_nonneg fun k _ ↦ hr₀ _) fun s hs ↦ ?_
  have h := prod_le_prod_range_card (fun k ↦ hr₀ (e k)) he (s.map e.symm.toEmbedding)
  simp only [prod_map, card_map, Equiv.coe_toEmbedding, Equiv.apply_symm_apply, hs] at h
  exact (hA s).trans h

end ProductMajorants

section Ultra

variable [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Weighted row bounds.** For `0 ≤ σ ≤ 1`, if `‖A i j‖ ≤ σ ^ w i` and the weights are
nondecreasing along an enumeration `e : ℕ ≃ ι`, then `‖A.charCoeff n‖ ≤ σ ^ ∑ k < n, w (e k)`.
No growth of the weights is needed for this bound. -/
theorem norm_charCoeff_le_pow_sum_range {A : Matrix ι ι R} {σ : ℝ} (hσ₀ : 0 ≤ σ)
    (hσ₁ : σ ≤ 1) {w : ι → ℕ} (hA : ∀ i j, ‖A i j‖ ≤ σ ^ w i) (e : ℕ ≃ ι)
    (he : Monotone (w ∘ e)) (n : ℕ) :
    ‖A.charCoeff n‖ ≤ σ ^ ∑ k ∈ range n, w (e k) := by
  rw [← prod_pow_eq_pow_sum]
  exact norm_charCoeff_le_prod_range_of_antitone (norm_principalMinor_le hA) e
    (fun _ _ hab ↦ pow_le_pow_of_le_one hσ₀ hσ₁ (he hab)) n

/-- **Two-sided weighted bounds.** For `0 < σ ≤ 1`, if `‖A i j‖ ≤ σ ^ (w i - w' j)` and the
diagonal differences `w (e k) - w' (e k)` are nondecreasing along an enumeration `e : ℕ ≃ ι`,
then the `n`-th coefficient is bounded by `σ` to the sum of the first `n` differences. The
differences may be negative, and the matrix need not have a row majorant. -/
theorem norm_charCoeff_le_zpow_sum_range {A : Matrix ι ι R} {σ : ℝ} (hσ₀ : 0 < σ)
    (hσ₁ : σ ≤ 1) {w w' : ι → ℤ} (hA : ∀ i j, ‖A i j‖ ≤ σ ^ (w i - w' j)) (e : ℕ ≃ ι)
    (he : Monotone fun k ↦ w (e k) - w' (e k)) (n : ℕ) :
    ‖A.charCoeff n‖ ≤ σ ^ ∑ k ∈ range n, (w (e k) - w' (e k)) := by
  rw [← prod_zpow_eq_zpow_sum_of_isUnit _ hσ₀.ne'.isUnit]
  refine norm_charCoeff_le_prod_range_of_antitone (r := fun i ↦ σ ^ (w i - w' i))
    (fun s ↦ ?_) e (fun _ _ hab ↦ zpow_le_zpow_right_of_le_one₀ hσ₀ hσ₁ (he hab)) n
  rw [prod_zpow_eq_zpow_sum_of_isUnit s hσ₀.ne'.isUnit]
  exact norm_principalMinor_le_zpow hσ₀ hA s

/-- **The weight `i` on `ℕ`.** For `0 ≤ σ ≤ 1`, if `‖A i j‖ ≤ σ ^ i`, then
`‖A.charCoeff n‖ ≤ σ ^ (n choose 2)`, where `n choose 2 = n (n - 1) / 2`. -/
theorem norm_charCoeff_le_pow_choose_two {A : Matrix ℕ ℕ R} {σ : ℝ} (hσ₀ : 0 ≤ σ)
    (hσ₁ : σ ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ σ ^ i) (n : ℕ) :
    ‖A.charCoeff n‖ ≤ σ ^ n.choose 2 := by
  simpa only [Equiv.refl_apply, id_eq, sum_range_id, ← Nat.choose_two_right] using
    norm_charCoeff_le_pow_sum_range hσ₀ hσ₁ (w := id) hA (Equiv.refl ℕ) monotone_id n

/-- **The weight `k` on `J × ℕ`.** For a finite `J` and `0 ≤ σ ≤ 1`, if every entry in a row
indexed by `(j, k)` has norm at most `σ ^ k`, then
`‖A.charCoeff n‖ ≤ σ ^ ∑ i < n, i / Nat.card J`. The exponent counts the rows of the blocks
`J × {k}` in order of increasing `k`. For empty `J` it is zero and the bound reads
`‖A.charCoeff n‖ ≤ 1`. -/
theorem norm_charCoeff_le_pow_sum_range_div {J : Type*} [Finite J] [DecidableEq J]
    {A : Matrix (J × ℕ) (J × ℕ) R} {σ : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (hA : ∀ i j, ‖A i j‖ ≤ σ ^ i.2) (n : ℕ) :
    ‖A.charCoeff n‖ ≤ σ ^ ∑ i ∈ range n, i / Nat.card J := by
  cases isEmpty_or_nonempty J with
  | inl hJ =>
    simp only [Nat.card_of_isEmpty, Nat.div_zero, sum_const_zero, pow_zero]
    refine norm_charCoeff_le_of_principalMinor_le zero_le_one fun s _ ↦ ?_
    rw [eq_empty_of_isEmpty s, principalMinor_empty, norm_one]
  | inr hJ =>
    have : NeZero (Nat.card J) := ⟨Nat.card_pos.ne'⟩
    -- Enumerate `J × ℕ` block by block: the index `i` goes to the block `i / #J`.
    let e : ℕ ≃ J × ℕ := (Nat.divModEquiv (Nat.card J)).trans
      ((Equiv.prodComm _ _).trans ((Finite.equivFin J).symm.prodCongr (Equiv.refl ℕ)))
    have he (i : ℕ) : (e i).2 = i / Nat.card J := rfl
    simpa only [he] using norm_charCoeff_le_pow_sum_range hσ₀ hσ₁ (w := Prod.snd) hA e
      (fun _ _ hab ↦ by simpa only [Function.comp_apply, he] using Nat.div_le_div_right hab) n

end Ultra

end Matrix
