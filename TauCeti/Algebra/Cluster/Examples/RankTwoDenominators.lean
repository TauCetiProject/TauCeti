/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Chebyshev.Growth

/-!
# Rank-two tropical denominator recurrence

The initial vectors are the two negative coordinate vectors. Each subsequent vector
is the alternating exchange exponent times the positive part of the current vector,
minus the previous vector. When the product of the two positive exchange exponents
is at least four, the forward recurrence is described by rescaled Chebyshev
polynomials. The even-indexed forward vectors are pairwise distinct.

## Reference

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Annals of Mathematics 158 (2003), §§5 and 7.
-/

public section

namespace TauCeti.Cluster

open Polynomial.Chebyshev

/-- Adjacent pairs of denominator vectors in the rank-two tropical recurrence.
Pair `n` consists of the vectors at indices `2n` and `2n+1`. -/
def rankTwoDenominatorPair (b c : ℤ) : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((-1, 0), (0, -1))
  | n + 1 =>
    let p := rankTwoDenominatorPair b c n
    let v := (c * max p.2.1 0 - p.1.1, c * max p.2.2 0 - p.1.2)
    (v, (b * max v.1 0 - p.2.1, b * max v.2 0 - p.2.2))

@[simp] theorem rankTwoDenominatorPair_zero (b c : ℤ) :
    rankTwoDenominatorPair b c 0 = ((-1, 0), (0, -1)) := by
  rfl

/-- Two consecutive tropical mutations advance one pair. -/
theorem rankTwoDenominatorPair_succ (b c : ℤ) (n : ℕ) :
    let p := rankTwoDenominatorPair b c n
    let v := (c * max p.2.1 0 - p.1.1, c * max p.2.2 0 - p.1.2)
    rankTwoDenominatorPair b c (n + 1) =
      (v, (b * max v.1 0 - p.2.1, b * max v.2 0 - p.2.2)) := by
  rfl

/-- The first forward pair has already passed the two negative initial vectors. -/
@[simp] theorem rankTwoDenominatorPair_one (b c : ℤ) :
    rankTwoDenominatorPair b c 1 = ((1, 0), (b, 1)) := by
  simp [rankTwoDenominatorPair_succ]

private theorem S_eval_prev_nonneg (t : ℤ) (ht : 2 ≤ t) (n : ℕ) :
    0 ≤ (S ℤ ((n : ℤ) - 1)).eval t := by
  cases n with
  | zero => simp [S_neg_one]
  | succ n =>
    have h := natCast_add_one_le_S_eval (R := ℤ) ht n
    rw [Nat.cast_succ, add_sub_cancel_right]
    omega

private theorem rankTwo_pair_step {b c s p q : ℤ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (hp : 0 ≤ p) (hq : 0 ≤ q) (h : q = (b * c - 2) * s - p)
    (n : ℕ)
    (hn : rankTwoDenominatorPair b c n = ((s + p, c * p), (b * s, s + p))) :
    rankTwoDenominatorPair b c (n + 1) = ((q + s, c * s), (b * q, q + s)) := by
  let v : ℤ × ℤ := (c * max (b * s) 0 - (s + p), c * max (s + p) 0 - c * p)
  have hv : v = (q + s, c * s) := by
    dsimp [v]
    simp only [max_eq_left (mul_nonneg hb hs), max_eq_left (add_nonneg hs hp)]
    apply Prod.ext
    · dsimp
      linear_combination -h
    · dsimp
      ring
  rw [rankTwoDenominatorPair_succ, hn]
  change (v, (b * max v.1 0 - b * s, b * max v.2 0 - (s + p))) = _
  rw [hv]
  simp only [max_eq_left (add_nonneg hq hs), max_eq_left (mul_nonneg hc hs)]
  congr 1
  apply Prod.ext
  · dsimp
    ring
  · dsimp
    linear_combination -h

private theorem positive_exchange_coefficients {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    0 < b ∧ 0 < c := by
  constructor
  · by_contra! h
    have hz : b = 0 := le_antisymm h hb
    simp [hz] at hbc
  · by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hb h
    omega

/-- The Chebyshev formulas for the forward even and odd denominator vectors. -/
theorem rankTwoDenominatorPair_chebyshev {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let t := b * c - 2
    let s := (S ℤ (n : ℤ)).eval t
    let p := (S ℤ ((n : ℤ) - 1)).eval t
    rankTwoDenominatorPair b c (n + 1) = ((s + p, c * p), (b * s, s + p)) := by
  have hc : 0 ≤ c := (positive_exchange_coefficients hb hbc).2.le
  let t := b * c - 2
  have ht : 2 ≤ t := by dsimp [t]; omega
  change rankTwoDenominatorPair b c (n + 1) =
    (((S ℤ (n : ℤ)).eval t + (S ℤ ((n : ℤ) - 1)).eval t,
        c * (S ℤ ((n : ℤ) - 1)).eval t),
      (b * (S ℤ (n : ℤ)).eval t,
        (S ℤ (n : ℤ)).eval t + (S ℤ ((n : ℤ) - 1)).eval t))
  induction n with
  | zero => simp [S_zero, S_neg_one]
  | succ n ih =>
    rw [Nat.cast_succ, add_sub_cancel_right]
    have hs := natCast_add_one_le_S_eval (R := ℤ) ht n
    have hq := natCast_add_one_le_S_eval (R := ℤ) ht (n + 1)
    rw [Nat.cast_succ] at hq
    have hstep : (S ℤ ((n : ℤ) + 1)).eval t =
        t * (S ℤ (n : ℤ)).eval t - (S ℤ ((n : ℤ) - 1)).eval t := by
      simpa using congrArg (fun p : Polynomial ℤ ↦ p.eval t) (S_add_one ℤ (n : ℤ))
    exact rankTwo_pair_step hb hc (by omega) (S_eval_prev_nonneg t ht n) (by omega)
      hstep (n + 1) ih

/-- Both forward vectors have positive first coordinate and nonnegative second coordinate.
The odd vector is positive in both coordinates. -/
theorem rankTwoDenominatorPair_forward_pos {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    (0 < p.1.1 ∧ 0 ≤ p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2) := by
  obtain ⟨hb', hc⟩ := positive_exchange_coefficients hb hbc
  have ht : 2 ≤ b * c - 2 := by omega
  have h := natCast_add_one_le_S_eval (R := ℤ) ht n
  have hp := S_eval_prev_nonneg (b * c - 2) ht n
  have hs : 0 < (S ℤ (n : ℤ)).eval (b * c - 2) := by omega
  rw [rankTwoDenominatorPair_chebyshev hb hbc n]
  exact ⟨⟨add_pos_of_pos_of_nonneg hs hp, mul_nonneg hc.le hp⟩,
    ⟨mul_pos hb' hs, add_pos_of_pos_of_nonneg hs hp⟩⟩

private theorem S_eval_sum_strictMono (t : ℤ) (ht : 2 ≤ t) :
    StrictMono fun n : ℕ ↦ (S ℤ (n : ℤ)).eval t + (S ℤ ((n : ℤ) - 1)).eval t := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := S_eval_add_one_le (R := ℤ) ht n
  rw [Nat.cast_succ, add_sub_cancel_right]
  have hp : (S ℤ ((n : ℤ) - 1)).eval t ≤ (S ℤ (n : ℤ)).eval t := by
    cases n with
    | zero => simp [S_zero, S_neg_one]
    | succ n =>
      rw [Nat.cast_succ, add_sub_cancel_right]
      have h' := S_eval_add_one_le (R := ℤ) ht n
      omega
  omega

/-- The second entries of the odd forward denominator vectors grow strictly. -/
theorem rankTwoDenominatorPair_odd_snd_strictMono {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    StrictMono fun n : ℕ ↦ (rankTwoDenominatorPair b c (n + 1)).2.2 := by
  simp_rw [rankTwoDenominatorPair_chebyshev hb hbc]
  exact S_eval_sum_strictMono (b * c - 2) (by omega)

/-- The first entries of the even forward denominator vectors grow strictly. -/
theorem rankTwoDenominatorPair_even_fst_strictMono {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    StrictMono fun n : ℕ ↦ (rankTwoDenominatorPair b c (n + 1)).1.1 := by
  simp_rw [rankTwoDenominatorPair_chebyshev hb hbc]
  exact S_eval_sum_strictMono (b * c - 2) (by omega)

/-- The even denominator vectors at indices `2, 4, 6, …` are pairwise distinct. -/
theorem rankTwoDenominatorPair_even_injective {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    Function.Injective fun n : ℕ ↦ (rankTwoDenominatorPair b c (n + 1)).1 := by
  intro m n h
  exact (rankTwoDenominatorPair_even_fst_strictMono hb hbc).injective (congrArg Prod.fst h)

end TauCeti.Cluster
