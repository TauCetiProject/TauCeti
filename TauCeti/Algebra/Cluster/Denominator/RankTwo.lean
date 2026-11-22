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
polynomials. Under these same nonnegative-exponent and product hypotheses, all even-indexed vectors
are pairwise distinct, giving the infinite-denominator step in the rank-two finite-type
obstruction. No Laurent-numerator or cluster-variable realization is asserted here.

The closed form uses Mathlib's `Polynomial.Chebyshev.S` and `S_add_one`. Positivity and
growth use `one_le_S_eval` and `nonneg_S_eval_sub_one` for the coordinate signs, and
`S_eval_add_S_sub_one_eval_strictMono` for growth of the even first coordinates.

## Reference

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Annals of Mathematics 158 (2003), §§5 and 7.
-/

public section

namespace TauCeti.Cluster

open Polynomial.Chebyshev

/-- One vector update in the rank-two denominator recurrence. -/
def rankTwoDenominatorUpdate (k : ℤ) (u v : ℤ × ℤ) : ℤ × ℤ :=
  k • v⁺ - u

/-- The coordinate formula for one denominator-vector update. -/
@[simp] theorem rankTwoDenominatorUpdate_eq (k : ℤ) (u v : ℤ × ℤ) :
    rankTwoDenominatorUpdate k u v =
      (k * max v.1 0 - u.1, k * max v.2 0 - u.2) := by
  ext <;> simp [rankTwoDenominatorUpdate, posPart_def]

/-- Two consecutive vector updates, in the alternating order `c` then `b`. -/
def rankTwoDenominatorStep (b c : ℤ) (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  let v := rankTwoDenominatorUpdate c p.1 p.2
  (v, rankTwoDenominatorUpdate b p.2 v)

/-- The pair step consists of a `c` update followed by a `b` update. -/
@[simp] theorem rankTwoDenominatorStep_eq (b c : ℤ) (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    rankTwoDenominatorStep b c p =
      (rankTwoDenominatorUpdate c p.1 p.2,
        rankTwoDenominatorUpdate b p.2 (rankTwoDenominatorUpdate c p.1 p.2)) := by
  rfl

/-- Adjacent pairs of denominator vectors in the rank-two tropical recurrence.
Pair `n` consists of the vectors at indices `2n` and `2n+1`. -/
def rankTwoDenominatorPair (b c : ℤ) (n : ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  (rankTwoDenominatorStep b c)^[n] ((-1, 0), (0, -1))

/-- Pair zero consists of the two negative coordinate vectors, independently of the exponents. -/
@[simp] theorem rankTwoDenominatorPair_zero (b c : ℤ) :
    rankTwoDenominatorPair b c 0 = ((-1, 0), (0, -1)) :=
  Function.iterate_zero_apply _ _

/-- Two consecutive tropical mutations advance one pair. -/
@[grind =]
theorem rankTwoDenominatorPair_succ (b c : ℤ) (n : ℕ) :
    rankTwoDenominatorPair b c (n + 1) =
      rankTwoDenominatorStep b c (rankTwoDenominatorPair b c n) :=
  Function.iterate_succ_apply' _ _ _

/-- Any pair sequence with the same initial pair and transition equals the denominator
recurrence, for arbitrary integer exponents. -/
theorem eq_rankTwoDenominatorPair (b c : ℤ) (f : ℕ → (ℤ × ℤ) × (ℤ × ℤ))
    (hzero : f 0 = ((-1, 0), (0, -1)))
    (hstep : ∀ n, f (n + 1) = rankTwoDenominatorStep b c (f n)) :
    f = rankTwoDenominatorPair b c := by
  have h : Function.Semiconj f Nat.succ (rankTwoDenominatorStep b c) := hstep
  funext n
  simpa [Nat.succ_iterate, hzero, rankTwoDenominatorPair] using h.iterate_right n 0

/-- The first forward pair has already passed the two negative initial vectors. -/
@[simp] theorem rankTwoDenominatorPair_one (b c : ℤ) :
    rankTwoDenominatorPair b c 1 = ((1, 0), (b, 1)) := by
  rw [rankTwoDenominatorPair_succ, rankTwoDenominatorPair_zero]
  simp only [rankTwoDenominatorStep_eq, rankTwoDenominatorUpdate_eq]
  norm_num

/-- On a nonnegative current vector the tropical update is linear. -/
theorem rankTwoDenominatorUpdate_of_nonneg (k : ℤ) (u v : ℤ × ℤ) (hv : 0 ≤ v) :
    rankTwoDenominatorUpdate k u v = k • v - u := by
  simp [rankTwoDenominatorUpdate, posPart_def, sup_eq_left.mpr hv]

private theorem rankTwo_pair_step {b c s p q : ℤ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (hp : 0 ≤ p) (hq : 0 ≤ q) (h : q = (b * c - 2) * s - p)
    (n : ℕ)
    (hn : rankTwoDenominatorPair b c n = ((s + p, c * p), (b * s, s + p))) :
    rankTwoDenominatorPair b c (n + 1) = ((q + s, c * s), (b * q, q + s)) := by
  let v := rankTwoDenominatorUpdate c (s + p, c * p) (b * s, s + p)
  have hv : v = (q + s, c * s) := by
    dsimp only [v]
    rw [rankTwoDenominatorUpdate_of_nonneg _ _ _
      ⟨mul_nonneg hb hs, add_nonneg hs hp⟩]
    apply Prod.ext <;> simp
    · linear_combination -h
    · ring
  calc
    rankTwoDenominatorPair b c (n + 1) =
        (v, rankTwoDenominatorUpdate b (b * s, s + p) v) := by
      rw [rankTwoDenominatorPair_succ, hn, rankTwoDenominatorStep_eq]
    _ = ((q + s, c * s), (b * q, q + s)) := by
      rw [hv]
      congr 1
      rw [rankTwoDenominatorUpdate_of_nonneg _ _ _
        ⟨add_nonneg hq hs, mul_nonneg hc hs⟩]
      apply Prod.ext <;> simp
      · ring
      · linear_combination -h

/-- For `0 ≤ b` and `4 ≤ b * c`, the forward even and odd denominator vectors have the
following Chebyshev closed form. -/
theorem rankTwoDenominatorPair_succ_eq_chebyshev {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let t := b * c - 2
    let s := (S ℤ (n : ℤ)).eval t
    let p := (S ℤ ((n : ℤ) - 1)).eval t
    rankTwoDenominatorPair b c (n + 1) = ((s + p, c * p), (b * s, s + p)) := by
  have hprod : 0 < b * c := lt_of_lt_of_le (by norm_num) hbc
  have hc : 0 ≤ c := (pos_of_mul_pos_right hprod hb).le
  dsimp only
  let t := b * c - 2
  have ht : 2 ≤ t := by dsimp [t]; omega
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
    exact rankTwo_pair_step hb hc (by omega) (nonneg_S_eval_sub_one ht n) (by omega)
      hstep (n + 1) ih

private theorem rankTwo_forward_signs {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    (0 < p.1.1 ∧ 0 ≤ p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2) := by
  have hprod : 0 < b * c := lt_of_lt_of_le (by norm_num) hbc
  have hc : 0 < c := pos_of_mul_pos_right hprod hb
  have hb' : 0 < b := pos_of_mul_pos_left hprod hc.le
  have ht : 2 ≤ b * c - 2 := by omega
  have hs : 0 < (S ℤ (n : ℤ)).eval (b * c - 2) :=
    lt_of_lt_of_le zero_lt_one (one_le_S_eval ht n)
  have hp := nonneg_S_eval_sub_one ht n
  have hsum := add_pos_of_pos_of_nonneg hs hp
  rw [rankTwoDenominatorPair_succ_eq_chebyshev hb hbc n]
  exact ⟨⟨hsum, mul_nonneg hc.le hp⟩, ⟨mul_pos hb' hs, hsum⟩⟩

/-- For `0 ≤ b` and `4 ≤ b * c`, each even forward vector has positive first coordinate and
nonnegative second coordinate. -/
theorem rankTwoDenominatorPair_forward_even_fst_pos_and_snd_nonneg {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    0 < p.1.1 ∧ 0 ≤ p.1.2 :=
  (rankTwo_forward_signs hb hbc n).1

/-- For `0 ≤ b` and `4 ≤ b * c`, each odd forward vector is strictly positive in both
coordinates. -/
theorem rankTwoDenominatorPair_forward_odd_fst_pos_and_snd_pos {b c : ℤ}
    (hb : 0 ≤ b) (hbc : 4 ≤ b * c) (n : ℕ) :
    let p := rankTwoDenominatorPair b c (n + 1)
    0 < p.2.1 ∧ 0 < p.2.2 :=
  (rankTwo_forward_signs hb hbc n).2

/-- For `0 ≤ b` and `4 ≤ b * c`, the first entries of the even denominator vectors grow
strictly, including the initial pair. -/
theorem rankTwoDenominatorPair_even_fst_strictMono {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    StrictMono fun n : ℕ ↦ (rankTwoDenominatorPair b c n).1.1 := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have h := Polynomial.Chebyshev.S_eval_add_S_sub_one_eval_strictMono
      (R := ℤ) (t := b * c - 2) (by omega)
    simpa only [rankTwoDenominatorPair_succ_eq_chebyshev hb hbc] using h (Nat.lt_succ_self n)

/-- Under the growth hypotheses, all even denominator vectors are pairwise distinct. -/
theorem rankTwoDenominatorPair_even_injective {b c : ℤ} (hb : 0 ≤ b) (hbc : 4 ≤ b * c) :
    Function.Injective fun n : ℕ ↦ (rankTwoDenominatorPair b c n).1 :=
  Function.Injective.of_comp (f := Prod.fst)
    (rankTwoDenominatorPair_even_fst_strictMono hb hbc).injective

end TauCeti.Cluster
