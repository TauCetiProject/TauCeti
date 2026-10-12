/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Multiplicity

/-!
# The prime `p` divides `(x - 1) ^ p ^ k` when `x ^ p ^ k = 1`

In any ring, an element `x` with `x ^ p ^ k = 1` for a prime `p` satisfies
`(p : A) ∣ (x - 1) ^ p ^ k`: expanding `1 = (1 + (x - 1)) ^ p ^ k` by the binomial theorem, the
extreme terms are `1` and `(x - 1) ^ p ^ k`, and every other binomial coefficient
`(p ^ k).choose m` with `0 < m < p ^ k` is divisible by `p`. No commutativity is needed, because
`x - 1` commutes with `1`.

This is the integral shadow of the freshman's dream `(x - 1) ^ p ^ k = x ^ p ^ k - 1 = 0` in
characteristic `p`. It is what makes the group-like elements `g - 1`, for `g` of `p`-power order
in a group algebra over the `p`-adic integers, topologically nilpotent.

## Main result

* `Nat.Prime.dvd_sub_one_pow_of_pow_eq_one`: `(p : A) ∣ (x - 1) ^ p ^ k` when `x ^ p ^ k = 1`.
-/

public section

/-- If `x ^ p ^ k = 1` in a ring, for a prime `p`, then `p` divides `(x - 1) ^ p ^ k`. -/
theorem Nat.Prime.dvd_sub_one_pow_of_pow_eq_one {A : Type*} [Ring A] {p : ℕ} (hp : p.Prime)
    {x : A} {k : ℕ} (hx : x ^ p ^ k = 1) : (p : A) ∣ (x - 1) ^ p ^ k := by
  -- Expand `1 = ((x - 1) + 1) ^ p ^ k` by the binomial theorem.
  have h : (1 : A) = ∑ m ∈ Finset.range (p ^ k + 1), (x - 1) ^ m * ((p ^ k).choose m : A) := by
    simpa [hx] using (Commute.one_right (x - 1)).add_pow (p ^ k)
  -- Split off the extreme terms `m = 0` and `m = p ^ k`, which are `1` and `(x - 1) ^ p ^ k`;
  -- what remains is `(x - 1) ^ p ^ k + S = 0` for the sum `S` of the middle terms.
  rw [Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (pow_pos hp.pos k)] at h
  simp only [pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, mul_one,
    zero_add, add_assoc, left_eq_add] at h
  -- Every middle term is divisible by `p`, through its binomial coefficient.
  rw [eq_neg_of_add_eq_zero_right h, dvd_neg]
  refine Finset.dvd_sum fun m hm ↦ ?_
  rw [Finset.mem_Ico] at hm
  rw [← (Nat.cast_commute _ _).eq]
  exact (Nat.cast_dvd_cast (hp.dvd_choose_pow (by omega) hm.2.ne)).mul_right _
