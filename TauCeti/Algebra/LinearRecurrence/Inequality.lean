/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Bounded solutions of a second-order recurrence inequality

Let `d ≥ 1` and `r` be natural numbers, and let `c : ℕ → ℕ` start at `c 0 = 0` and satisfy

```text
c (n + 2) + r c n ≥ 1 + d c (n + 1)       for every n.
```

If `d² ≥ 4 r`, the characteristic polynomial `X² - d X + r` has real roots `α ≥ β ≥ 0` with
`α ≥ 1`, and the differences `w n = c (n + 1) - β c n` satisfy `w (n + 1) ≥ α w n + 1 ≥ w n + 1`,
so `c (n + 1) ≥ w n ≥ n` grows without bound. Hence a bounded such sequence forces `d² < 4 r`.

This is the numerical half of the Golod–Shafarevich inequality: for a finite-dimensional algebra
with a presentation by `d` generators and `r` relations of degree at least two, the codimensions of
the powers of the augmentation ideal satisfy this recurrence, and are bounded by the dimension.

## Main results

* `TauCeti.sq_lt_four_mul_of_forall_add_mul_le`: a bounded sequence of natural numbers with
  `c 0 = 0` and `1 + d c (n + 1) ≤ c (n + 2) + r c n`, for `d ≥ 1`, forces `d² < 4 r`.

## References

* E. S. Golod and I. R. Shafarevich, *On the class field tower*, Izv. Akad. Nauk SSSR Ser. Mat.
  28 (1964).
* P. Roquette, *On class field towers*, in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic
  Number Theory*, Chapter IX, §4.
-/

public section

namespace TauCeti

/-- **A bounded solution of `c (n + 2) + r c n ≥ 1 + d c (n + 1)` forces `d² < 4 r`.** Let
`d ≥ 1`, and let `c : ℕ → ℕ` be bounded, with `c 0 = 0` and `1 + d c (n + 1) ≤ c (n + 2) + r c n`
for every `n`. Then `d² < 4 r`. -/
theorem sq_lt_four_mul_of_forall_add_mul_le {d r : ℕ} (hd : 0 < d) {c : ℕ → ℕ} (h0 : c 0 = 0)
    (hbdd : BddAbove (Set.range c)) (hrec : ∀ n, 1 + d * c (n + 1) ≤ c (n + 2) + r * c n) :
    d ^ 2 < 4 * r := by
  by_contra! hdr
  obtain ⟨B, hB⟩ := hbdd
  -- The roots `α = (d + s) / 2 ≥ β = (d - s) / 2 ≥ 0` of `X² - d X + r`, with `α ≥ 1`.
  set s := √((d : ℝ) ^ 2 - 4 * r)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = d ^ 2 - 4 * r := Real.sq_sqrt (by rw [sub_nonneg]; exact_mod_cast hdr)
  have hsd : s ≤ d := by nlinarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]
  have hα : 2 ≤ (d : ℝ) + s := by
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · -- For `d = 1` the hypothesis `d² ≥ 4 r` forces `r = 0`, so `s = 1`.
      obtain rfl : d = 1 := by omega
      obtain rfl : r = 0 := by omega
      norm_num [s]
    · have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
      linarith
  -- The differences `w n = c (n + 1) - β c n` satisfy `w (n + 1) ≥ α w n + 1 ≥ w n + 1`, so they
  -- grow at least linearly.
  have hw (n : ℕ) : (n : ℝ) ≤ c (n + 1) - (d - s) / 2 * c n := by
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      have h : 1 + (d : ℝ) * c (n + 1) ≤ c (n + 2) + r * c n := by exact_mod_cast hrec n
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (B : ℝ)
  have hcB : (c (n + 1) : ℝ) ≤ B := by exact_mod_cast hB ⟨n + 1, rfl⟩
  nlinarith [hw n, (c n).cast_nonneg (α := ℝ)]

end TauCeti
