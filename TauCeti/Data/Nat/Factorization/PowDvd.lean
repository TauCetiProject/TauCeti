/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

/-!
# Divisibility from divisibility of all powers up to a fixed factor

If `d ^ (m + 1)` divides `c * i ^ (m + 1)` for every `m`, with `c` nonzero, then `d` divides
`i`. At each prime `p` the hypothesis gives
`(m + 1) v_p(d) ≤ v_p(c) + (m + 1) v_p(i)`, and for `m + 1 > v_p(c)` this forces
`v_p(d) ≤ v_p(i)`. The fixed factor `c` is thus washed out by taking powers. This is how the
tensor-power argument turns `χ(1)^m ∣ |Z| · |H : Z|^m` for all `m` into `χ(1) ∣ |H : Z|`.

## Main results

* `Nat.dvd_of_forall_pow_dvd_mul_pow`: if `d ^ (m + 1) ∣ c * i ^ (m + 1)` for every `m`, with
  `c ≠ 0`, then `d ∣ i`.
-/

public section

namespace Nat

/-- **A fixed factor does not survive taking powers.** If `d ^ (m + 1)` divides `c * i ^ (m + 1)`
for every `m`, with `c` nonzero, then `d` divides `i`: for each prime the exponent in `d`
exceeds that in `i` by at most `v_p(c) / (m + 1)`. -/
theorem dvd_of_forall_pow_dvd_mul_pow {d c i : ℕ} (hc : c ≠ 0)
    (h : ∀ m : ℕ, d ^ (m + 1) ∣ c * i ^ (m + 1)) : d ∣ i := by
  rcases eq_or_ne i 0 with rfl | hi
  · exact dvd_zero d
  rcases eq_or_ne d 0 with rfl | hd
  · -- `0 ∣ c * i` would force `i = 0`
    simpa [hc, hi] using h 0
  rw [← factorization_le_iff_dvd hd hi]
  intro p
  have hm := (factorization_le_iff_dvd (pow_ne_zero _ hd)
    (mul_ne_zero hc (pow_ne_zero _ hi))).mpr (h (c.factorization p)) p
  rw [factorization_mul hc (pow_ne_zero _ hi), factorization_pow, factorization_pow] at hm
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply] at hm
  by_contra hlt
  nlinarith [not_le.mp hlt]

end Nat
