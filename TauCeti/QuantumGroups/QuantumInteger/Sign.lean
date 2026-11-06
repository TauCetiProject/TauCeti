/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Binomial

import Mathlib.Tactic

/-!
# Changing the sign of the quantum parameter

The symmetric quantum binomials satisfy
`[n choose k]_{-q} = (-1)^{k(n-k)} [n choose k]_q`.
The identity is proved without dividing by quantum integers, so it includes roots of unity
and the parameters `q = ±1`. In particular, specialization at `-1` gives a signed ordinary
binomial coefficient. These signs enter comparisons of quantum divided-power relations
at opposite parameters.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Sections 1.3 and 33.2, for the symmetric
  normalization and sign comparisons.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K]

/-- Negating the parameter multiplies the symmetric quantum binomial by
`(-1)^(k * (n - k))`. This includes zero parameters and indices above the diagonal. -/
@[simp]
theorem quantumBinomial_neg_left (q : K) (n k : ℕ) :
    quantumBinomial (-q) n k = (-1 : K) ^ (k * (n - k)) * quantumBinomial q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases lt_or_ge k n with hk | hk
      · have he : n - k = n - (k + 1) + 1 := by omega
        have h₁ : (-1 : K) ^ (n - k) * (-1) ^ (k * (n - k)) =
            (-1) ^ ((k + 1) * (n - k)) := by
          rw [← pow_add]
          congr 1
          ring
        have h₂ : (-1 : K) ^ (k + 1) * (-1) ^ ((k + 1) * (n - (k + 1))) =
            (-1) ^ ((k + 1) * (n - k)) := by
          rw [← pow_add, he]
          congr 1
          ring
        rw [quantumBinomial_succ_succ, quantumBinomial_succ_succ, ih, ih]
        simp only [inv_neg, neg_pow q, neg_pow q⁻¹, Nat.add_sub_add_right]
        calc
          _ = ((-1 : K) ^ (n - k) * (-1) ^ (k * (n - k))) *
                (q ^ (n - k) * quantumBinomial q n k) +
              ((-1 : K) ^ (k + 1) * (-1) ^ ((k + 1) * (n - (k + 1)))) *
                (q⁻¹ ^ (k + 1) * quantumBinomial q n (k + 1)) := by ring
          _ = _ := by rw [h₁, h₂]; ring
      · rcases eq_or_lt_of_le hk with rfl | hk
        · simp
        · simp [quantumBinomial_eq_zero_of_lt q (by omega : n + 1 < k + 1),
            quantumBinomial_eq_zero_of_lt (-q) (by omega : n + 1 < k + 1)]

end TauCeti
