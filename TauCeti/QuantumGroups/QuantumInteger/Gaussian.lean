/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Binomial
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import Mathlib.Tactic.FieldSimp

/-!
# Gaussian and symmetric quantum binomial coefficients

The Gaussian binomial coefficient `TauCeti.gaussianBinomial` is the non-symmetric normalization of
the symmetric quantum binomial coefficient `TauCeti.quantumBinomial`: over a field,
`[n k]_(q²) = q^(k (n-k)) [n choose k]_q` for `q ≠ 0`. Unlike the symmetric coefficient, the
Gaussian coefficient needs neither inverses nor a square root of the parameter.

## Main results

* `TauCeti.gaussianBinomial_sq`: the comparison of `TauCeti.gaussianBinomial` with
  `TauCeti.quantumBinomial`.
-/

public section

namespace TauCeti

/-- The Gaussian binomial coefficient is the non-symmetric normalization of the symmetric quantum
binomial coefficient: `[n k]_(q²) = q^(k (n-k)) [n choose k]_q` for `q ≠ 0` in a field. -/
theorem gaussianBinomial_sq {K : Type*} [Field K] {q : K} (hq : q ≠ 0) (n k : ℕ) :
    gaussianBinomial (q ^ 2) n k = q ^ (k * (n - k)) * quantumBinomial q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases lt_or_ge n k with hnk | hkn
      · rw [gaussianBinomial_eq_zero_of_lt _ (by omega), quantumBinomial_eq_zero_of_lt _ (by omega),
          mul_zero]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
      rw [gaussianBinomial_succ_succ, quantumBinomial_succ_succ', ih, ih]
      rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel_left, show k + (m + 1) + 1 - (k + 1) = m + 1 by omega,
          show k + (m + 1) - (k + 1) = m by omega]
        rw [inv_pow]
        field_simp
        ring

end TauCeti
