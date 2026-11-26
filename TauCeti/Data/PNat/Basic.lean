/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic

/-!
# Positive integers: exact division and `succPNat` strong induction

For positive integers `k ∣ m`, `PNat.divExact m k` is the quotient `m / k` as a positive integer.
This file identifies it with the natural-number quotient and provides strong induction on `i : ℕ+`
written as `n.succPNat` with hypotheses ranging over `(j : ℕ) ≤ n`.

## Main results

* `PNat.coe_divExact`: for `k ∣ m`, `(PNat.divExact m k : ℕ) = m / k`.
* `PNat.lt_succPNat_iff`: `j < n.succPNat ↔ (j : ℕ) ≤ n`.
* `PNat.strongInductionOnSuccPNat`: strong induction on `n.succPNat`.
-/

public section

namespace PNat

/-- For `k ∣ m`, the exact quotient `PNat.divExact m k` is the natural-number quotient `m / k`. -/
theorem coe_divExact {m k : ℕ+} (h : k ∣ m) : (divExact m k : ℕ) = m / k :=
  (Nat.div_eq_of_eq_mul_right k.pos (by rw [← mul_coe, mul_div_exact h])).symm

/-- A positive integer `j` is strictly less than `n.succPNat` if and only if `(j : ℕ) ≤ n`. -/
@[simp]
theorem lt_succPNat_iff {j : ℕ+} {n : ℕ} : j < n.succPNat ↔ (j : ℕ) ≤ n := by
  rw [← coe_lt_coe, Nat.succPNat_coe, Nat.lt_succ_iff]

/-- Strong induction on `i : ℕ+` written as `n.succPNat`, giving the induction hypothesis for all
`j : ℕ+` with `(j : ℕ) ≤ n`. -/
@[elab_as_elim]
def strongInductionOnSuccPNat {motive : ℕ+ → Sort*} (i : ℕ+)
    (ih : ∀ n : ℕ, (∀ j : ℕ+, (j : ℕ) ≤ n → motive j) → motive n.succPNat) : motive i :=
  i.strongInductionOn fun k ihk ↦
    k.succPNat_natPred ▸ ih k.natPred fun j hj ↦
      ihk j ((lt_succPNat_iff.mpr hj).trans_eq k.succPNat_natPred)

end PNat
