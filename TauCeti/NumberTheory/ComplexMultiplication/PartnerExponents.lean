/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.NumberTheory.LegendreSymbol.NegOne

/-!
# The valuation of `π_p` and the partner exponents at a prime

Let `d` be a prime and `χ = (· / d)` the Legendre symbol `legendreSym d`. At a natural number `p`,
the theta-function estimates of `ℚ(√-d)` and the local prime sums of the Legendre symbol modulo `d`
use the same weight and the same exponents of `p`:

* `piPrimeValuation d p = v(π_p)`: `1 / 2` if `p = d` and `1` otherwise, the valuation of the
  number `π_p` (`TauCeti.ComplexMultiplication.piPrime`) normalised by `v(p) = 1`.
* `partnerExponents d p = I_p°`: all `e ≥ 0` if `p = d`, the odd `e ≥ 0` if `(p / d) = -1`, and no
  `e` otherwise; `positivePartnerExponents d p = I_p` is its subset of positive exponents.

This file computes the two exponent sets in the three cases.

## Main definitions

* `TauCeti.ComplexMultiplication.piPrimeValuation`,
  `TauCeti.ComplexMultiplication.partnerExponents`,
  `TauCeti.ComplexMultiplication.positivePartnerExponents`.

## References

* The definitions follow the formal proof in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `src/Lib/CM/FormalGroup/PrimeNotation.lean` (`New.piPrimeValuation`, `New.partnerExponents`,
  `New.positivePartnerExponents`).
-/

public section

namespace TauCeti.ComplexMultiplication

variable (d p : ℕ)

/-- `v(π_p)`: `1 / 2` if `p = d` and `1` otherwise, the valuation of `π_p` at `p` normalised by
`v(p) = 1` (`norm_map_piPrime`). -/
noncomputable def piPrimeValuation : ℝ := if p = d then 1 / 2 else 1

section Valuation

variable {d p}

theorem piPrimeValuation_def : piPrimeValuation d p = if p = d then 1 / 2 else 1 := by
  rw [piPrimeValuation]

@[simp] theorem piPrimeValuation_self : piPrimeValuation d d = 1 / 2 := by
  simp [piPrimeValuation]

theorem piPrimeValuation_of_ne (h : p ≠ d) : piPrimeValuation d p = 1 := by
  simp [piPrimeValuation, h]

theorem piPrimeValuation_pos : 0 < piPrimeValuation d p := by
  unfold piPrimeValuation
  split_ifs <;> norm_num

theorem piPrimeValuation_le_one : piPrimeValuation d p ≤ 1 := by
  unfold piPrimeValuation
  split_ifs <;> norm_num

end Valuation

variable [Fact d.Prime]

/-- `I_p°`: all `e` if `p = d`, the odd `e` if `(p / d) = -1`, and no `e` otherwise. -/
def partnerExponents : Set ℕ := {e | p = d ∨ legendreSym d p = -1 ∧ Odd e}

/-- `I_p`: the positive elements of `I_p°`. -/
def positivePartnerExponents : Set ℕ := {e | e ∈ partnerExponents d p ∧ 0 < e}

variable {d p}

@[simp] theorem mem_partnerExponents_iff {e : ℕ} :
    e ∈ partnerExponents d p ↔ p = d ∨ legendreSym d p = -1 ∧ Odd e := by
  rw [partnerExponents, Set.mem_ofPred_eq]

@[simp] theorem mem_positivePartnerExponents_iff {e : ℕ} :
    e ∈ positivePartnerExponents d p ↔ e ∈ partnerExponents d p ∧ 0 < e := by
  rw [positivePartnerExponents, Set.mem_ofPred_eq]

/-- `I_p° = ∅` when `p ≠ d` and `(p / d) ≠ -1`. -/
theorem partnerExponents_of_ne_of_legendreSym_ne_neg_one (h₁ : p ≠ d)
    (h₂ : legendreSym d p ≠ -1) : partnerExponents d p = ∅ := by
  ext e
  simp [mem_partnerExponents_iff, h₁, h₂]

/-- `I_p = ∅` when `p ≠ d` and `(p / d) ≠ -1`. -/
theorem positivePartnerExponents_of_ne_of_legendreSym_ne_neg_one (h₁ : p ≠ d)
    (h₂ : legendreSym d p ≠ -1) : positivePartnerExponents d p = ∅ := by
  ext e
  simp [mem_positivePartnerExponents_iff, partnerExponents_of_ne_of_legendreSym_ne_neg_one h₁ h₂]

/-- `I_p°` is the set of odd exponents when `(p / d) = -1`. -/
theorem partnerExponents_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) :
    partnerExponents d p = {e | Odd e} := by
  ext e
  simp [mem_partnerExponents_iff, ne_of_legendreSym_eq_neg_one h, h]

/-- When `(p / d) = -1`, `I_p` is the set of odd exponents `2k + 1`; for `d ≡ 3 (mod 4)` and a
prime `p`, this is the case of `p` inert in `ℚ(√-d)`. -/
theorem positivePartnerExponents_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) :
    positivePartnerExponents d p = Set.range (fun k : ℕ ↦ 2 * k + 1) := by
  ext e
  rw [mem_positivePartnerExponents_iff, partnerExponents_of_legendreSym_eq_neg_one h,
    Set.mem_ofPred_eq, and_iff_left_of_imp Odd.pos, odd_iff_exists_bit1, Set.mem_range]
  exact exists_congr fun _ ↦ eq_comm

/-- `I_d°` is the set of all exponents in the ramified case `p = d`. -/
@[simp] theorem partnerExponents_self : partnerExponents d d = Set.univ := by
  ext e
  simp [mem_partnerExponents_iff]

/-- For `p = d`, `I_p` is the set of exponents `k + 1`. -/
theorem positivePartnerExponents_self :
    positivePartnerExponents d d = Set.range (fun k : ℕ ↦ k + 1) := by
  ext e
  rw [Nat.range_succ, mem_positivePartnerExponents_iff, partnerExponents_self]
  simp

end TauCeti.ComplexMultiplication
