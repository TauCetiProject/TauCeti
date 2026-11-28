/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# The least quadratic nonresidue

For an odd prime `p`, the least quadratic nonresidue `q(p)` is the least integer `n ≥ 1` whose
Jacobi symbol modulo `p` is `-1`. Multiples of `p` have symbol `0` and are not nonresidues, so
`q(p) < p`. Outside the odd primes the value is declared to be `0`.

## Main definitions

* `TauCeti.SieveApplications.leastNonresidue p`: the least `n ≥ 1` with `J(n | p) = -1` for an odd
  prime `p`, and `0` if `p` is not an odd prime.

## Main results

* `TauCeti.SieveApplications.exists_jacobiSym_eq_neg_one`: an odd prime `p` has a nonresidue `n`
  with `0 < n < p`.
* `TauCeti.SieveApplications.leastNonresidue_pos`,
  `TauCeti.SieveApplications.jacobiSym_leastNonresidue`: at an odd prime, `q(p)` is positive and
  has symbol `-1`.
* `TauCeti.SieveApplications.leastNonresidue_lt`: `q(p) < p` for every positive `p`.
* `TauCeti.SieveApplications.jacobiSym_ne_neg_one_of_lt_leastNonresidue`,
  `TauCeti.SieveApplications.leastNonresidue_le`: minimality.
* `TauCeti.SieveApplications.leastNonresidue_eq_iff`: the characterization of the value at an odd
  prime.
* `TauCeti.SieveApplications.leastNonresidue_eq_zero_iff`: the value is `0` exactly outside the
  odd primes.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 16, §16.3, Definition 16.6.
-/

public section

namespace TauCeti.SieveApplications

variable {p n : ℕ}

/-- An odd prime `p` has a quadratic nonresidue `n` with `0 < n < p`. -/
theorem exists_jacobiSym_eq_neg_one (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ n : ℕ, 0 < n ∧ n < p ∧ jacobiSym n p = -1 := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨a.val, Nat.pos_of_ne_zero fun h0 ↦ ha ?_, ZMod.val_lt a, ?_⟩
  · rw [(ZMod.val_eq_zero a).1 h0]
    exact IsSquare.zero
  · rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff']
    rwa [ZMod.natCast_zmod_val]

open Classical in
/-- The least quadratic nonresidue modulo `p`: for an odd prime `p`, the least natural number
`n ≥ 1` with Jacobi symbol `J(n | p) = -1`; for every other `p`, the value `0`. -/
noncomputable def leastNonresidue (p : ℕ) : ℕ :=
  if h : ∃ n : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ jacobiSym n p = -1 then Nat.find h else 0

/-- The search predicate of `leastNonresidue` is satisfiable at an odd prime. -/
private theorem exists_search (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ n : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ jacobiSym n p = -1 :=
  let ⟨n, hn, _, hJ⟩ := exists_jacobiSym_eq_neg_one hp hp2
  ⟨n, hp, hp2, hn, hJ⟩

/-- **The value of the least quadratic nonresidue.** At an odd prime `p`, `leastNonresidue p = n`
exactly when `n` has symbol `-1` and no smaller natural number has symbol `-1`. Positivity of `n`
is automatic, since `J(0 | p) = 0`. -/
theorem leastNonresidue_eq_iff (hp : p.Prime) (hp2 : p ≠ 2) :
    leastNonresidue p = n ↔ jacobiSym n p = -1 ∧ ∀ m < n, jacobiSym m p ≠ -1 := by
  classical
  have hpos {m : ℕ} (hJ : jacobiSym m p = -1) : 0 < m := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    rw [Nat.cast_zero, jacobiSym.zero_left hp.one_lt] at hJ
    exact absurd hJ (by decide)
  rw [leastNonresidue, dite_eq_left (exists_search hp hp2), Nat.find_eq_iff]
  exact ⟨fun ⟨⟨_, _, _, hJ⟩, hmin⟩ ↦ ⟨hJ, fun m hmn hJm ↦ hmin m hmn ⟨hp, hp2, hpos hJm, hJm⟩⟩,
    fun ⟨hJ, hmin⟩ ↦ ⟨⟨hp, hp2, hpos hJ, hJ⟩, fun m hmn ⟨_, _, _, hJm⟩ ↦ hmin m hmn hJm⟩⟩

/-- The least quadratic nonresidue is `0` when `p` is not prime. -/
@[simp]
theorem leastNonresidue_eq_zero_of_not_prime (hp : ¬p.Prime) : leastNonresidue p = 0 := by
  classical
  exact dite_eq_right fun ⟨_, hp', _⟩ ↦ hp hp'

/-- The least quadratic nonresidue modulo `2` is `0`, by convention. -/
@[simp]
theorem leastNonresidue_two : leastNonresidue 2 = 0 := by
  classical
  exact dite_eq_right fun ⟨_, _, h2, _⟩ ↦ h2 rfl

/-- At an odd prime the least quadratic nonresidue is positive. -/
@[simp]
theorem leastNonresidue_pos (hp : p.Prime) (hp2 : p ≠ 2) : 0 < leastNonresidue p := by
  classical
  rw [leastNonresidue, dite_eq_left (exists_search hp hp2)]
  exact (Nat.find_spec (exists_search hp hp2)).2.2.1

/-- At an odd prime the least quadratic nonresidue has Jacobi symbol `-1`. -/
@[simp]
theorem jacobiSym_leastNonresidue (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiSym (leastNonresidue p) p = -1 :=
  ((leastNonresidue_eq_iff hp hp2).1 rfl).1

/-- The least quadratic nonresidue is `0` exactly when `p` is not an odd prime. -/
@[simp]
theorem leastNonresidue_eq_zero_iff : leastNonresidue p = 0 ↔ ¬(p.Prime ∧ p ≠ 2) := by
  refine ⟨fun h ⟨hp, hp2⟩ ↦ (leastNonresidue_pos hp hp2).ne' h, fun h ↦ ?_⟩
  by_cases hp : p.Prime
  · obtain rfl : p = 2 := by_contra fun hp2 ↦ h ⟨hp, hp2⟩
    exact leastNonresidue_two
  · exact leastNonresidue_eq_zero_of_not_prime hp

/-- No natural number below the least quadratic nonresidue has Jacobi symbol `-1`. No hypothesis
on `p` is needed: outside the odd primes the value is `0`. -/
theorem jacobiSym_ne_neg_one_of_lt_leastNonresidue (h : n < leastNonresidue p) :
    jacobiSym n p ≠ -1 := by
  have hp : p.Prime ∧ p ≠ 2 := by
    by_contra hp
    rw [leastNonresidue_eq_zero_iff.2 hp] at h
    exact Nat.not_lt_zero n h
  exact ((leastNonresidue_eq_iff hp.1 hp.2).1 rfl).2 n h

/-- The least quadratic nonresidue is at most every natural number with Jacobi symbol `-1`. No
hypothesis on `p` is needed: outside the odd primes the value is `0`. -/
theorem leastNonresidue_le (h : jacobiSym n p = -1) : leastNonresidue p ≤ n :=
  not_lt.1 fun hlt ↦ jacobiSym_ne_neg_one_of_lt_leastNonresidue hlt h

/-- The least quadratic nonresidue modulo a positive `p` is less than `p`: at an odd prime some
`n < p` has symbol `-1`, and for every other `p` the value is `0`. -/
theorem leastNonresidue_lt (hp : 0 < p) : leastNonresidue p < p := by
  by_cases h : p.Prime ∧ p ≠ 2
  · obtain ⟨_, _, hnp, hJ⟩ := exists_jacobiSym_eq_neg_one h.1 h.2
    exact (leastNonresidue_le hJ).trans_lt hnp
  · rwa [leastNonresidue_eq_zero_iff.2 h]

/-! ### Examples -/

/-- `q(3) = 2`. -/
example : leastNonresidue 3 = 2 :=
  (leastNonresidue_eq_iff Nat.prime_three (by norm_num)).2
    ⟨by norm_num, fun m hm ↦ by interval_cases m <;> norm_num⟩

/-- `q(7) = 3`, since `2` is a residue modulo `7`. -/
example : leastNonresidue 7 = 3 :=
  (leastNonresidue_eq_iff (by decide) (by norm_num)).2
    ⟨by norm_num, fun m hm ↦ by interval_cases m <;> norm_num⟩

/-- `q(2) = 0`, by the convention outside the odd primes. -/
example : leastNonresidue 2 = 0 := leastNonresidue_two

/-- `3` is not a nonresidue modulo `3`: its symbol is `0`. -/
example : jacobiSym 3 3 ≠ -1 := by norm_num

end TauCeti.SieveApplications
