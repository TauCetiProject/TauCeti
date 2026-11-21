/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Find

/-!
# The Benjamini–Hochberg count

For p-values `p : Fin m → ℝ` and a level `α`, the Benjamini–Hochberg count is the largest
`k ≤ m` such that at least `k` of the p-values are at most `k α / m` (Dickhaus, Def 5.6). The
Benjamini–Hochberg procedure rejects the hypotheses whose p-values are at most `k α / m` for this
`k`.

## Main definitions

* `TauCeti.benjaminiHochbergCount p α`: the Benjamini–Hochberg count.

## Main results

* `TauCeti.benjaminiHochbergCount_le`: the count is at most `m`.
* `TauCeti.le_benjaminiHochbergCount`, `TauCeti.benjaminiHochbergCount_le_iff`: lower bounds
  from a qualifying `k`, and upper bounds from the failure of every larger `j`.
* `TauCeti.benjaminiHochbergCount_right_monotone`: the count is monotone in `α`.
* `TauCeti.benjaminiHochbergCount_left_antitone`: the count is antitone in the p-values.
* `TauCeti.card_filter_eq_benjaminiHochbergCount`: for `0 ≤ α`, exactly `k` p-values are at
  most `k α / m`, where `k` is the count, so the procedure rejects exactly `k` hypotheses. For
  negative `α` there can be more.

## References

* T. Dickhaus, *Simultaneous Statistical Inference*, Springer, 2014, Def 5.6 (p. 80).

The definition is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Nonparametric/Basic.lean`; the proofs are new.
-/

public section

open Finset

namespace TauCeti

variable {m : ℕ}

/-- The Benjamini–Hochberg count of the p-values `p` at level `α`: the largest `k ≤ m` such that
at least `k` of the p-values are at most `k α / m`. It is `0` when no `k ≥ 1` qualifies. -/
noncomputable def benjaminiHochbergCount (p : Fin m → ℝ) (α : ℝ) : ℕ :=
  Nat.findGreatest (fun k ↦ k ≤ #{i | p i ≤ k * α / m}) m

/-- The Benjamini–Hochberg count is the largest qualifying `k ≤ m`. -/
theorem benjaminiHochbergCount_def (p : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount p α = Nat.findGreatest (fun k ↦ k ≤ #{i | p i ≤ k * α / m}) m :=
  (rfl)

/-- Every `k` such that at least `k` p-values are at most `k α / m` is at most the
Benjamini–Hochberg count. -/
theorem le_benjaminiHochbergCount (p : Fin m → ℝ) (α : ℝ) {k : ℕ}
    (h : k ≤ #{i | p i ≤ k * α / m}) : k ≤ benjaminiHochbergCount p α :=
  Nat.le_findGreatest (h.trans ((card_le_univ _).trans_eq (Fintype.card_fin m))) h

/-- The Benjamini–Hochberg count is at most the number of p-values. -/
@[grind! .]
theorem benjaminiHochbergCount_le (p : Fin m → ℝ) (α : ℝ) : benjaminiHochbergCount p α ≤ m :=
  Nat.findGreatest_le m

/-- At least `k` p-values are at most `k α / m`, where `k` is the Benjamini–Hochberg count. -/
@[grind! .]
theorem benjaminiHochbergCount_le_card_filter (p : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount p α ≤ #{i | p i ≤ benjaminiHochbergCount p α * α / m} :=
  Nat.findGreatest_spec (P := fun k ↦ k ≤ #{i | p i ≤ k * α / m}) (Nat.zero_le m)
    (Nat.zero_le _)

/-- The Benjamini–Hochberg count is at most `k` iff every `j > k` fails to qualify: fewer than
`j` p-values are at most `j α / m`. -/
theorem benjaminiHochbergCount_le_iff (p : Fin m → ℝ) (α : ℝ) {k : ℕ} :
    benjaminiHochbergCount p α ≤ k ↔ ∀ j, k < j → #{i | p i ≤ j * α / m} < j := by
  refine ⟨fun h j hj ↦ lt_of_not_ge fun hq ↦ ?_, fun h ↦ le_of_not_gt fun hk ↦ ?_⟩
  · exact absurd ((le_benjaminiHochbergCount p α hq).trans h) (not_le.2 hj)
  · exact absurd (benjaminiHochbergCount_le_card_filter p α) (not_le.2 (h _ hk))

/-- The Benjamini–Hochberg count is monotone in the level `α`. -/
theorem benjaminiHochbergCount_right_monotone (p : Fin m → ℝ) :
    Monotone (benjaminiHochbergCount p) := by
  intro α α' hαα'
  rw [benjaminiHochbergCount_def, benjaminiHochbergCount_def]
  refine Nat.findGreatest_mono_left (fun k hk ↦
    hk.trans (card_le_card (monotone_filter_right _ fun i _ hi ↦ hi.trans ?_))) m
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hαα' (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- The Benjamini–Hochberg count is antitone in the p-values. -/
theorem benjaminiHochbergCount_left_antitone (α : ℝ) :
    Antitone fun p : Fin m → ℝ ↦ benjaminiHochbergCount p α := by
  intro p q hpq
  dsimp only
  rw [benjaminiHochbergCount_def, benjaminiHochbergCount_def]
  exact Nat.findGreatest_mono_left (fun k hk ↦
    hk.trans (card_le_card (monotone_filter_right _ fun i _ hi ↦ (hpq i).trans hi))) m

/-- For a nonnegative level `α`, exactly `k` p-values are at most `k α / m`, where `k` is the
Benjamini–Hochberg count: the Benjamini–Hochberg procedure rejects exactly `k` hypotheses. -/
theorem card_filter_eq_benjaminiHochbergCount (p : Fin m → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    #{i | p i ≤ benjaminiHochbergCount p α * α / m} = benjaminiHochbergCount p α := by
  set k := benjaminiHochbergCount p α
  have hkj : k ≤ #{i | p i ≤ k * α / m} := benjaminiHochbergCount_le_card_filter p α
  refine le_antisymm ?_ hkj
  -- The number `j` of p-values at most `k α / m` itself qualifies, since `k ≤ j`.
  refine le_benjaminiHochbergCount p α
    (card_le_card (monotone_filter_right _ fun i _ hi ↦ hi.trans ?_))
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hα)
    (Nat.cast_nonneg _)

end TauCeti
