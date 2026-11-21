/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Card

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
* `TauCeti.monotone_benjaminiHochbergCount`: the count is monotone in `α`.
* `TauCeti.antitone_benjaminiHochbergCount`: the count is antitone in the p-values.
* `TauCeti.card_filter_le_benjaminiHochbergCount_eq`: for `0 ≤ α`, exactly `k` p-values are at
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
  ((range (m + 1)).filter fun k : ℕ ↦ k ≤ #{i | p i ≤ k * α / m}).sup id

/-- The Benjamini–Hochberg count is the largest qualifying `k ≤ m`. -/
theorem benjaminiHochbergCount_def (p : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount p α =
      ((range (m + 1)).filter fun k : ℕ ↦ k ≤ #{i | p i ≤ k * α / m}).sup id :=
  (rfl)

/-- Every `k` such that at least `k` p-values are at most `k α / m` is at most the
Benjamini–Hochberg count. -/
theorem le_benjaminiHochbergCount (p : Fin m → ℝ) (α : ℝ) {k : ℕ}
    (h : k ≤ #{i | p i ≤ k * α / m}) : k ≤ benjaminiHochbergCount p α := by
  have hk : k ≤ m := h.trans ((card_le_univ _).trans_eq (Fintype.card_fin m))
  exact le_sup (f := id) (mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le hk), h⟩)

/-- The Benjamini–Hochberg count is at most the number of p-values. -/
theorem benjaminiHochbergCount_le (p : Fin m → ℝ) (α : ℝ) : benjaminiHochbergCount p α ≤ m :=
  Finset.sup_le fun _ hk ↦ Nat.le_of_lt_succ (mem_range.1 (mem_filter.1 hk).1)

/-- At least `k` p-values are at most `k α / m`, where `k` is the Benjamini–Hochberg count. -/
theorem benjaminiHochbergCount_le_card_filter (p : Fin m → ℝ) (α : ℝ) :
    benjaminiHochbergCount p α ≤ #{i | p i ≤ benjaminiHochbergCount p α * α / m} := by
  obtain ⟨k, hk, hsup⟩ := exists_mem_eq_sup
    ((range (m + 1)).filter fun k : ℕ ↦ k ≤ #{i | p i ≤ k * α / m})
    ⟨0, mem_filter.2 ⟨mem_range.2 m.succ_pos, Nat.zero_le _⟩⟩ id
  rw [benjaminiHochbergCount_def, hsup]
  exact (mem_filter.1 hk).2

/-- The Benjamini–Hochberg count is monotone in the level `α`. -/
theorem monotone_benjaminiHochbergCount (p : Fin m → ℝ) :
    Monotone (benjaminiHochbergCount p) := by
  intro α α' hαα'
  refine le_benjaminiHochbergCount p α'
    ((benjaminiHochbergCount_le_card_filter p α).trans (card_le_card fun i hi ↦ ?_))
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hαα' (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

/-- The Benjamini–Hochberg count is antitone in the p-values. -/
theorem antitone_benjaminiHochbergCount (α : ℝ) :
    Antitone fun p : Fin m → ℝ ↦ benjaminiHochbergCount p α := by
  intro p q hpq
  refine le_benjaminiHochbergCount p α
    ((benjaminiHochbergCount_le_card_filter q α).trans (card_le_card fun i hi ↦ ?_))
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact (hpq i).trans hi

/-- For a nonnegative level `α`, exactly `k` p-values are at most `k α / m`, where `k` is the
Benjamini–Hochberg count: the Benjamini–Hochberg procedure rejects exactly `k` hypotheses. -/
theorem card_filter_le_benjaminiHochbergCount_eq (p : Fin m → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    #{i | p i ≤ benjaminiHochbergCount p α * α / m} = benjaminiHochbergCount p α := by
  set k := benjaminiHochbergCount p α
  set j := #{i | p i ≤ k * α / m}
  refine le_antisymm ?_ (benjaminiHochbergCount_le_card_filter p α)
  -- The number `j` of p-values at most `k α / m` itself qualifies, since `k ≤ j`.
  have hkj : k ≤ j := benjaminiHochbergCount_le_card_filter p α
  refine le_benjaminiHochbergCount p α (card_le_card fun i hi ↦ ?_)
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  refine hi.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ?_ hα) (Nat.cast_nonneg _))
  exact_mod_cast hkj

end TauCeti
