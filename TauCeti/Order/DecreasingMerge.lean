/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card

/-!
# The generalized decreasing merge of two sequences

For bounded sequences `a b : ℕ → α` in a conditionally complete lattice `α` (such as `ℝ≥0`), the
generalized decreasing merge `TauCeti.decreasingMerge a b` is the sequence of generalized
decreasing order statistics of the multiset union of the entries of `a` and `b`: its `n`-th term
is the supremum of the thresholds `r` attained by at least `n + 1` distinct entries, that is, the
supremum of those `r` for which some injective `q : Fin (n + 1) → ℕ ⊕ ℕ` has
`r ≤ Sum.elim a b (q i)` for every `i`. In the documentation below this term is written
`(a ⊔↓ b)ₙ`.

This is the operation that computes the approximation numbers of an orthogonal block sum from
those of its blocks (see `TauCeti.Analysis.OperatorIdeal.ApproximationNumber.BlockSum`). It is not
required to enumerate every entry of the union: if `a` is constant with value `1` and `b` is
constant with value `0`, then the merge is constant with value `1`, and the entries of `b` never
appear. This is the right behaviour for noncompact blocks, whose approximation numbers can have an
infinite plateau.

For antitone sequences in a conditionally complete linear order the threshold condition only
involves initial segments, so the merge is computed by splitting `n + 1 = i + j` between the two
sequences:

* `TauCeti.exists_injective_forall_le_sumElim_iff`: for antitone `a` and `b`, a threshold is
  attained by `n + 1` distinct entries exactly when it bounds the first `i` terms of `a` and the
  first `j` terms of `b` for some `i + j = n + 1`;
* `TauCeti.not_exists_add_eq_forall_le_iff`: in a linear order, no such split exists for `s`
  exactly when `aᵢ < s` and `bⱼ < s` for some `i + j ≤ n`;
* `TauCeti.le_decreasingMerge_iff`: `r ≤ (a ⊔↓ b)ₙ` exactly when, for some `i + j = n + 1`, the
  first `i` terms of `a` and the first `j` terms of `b` are all at least `r`;
* `TauCeti.decreasingMerge_lt_iff`: `(a ⊔↓ b)ₙ < s` exactly when `aᵢ < s` and `bⱼ < s` for some
  `i + j ≤ n`.

In particular the supremum defining the merge is attained for antitone sequences.

The merge is symmetric (`TauCeti.decreasingMerge_comm`) and antitone for bounded sequences
(`TauCeti.antitone_decreasingMerge`), and for antitone sequences its zeroth term is
`max (a 0) (b 0)` (`TauCeti.decreasingMerge_zero`).

## References

* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
-/

public section

namespace TauCeti

variable {α : Type*}

section Lattice

variable [ConditionallyCompleteLattice α] {a b : ℕ → α} {n : ℕ} {r : α}

/-- The **generalized decreasing merge** of two sequences `a b : ℕ → α`: its `n`-th term is the
supremum of the thresholds `r` attained by at least `n + 1` distinct entries of the multiset union
of `a` and `b`, that is, by `Sum.elim a b` at `n + 1` distinct indices of `ℕ ⊕ ℕ`.

It is meaningful for bounded sequences; for antitone sequences in a linear order it is computed by
`TauCeti.le_decreasingMerge_iff` and `TauCeti.decreasingMerge_lt_iff`. -/
noncomputable def decreasingMerge (a b : ℕ → α) (n : ℕ) : α :=
  sSup {r | ∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)}

/-- Unfolding `TauCeti.decreasingMerge`. -/
theorem decreasingMerge_def (a b : ℕ → α) (n : ℕ) :
    decreasingMerge a b n =
      sSup {r | ∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)} :=
  (rfl)

/-- A threshold attained by `n + 1` distinct entries of two bounded sequences is at most the
`n`-th term of their merge. -/
theorem le_decreasingMerge (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b))
    {q : Fin (n + 1) → ℕ ⊕ ℕ} (hq : Function.Injective q) (hr : ∀ i, r ≤ Sum.elim a b (q i)) :
    r ≤ decreasingMerge a b n := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  refine le_csSup ⟨A ⊔ B, ?_⟩ ⟨q, hq, hr⟩
  rintro t ⟨q', -, ht⟩
  refine (ht 0).trans ?_
  rcases q' 0 with k | k
  · exact (hA ⟨k, rfl⟩).trans le_sup_left
  · exact (hB ⟨k, rfl⟩).trans le_sup_right

/-- The merge is symmetric in its two arguments. -/
theorem decreasingMerge_comm (a b : ℕ → α) : decreasingMerge a b = decreasingMerge b a := by
  have key {a b : ℕ → α} {n : ℕ} {r : α} :
      (∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)) →
        ∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim b a (q i) :=
    fun ⟨q, hq, hr⟩ ↦ ⟨Sum.swap ∘ q, Sum.swap_leftInverse.injective.comp hq, fun i ↦
      (hr i).trans_eq (congrFun Sum.elim_swap (q i)).symm⟩
  ext1 n
  rw [decreasingMerge_def, decreasingMerge_def]
  exact congrArg sSup (Set.ext fun r ↦ ⟨key, key⟩)

/-- The `n`-th term of the merge is at most every common upper bound of the thresholds attained
by `n + 1` distinct entries. -/
theorem decreasingMerge_le {c : α}
    (h : ∀ r (q : Fin (n + 1) → ℕ ⊕ ℕ), Function.Injective q →
      (∀ i, r ≤ Sum.elim a b (q i)) → r ≤ c) :
    decreasingMerge a b n ≤ c := by
  -- The set of thresholds is nonempty: the least of `a 0, …, a n` is attained by those entries.
  refine csSup_le ⟨Finset.univ.inf' Finset.univ_nonempty (a ∘ Fin.val), Sum.inl ∘ Fin.val,
    Sum.inl_injective.comp Fin.val_injective, fun i ↦ Finset.inf'_le _ (Finset.mem_univ i)⟩ ?_
  rintro r ⟨q, hq, hr⟩
  exact h r q hq hr

/-- The merge of two bounded sequences is antitone. -/
theorem antitone_decreasingMerge (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b)) :
    Antitone (decreasingMerge a b) :=
  antitone_nat_of_succ_le fun _ ↦ decreasingMerge_le fun _ _ hq hr ↦
    le_decreasingMerge ha hb (hq.comp (Fin.castSucc_injective _)) fun i ↦ hr i.castSucc

end Lattice

section Preorder

variable [Preorder α] {a b : ℕ → α} {n : ℕ} {r : α}

/-- For antitone sequences, a threshold is attained by `n + 1` distinct entries exactly when it
bounds the first `i` terms of `a` and the first `j` terms of `b` for some `i + j = n + 1`. -/
theorem exists_injective_forall_le_sumElim_iff (ha : Antitone a) (hb : Antitone b) :
    (∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)) ↔
      ∃ i j, i + j = n + 1 ∧ (∀ k < i, r ≤ a k) ∧ ∀ k < j, r ≤ b k := by
  constructor
  · -- Count the indices `q` takes in each summand. The `i` distinct indices in the first summand
    -- include one at least `k` for each `k < i`, and `a` is antitone.
    rintro ⟨q, hq, hr⟩
    set u := Finset.univ.image q
    have hu : u.card = n + 1 := by
      rw [Finset.card_image_of_injective _ hq, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ x ∈ u, r ≤ Sum.elim a b x := by
      intro x hx
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hx
      exact hr l
    -- A finset of naturals with more than `k` elements is not contained in `range k`.
    have hge {t : Finset ℕ} {k : ℕ} (hk : k < t.card) : ∃ m ∈ t, k ≤ m := by
      obtain ⟨m, hm, hkm⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card ((Finset.card_range k).trans_lt hk)
      exact ⟨m, hm, not_lt.mp (Finset.mem_range.not.mp hkm)⟩
    refine ⟨u.toLeft.card, u.toRight.card, Finset.card_toLeft_add_card_toRight.trans hu,
      fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · obtain ⟨m, hm, hkm⟩ := hge hk
      exact (hmem _ (Finset.mem_toLeft.mp hm)).trans (ha hkm)
    · obtain ⟨m, hm, hkm⟩ := hge hk
      exact (hmem _ (Finset.mem_toRight.mp hm)).trans (hb hkm)
  · -- Take the first `i` indices of `a` followed by the first `j` indices of `b`.
    rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨fun l ↦ if (l : ℕ) < i then .inl l else .inr (l - i), fun l l' h ↦ ?_, fun l ↦ ?_⟩
    · dsimp only at h
      ext
      split_ifs at h with h₁ h₂ h₂ <;> simp only [Sum.inl.injEq, Sum.inr.injEq] at h
        <;> omega
    · dsimp only
      split_ifs with h
      · exact hi l h
      · exact hj _ (by omega)

end Preorder

/-- No split `i + j = n + 1` has `s` bounding the first `i` terms of `a` and the first `j` terms
of `b` exactly when `aᵢ < s` and `bⱼ < s` for some `i + j ≤ n`. -/
theorem not_exists_add_eq_forall_le_iff [LinearOrder α] {a b : ℕ → α} {n : ℕ} {s : α} :
    (¬∃ i j, i + j = n + 1 ∧ (∀ k < i, s ≤ a k) ∧ ∀ k < j, s ≤ b k) ↔
      ∃ i j, i + j ≤ n ∧ a i < s ∧ b j < s := by
  constructor
  · -- Take `i` and `j` least with `aᵢ < s` and `bⱼ < s`; they exist and `i + j ≤ n`, since
    -- otherwise `s` would bound enough initial terms of `a` and `b`.
    intro h
    have hex {c : ℕ → α} {m : ℕ} (hm : ¬∀ k < m, s ≤ c k) : ∃ i, c i < s := by
      push Not at hm
      obtain ⟨k, -, hk⟩ := hm
      exact ⟨k, hk⟩
    have ha' : ∃ i, a i < s := hex fun hn ↦ h ⟨n + 1, 0, rfl, hn, by simp⟩
    have hb' : ∃ j, b j < s := hex fun hn ↦ h ⟨0, n + 1, Nat.zero_add _, by simp, hn⟩
    classical
    refine ⟨Nat.find ha', Nat.find hb', ?_, Nat.find_spec ha', Nat.find_spec hb'⟩
    by_contra! hn
    refine h ⟨min (Nat.find ha') (n + 1), n + 1 - min (Nat.find ha') (n + 1), by omega,
      fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · exact not_lt.mp (Nat.find_min ha' (by omega))
    · exact not_lt.mp (Nat.find_min hb' (by omega))
  · rintro ⟨i, j, hij, hai, hbj⟩ ⟨i', j', hij', hi, hj⟩
    rcases lt_or_ge i i' with h | h
    · exact (hi i h).not_gt hai
    · exact (hj j (by omega)).not_gt hbj

section LinearOrder

variable [ConditionallyCompleteLinearOrder α] {a b : ℕ → α} {n : ℕ} {r s : α}

/-- For antitone sequences, `r ≤ (a ⊔↓ b)ₙ` exactly when `r` bounds the first `i` terms of `a` and
the first `j` terms of `b` for some `i + j = n + 1`. In particular the supremum defining the merge
is attained. -/
theorem le_decreasingMerge_iff (ha : Antitone a) (hb : Antitone b) :
    r ≤ decreasingMerge a b n ↔ ∃ i j, i + j = n + 1 ∧ (∀ k < i, r ≤ a k) ∧ ∀ k < j, r ≤ b k := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- Otherwise `aᵢ < r` and `bⱼ < r` for some `i + j ≤ n`, and every attained threshold is at
    -- most `aᵢ` or at most `bⱼ`, so the merge is less than `r`.
    by_contra hsplit
    obtain ⟨i, j, hij, hai, hbj⟩ := not_exists_add_eq_forall_le_iff.mp hsplit
    refine (h.trans (decreasingMerge_le fun t q hq ht ↦ ?_)).not_gt (max_lt hai hbj)
    obtain ⟨i', j', hij', hi', hj'⟩ := (exists_injective_forall_le_sumElim_iff ha hb).mp ⟨q, hq, ht⟩
    rcases lt_or_ge i i' with h' | h'
    · exact (hi' i h').trans (le_max_left _ _)
    · exact (hj' j (by omega)).trans (le_max_right _ _)
  · have hbdd {c : ℕ → α} (hc : Antitone c) : BddAbove (Set.range c) :=
      ⟨c 0, Set.forall_mem_range.mpr fun k ↦ hc k.zero_le⟩
    obtain ⟨q, hq, hr⟩ := (exists_injective_forall_le_sumElim_iff ha hb).mpr h
    exact le_decreasingMerge (hbdd ha) (hbdd hb) hq hr

/-- For antitone sequences, the zeroth term of the merge is the larger of the zeroth terms. -/
@[simp]
theorem decreasingMerge_zero (ha : Antitone a) (hb : Antitone b) :
    decreasingMerge a b 0 = max (a 0) (b 0) := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · obtain ⟨i, j, hij, hi, hj⟩ := (le_decreasingMerge_iff ha hb).mp le_rfl
    rcases i with _ | i
    · exact (hj 0 (by omega)).trans (le_max_right _ _)
    · exact (hi 0 (by omega)).trans (le_max_left _ _)
  · exact (le_decreasingMerge_iff ha hb).mpr ⟨1, 0, rfl, fun k hk ↦ by rw [Nat.lt_one_iff.mp hk],
      fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  · exact (le_decreasingMerge_iff ha hb).mpr ⟨0, 1, rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _),
      fun k hk ↦ by rw [Nat.lt_one_iff.mp hk]⟩

/-- For antitone sequences, `(a ⊔↓ b)ₙ < s` exactly when `aᵢ < s` and `bⱼ < s` for some
`i + j ≤ n`. -/
theorem decreasingMerge_lt_iff (ha : Antitone a) (hb : Antitone b) :
    decreasingMerge a b n < s ↔ ∃ i j, i + j ≤ n ∧ a i < s ∧ b j < s := by
  rw [← not_le, le_decreasingMerge_iff ha hb, not_exists_add_eq_forall_le_iff]

end LinearOrder

end TauCeti
