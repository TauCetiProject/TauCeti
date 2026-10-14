/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Finset.Sum
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Monotone

/-!
# The generalized decreasing merge of two sequences

For bounded sequences `a b : ℕ → ℝ≥0`, the generalized decreasing merge
`TauCeti.decreasingMerge a b` is the sequence of generalized decreasing order statistics of the
multiset union of the entries of `a` and `b`: its `n`-th term is the supremum of the thresholds
`r` attained by at least `n + 1` distinct entries, that is, the supremum of those `r` for which
some injective `q : Fin (n + 1) → ℕ ⊕ ℕ` has `r ≤ Sum.elim a b (q i)` for every `i`. In the
documentation below this term is written `(a ⊔↓ b)ₙ`.

This is the operation that computes the approximation numbers of an orthogonal block sum from
those of its blocks. It is not required to enumerate every entry of the union: if `a` is constant
with value `1` and `b` is constant with value `0`, then the merge is constant with value `1`,
and the entries of `b` never appear. This is the right behaviour for noncompact blocks, whose
approximation numbers can have an infinite plateau.

For antitone sequences the threshold condition only involves initial segments, so the merge is
computed by splitting `n + 1 = i + j` between the two sequences:

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

open scoped NNReal

namespace TauCeti

/-- The **generalized decreasing merge** of two sequences `a b : ℕ → ℝ≥0`: its `n`-th term is the
supremum of the thresholds `r` attained by at least `n + 1` distinct entries of the multiset union
of `a` and `b`, that is, by `Sum.elim a b` at `n + 1` distinct indices of `ℕ ⊕ ℕ`.

It is meaningful for bounded sequences; for antitone sequences it is computed by
`TauCeti.le_decreasingMerge_iff` and `TauCeti.decreasingMerge_lt_iff`. -/
noncomputable def decreasingMerge (a b : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 :=
  sSup {r | ∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)}

variable {a b : ℕ → ℝ≥0} {n : ℕ} {r s : ℝ≥0}

/-- Unfolding `TauCeti.decreasingMerge`. -/
theorem decreasingMerge_def (a b : ℕ → ℝ≥0) (n : ℕ) :
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
  refine le_csSup ⟨max A B, ?_⟩ ⟨q, hq, hr⟩
  rintro t ⟨q', -, ht⟩
  refine (ht 0).trans ?_
  rcases q' 0 with k | k
  · exact (hA ⟨k, rfl⟩).trans (le_max_left _ _)
  · exact (hB ⟨k, rfl⟩).trans (le_max_right _ _)

/-- The `n`-th term of the merge is at most every common upper bound of the thresholds attained
by `n + 1` distinct entries. -/
theorem decreasingMerge_le {c : ℝ≥0}
    (h : ∀ r (q : Fin (n + 1) → ℕ ⊕ ℕ), Function.Injective q →
      (∀ i, r ≤ Sum.elim a b (q i)) → r ≤ c) :
    decreasingMerge a b n ≤ c := by
  refine csSup_le ⟨0, Sum.inl ∘ Fin.val, Sum.inl_injective.comp Fin.val_injective,
    fun _ ↦ zero_le⟩ ?_
  rintro r ⟨q, hq, hr⟩
  exact h r q hq hr

/-- The merge is symmetric in its two arguments. -/
theorem decreasingMerge_comm (a b : ℕ → ℝ≥0) : decreasingMerge a b = decreasingMerge b a := by
  have key {a b : ℕ → ℝ≥0} {n : ℕ} {r : ℝ≥0} :
      (∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)) →
        ∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim b a (q i) :=
    fun ⟨q, hq, hr⟩ ↦ ⟨Sum.swap ∘ q, Sum.swap_leftInverse.injective.comp hq, fun i ↦
      (hr i).trans_eq (congrFun Sum.elim_swap (q i)).symm⟩
  ext1 n
  rw [decreasingMerge_def, decreasingMerge_def]
  exact congrArg sSup (Set.ext fun r ↦ ⟨key, key⟩)

/-- The merge of two bounded sequences is antitone. -/
theorem antitone_decreasingMerge (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b)) :
    Antitone (decreasingMerge a b) :=
  antitone_nat_of_succ_le fun _ ↦ decreasingMerge_le fun _ _ hq hr ↦
    le_decreasingMerge ha hb (hq.comp (Fin.castSucc_injective _)) fun i ↦ hr i.castSucc

/-- For antitone sequences, a threshold is attained by `n + 1` distinct entries exactly when it
bounds the first `i` terms of `a` and the first `j` terms of `b` for some `i + j = n + 1`. -/
private theorem exists_injective_iff (ha : Antitone a) (hb : Antitone b) :
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
    refine ⟨u.toLeft.card, u.toRight.card, Finset.card_toLeft_add_card_toRight.trans hu,
      fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · obtain ⟨m, hm, hkm⟩ : ∃ m ∈ u.toLeft, k ≤ m := by
        by_contra! h
        exact hk.not_ge ((Finset.card_le_card fun m hm ↦ Finset.mem_range.mpr (h m hm)).trans
          (Finset.card_range k).le)
      exact (hmem _ (Finset.mem_toLeft.mp hm)).trans (ha hkm)
    · obtain ⟨m, hm, hkm⟩ : ∃ m ∈ u.toRight, k ≤ m := by
        by_contra! h
        exact hk.not_ge ((Finset.card_le_card fun m hm ↦ Finset.mem_range.mpr (h m hm)).trans
          (Finset.card_range k).le)
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

/-- For antitone sequences, `r ≤ (a ⊔↓ b)ₙ` exactly when `r` bounds the first `i` terms of `a` and
the first `j` terms of `b` for some `i + j = n + 1`. In particular the supremum defining the merge
is attained. -/
theorem le_decreasingMerge_iff (ha : Antitone a) (hb : Antitone b) :
    r ≤ decreasingMerge a b n ↔ ∃ i j, i + j = n + 1 ∧ (∀ k < i, r ≤ a k) ∧ ∀ k < j, r ≤ b k := by
  have hbdd {c : ℕ → ℝ≥0} (hc : Antitone c) : BddAbove (Set.range c) :=
    ⟨c 0, by rintro _ ⟨k, rfl⟩; exact hc (Nat.zero_le k)⟩
  refine ⟨fun h ↦ ?_, fun ⟨i, j, hij, hi, hj⟩ ↦ ?_⟩
  · -- The set of attained thresholds is a finite union of closed sets, so it contains its
    -- supremum.
    set S := {r | ∃ q : Fin (n + 1) → ℕ ⊕ ℕ, Function.Injective q ∧ ∀ i, r ≤ Sum.elim a b (q i)}
    have hS : S = ⋃ i ∈ Finset.range (n + 2),
        (⋂ k ∈ Set.Iio i, Set.Iic (a k)) ∩ ⋂ k ∈ Set.Iio (n + 1 - i), Set.Iic (b k) := by
      ext t
      simp only [S, Set.mem_ofPred_eq, exists_injective_iff ha hb, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_Iio, Set.mem_Iic, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        exact ⟨i, by omega, hi, fun k hk ↦ hj k (by omega)⟩
      · rintro ⟨i, hi, hia, hib⟩
        exact ⟨i, n + 1 - i, by omega, hia, hib⟩
    have hclosed : IsClosed S := by
      rw [hS]
      exact (Finset.range (n + 2)).finite_toSet.isClosed_biUnion fun i _ ↦
        (isClosed_biInter fun k _ ↦ isClosed_Iic).inter (isClosed_biInter fun k _ ↦ isClosed_Iic)
    have hne : S.Nonempty := ⟨0, Sum.inl ∘ Fin.val, Sum.inl_injective.comp Fin.val_injective,
      fun _ ↦ zero_le⟩
    have hmem := hclosed.csSup_mem hne ⟨_, fun t ⟨_, hq, ht⟩ ↦ le_decreasingMerge (hbdd ha)
      (hbdd hb) hq ht⟩
    obtain ⟨i, j, hij, hi, hj⟩ := (exists_injective_iff ha hb).mp hmem
    exact ⟨i, j, hij, fun k hk ↦ h.trans (hi k hk), fun k hk ↦ h.trans (hj k hk)⟩
  · obtain ⟨q, hq, hr⟩ := (exists_injective_iff ha hb).mpr ⟨i, j, hij, hi, hj⟩
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
  rw [← not_le, le_decreasingMerge_iff ha hb]
  constructor
  · -- Take `i` and `j` least with `aᵢ < s` and `bⱼ < s`; they exist and `i + j ≤ n`, since
    -- otherwise `s` would bound enough initial terms of `a` and `b`.
    intro h
    have hex {c : ℕ → ℝ≥0} {m : ℕ} (hm : ¬∀ k < m, s ≤ c k) : ∃ i, c i < s := by
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

end TauCeti
