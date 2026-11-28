/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice

/-!
# Online learners and mistake bounds

In online classification a learner sees labelled examples one at a time. In each round it
predicts the label of the next instance from the examples it has already seen, and then it sees
the true label. A class `H : Set (X → Bool)` of classifiers realizes a sequence of examples when
one of its members gives every example its label. The mistake bound of a learner on `H` is the
largest number of mistakes that it makes on a sequence that `H` realizes.

The learner is deterministic, so an adversary that adapts to its predictions produces nothing
that a fixed sequence does not; the mistake bound is a supremum over fixed finite sequences.

## Main definitions

* `TauCeti.Learner X`: a deterministic online learner, a function from the history of labelled
  examples and the next instance to a predicted label.
* `TauCeti.mistakes A s`: the number of rounds `i` of `s` at which the prediction of `A` from the
  first `i` examples differs from the label of example `i`.
* `TauCeti.IsRealizable H s`: some member of `H` gives every example of `s` its label.
* `TauCeti.mistakeBound A H`: the supremum in `ℕ∞` of `mistakes A s` over the sequences `s`
  that `H` realizes.

## Main results

* `TauCeti.mistakes_append_singleton`: one more round adds one mistake exactly when the
  prediction from the earlier examples is wrong.
* `TauCeti.mistakeBound_le_iff`: a bound on `mistakeBound A H` is a bound on the number of
  mistakes on each realizable sequence.
* `TauCeti.mistakeBound_empty`: on the empty class no sequence is realizable, and every learner
  has mistake bound `0`.

## References

* S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press (2014), Definition 21.1.
* M. Mohri, A. Rostamizadeh and A. Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
  MIT Press (2018), equations (8.2) and (8.3).
-/

public section

namespace TauCeti

variable {X : Type*}

/-- A deterministic online learner on the instance type `X`: from the history of labelled
examples and the next instance, a predicted label. In round `i` of a sequence `s` it predicts
`A (s.take i) s[i].1`. -/
abbrev Learner (X : Type*) := List (X × Bool) → X → Bool

/-- The number of mistakes of the learner `A` on the sequence `s`: the number of rounds `i` at
which the prediction from the first `i` examples differs from the label of example `i`. -/
def mistakes (A : Learner X) (s : List (X × Bool)) : ℕ :=
  ((List.finRange s.length).filter fun i : Fin s.length ↦
    decide (A (s.take i) s[i].1 ≠ s[i].2)).length

/-- A learner makes no mistake on the empty sequence. -/
@[simp]
theorem mistakes_nil (A : Learner X) : mistakes A [] = 0 := by
  simp [mistakes]

/-- One more round adds one mistake exactly when the prediction from the earlier examples is
wrong. -/
@[simp]
theorem mistakes_append_singleton (A : Learner X) (s : List (X × Bool)) (p : X × Bool) :
    mistakes A (s ++ [p]) = mistakes A s + if A s p.1 = p.2 then 0 else 1 := by
  -- Reindex the rounds of `s ++ [p]` by `Fin (s.length + 1)`, then split off the last round.
  have reindex : ∀ (m : ℕ) (hm : m = s.length + 1) (q : Fin m → Bool),
      ((List.finRange m).filter q).length =
        ((List.finRange (s.length + 1)).filter (q ∘ Fin.cast hm.symm)).length := by
    rintro m rfl q
    simp
  rw [mistakes, reindex _ (by simp), List.finRange_succ_last, List.filter_append,
    List.filter_map, List.length_append, List.length_map, mistakes]
  congr 1
  · congr 1
    refine List.filter_congr fun i _ ↦ ?_
    simp [List.take_append_of_le_length i.isLt.le, List.getElem_append_left]
  · by_cases h : A s p.1 = p.2 <;> simp [h]

/-- A sequence of labelled examples is realizable by the class `H` when one member of `H` gives
every example its label. -/
def IsRealizable (H : Set (X → Bool)) (s : List (X × Bool)) : Prop :=
  ∃ h ∈ H, ∀ p ∈ s, h p.1 = p.2

/-- The defining property of `IsRealizable`. -/
theorem isRealizable_iff {H : Set (X → Bool)} {s : List (X × Bool)} :
    IsRealizable H s ↔ ∃ h ∈ H, ∀ p ∈ s, h p.1 = p.2 :=
  Iff.rfl

/-- A sequence realizable by a class is realizable by every larger class. -/
theorem IsRealizable.mono {H H' : Set (X → Bool)} (hH : H ⊆ H') {s : List (X × Bool)}
    (hs : IsRealizable H s) : IsRealizable H' s :=
  let ⟨h, hh, hs⟩ := hs
  ⟨h, hH hh, hs⟩

/-- No sequence, not even the empty one, is realizable by the empty class. -/
@[simp]
theorem not_isRealizable_empty (s : List (X × Bool)) : ¬IsRealizable ∅ s := by
  simp [IsRealizable]

/-- The mistake bound of the learner `A` on the class `H`: the supremum in `ℕ∞` of its numbers
of mistakes over all finite sequences realizable by `H`. -/
noncomputable def mistakeBound (A : Learner X) (H : Set (X → Bool)) : ℕ∞ :=
  ⨆ (s : List (X × Bool)) (_ : IsRealizable H s), (mistakes A s : ℕ∞)

/-- On a realizable sequence a learner makes at most its mistake bound of mistakes. -/
theorem mistakes_le_mistakeBound (A : Learner X) {H : Set (X → Bool)} {s : List (X × Bool)}
    (hs : IsRealizable H s) : (mistakes A s : ℕ∞) ≤ mistakeBound A H :=
  le_iSup₂ (f := fun s (_ : IsRealizable H s) ↦ (mistakes A s : ℕ∞)) s hs

/-- A bound on `mistakeBound A H` is a bound on the number of mistakes of `A` on each sequence
realizable by `H`. -/
theorem mistakeBound_le_iff {A : Learner X} {H : Set (X → Bool)} {n : ℕ∞} :
    mistakeBound A H ≤ n ↔ ∀ s, IsRealizable H s → (mistakes A s : ℕ∞) ≤ n :=
  iSup₂_le_iff

/-- The mistake bound of a learner is monotone in the class. -/
theorem mistakeBound_mono (A : Learner X) {H H' : Set (X → Bool)} (hH : H ⊆ H') :
    mistakeBound A H ≤ mistakeBound A H' :=
  mistakeBound_le_iff.2 fun _ hs ↦ mistakes_le_mistakeBound A (hs.mono hH)

/-- On the empty class every learner has mistake bound `0`. -/
@[simp]
theorem mistakeBound_empty (A : Learner X) : mistakeBound A (∅ : Set (X → Bool)) = 0 :=
  nonpos_iff_eq_zero.1 <| mistakeBound_le_iff.2 fun s hs ↦ absurd hs (not_isRealizable_empty s)

end TauCeti
