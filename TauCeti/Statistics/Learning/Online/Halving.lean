/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.Card
public import TauCeti.Statistics.Learning.Online.MistakeBound

/-!
# The halving bound

The version space of a class `H : Set (X → Bool)` after a sequence `s` of labelled examples is
the set of the members of `H` that give every example of `s` its label. The halving learner
predicts the majority vote of the version space, counted with `Set.ncard`, with ties broken
towards `true`. At each mistake the members that voted for the wrong label leave the version
space, and they are at least half of it. So on a finite class, after `M` mistakes the version
space has at most `|H| / 2 ^ M` members. On a realizable sequence it is never empty, and the
learner makes at most `⌊log₂ |H|⌋` mistakes.

## Main definitions

* `TauCeti.versionSpace H s`: the members of `H` consistent with every example of `s`.
* `TauCeti.halvingLearner H`: the majority vote of the version space, ties to `true`.

## Main results

* `TauCeti.two_mul_ncard_versionSpace_append_singleton_le`: a mistake of the halving learner at
  least halves a finite version space.
* `TauCeti.two_pow_mistakes_mul_ncard_versionSpace_le`: on a finite class,
  `2 ^ M * |versionSpace H s| ≤ |H|`, where `M` is the number of mistakes of the halving learner
  on `s`.
* `TauCeti.mistakeBound_halvingLearner_le`: the halving bound, `mistakeBound (halvingLearner H) H
  ≤ ⌊log₂ |H|⌋` for a finite class `H`.

The finiteness of `H` is necessary: `Set.ncard` is `0` on an infinite set, so the right-hand side
is then `0`, while the halving learner on the thresholds `x ↦ decide (x < a)` on `ℕ` predicts
`true` in round `0` and errs on the realizable sequence `[(0, false)]`.

## References

* S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press (2014), Theorem 21.3.
* M. Mohri, A. Rostamizadeh and A. Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
  MIT Press (2018), Theorem 8.1.
-/

public section

namespace TauCeti

variable {X : Type*}

/-- The version space of the class `H` after the sequence `s`: the members of `H` that give
every example of `s` its label. -/
def versionSpace (H : Set (X → Bool)) (s : List (X × Bool)) : Set (X → Bool) :=
  {h ∈ H | ∀ p ∈ s, h p.1 = p.2}

/-- The defining property of `versionSpace`. -/
@[simp]
theorem mem_versionSpace {H : Set (X → Bool)} {s : List (X × Bool)} {h : X → Bool} :
    h ∈ versionSpace H s ↔ h ∈ H ∧ ∀ p ∈ s, h p.1 = p.2 :=
  Iff.rfl

/-- The version space is a subset of the class. -/
theorem versionSpace_subset (H : Set (X → Bool)) (s : List (X × Bool)) :
    versionSpace H s ⊆ H :=
  fun _ hh ↦ hh.1

/-- Before any example, the version space is the whole class. -/
@[simp]
theorem versionSpace_nil (H : Set (X → Bool)) : versionSpace H [] = H := by
  simp [versionSpace]

/-- More examples give a smaller version space. -/
theorem versionSpace_append_subset (H : Set (X → Bool)) (s t : List (X × Bool)) :
    versionSpace H (s ++ t) ⊆ versionSpace H s :=
  fun _ hh ↦ ⟨hh.1, fun p hp ↦ hh.2 p (List.mem_append_left t hp)⟩

/-- One more example `(x, y)` keeps the members of the version space that are `y` at `x`. -/
theorem versionSpace_append_singleton (H : Set (X → Bool)) (s : List (X × Bool)) (x : X)
    (y : Bool) : versionSpace H (s ++ [(x, y)]) = {h ∈ versionSpace H s | h x = y} := by
  ext h
  simp only [Set.mem_ofPred_eq, mem_versionSpace, List.forall_mem_append,
    List.forall_mem_singleton]
  exact and_assoc.symm

/-- A sequence is realizable by `H` exactly when its version space is nonempty. -/
theorem isRealizable_iff_versionSpace_nonempty {H : Set (X → Bool)} {s : List (X × Bool)} :
    IsRealizable H s ↔ (versionSpace H s).Nonempty :=
  isRealizable_iff

/-- The halving learner of the class `H`: it predicts `true` at `x` exactly when at least half of
the version space, counted with `Set.ncard`, is `true` at `x`. Ties go to `true`. -/
noncomputable def halvingLearner (H : Set (X → Bool)) : Learner X := fun s x ↦
  decide ((versionSpace H s).ncard ≤ 2 * {h ∈ versionSpace H s | h x = true}.ncard)

/-- The halving learner predicts `true` at `x` exactly when at least half of the version space
is `true` at `x`. -/
theorem halvingLearner_eq_true_iff {H : Set (X → Bool)} {s : List (X × Bool)} {x : X} :
    halvingLearner H s x = true ↔
      (versionSpace H s).ncard ≤ 2 * {h ∈ versionSpace H s | h x = true}.ncard := by
  simp [halvingLearner]

/-- A mistake of the halving learner at least halves a finite version space. -/
theorem two_mul_ncard_versionSpace_append_singleton_le {H : Set (X → Bool)}
    {s : List (X × Bool)} {x : X} {y : Bool} (hs : (versionSpace H s).Finite)
    (hy : halvingLearner H s x ≠ y) :
    2 * (versionSpace H (s ++ [(x, y)])).ncard ≤ (versionSpace H s).ncard := by
  rw [versionSpace_append_singleton]
  have hsplit : {h ∈ versionSpace H s | h x = true}.ncard +
      {h ∈ versionSpace H s | h x = false}.ncard = (versionSpace H s).ncard := by
    rw [← Set.ncard_union_eq _ (hs.subset (Set.sep_subset _ _))
      (hs.subset (Set.sep_subset _ _))]
    · congr 1
      ext h
      cases hx : h x <;> simp [hx]
    · exact Set.disjoint_left.2 fun h h₁ h₂ ↦ by simp_all
  cases y with
  | false =>
    rw [ne_eq, Bool.not_eq_false, halvingLearner_eq_true_iff] at hy
    omega
  | true =>
    rw [ne_eq, halvingLearner_eq_true_iff] at hy
    omega

/-- On a finite class, after `M` mistakes of the halving learner on `s`, the version space has
at most `|H| / 2 ^ M` members: `2 ^ M * |versionSpace H s| ≤ |H|`. -/
theorem two_pow_mistakes_mul_ncard_versionSpace_le (H : Set (X → Bool)) (hH : H.Finite)
    (s : List (X × Bool)) :
    2 ^ mistakes (halvingLearner H) s * (versionSpace H s).ncard ≤ H.ncard := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s p ih =>
    obtain ⟨x, y⟩ := p
    have hs : (versionSpace H s).Finite := hH.subset (versionSpace_subset H s)
    rw [mistakes_append_singleton]
    by_cases hp : halvingLearner H s x = y
    · simp only [hp, ↓reduceIte, add_zero]
      exact (Nat.mul_le_mul_left _ (Set.ncard_le_ncard (versionSpace_append_subset H s _)
        hs)).trans ih
    · simp only [hp, ↓reduceIte, pow_succ, mul_assoc]
      exact (Nat.mul_le_mul_left _
        (two_mul_ncard_versionSpace_append_singleton_le hs hp)).trans ih

/-- **The halving bound.** On a finite class `H`, the halving learner makes at most
`⌊log₂ |H|⌋` mistakes on every sequence realizable by `H`. -/
theorem mistakeBound_halvingLearner_le (H : Set (X → Bool)) (hH : H.Finite) :
    mistakeBound (halvingLearner H) H ≤ (Nat.log 2 H.ncard : ℕ∞) := by
  refine mistakeBound_le_iff.2 fun s hs ↦ ?_
  have hV : 0 < (versionSpace H s).ncard :=
    (Set.ncard_pos (hH.subset (versionSpace_subset H s))).2
      (isRealizable_iff_versionSpace_nonempty.1 hs)
  exact_mod_cast Nat.le_log_of_pow_le one_lt_two
    ((Nat.le_mul_of_pos_right _ hV).trans (two_pow_mistakes_mul_ncard_versionSpace_le H hH s))

end TauCeti
