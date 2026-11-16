/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SacksSplitting.Low
public import TauCeti.Computability.Join
import TauCeti.Computability.Split

/-!
# Consequences of Sacks splitting for c.e. degrees

Sacks's splitting theorem with low halves, combined with the reductions of a disjoint c.e.
splitting `B = A₀ ∪ A₁` (each half reduces to `B`, and `B` has the degree of `A₀ ⊕ A₁`), gives
the classical structural facts about c.e. degrees. Degrees are those of Mathlib's quotient
`TuringDegree`, represented by the oracles of sets.

* Splitting a noncomputable c.e. set `B` against itself gives two low c.e. degrees, strictly below
  the degree of `B` and incomparable with each other, whose supremum is the degree of `B`.
* Splitting a c.e. set against the halting set `(∅ : Set ℕ).jump` shows that every c.e. degree is
  the supremum of two low c.e. degrees.
* Hence no nonzero c.e. degree is minimal among c.e. degrees: a half of the splitting of `B`
  against itself has nonzero degree strictly below that of `B`.
* Splitting the halting set against a noncomputable c.e. set `B` gives two halves, neither of
  which computes `B`. If `B` is incomplete, the halves cannot both reduce to `B`, so at least one
  of them is incomparable with `B`. Which half has this property is not determined by the
  construction; the pair is exported with the disjunction, and the existence of an incomparable
  c.e. degree is derived from it.
* The halves of a splitting of the halting set are low, but their join has the degree of the
  halting set and is not low. So the jump of a join need not reduce to the join of the jumps.

## Main results

* `TauCeti.exists_split_low_incomparable`: a noncomputable c.e. set splits into two disjoint,
  Turing incomparable, low c.e. sets, each strictly Turing below it;
  `TauCeti.exists_low_incomparable_degrees_sup_eq`: so the degree of a noncomputable c.e. set is
  the supremum of two incomparable low c.e. degrees strictly below it.
* `TauCeti.exists_low_degrees_sup_eq`: every c.e. degree is the supremum of two low c.e. degrees.
* `TauCeti.exists_low_degree_mem_Ioo`: no nonzero c.e. degree is minimal.
* `TauCeti.exists_split_jump_empty_incomparable_half`,
  `TauCeti.exists_low_incomparable_degree`: every nonzero incomplete c.e. degree is incomparable
  with some low c.e. degree.
* `TauCeti.exists_low_join_not_low`, `TauCeti.not_forall_jump_join_turingReducible`: the halting
  set splits into two low c.e. sets whose join is not low, and the jump does not distribute over
  joins.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII, §3,
  the corollaries of the Sacks splitting theorem VII.3.2.
-/

public section

namespace TauCeti

open SacksSplitting

variable {B : Set ℕ}

/-- **Splitting a noncomputable c.e. set into incomparable low halves.** A noncomputable c.e. set
`B` is the disjoint union of two low c.e. sets `A₀` and `A₁`, each strictly Turing below `B` and
Turing incomparable with the other, whose join `A₀ ⊕ A₁` is Turing equivalent to `B`. -/
theorem exists_split_low_incomparable (hB : REPred (· ∈ B)) (hnc : ¬ComputablePred (· ∈ B)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = B ∧
      A₀.Low ∧ A₁.Low ∧
      TuringReducible A₀.oracle B.oracle ∧ ¬TuringReducible B.oracle A₀.oracle ∧
      TuringReducible A₁.oracle B.oracle ∧ ¬TuringReducible B.oracle A₁.oracle ∧
      ¬TuringReducible A₀.oracle A₁.oracle ∧ ¬TuringReducible A₁.oracle A₀.oracle ∧
      TuringEquivalent (A₀.join A₁).oracle B.oracle := by
  obtain ⟨A₀, A₁, h₀, h₁, hd, rfl, hl₀, hl₁, hn₀, hn₁⟩ :=
    exists_split_low_not_turingReducible hB hB hnc
  refine ⟨A₀, A₁, h₀, h₁, hd, rfl, hl₀, hl₁, hd.turingReducible_union_left h₀ h₁, hn₀,
    hd.turingReducible_union_right h₀ h₁, hn₁, ?_, ?_, (hd.turingEquivalent_union_join h₀ h₁).symm⟩
  · exact fun h => hn₁ <| Set.union_turingReducible h (.refl _)
  · exact fun h => hn₀ <| Set.union_turingReducible (.refl _) h

/-- **Splitting a noncomputable c.e. degree.** The degree of a noncomputable c.e. set `B` is the
supremum of two incomparable low c.e. degrees, each strictly below the degree of `B`. -/
theorem exists_low_incomparable_degrees_sup_eq (hB : REPred (· ∈ B))
    (hnc : ¬ComputablePred (· ∈ B)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ A₀.Low ∧ A₁.Low ∧
      toAntisymmetrization TuringReducible A₀.oracle <
        toAntisymmetrization TuringReducible B.oracle ∧
      toAntisymmetrization TuringReducible A₁.oracle <
        toAntisymmetrization TuringReducible B.oracle ∧
      ¬toAntisymmetrization TuringReducible A₀.oracle ≤
        toAntisymmetrization TuringReducible A₁.oracle ∧
      ¬toAntisymmetrization TuringReducible A₁.oracle ≤
        toAntisymmetrization TuringReducible A₀.oracle ∧
      toAntisymmetrization TuringReducible A₀.oracle ⊔
        toAntisymmetrization TuringReducible A₁.oracle =
          toAntisymmetrization TuringReducible B.oracle := by
  obtain ⟨A₀, A₁, h₀, h₁, hd, rfl, hl₀, hl₁, hr₀, hn₀, hr₁, hn₁, h₀₁, h₁₀, -⟩ :=
    exists_split_low_incomparable hB hnc
  refine ⟨A₀, A₁, h₀, h₁, hl₀, hl₁, ?_, ?_, mt turingDegree_le_iff.1 h₀₁,
    mt turingDegree_le_iff.1 h₁₀, (hd.degree_union_eq_sup h₀ h₁).symm⟩
  · rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
    exact ⟨hr₀, hn₀⟩
  · rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
    exact ⟨hr₁, hn₁⟩

/-- **Every c.e. degree is the supremum of two low c.e. degrees.** No noncomputability is assumed
of the c.e. set `B`; it is split against the halting set `(∅ : Set ℕ).jump`. -/
theorem exists_low_degrees_sup_eq (hB : REPred (· ∈ B)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ A₀.Low ∧ A₁.Low ∧
      toAntisymmetrization TuringReducible A₀.oracle ⊔
        toAntisymmetrization TuringReducible A₁.oracle =
          toAntisymmetrization TuringReducible B.oracle := by
  obtain ⟨A₀, A₁, h₀, h₁, hd, rfl, hl₀, hl₁, -, -⟩ :=
    exists_split_low_not_turingReducible hB Set.rePred_mem_jump_empty
      (Set.not_computablePred_mem_jump ∅)
  exact ⟨A₀, A₁, h₀, h₁, hl₀, hl₁, (hd.degree_union_eq_sup h₀ h₁).symm⟩

/-- **No nonzero c.e. degree is minimal.** Below the degree of a noncomputable c.e. set `B` lies
the degree of a low c.e. set, strictly between the computable degree and the degree of `B`. -/
theorem exists_low_degree_mem_Ioo (hB : REPred (· ∈ B)) (hnc : ¬ComputablePred (· ∈ B)) :
    ∃ A : Set ℕ, REPred (· ∈ A) ∧ A.Low ∧
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible B.oracle) := by
  obtain ⟨A₀, A₁, h₀, -, hl₀, -, hlt, -, hinc, -⟩ :=
    exists_low_incomparable_degrees_sup_eq hB hnc
  refine ⟨A₀, h₀, hl₀, ?_, hlt⟩
  rw [lt_iff_le_not_ge, turingDegree_le_iff, turingDegree_le_iff]
  -- a computable half would reduce to the other half
  exact ⟨Set.empty_turingReducible _,
    fun h => hinc (turingDegree_le_iff.2 (h.trans (Set.empty_turingReducible _)))⟩

/-- **Splitting the halting set against an incomplete c.e. set.** For a noncomputable c.e. set
`B`, the halting set `(∅ : Set ℕ).jump` is the disjoint union of two low c.e. sets, neither of
which computes `B`. If `B` does not compute the halting set, at least one of the two halves is not
computable from `B`, and so is incomparable with `B`. Which half this is is not specified. -/
theorem exists_split_jump_empty_incomparable_half (hB : REPred (· ∈ B))
    (hnc : ¬ComputablePred (· ∈ B)) (hK : ¬TuringReducible (∅ : Set ℕ).jump.oracle B.oracle) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ Disjoint A₀ A₁ ∧
      A₀ ∪ A₁ = (∅ : Set ℕ).jump ∧ A₀.Low ∧ A₁.Low ∧
      ¬TuringReducible B.oracle A₀.oracle ∧ ¬TuringReducible B.oracle A₁.oracle ∧
      (¬TuringReducible A₀.oracle B.oracle ∨ ¬TuringReducible A₁.oracle B.oracle) := by
  obtain ⟨A₀, A₁, h₀, h₁, hd, hU, hl₀, hl₁, hn₀, hn₁⟩ :=
    exists_split_low_not_turingReducible Set.rePred_mem_jump_empty hB hnc
  refine ⟨A₀, A₁, h₀, h₁, hd, hU, hl₀, hl₁, hn₀, hn₁, not_and_or.1 fun h => hK ?_⟩
  rw [← hU]
  exact Set.union_turingReducible h.1 h.2

/-- **Incomparable c.e. degrees.** Every nonzero incomplete c.e. degree is incomparable with some
low c.e. degree. -/
theorem exists_low_incomparable_degree (hB : REPred (· ∈ B)) (hnc : ¬ComputablePred (· ∈ B))
    (hK : ¬TuringReducible (∅ : Set ℕ).jump.oracle B.oracle) :
    ∃ A : Set ℕ, REPred (· ∈ A) ∧ A.Low ∧
      ¬toAntisymmetrization TuringReducible A.oracle ≤
        toAntisymmetrization TuringReducible B.oracle ∧
      ¬toAntisymmetrization TuringReducible B.oracle ≤
        toAntisymmetrization TuringReducible A.oracle := by
  obtain ⟨A₀, A₁, h₀, h₁, -, -, hl₀, hl₁, hn₀, hn₁, h | h⟩ :=
    exists_split_jump_empty_incomparable_half hB hnc hK
  · exact ⟨A₀, h₀, hl₀, mt turingDegree_le_iff.1 h, mt turingDegree_le_iff.1 hn₀⟩
  · exact ⟨A₁, h₁, hl₁, mt turingDegree_le_iff.1 h, mt turingDegree_le_iff.1 hn₁⟩

/-- **The join of two low c.e. sets need not be low.** The halting set `(∅ : Set ℕ).jump` is the
disjoint union of two low c.e. sets whose join has the degree of the halting set, and so is not
low. -/
theorem exists_low_join_not_low :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ Disjoint A₀ A₁ ∧
      A₀ ∪ A₁ = (∅ : Set ℕ).jump ∧ A₀.Low ∧ A₁.Low ∧ ¬(A₀.join A₁).Low := by
  have hK := Set.rePred_mem_jump_empty
  obtain ⟨A₀, A₁, h₀, h₁, hd, hU, hl₀, hl₁, -, -⟩ :=
    exists_split_low_not_turingReducible hK hK (Set.not_computablePred_mem_jump ∅)
  refine ⟨A₀, A₁, h₀, h₁, hd, hU, hl₀, hl₁, ?_⟩
  rw [← Set.low_congr (hd.turingEquivalent_union_join h₀ h₁), hU]
  exact Set.not_low_jump ∅

/-- **The jump does not distribute over joins.** The jump of `A₀ ⊕ A₁` is not in general Turing
reducible to `A₀' ⊕ A₁'`: for the low halves of a splitting of the halting set, the latter
reduces to `(∅ : Set ℕ).jump` while the former does not. -/
theorem not_forall_jump_join_turingReducible :
    ¬∀ A₀ A₁ : Set ℕ,
      TuringReducible (A₀.join A₁).jump.oracle (A₀.jump.join A₁.jump).oracle := by
  intro h
  obtain ⟨A₀, A₁, -, -, -, -, hl₀, hl₁, hn⟩ := exists_low_join_not_low
  exact hn <| Set.low_iff_jump_turingReducible.2 <|
    (h A₀ A₁).trans (Set.join_turingReducible (Set.low_iff_jump_turingReducible.1 hl₀)
      (Set.low_iff_jump_turingReducible.1 hl₁))

end TauCeti
