/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.Data.Set.Card

/-!
# Degrees of vertices of Serre graphs

The degree of a vertex of a Serre graph is the number of darts issuing from it, as an extended
natural number, so that vertices of infinite degree are allowed. A loop at a vertex contributes
both of its darts and so counts twice, and parallel edges count separately: the rose with petals
indexed by `α` has a vertex of degree `2 * ENat.card α`, while each end of the segment has
degree one.

The degree is characterized by the number of darts issuing from the vertex: it vanishes exactly
when there is none, is one exactly when there is a unique one, and is at least two (or three)
exactly when there are two (or three) distinct ones.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, Section 2,
  Convention 2.2 and the remark after Definition 2.3, where the degree of a vertex counts the
  edges of the doubled graph with that origin.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph)

/-- The degree of a vertex: the number of darts issuing from it. A loop at the vertex contributes
both of its darts. -/
noncomputable def degree (a : Γ.V) : ℕ∞ :=
  {e | Γ.src e = a}.encard

theorem degree_def (a : Γ.V) : Γ.degree a = {e | Γ.src e = a}.encard := (rfl)

variable {Γ} {a : Γ.V}

/-- A vertex has degree zero exactly when no dart issues from it. -/
@[simp] theorem degree_eq_zero_iff : Γ.degree a = 0 ↔ ∀ e, Γ.src e ≠ a := by
  simp [degree, Set.eq_empty_iff_forall_notMem]

/-- A vertex has degree one exactly when a unique dart issues from it. -/
theorem degree_eq_one_iff : Γ.degree a = 1 ↔ ∃ e, Γ.src e = a ∧ ∀ f, Γ.src f = a → f = e := by
  simp [degree, Set.encard_eq_one, Set.eq_singleton_iff_unique_mem]

/-- A vertex has degree at most one exactly when at most one dart issues from it. -/
theorem degree_le_one_iff :
    Γ.degree a ≤ 1 ↔ ∀ e f, Γ.src e = a → Γ.src f = a → e = f := by
  simp [degree, Set.encard_le_one_iff]

/-- A vertex has degree at least two exactly when two distinct darts issue from it. -/
theorem two_le_degree_iff :
    2 ≤ Γ.degree a ↔ ∃ e f, Γ.src e = a ∧ Γ.src f = a ∧ e ≠ f := by
  rw [degree, ← one_add_one_eq_two, ENat.add_one_le_iff ENat.one_ne_top, Set.one_lt_encard_iff]
  rfl

/-- A vertex has degree at least three exactly when three distinct darts issue from it. -/
theorem three_le_degree_iff :
    3 ≤ Γ.degree a ↔ ∃ e f g, Γ.src e = a ∧ Γ.src f = a ∧ Γ.src g = a ∧
      e ≠ f ∧ e ≠ g ∧ f ≠ g := by
  constructor
  · intro h
    obtain ⟨t, ht, h⟩ := Set.exists_subset_encard_eq h
    obtain ⟨e, f, g, hef, heg, hfg, rfl⟩ := Set.encard_eq_three.mp h
    exact ⟨e, f, g, ht (by simp), ht (by simp), ht (by simp), hef, heg, hfg⟩
  · rintro ⟨e, f, g, he, hf, hg, hef, heg, hfg⟩
    exact (Set.encard_eq_three.mpr ⟨e, f, g, hef, heg, hfg, rfl⟩).symm.le.trans
      (Set.encard_le_encard (by simp [Set.insert_subset_iff, he, hf, hg]))

/-- The vertex of the rose has degree twice the number of petals: each petal is a loop. -/
@[simp] theorem degree_rose (α : Type*) (a : (rose α).V) : (rose α).degree a = 2 * ENat.card α := by
  have h : {e | (rose α).src e = a} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  rw [degree, h, Set.encard_univ]
  simp [rose, ENat.card_prod, mul_comm]

/-- Each end of the segment has degree one. -/
@[simp] theorem degree_segment (b : segment.V) : segment.degree b = 1 :=
  degree_eq_one_iff.mpr ⟨b, rfl, fun _ hf => hf⟩

end TauCeti.SerreGraph
