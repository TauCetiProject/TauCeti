/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Bounds below the first uncountable ordinal

`TauCeti.BoundedRankOn ρ K` means that the ordinal-valued map `ρ` is strictly bounded below `ω₁`
on `K`. Its negation is `TauCeti.UnboundedRankOn ρ K`. No invariance or isolation property of
`ρ` is imposed. Boundedness is closed under subsets and countable unions, by regularity of `ω₁`.
It therefore supplies a smallness predicate for selecting large back-and-forth classes.
-/

public section

universe o

open Ordinal Set

namespace TauCeti

variable {X : Type*} {ρ : X → Ordinal.{o}} {A B : Set X}

/-- The values of `ρ` on `K` have a strict bound below the first uncountable ordinal. -/
def BoundedRankOn (ρ : X → Ordinal.{o}) (K : Set X) : Prop :=
  ∃ β < ω₁, ∀ x ∈ K, ρ x < β

/-- The values of `ρ` on `K` have no strict bound below the first uncountable ordinal. -/
def UnboundedRankOn (ρ : X → Ordinal.{o}) (K : Set X) : Prop :=
  ¬ BoundedRankOn ρ K

/-- The defining bound for rank boundedness. -/
theorem boundedRankOn_iff : BoundedRankOn ρ A ↔ ∃ β < ω₁, ∀ x ∈ A, ρ x < β := Iff.rfl

/-- Unboundedness is the negation of boundedness below `ω₁`. -/
theorem unboundedRankOn_iff_not_boundedRankOn : UnboundedRankOn ρ A ↔ ¬ BoundedRankOn ρ A :=
  Iff.rfl

/-- Every countable threshold is attained or exceeded on a rank-unbounded set. -/
theorem unboundedRankOn_iff : UnboundedRankOn ρ A ↔
    ∀ β < ω₁, ∃ x ∈ A, β ≤ ρ x := by
  simp [unboundedRankOn_iff_not_boundedRankOn, boundedRankOn_iff]

/-- A bound on a set restricts to every subset. -/
theorem BoundedRankOn.mono (hB : BoundedRankOn ρ B) (hAB : A ⊆ B) : BoundedRankOn ρ A := by
  obtain ⟨β, hβ, hbound⟩ := hB
  exact ⟨β, hβ, fun x hx => hbound x (hAB hx)⟩

/-- A superset of a rank-unbounded set is rank-unbounded. -/
theorem UnboundedRankOn.mono (hA : UnboundedRankOn ρ A) (hAB : A ⊆ B) : UnboundedRankOn ρ B :=
  fun hB => hA (hB.mono hAB)

/-- Every rank is bounded on the empty set. -/
@[simp]
theorem boundedRankOn_empty (ρ : X → Ordinal.{o}) : BoundedRankOn ρ ∅ :=
  ⟨0, omega_pos 1, by simp⟩

/-- No rank is unbounded on the empty set. -/
@[simp]
theorem not_unboundedRankOn_empty (ρ : X → Ordinal.{o}) : ¬ UnboundedRankOn ρ ∅ :=
  fun h => h (boundedRankOn_empty ρ)

/-- A rank is bounded on a countable union exactly when it is bounded on each member. -/
@[simp]
theorem boundedRankOn_sUnion_iff {S : Set (Set X)} (hS : S.Countable) :
    BoundedRankOn ρ (⋃₀ S) ↔ ∀ A ∈ S, BoundedRankOn ρ A := by
  constructor
  · exact fun h A hA => h.mono (subset_sUnion_of_mem hA)
  · intro h
    classical
    have := hS.to_subtype
    choose β hβ hbound using fun A : S => h A.val A.prop
    refine ⟨⨆ A : S, β A, iSup_lt_omega_one hβ, ?_⟩
    rintro x ⟨A, hA, hx⟩
    exact (hbound ⟨A, hA⟩ x hx).trans_le (Ordinal.le_iSup β ⟨A, hA⟩)

/-- A countable union is rank-unbounded exactly when one of its members is rank-unbounded. -/
@[simp]
theorem unboundedRankOn_sUnion_iff {S : Set (Set X)} (hS : S.Countable) :
    UnboundedRankOn ρ (⋃₀ S) ↔ ∃ A ∈ S, UnboundedRankOn ρ A := by
  simp only [unboundedRankOn_iff_not_boundedRankOn, boundedRankOn_sUnion_iff hS,
    not_forall, exists_prop]

end TauCeti
