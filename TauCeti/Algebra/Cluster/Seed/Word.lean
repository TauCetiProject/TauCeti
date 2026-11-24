/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.Seed.Exchange
public import Mathlib.Logic.Relation

/-!
# Certified mutation words for realized seeds

A finite word of realized seed mutations is certified by its successive one-step relations.
The certificates compose by concatenation and reverse along the reversed word. Deleting a
consecutive pair of equal directions preserves the endpoint, and inserting such a pair
requires the first exchange to be defined. Erasing the labels gives precisely the reflexive
transitive closure of one-step exchange.

The word relation uses the common seed type in an arbitrary ambient semiring. It retains
partiality, the chosen compatibility weights, and functoriality under the existing ambient
and coefficient maps.
-/

public section

namespace TauCeti.Seed

variable {𝕂 R I K B : Type*} [CommMonoidWithZero 𝕂] [CommSemiring R] [Fintype I]
  [DecidableEq I] [DecidableEq K] [Semiring B] [Algebra R B]
  {c : CoefficientSystem 𝕂 R} {row : K ↪ I} {u : Rˣ}

/-- A path of realized seed mutations with the specified list of directions. -/
inductive IsMutationWord : List K → Seed c row u B → Seed c row u B → Prop where
  /-- The empty word leaves the seed fixed. -/
  | nil (s) : IsMutationWord [] s s
  /-- A first realized exchange followed by a certified word. -/
  | cons {k w s t v} : s.IsMutation k t → IsMutationWord w t v → IsMutationWord (k :: w) s v

variable {s t v : Seed c row u B} {w w' : List K} {k : K}

/-- Certified concatenation splits at an intermediate seed. -/
theorem isMutationWord_append_iff :
    IsMutationWord (w ++ w') s v ↔
      ∃ t, IsMutationWord w s t ∧ IsMutationWord w' t v := by
  induction w generalizing s with
  | nil =>
    simp only [List.nil_append]
    constructor
    · exact fun h ↦ ⟨s, .nil s, h⟩
    · rintro ⟨_, h, h'⟩
      cases h
      exact h'
  | cons k w ih =>
    constructor
    · intro h
      cases h with
      | cons hst htail =>
        obtain ⟨m, hw, hw'⟩ := ih.mp htail
        exact ⟨m, .cons hst hw, hw'⟩
    · rintro ⟨m, h, h'⟩
      cases h with
      | cons hst htail => exact .cons hst (ih.mpr ⟨m, htail, h'⟩)

/-- Compose two certified mutation words by concatenation. -/
theorem IsMutationWord.append (h : IsMutationWord w s t) (h' : IsMutationWord w' t v) :
    IsMutationWord (w ++ w') s v :=
  isMutationWord_append_iff.mpr ⟨t, h, h'⟩

/-- A certified word has a unique endpoint for a fixed initial seed. -/
theorem IsMutationWord.eq (h : IsMutationWord w s t) (h' : IsMutationWord w s v) :
    t = v := by
  induction h generalizing v with
  | nil =>
    cases h'
    rfl
  | cons hstep _ ih =>
    cases h' with
    | cons hstep' htail' =>
      cases hstep.eq hstep'
      exact ih htail'

/-- A certified path reverses along the reversed list of directions. -/
theorem IsMutationWord.reverse (h : IsMutationWord w s t) : IsMutationWord w.reverse t s := by
  induction h with
  | nil s => exact .nil s
  | cons hstep _ ih =>
    simpa only [List.reverse_cons] using ih.append (.cons hstep.symm (.nil _))

/-- An initial consecutive pair of equal directions can be deleted. Inserting it requires
that the first exchange element be a unit. -/
theorem isMutationWord_cons_cons_iff :
    IsMutationWord (k :: k :: w) s t ↔
      IsMutationWord w s t ∧ IsUnit (s.exchangeElement k) := by
  constructor
  · intro h
    cases h with
    | cons h₁ h =>
      cases h with
      | cons h₂ h =>
        rw [h₂.eq h₁.symm] at h
        exact ⟨h, h₁.isUnit_exchangeElement⟩
  · rintro ⟨h, hu⟩
    let h₁ := s.isMutation_mutation k hu
    exact .cons h₁ (.cons h₁.symm h)

/-- A certified word preserves the compatibility weights. -/
theorem IsMutationWord.weights_eq (h : IsMutationWord w s t) : t.weights = s.weights := by
  induction h with
  | nil => rfl
  | cons hstep _ ih => exact ih.trans hstep.weights_eq

/-- An injective ambient algebra map transports the whole certified word. -/
theorem IsMutationWord.map {D : Type*} [Semiring D] [Algebra R D]
    (h : IsMutationWord w s t) (f : B →ₐ[R] D) (hf : Function.Injective f) :
    IsMutationWord w (s.map f hf) (t.map f hf) := by
  induction h with
  | nil => exact .nil _
  | cons hstep _ ih => exact .cons (hstep.map f hf) ih

/-- A morphism of coefficient systems transports the whole certified word. -/
theorem IsMutationWord.mapCoefficients {𝕂' : Type*} [CommMonoidWithZero 𝕂']
    {c' : CoefficientSystem 𝕂' R} (h : IsMutationWord w s t) (f : c.Hom c') :
    IsMutationWord w (s.mapCoefficients f) (t.mapCoefficients f) := by
  induction h with
  | nil => exact .nil _
  | cons hstep _ ih => exact .cons (hstep.mapCoefficients f) ih

/-- One unlabelled edge of the realized mutation graph. -/
def Step (s t : Seed c row u B) : Prop := ∃ k, s.IsMutation k t

/-- An unlabelled edge is realized by a one-step mutation in some direction. -/
@[simp]
theorem step_iff : Step s t ↔ ∃ k, s.IsMutation k t := Iff.rfl

/-- Realized seed reachability is the reflexive transitive closure of one-step exchange. -/
abbrev Reachable : Seed c row u B → Seed c row u B → Prop := Relation.ReflTransGen Step

/-- Every certified word determines a reachable seed. -/
theorem IsMutationWord.reachable (h : IsMutationWord w s t) : Reachable s t := by
  induction h with
  | nil => exact .refl
  | cons hstep _ ih => exact ih.head (step_iff.mpr ⟨_, hstep⟩)

/-- A reachable seed admits a certificate labelled by a finite mutation word. -/
theorem reachable_iff_exists_isMutationWord :
    Reachable s t ↔ ∃ w, IsMutationWord w s t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], .nil _⟩
    | tail _ hstep ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨k, hk⟩ := step_iff.mp hstep
      exact ⟨w ++ [k], hw.append (.cons hk (.nil _))⟩
  · rintro ⟨_, hw⟩
    exact hw.reachable

/-- Realized mutation reachability is symmetric by reversing a certified word. -/
theorem Reachable.symm (h : Reachable s t) : Reachable t s := by
  obtain ⟨_, hw⟩ := reachable_iff_exists_isMutationWord.mp h
  exact hw.reverse.reachable

section DivisionSemiring

variable {D : Type*} [DivisionSemiring D] [Algebra R D]

/-- Over a division semiring, every finite word has a unique realization from an admissible
initial seed. The existing one-step admissibility theorem keeps all subsequent exchanges
defined. -/
theorem existsUnique_isMutationWord (s : Seed c row u D) (hs : s.Admissible) (w : List K) :
    ∃! t, IsMutationWord w s t := by
  induction w generalizing s with
  | nil =>
    refine ⟨s, .nil s, ?_⟩
    intro t h
    cases h
    rfl
  | cons k w ih =>
    have hu := (admissible_iff_isUnit_exchangeElement s).mp hs k
    have hstep := s.isMutation_mutation k hu
    obtain ⟨t, htail, _⟩ := ih _ (hstep.admissible_iff.mpr hs)
    exact ⟨t, .cons hstep htail, fun _ h ↦ h.eq (.cons hstep htail)⟩

end DivisionSemiring

end TauCeti.Seed
