/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.AlmostInvariant
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Relative property (T) for discrete groups

A subgroup has relative property (T) if every unitary representation of the ambient group with
almost invariant vectors has a nonzero vector fixed by the subgroup. Property (T) of a group
is the case of the whole subgroup. Relative property (T) passes to smaller subgroups and to
images under group homomorphisms, in particular quotients. Every finite subgroup has relative
property (T), even when the ambient group is infinite, by averaging over that subgroup.

The definition quantifies over complex Hilbert spaces in an explicit universe. The acting group
needs no topology: `ContRepresentation` requires continuity only of the action operators.

The mathematical reference is Anantharaman–Popa, *An Introduction to II₁ Factors*,
Definition 14.1.1 and Proposition 14.1.2.
-/

public section

namespace Subgroup

universe u v w

variable {G : Type v} [Group G]

/-- A subgroup has relative property (T) if every unitary representation with almost invariant
vectors on a complex Hilbert space in universe `u` has a nonzero vector fixed by this subgroup. -/
def RelativePropertyT (Λ : Subgroup G) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ContRepresentation ℂ G H), ρ.IsUnitary → ρ.HasAlmostInvariantVectors →
      ∃ v : H, v ≠ 0 ∧ v ∈ (ρ.restrict Λ.subtype).invariants

/-- The unitary-representation criterion for relative property (T). -/
theorem relativePropertyT_def (Λ : Subgroup G) :
    Λ.RelativePropertyT.{u} ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (ρ : ContRepresentation ℂ G H), ρ.IsUnitary → ρ.HasAlmostInvariantVectors →
          ∃ v : H, v ≠ 0 ∧ v ∈ (ρ.restrict Λ.subtype).invariants :=
  Iff.rfl

/-- Relative property (T) passes to smaller subgroups of the same ambient group. -/
theorem RelativePropertyT.mono {Λ K : Subgroup G} (hΛ : Λ.RelativePropertyT.{u})
    (hK : K ≤ Λ) : K.RelativePropertyT.{u} := by
  intro H _ _ _ ρ hunit hρ
  obtain ⟨v, hv, hfixed⟩ := hΛ H ρ hunit hρ
  exact ⟨v, hv, fun g ↦ hfixed ⟨g, hK g.property⟩⟩

/-- Relative property (T) passes to images under group homomorphisms. In particular, it passes
to the image subgroup in every quotient of the ambient group. -/
theorem RelativePropertyT.map {K : Type w} [Group K] {Λ : Subgroup G}
    (hΛ : Λ.RelativePropertyT.{u}) (f : G →* K) : (Λ.map f).RelativePropertyT.{u} := by
  intro H _ _ _ ρ hunit hρ
  obtain ⟨v, hv, hfixed⟩ := hΛ H (ρ.restrict f) (hunit.restrict f) (hρ.restrict f)
  refine ⟨v, hv, ?_⟩
  intro g
  obtain ⟨x, hx, hfx⟩ := g.property
  simpa [hfx] using hfixed ⟨x, hx⟩

/-- Every finite subgroup has relative property (T), regardless of the ambient group. -/
theorem relativePropertyT_of_finite (Λ : Subgroup G) [Finite Λ] :
    Λ.RelativePropertyT.{u} := by
  intro H _ _ _ ρ _ hρ
  exact (hρ.restrict Λ.subtype).exists_invariant_ne_zero

/-- The trivial subgroup has relative property (T) in every group. -/
@[simp]
theorem relativePropertyT_bot : (⊥ : Subgroup G).RelativePropertyT.{u} :=
  relativePropertyT_of_finite ⊥

/-- A finite group has property (T). -/
theorem relativePropertyT_top_of_finite [Finite G] :
    (⊤ : Subgroup G).RelativePropertyT.{u} :=
  relativePropertyT_of_finite ⊤

end Subgroup
