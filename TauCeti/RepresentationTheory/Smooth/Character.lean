/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.Topology.Algebra.Group.SmoothCharacter

/-!
# Smooth characters and twists of smooth representations

Let `G` be a topological group with separately continuous multiplication and `A` a commutative
semiring. A character `χ : G →* Aˣ` is smooth (`TauCeti.IsSmoothCharacter χ`, its kernel is open)
exactly when the rank-one representation `A(χ)` (`Representation.ofLinearCharacter χ`) is smooth,
and twisting a representation by a smooth character (`Representation.charTwist`) preserves and
reflects smoothness.

## Main results

* `TauCeti.isSmooth_ofLinearCharacter_iff`: `A(χ)` is smooth exactly when `χ` is.
* `TauCeti.IsSmoothCharacter.isSmooth_charTwist`,
  `TauCeti.IsSmoothCharacter.isSmooth_charTwist_iff`: the twist of a representation by a smooth
  character is smooth exactly when the representation is.

## References

* I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n, F) where F is a
  non-archimedean local field*, Russian Math. Surveys 31:3 (1976), Ch. I §1, 1.19, p. 11, and
  Ch. I §2, 2.25(c), p. 23.
-/

public section

open Representation

namespace TauCeti

variable {A G V : Type*} [Group G] [TopologicalSpace G] [CommSemiring A]
  [SeparatelyContinuousMul G] [AddCommMonoid V] [Module A V]

/-- The rank-one representation `A(χ)` of a character is smooth exactly when the character is. -/
@[simp]
theorem isSmooth_ofLinearCharacter_iff {χ : G →* Aˣ} :
    IsSmooth (ofLinearCharacter χ) ↔ IsSmoothCharacter χ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun x ↦ Subgroup.isOpen_mono
    (ker_le_stabilizer_ofLinearCharacter χ x) (isSmoothCharacter_iff.1 h)⟩⟩
  rw [isSmoothCharacter_iff, ← stabilizer_ofLinearCharacter_one]
  exact IsSmooth.isOpen_stabilizer 1

/-- The twist of a smooth representation by a smooth character is smooth. -/
theorem IsSmoothCharacter.isSmooth_charTwist {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ)
    (ρ : Representation A G V) [IsSmooth ρ] : IsSmooth (charTwist χ ρ) := by
  refine ⟨fun v ↦ Subgroup.isOpen_mono (ker_inf_stabilizer_le_stabilizer_charTwist χ ρ v) ?_⟩
  rw [Subgroup.coe_inf]
  exact (isSmoothCharacter_iff.1 hχ).inter (IsSmooth.isOpen_stabilizer v)

/-- Twisting by a smooth character preserves and reflects smoothness. -/
@[simp]
theorem IsSmoothCharacter.isSmooth_charTwist_iff {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ)
    (ρ : Representation A G V) : IsSmooth (charTwist χ ρ) ↔ IsSmooth ρ := by
  refine ⟨fun h ↦ ?_, fun _ ↦ hχ.isSmooth_charTwist ρ⟩
  have := hχ.inv.isSmooth_charTwist (charTwist χ ρ)
  rwa [charTwist_charTwist, show χ⁻¹ * χ = 1 by ext; simp, charTwist_one] at this

end TauCeti
