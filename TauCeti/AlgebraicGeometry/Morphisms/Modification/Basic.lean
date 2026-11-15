/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Modifications

A morphism of schemes `f : X ⟶ Y` is a *modification* if it is proper and there is a dense open
`U ⊆ Y`, with dense preimage `f ⁻¹ U ⊆ X`, over which `f` is an isomorphism (Stacks,
Definition 29.52.11 (0AAZ), where `X` and `Y` are integral). Blow-ups and finite normalizations of
integral schemes are typical examples. A modification changes its target only over a nowhere
dense closed subset, so it identifies dense opens of source and target: it is birational over its
target.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsModification f`: `f` is proper and an isomorphism over a dense open
  with dense preimage.

## Main results

* `TauCeti.AlgebraicGeometry.IsModification.of_isIso`: isomorphisms are modifications.
* `TauCeti.AlgebraicGeometry.IsModification.birationalOver`: a modification `f : X ⟶ Y` is
  birational over `Y`, comparing `f` with the identity of `Y`.
* `TauCeti.AlgebraicGeometry.IsModification.birational`: the source and target of a modification
  are birational.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ Y` is a *modification* if it is proper and there is a dense open
`U ⊆ Y` with dense preimage in `X` over which `f` is an isomorphism. Stacks, Definition 29.52.11
(0AAZ), where `X` and `Y` are integral. -/
@[stacks 0AAZ]
class IsModification (f : X ⟶ Y) : Prop extends IsProper f where
  exists_isIso_morphismRestrict :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Dense (f ⁻¹ᵁ U : Set X) ∧ IsIso (f ∣_ U)

namespace IsModification

/-- An isomorphism is a modification, over the whole target. -/
instance (priority := 100) of_isIso (f : X ⟶ Y) [IsIso f] : IsModification f where
  exists_isIso_morphismRestrict := ⟨⊤, by simp, by simp, inferInstance⟩

/-- A modification `f : X ⟶ Y` is birational over `Y`: restricting `f` over a dense open of `Y`
gives a partial isomorphism from `X` to `Y` lying over `Y`. -/
theorem birationalOver (f : X ⟶ Y) [IsModification f] : Scheme.BirationalOver f (𝟙 Y) := by
  obtain ⟨U, hU, hfU, _⟩ := exists_isIso_morphismRestrict (f := f)
  exact ⟨⟨f ⁻¹ᵁ U, hfU, U, hU, asIso (f ∣_ U)⟩, by simp [Scheme.PartialIso.IsOver]⟩

/-- The source and target of a modification are birational. -/
theorem birational (f : X ⟶ Y) [IsModification f] : X.Birational Y :=
  ⟨(birationalOver f).choose⟩

end IsModification

end TauCeti.AlgebraicGeometry
