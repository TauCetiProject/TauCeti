/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

/-!
# Alterations

A morphism of schemes `f : X ⟶ Y` is an *alteration* if it is proper, dominant, and finite over
some nonempty open `U ⊆ Y` (Stacks, Definition 29.52.12 (0AB0), where `X` and `Y` are integral).
For integral schemes this says that `f` is proper and surjective and that the function field of
`X` is a finite extension of that of `Y`. Modifications of nonempty schemes are alterations; when
`X` and `Y` are integral, the modifications are exactly the alterations of generic degree one.
De Jong's theorem resolves singularities up to alterations.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsAlteration f`: `f` is proper, dominant, and finite over a nonempty
  open of its target.

## Main results

* `TauCeti.AlgebraicGeometry.isAlteration_iff`: unfolds `IsAlteration f` into its defining
  conditions.
* `TauCeti.AlgebraicGeometry.IsModification.isAlteration`: a modification of a nonempty scheme is
  an alteration.
* `TauCeti.AlgebraicGeometry.isAlteration_of_isFinite`: a finite dominant morphism to a nonempty
  scheme is an alteration. `TauCeti/Examples/AlgebraicGeometry/Morphisms/Alteration.lean` applies
  it to `Spec ℂ ⟶ Spec ℝ`, an alteration of generic degree two.

## References

* [Stacks Project, Definition 29.52.12](https://stacks.math.columbia.edu/tag/0AB0).
* A. J. de Jong, *Smoothness, semi-stability and alterations*, Publ. Math. IHÉS 83 (1996),
  2.20.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ Y` is an *alteration* if it is proper, dominant, and finite
over some nonempty open `U ⊆ Y`. Stacks, Definition 29.52.12 (0AB0), where `X` and `Y` are
integral. -/
@[stacks 0AB0]
class IsAlteration (f : X ⟶ Y) : Prop extends IsProper f, IsDominant f where
  exists_isFinite_morphismRestrict : ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsFinite (f ∣_ U)

/-- `f` is an alteration if and only if it is proper, dominant, and finite over some nonempty open
of its target. -/
theorem isAlteration_iff (f : X ⟶ Y) :
    IsAlteration f ↔
      IsProper f ∧ IsDominant f ∧ ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsFinite (f ∣_ U) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance, IsAlteration.exists_isFinite_morphismRestrict⟩,
    fun ⟨_, _, h⟩ ↦ { exists_isFinite_morphismRestrict := h }⟩

/-- A modification of a nonempty scheme is an alteration: it is an isomorphism, hence finite,
over a dense open, which is nonempty. -/
instance (priority := 100) IsModification.isAlteration (f : X ⟶ Y) [IsModification f]
    [Nonempty Y] : IsAlteration f where
  exists_isFinite_morphismRestrict := by
    obtain ⟨U, hU, -, _⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
    exact ⟨U, hU.nonempty, inferInstance⟩

/-- A finite dominant morphism to a nonempty scheme is an alteration: it is finite over the whole
target. -/
instance (priority := 100) isAlteration_of_isFinite (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [Nonempty Y] : IsAlteration f where
  exists_isFinite_morphismRestrict :=
    ⟨⊤, by rw [TopologicalSpace.Opens.coe_top]; exact Set.univ_nonempty, inferInstance⟩

end TauCeti.AlgebraicGeometry
