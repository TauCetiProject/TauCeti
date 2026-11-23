/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Bounds
public import TauCeti.Combinatorics.Network.Isomorphism.Basic

/-!
# Bound replacement under network isomorphisms

Replacing the bounds of a network does not change its vertices or arrows.  Consequently, a
network isomorphism induces an isomorphism after replacing both bounds, only the lower bounds, or
only the upper bounds, provided the replacement assignments are transported along the original
isomorphism.

The induced isomorphisms retain the original vertex and arrow equivalences.  Their assignment
transport is therefore the original assignment transport, so all of the existing feasibility,
excess, flow, and path transport API applies without an additional conversion.

## Main definitions

* `TauCeti.Network.Iso.replaceBounds`: transport a simultaneous replacement of both bounds.
* `TauCeti.Network.Iso.replaceLower`: transport a replacement of only the lower bounds.
* `TauCeti.Network.Iso.replaceUpper`: transport a replacement of only the upper bounds.
-/

public section

namespace TauCeti.Network.Iso

universe u u' w w'

variable {K : Type w} [LE K]
variable {V : Type u} {W : Type u'}
variable {N : Network K V} {N' : Network K W}

/-- Transport a simultaneous replacement of both network bounds along an isomorphism.

The replacement on the target uses the transported bound assignments.  No vertex or arrow
finiteness is needed.  The definition is exposed so that the unchanged arrow family reduces in
dependent assignment expressions. -/
@[expose]
def replaceBounds (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) :
    N.replaceBounds lower upper h ≃ₙ
      N'.replaceBounds (e.assignmentEquiv K lower) (e.assignmentEquiv K upper)
        (by
          intro x y a
          exact ((e.assignmentEquiv_le_assignmentEquiv_iff lower upper).2
            (fun _ _ a ↦ h a)) x y a) where
  vertexEquiv := e.vertexEquiv
  homEquiv := e.homEquiv
  map_lower := e.assignmentEquiv_apply K lower
  map_upper := e.assignmentEquiv_apply K upper

/-- Replacing both bounds retains the vertex equivalence of the original isomorphism. -/
@[simp]
theorem replaceBounds_vertexEquiv (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) :
    (e.replaceBounds lower upper h).vertexEquiv = e.vertexEquiv :=
  (rfl)

/-- Assignment transport is unchanged after replacing both bounds. -/
@[simp]
theorem replaceBounds_assignmentEquiv (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) (R : Type w') :
    (e.replaceBounds lower upper h).assignmentEquiv R = e.assignmentEquiv R :=
  by
    apply Equiv.ext
    intro f
    funext x y a
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
    obtain ⟨a, rfl⟩ := (e.homEquiv x y).surjective a
    exact (e.replaceBounds lower upper h).assignmentEquiv_apply R f a |>.trans
      (e.assignmentEquiv_apply R f a).symm

/-- Transport a replacement of only the lower bounds along a network isomorphism.

The definition is exposed so that the unchanged arrow family reduces in dependent assignment
expressions. -/
@[expose]
def replaceLower (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) :
    N.replaceLower lower h ≃ₙ
      N'.replaceLower (e.assignmentEquiv K lower) (by
        intro x y a
        rw [← e.assignmentEquiv_upper]
        exact ((e.assignmentEquiv_le_assignmentEquiv_iff lower N.upper).2
          (fun _ _ a ↦ h a)) x y a) where
  vertexEquiv := e.vertexEquiv
  homEquiv := e.homEquiv
  map_lower := e.assignmentEquiv_apply K lower
  map_upper := e.map_upper

/-- Replacing lower bounds retains the vertex equivalence of the original isomorphism. -/
@[simp]
theorem replaceLower_vertexEquiv (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) :
    (e.replaceLower lower h).vertexEquiv = e.vertexEquiv :=
  (rfl)

/-- Assignment transport is unchanged after replacing lower bounds. -/
@[simp]
theorem replaceLower_assignmentEquiv (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) (R : Type w') :
    (e.replaceLower lower h).assignmentEquiv R = e.assignmentEquiv R :=
  by
    apply Equiv.ext
    intro f
    funext x y a
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
    obtain ⟨a, rfl⟩ := (e.homEquiv x y).surjective a
    exact (e.replaceLower lower h).assignmentEquiv_apply R f a |>.trans
      (e.assignmentEquiv_apply R f a).symm

/-- Transport a replacement of only the upper bounds along a network isomorphism.

The definition is exposed so that the unchanged arrow family reduces in dependent assignment
expressions. -/
@[expose]
def replaceUpper (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) :
    N.replaceUpper upper h ≃ₙ
      N'.replaceUpper (e.assignmentEquiv K upper) (by
        intro x y a
        rw [← e.assignmentEquiv_lower]
        exact ((e.assignmentEquiv_le_assignmentEquiv_iff N.lower upper).2
          (fun _ _ a ↦ h a)) x y a) where
  vertexEquiv := e.vertexEquiv
  homEquiv := e.homEquiv
  map_lower := e.map_lower
  map_upper := e.assignmentEquiv_apply K upper

/-- Replacing upper bounds retains the vertex equivalence of the original isomorphism. -/
@[simp]
theorem replaceUpper_vertexEquiv (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) :
    (e.replaceUpper upper h).vertexEquiv = e.vertexEquiv :=
  (rfl)

/-- Assignment transport is unchanged after replacing upper bounds. -/
@[simp]
theorem replaceUpper_assignmentEquiv (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) (R : Type w') :
    (e.replaceUpper upper h).assignmentEquiv R = e.assignmentEquiv R :=
  by
    apply Equiv.ext
    intro f
    funext x y a
    obtain ⟨x, rfl⟩ := e.vertexEquiv.surjective x
    obtain ⟨y, rfl⟩ := e.vertexEquiv.surjective y
    obtain ⟨a, rfl⟩ := (e.homEquiv x y).surjective a
    exact (e.replaceUpper upper h).assignmentEquiv_apply R f a |>.trans
      (e.assignmentEquiv_apply R f a).symm

end TauCeti.Network.Iso
