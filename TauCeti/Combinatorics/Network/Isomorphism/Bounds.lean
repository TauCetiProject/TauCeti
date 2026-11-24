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

* `TauCeti.Network.Iso.replaceBoundsWith`: transport arbitrary corresponding bound replacements.
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

section ReplaceBoundsWith

variable (e : N ≃ₙ N')
variable (lower upper : N.Assignment K)
variable (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a)
variable (lower' upper' : N'.Assignment K)
variable (h' : ∀ {x y} (a : N'.Hom x y), lower' a ≤ upper' a)
variable (map_lower : ∀ {x y} (a : N.Hom x y), lower' (e.homEquiv x y a) = lower a)
variable (map_upper : ∀ {x y} (a : N.Hom x y), upper' (e.homEquiv x y a) = upper a)

/-- Transport arbitrary corresponding replacements of both bounds along a network isomorphism.

The supplied equalities say that the target bounds agree with the source bounds after arrow
transport.  The resulting isomorphism retains the vertex and arrow equivalences of `e`. -/
@[expose]
def replaceBoundsWith :
    N.replaceBounds lower upper h ≃ₙ N'.replaceBounds lower' upper' h' where
  vertexEquiv := e.vertexEquiv
  homEquiv := e.homEquiv
  map_lower := map_lower
  map_upper := map_upper

/-- Arbitrary corresponding bound replacements retain the original vertex equivalence. -/
@[simp]
theorem replaceBoundsWith_vertexEquiv :
    (replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper).vertexEquiv =
      e.vertexEquiv :=
  (rfl)

/-- Arbitrary corresponding bound replacements retain the original arrow equivalences. -/
@[simp]
theorem replaceBoundsWith_homEquiv_apply (x y : V) (a : N.Hom x y) :
    (replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper).homEquiv x y a =
      e.homEquiv x y a :=
  (rfl)

/-- Arbitrary corresponding bound replacements retain the induced prefunctor. -/
@[simp]
theorem replaceBoundsWith_toPrefunctor :
    (replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper).toPrefunctor =
      e.toPrefunctor := by
  refine @Prefunctor.ext V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) _ _
    (fun x ↦ by simp) fun x y a ↦ eq_of_heq ?_
  rw [heq_eqRec_iff, heq_eqRec_iff]
  let f := replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper
  exact (f.toPrefunctor_map_heq a).trans
    ((heq_of_eq
      (replaceBoundsWith_homEquiv_apply e lower upper h lower' upper' h' map_lower map_upper
        x y a)).trans (e.toPrefunctor_map_heq a).symm)

/-- Arbitrary corresponding bound replacements retain total arrow transport. -/
@[simp]
theorem replaceBoundsWith_totalHomEquiv :
    (replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper).totalHomEquiv =
      e.totalHomEquiv := by
  apply e.eq_totalHomEquiv_of_apply
  intro x y a
  rw [totalHomEquiv_apply]
  have hx := congrArg (fun F : V ≃ W ↦ F x)
    (replaceBoundsWith_vertexEquiv e lower upper h lower' upper' h' map_lower map_upper)
  have hy := congrArg (fun F : V ≃ W ↦ F y)
    (replaceBoundsWith_vertexEquiv e lower upper h lower' upper' h' map_lower map_upper)
  apply Sigma.ext
  · exact hx
  · cases hx
    apply heq_of_eq
    apply Sigma.ext
    · exact hy
    · exact heq_of_eq
        (replaceBoundsWith_homEquiv_apply e lower upper h lower' upper' h' map_lower map_upper
          x y a)

/-- Arbitrary corresponding bound replacements retain transport of directed paths. -/
@[simp]
theorem replaceBoundsWith_mapPath {x y : V} (p : ArrowWalk N.Hom x y) :
    (replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper).mapPath p =
      e.mapPath p := by
  let f := replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper
  let hF : f.toPrefunctor = e.toPrefunctor :=
    replaceBoundsWith_toPrefunctor e lower upper h lower' upper' h' map_lower map_upper
  have hmap :=
    @Prefunctor.cast_mapPath_eq_of_eq V W (Quiver.mk N.Hom) (Quiver.mk N'.Hom)
      f.toPrefunctor e.toPrefunctor hF x y p
  have hmap' :
      @Prefunctor.mapPath V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) f.toPrefunctor x y p ≍
        @Prefunctor.mapPath V (Quiver.mk N.Hom) W (Quiver.mk N'.Hom) e.toPrefunctor x y p :=
    (@Quiver.Path.cast_heq W (Quiver.mk N'.Hom) _ _ _ _ _ _ _).symm.trans
      (heq_of_eq hmap)
  exact eq_of_heq ((f.mapPath_heq_toPrefunctor_mapPath p).trans
    (hmap'.trans (e.mapPath_heq_toPrefunctor_mapPath p).symm))

/-- Arbitrary corresponding bound replacements retain assignment transport. -/
@[simp]
theorem replaceBoundsWith_assignmentEquiv (R : Type w') :
    (replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper).assignmentEquiv R =
      e.assignmentEquiv R := by
  apply e.eq_assignmentEquiv_of_apply R
  intro f x y a
  rw [← replaceBoundsWith_homEquiv_apply e lower upper h lower' upper' h' map_lower map_upper]
  exact
    (replaceBoundsWith e lower upper h lower' upper' h' map_lower map_upper).assignmentEquiv_apply
      R f a

end ReplaceBoundsWith

/-- Transport a simultaneous replacement of both network bounds along an isomorphism.

The replacement on the target uses the transported bound assignments and retains the original
vertex and arrow equivalences.  No vertex or arrow finiteness is needed. -/
abbrev replaceBounds (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) :
    N.replaceBounds lower upper h ≃ₙ
      N'.replaceBounds (e.assignmentEquiv K lower) (e.assignmentEquiv K upper)
        (by
          intro x y a
          exact e.assignmentEquiv_le_apply lower upper (fun _ _ b ↦ h b) a) :=
  replaceBoundsWith e lower upper h _ _
    (e.assignmentEquiv_le_apply lower upper (fun _ _ b ↦ h b))
    (e.assignmentEquiv_apply K lower) (e.assignmentEquiv_apply K upper)

/-- A transported lower bound remains below the target network's upper bound. -/
theorem assignmentEquiv_le_upper (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) :
    ∀ {x y} (a : N'.Hom x y), e.assignmentEquiv K lower a ≤ N'.upper a := by
  intro x y a
  rw [← e.assignmentEquiv_upper]
  exact e.assignmentEquiv_le_apply lower N.upper (fun _ _ b ↦ h b) a

/-- Transport a replacement of only the lower bounds along a network isomorphism.

The induced isomorphism retains the vertex and arrow equivalences of `e`. -/
abbrev replaceLower (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) :
    N.replaceLower lower h ≃ₙ
      N'.replaceLower (e.assignmentEquiv K lower) (assignmentEquiv_le_upper e lower h) :=
  replaceBoundsWith e lower N.upper h _ N'.upper
    (assignmentEquiv_le_upper e lower h)
    (e.assignmentEquiv_apply K lower) e.map_upper

/-- The target network's lower bound remains below a transported upper bound. -/
theorem lower_le_assignmentEquiv (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) :
    ∀ {x y} (a : N'.Hom x y), N'.lower a ≤ e.assignmentEquiv K upper a := by
  intro x y a
  rw [← e.assignmentEquiv_lower]
  exact e.assignmentEquiv_le_apply N.lower upper (fun _ _ b ↦ h b) a

/-- Transport a replacement of only the upper bounds along a network isomorphism.

The induced isomorphism retains the vertex and arrow equivalences of `e`. -/
abbrev replaceUpper (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) :
    N.replaceUpper upper h ≃ₙ
      N'.replaceUpper (e.assignmentEquiv K upper) (lower_le_assignmentEquiv e upper h) :=
  replaceBoundsWith e N.lower upper h N'.lower _
    (lower_le_assignmentEquiv e upper h)
    e.map_lower (e.assignmentEquiv_apply K upper)

end TauCeti.Network.Iso
