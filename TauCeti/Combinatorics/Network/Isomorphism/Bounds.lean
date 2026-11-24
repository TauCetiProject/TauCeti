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

private theorem assignmentEquiv_le (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) :
    e.assignmentEquiv K lower ≤ e.assignmentEquiv K upper :=
  (e.assignmentEquiv_le_assignmentEquiv_iff lower upper).2 (fun _ _ a ↦ h a)

/-- Transport a simultaneous replacement of both network bounds along an isomorphism.

The replacement on the target uses the transported bound assignments and retains the original
vertex and arrow equivalences.  No vertex or arrow finiteness is needed. -/
@[expose]
def replaceBounds (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) :
    N.replaceBounds lower upper h ≃ₙ
      N'.replaceBounds (e.assignmentEquiv K lower) (e.assignmentEquiv K upper)
        (by
          intro x y a
          exact e.assignmentEquiv_le lower upper h x y a) where
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

/-- Replacing both bounds retains the arrow equivalences of the original isomorphism, after
identifying their endpoints using `replaceBounds_vertexEquiv`. -/
@[simp]
theorem replaceBounds_homEquiv_apply (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) (x y : V) (a : N.Hom x y) :
    @Quiver.homOfEq W ⟨N'.Hom⟩ _ _ _ _ ((e.replaceBounds lower upper h).homEquiv x y a)
      (congrArg (fun f : V ≃ W => f x) (e.replaceBounds_vertexEquiv lower upper h))
      (congrArg (fun f : V ≃ W => f y) (e.replaceBounds_vertexEquiv lower upper h)) =
        e.homEquiv x y a := by
  exact @Quiver.homOfEq_rfl W ⟨N'.Hom⟩ _ _ (e.homEquiv x y a)

/-- Replacing both bounds retains the prefunctor induced by the original isomorphism. -/
@[simp]
theorem replaceBounds_toPrefunctor (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) :
    (e.replaceBounds lower upper h).toPrefunctor = e.toPrefunctor := by
  refine e.eq_toPrefunctor_of_obj_map _ ?_ ?_
  · intro x
    simpa only [toPrefunctor_obj] using
      congrArg (fun f : V ≃ W => f x) (e.replaceBounds_vertexEquiv lower upper h)
  · intro x y a
    exact ((e.replaceBounds lower upper h).toPrefunctor_map a).trans
      (e.replaceBounds_homEquiv_apply lower upper h x y a)

/-- Replacing both bounds retains total arrow transport. -/
@[simp]
theorem replaceBounds_totalHomEquiv (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) :
    (e.replaceBounds lower upper h).totalHomEquiv = e.totalHomEquiv := by
  apply e.eq_totalHomEquiv_of_apply
  intro x y a
  simp only [totalHomEquiv_apply, replaceBounds, Network.replaceBounds]

/-- Replacing both bounds retains transport of directed paths. -/
@[simp]
theorem replaceBounds_mapPath (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) {x y : V}
    (p : ArrowWalk N.Hom x y) :
    (e.replaceBounds lower upper h).mapPath p = e.mapPath p := by
  exact ((e.replaceBounds lower upper h).mapPath_eq_toPrefunctor_mapPath p).symm.trans
    (e.cast_mapPath_eq_of_eq_toPrefunctor (e.replaceBounds lower upper h).toPrefunctor
      (fun x ↦ by
        simpa only [toPrefunctor_obj] using
          congrArg (fun f : V ≃ W => f x) (e.replaceBounds_vertexEquiv lower upper h))
      (e.replaceBounds_toPrefunctor lower upper h) p)

/-- Assignment transport is unchanged after replacing both bounds. -/
@[simp]
theorem replaceBounds_assignmentEquiv (e : N ≃ₙ N') (lower upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ upper a) (R : Type w') :
    (e.replaceBounds lower upper h).assignmentEquiv R = e.assignmentEquiv R :=
  by
    apply e.eq_assignmentEquiv_of_apply R
    exact (e.replaceBounds lower upper h).assignmentEquiv_apply R

/-- Transport a replacement of only the lower bounds along a network isomorphism.

The induced isomorphism retains the vertex and arrow equivalences of `e`. -/
@[expose]
def replaceLower (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) :
    N.replaceLower lower h ≃ₙ
      N'.replaceLower (e.assignmentEquiv K lower) (by
        intro x y a
        rw [← e.assignmentEquiv_upper]
        exact e.assignmentEquiv_le lower N.upper h x y a) where
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

/-- Replacing lower bounds retains the arrow equivalences of the original isomorphism, after
identifying their endpoints using `replaceLower_vertexEquiv`. -/
@[simp]
theorem replaceLower_homEquiv_apply (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) (x y : V) (a : N.Hom x y) :
    @Quiver.homOfEq W ⟨N'.Hom⟩ _ _ _ _ ((e.replaceLower lower h).homEquiv x y a)
      (congrArg (fun f : V ≃ W => f x) (e.replaceLower_vertexEquiv lower h))
      (congrArg (fun f : V ≃ W => f y) (e.replaceLower_vertexEquiv lower h)) =
        e.homEquiv x y a := by
  exact @Quiver.homOfEq_rfl W ⟨N'.Hom⟩ _ _ (e.homEquiv x y a)

/-- Replacing lower bounds retains the prefunctor induced by the original isomorphism. -/
@[simp]
theorem replaceLower_toPrefunctor (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) :
    (e.replaceLower lower h).toPrefunctor = e.toPrefunctor := by
  refine e.eq_toPrefunctor_of_obj_map _ ?_ ?_
  · intro x
    simpa only [toPrefunctor_obj] using
      congrArg (fun f : V ≃ W => f x) (e.replaceLower_vertexEquiv lower h)
  · intro x y a
    exact ((e.replaceLower lower h).toPrefunctor_map a).trans
      (e.replaceLower_homEquiv_apply lower h x y a)

/-- Replacing lower bounds retains total arrow transport. -/
@[simp]
theorem replaceLower_totalHomEquiv (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) :
    (e.replaceLower lower h).totalHomEquiv = e.totalHomEquiv := by
  apply e.eq_totalHomEquiv_of_apply
  intro x y a
  simp only [totalHomEquiv_apply, replaceLower, Network.replaceLower, Network.replaceBounds]

/-- Replacing lower bounds retains transport of directed paths. -/
@[simp]
theorem replaceLower_mapPath (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) {x y : V}
    (p : ArrowWalk N.Hom x y) :
    (e.replaceLower lower h).mapPath p = e.mapPath p := by
  exact ((e.replaceLower lower h).mapPath_eq_toPrefunctor_mapPath p).symm.trans
    (e.cast_mapPath_eq_of_eq_toPrefunctor (e.replaceLower lower h).toPrefunctor
      (fun x ↦ by
        simpa only [toPrefunctor_obj] using
          congrArg (fun f : V ≃ W => f x) (e.replaceLower_vertexEquiv lower h))
      (e.replaceLower_toPrefunctor lower h) p)

/-- Assignment transport is unchanged after replacing lower bounds. -/
@[simp]
theorem replaceLower_assignmentEquiv (e : N ≃ₙ N') (lower : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), lower a ≤ N.upper a) (R : Type w') :
    (e.replaceLower lower h).assignmentEquiv R = e.assignmentEquiv R :=
  by
    apply e.eq_assignmentEquiv_of_apply R
    exact (e.replaceLower lower h).assignmentEquiv_apply R

/-- Transport a replacement of only the upper bounds along a network isomorphism.

The induced isomorphism retains the vertex and arrow equivalences of `e`. -/
@[expose]
def replaceUpper (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) :
    N.replaceUpper upper h ≃ₙ
      N'.replaceUpper (e.assignmentEquiv K upper) (by
        intro x y a
        rw [← e.assignmentEquiv_lower]
        exact e.assignmentEquiv_le N.lower upper h x y a) where
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

/-- Replacing upper bounds retains the arrow equivalences of the original isomorphism, after
identifying their endpoints using `replaceUpper_vertexEquiv`. -/
@[simp]
theorem replaceUpper_homEquiv_apply (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) (x y : V) (a : N.Hom x y) :
    @Quiver.homOfEq W ⟨N'.Hom⟩ _ _ _ _ ((e.replaceUpper upper h).homEquiv x y a)
      (congrArg (fun f : V ≃ W => f x) (e.replaceUpper_vertexEquiv upper h))
      (congrArg (fun f : V ≃ W => f y) (e.replaceUpper_vertexEquiv upper h)) =
        e.homEquiv x y a := by
  exact @Quiver.homOfEq_rfl W ⟨N'.Hom⟩ _ _ (e.homEquiv x y a)

/-- Replacing upper bounds retains the prefunctor induced by the original isomorphism. -/
@[simp]
theorem replaceUpper_toPrefunctor (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) :
    (e.replaceUpper upper h).toPrefunctor = e.toPrefunctor := by
  refine e.eq_toPrefunctor_of_obj_map _ ?_ ?_
  · intro x
    simpa only [toPrefunctor_obj] using
      congrArg (fun f : V ≃ W => f x) (e.replaceUpper_vertexEquiv upper h)
  · intro x y a
    exact ((e.replaceUpper upper h).toPrefunctor_map a).trans
      (e.replaceUpper_homEquiv_apply upper h x y a)

/-- Replacing upper bounds retains total arrow transport. -/
@[simp]
theorem replaceUpper_totalHomEquiv (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) :
    (e.replaceUpper upper h).totalHomEquiv = e.totalHomEquiv := by
  apply e.eq_totalHomEquiv_of_apply
  intro x y a
  simp only [totalHomEquiv_apply, replaceUpper, Network.replaceUpper, Network.replaceBounds]

/-- Replacing upper bounds retains transport of directed paths. -/
@[simp]
theorem replaceUpper_mapPath (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) {x y : V}
    (p : ArrowWalk N.Hom x y) :
    (e.replaceUpper upper h).mapPath p = e.mapPath p := by
  exact ((e.replaceUpper upper h).mapPath_eq_toPrefunctor_mapPath p).symm.trans
    (e.cast_mapPath_eq_of_eq_toPrefunctor (e.replaceUpper upper h).toPrefunctor
      (fun x ↦ by
        simpa only [toPrefunctor_obj] using
          congrArg (fun f : V ≃ W => f x) (e.replaceUpper_vertexEquiv upper h))
      (e.replaceUpper_toPrefunctor upper h) p)

/-- Assignment transport is unchanged after replacing upper bounds. -/
@[simp]
theorem replaceUpper_assignmentEquiv (e : N ≃ₙ N') (upper : N.Assignment K)
    (h : ∀ {x y} (a : N.Hom x y), N.lower a ≤ upper a) (R : Type w') :
    (e.replaceUpper upper h).assignmentEquiv R = e.assignmentEquiv R :=
  by
    apply e.eq_assignmentEquiv_of_apply R
    exact (e.replaceUpper upper h).assignmentEquiv_apply R

end TauCeti.Network.Iso
