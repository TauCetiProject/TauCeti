/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.BasedTopologicalSpace
public import TauCeti.Topology.Constructions.ReducedSuspension

/-!
# The reduced suspension functor on based spaces

The reduced suspension `ΣX = (X × I) / (X × ∂I ∪ {x₀} × I)` of a based space, based at the image
of the collapsed locus, is a functor `TauCeti.BasedTopologicalSpace.reducedSuspension` from based
spaces to based spaces. It sends a based map `f` to `Σf : [x, s] ↦ [f x, s]`.

The functor carries pointed-homotopic maps to pointed-homotopic maps, so it descends to the
pointed homotopy category; see the module
`TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat.ReducedSuspension`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.reducedSuspension`: the reduced suspension functor.
* `TauCeti.BasedTopologicalSpace.reducedSuspension_map_apply_mk`: `Σf` sends `[x, s]` to
  `[f x, s]`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (the reduced
  suspension) and Section 4.3.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti.BasedTopologicalSpace

/-- The **reduced suspension functor** on based spaces: a based space `(X, x₀)` goes to its reduced
suspension `ΣX`, based at the image of the collapsed locus, and a based map `f` goes to
`Σf : [x, s] ↦ [f x, s]`. -/
@[expose, implicit_reducible]
def reducedSuspension : BasedTopologicalSpace.{u} ⥤ BasedTopologicalSpace.{u} where
  obj X := ⟨ReducedSuspension X.carrier X.basepoint, ReducedSuspension.basepoint⟩
  map f := ⟨ReducedSuspension.map f.toContinuousMap f.map_basepoint,
    ReducedSuspension.map_basepoint _ _⟩
  map_id X := Hom.ext <| by
    simp only [id_eq_hom_id, Hom.toContinuousMap_id]
    exact ReducedSuspension.map_id
  map_comp f g := Hom.ext <| by
    simp only [comp_eq_hom_comp, Hom.toContinuousMap_comp]
    exact ReducedSuspension.map_comp _ _ _ _

variable {X Y : BasedTopologicalSpace.{u}}

@[simp]
theorem reducedSuspension_obj_basepoint (X : BasedTopologicalSpace.{u}) :
    (reducedSuspension.obj X).basepoint =
      (ReducedSuspension.basepoint : ReducedSuspension X.carrier X.basepoint) :=
  (rfl)

@[simp]
theorem reducedSuspension_map_toContinuousMap (f : X ⟶ Y) :
    (reducedSuspension.map f).toContinuousMap =
      ReducedSuspension.map f.toContinuousMap f.map_basepoint :=
  (rfl)

/-- The suspension of a based map `f` sends `[x, s]` to `[f x, s]`. -/
@[simp]
theorem reducedSuspension_map_apply_mk (f : X ⟶ Y) (p : X.carrier × unitInterval) :
    DFunLike.coe (F := Hom (reducedSuspension.obj X) (reducedSuspension.obj Y))
        (reducedSuspension.map f) (ReducedSuspension.mk p) =
      ReducedSuspension.mk (DFunLike.coe (F := Hom X Y) f p.1, p.2) :=
  ReducedSuspension.map_mk _ _ p

end TauCeti.BasedTopologicalSpace
