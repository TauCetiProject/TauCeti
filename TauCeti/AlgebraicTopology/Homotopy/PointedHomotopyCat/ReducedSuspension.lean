/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
public import TauCeti.Topology.Category.BasedTopologicalSpace.ReducedSuspension

/-!
# The reduced suspension functor on the pointed homotopy category

The reduced suspension of based spaces carries pointed-homotopic maps to pointed-homotopic maps,
so it descends to an endofunctor `TauCeti.PointedHomotopyCat.reducedSuspension` of the pointed
homotopy category, sending the class of a based map `f` to the class of `Σf`. By construction it
commutes with the quotient functor from based spaces
(`TauCeti.PointedHomotopyCat.quotient_comp_reducedSuspension`).

This is the suspension in the suspension axiom of reduced cohomology theories. Such a theory is a
family of functors `E~ⁿ` on (a subcategory of) the pointed homotopy category, and its suspension
isomorphisms `E~ⁿ(X) ≅ E~ⁿ⁺¹(ΣX)` are natural in `X` with respect to this functor.

## Main declarations

* `TauCeti.BasedTopologicalSpace.homotopicRel_reducedSuspension_map`: the reduced suspensions of
  pointed-homotopic based maps are pointed homotopic.
* `TauCeti.PointedHomotopyCat.reducedSuspension`: the reduced suspension functor on the pointed
  homotopy category.
* `TauCeti.PointedHomotopyCat.quotient_comp_reducedSuspension`: it commutes with the quotient
  functor from based spaces.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (the reduced
  suspension) and Section 4.E, p. 448 (the suspension axiom of reduced cohomology theories).
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

namespace BasedTopologicalSpace

variable {X Y : BasedTopologicalSpace.{u}}

/-- **Suspension preserves pointed homotopy.** The reduced suspensions of two based maps that are
homotopic relative to the base point are homotopic relative to the base point. -/
theorem homotopicRel_reducedSuspension_map {f g : X ⟶ Y} (h : homotopicRel f g) :
    homotopicRel (reducedSuspension.map f) (reducedSuspension.map g) :=
  homotopicRel_iff.2 (ContinuousMap.HomotopicRel.reducedSuspensionMap (homotopicRel_iff.1 h) _ _)

end BasedTopologicalSpace

namespace PointedHomotopyCat

/-- The **reduced suspension functor on the pointed homotopy category**: a based space goes to its
reduced suspension, and the pointed homotopy class of a based map `f` to that of `Σf`. It is well
defined because suspension preserves pointed homotopy
(`TauCeti.BasedTopologicalSpace.homotopicRel_reducedSuspension_map`). -/
@[expose] def reducedSuspension : PointedHomotopyCat.{u} ⥤ PointedHomotopyCat.{u} :=
  CategoryTheory.Quotient.lift _ (BasedTopologicalSpace.reducedSuspension ⋙ quotient)
    fun _ _ _ _ h ↦ (quotient_map_eq_iff _ _).2
      (BasedTopologicalSpace.homotopicRel_iff.1
        (BasedTopologicalSpace.homotopicRel_reducedSuspension_map h))

/-- The reduced suspension on the pointed homotopy category is induced by the reduced suspension of
based spaces: it commutes with the quotient functor. -/
theorem quotient_comp_reducedSuspension :
    quotient.{u} ⋙ reducedSuspension = BasedTopologicalSpace.reducedSuspension ⋙ quotient :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem reducedSuspension_obj_quotient_obj (X : BasedTopologicalSpace.{u}) :
    reducedSuspension.obj (quotient.obj X) =
      quotient.obj (BasedTopologicalSpace.reducedSuspension.obj X) :=
  (rfl)

@[simp]
theorem reducedSuspension_map_quotient_map {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) :
    reducedSuspension.map (quotient.map f) =
      quotient.map (BasedTopologicalSpace.reducedSuspension.map f) :=
  (rfl)

end PointedHomotopyCat

end TauCeti
