/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Coherent

/-!
# Basic facts about colimits in `TopCat`

The initial object of `TopCat` is empty, through Mathlib's isomorphism `TopCat.initialIsoPEmpty`.
As an instance, this makes the separation properties of the empty space, such as being Hausdorff,
available for it by instance search. It is the base of every CW complex in Mathlib's categorical
sense, `TopCat.CWComplex X`, which is a relative CW complex over the map out of `⊥_ TopCat`.

A directed colimit in `TopCat` along injective transition maps has injective colimit maps
(`TauCeti.TopCat.injective_ι_of_isColimit`), since the forgetful functor to types preserves it.

The point of a colimit in `TopCat` is covered by the images of the objects of the diagram
(`TauCeti.TopCat.iUnion_range_ι_of_isColimit`) and carries the topology coherent with them
(`TauCeti.TopCat.isCoherentWith_range_ι_of_isColimit`): a set is closed as soon as it meets each
image in a closed subset of that image. So maps out of a colimit, and closedness in it, can be
checked on the images, which are subspaces of the colimit rather than objects of the diagram.
-/

public section

open CategoryTheory Limits

universe w u

namespace TopCat

/-- The initial topological space is empty. -/
instance initial_isEmpty : IsEmpty (⊥_ TopCat.{u}) :=
  Function.isEmpty initialIsoPEmpty.hom

end TopCat

namespace TauCeti.TopCat

/-- If all transition maps of a directed diagram in `TopCat` are injective, then so are the maps
from the objects of the diagram to its colimit. -/
theorem injective_ι_of_isColimit {J : Type w} [Preorder J] [IsDirectedOrder J]
    {F : J ⥤ TopCat.{u}} (hF : ∀ ⦃i j : J⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    {c : Cocone F} (hc : IsColimit c) (i : J) : Function.Injective (c.ι.app i) := fun x y h ↦ by
  have : Nonempty J := ⟨i⟩
  obtain ⟨k, g, hk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget TopCat) hc) x y).1 h
  exact hF (leOfHom g) hk

section Coherent

variable {J : Type w} [Category J] {F : J ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
include hc

/-- Every point of a colimit in `TopCat` lies in the image of an object of the diagram. -/
theorem iUnion_range_ι_of_isColimit : ⋃ j, (Set.range (c.ι.app j) : Set c.pt) = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ by
    have hc' := isColimitOfPreserves (forget TopCat) hc
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc' x
    exact Set.mem_iUnion.2 ⟨j, y, hy⟩

/-- A colimit in `TopCat` carries the topology coherent with the images of the objects of the
diagram. -/
theorem isCoherentWith_range_ι_of_isColimit :
    Topology.IsCoherentWith (Set.range fun j ↦ (Set.range (c.ι.app j) : Set c.pt)) :=
  .of_isClosed fun t ht ↦ (_root_.TopCat.isClosed_iff_of_isColimit _ hc t).2 fun j ↦
    (ht _ (Set.mem_range_self j)).preimage
      ((c.ι.app j).hom.continuous.subtype_mk Set.mem_range_self)

end Coherent

end TauCeti.TopCat
