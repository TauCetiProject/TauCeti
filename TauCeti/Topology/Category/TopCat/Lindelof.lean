/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Lindelöf colimits in `TopCat`

The corner of a pushout square in `TopCat` is a quotient of the disjoint union of the two sides
opposite the source, and the colimit of a diagram is a quotient of the disjoint union of its
objects. Hence attaching a Lindelöf space to a Lindelöf space gives a Lindelöf space
(`TauCeti.TopCat.lindelofSpace_of_isPushout`), and the colimit of a countable diagram of Lindelöf
spaces is Lindelöf (`TauCeti.TopCat.lindelofSpace_of_isColimit`).
-/

public section

open CategoryTheory Limits

universe w u

namespace TauCeti.TopCat

/-- Attaching a Lindelöf space `B` to a Lindelöf space `X` gives a Lindelöf space: the corner of
a pushout square in `TopCat` is Lindelöf when the two sides opposite the source are. -/
theorem lindelofSpace_of_isPushout {A B X P : TopCat.{u}} {g : A ⟶ X} {m : A ⟶ B} {f : X ⟶ P}
    {g₂ : B ⟶ P} (sq : IsPushout g m f g₂) [LindelofSpace X] [LindelofSpace B] :
    LindelofSpace P := by
  refine LindelofSpace.of_continuous_surjective (f := Sum.elim f g₂)
    (f.hom.continuous.sumElim g₂.hom.continuous) fun p ↦ ?_
  obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ := Types.eq_or_eq_of_isPushout ((forget TopCat).map_isPushout sq) p
  exacts [⟨.inl x, rfl⟩, ⟨.inr b, rfl⟩]

/-- The colimit of a countable diagram of Lindelöf spaces in `TopCat` is Lindelöf. -/
theorem lindelofSpace_of_isColimit {J : Type w} [SmallCategory J] [Countable J]
    {F : J ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c) [∀ j, LindelofSpace (F.obj j)] :
    LindelofSpace c.pt := by
  refine LindelofSpace.of_continuous_surjective (f := fun p : Σ j, F.obj j ↦ c.ι.app p.1 p.2)
    (continuous_sigma fun j ↦ (c.ι.app j).hom.continuous) fun p ↦ ?_
  obtain ⟨j, x, rfl⟩ :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) p
  exact ⟨⟨j, x⟩, rfl⟩

end TauCeti.TopCat
