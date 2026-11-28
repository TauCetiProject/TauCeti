/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.HomotopyCategory.Functor

/-!
# Adjunctions on homotopy categories

An adjunction of additive functors descends from homological complexes to homotopy categories
of any complex shape. The unit and counit are the classes of the degreewise unit and counit.
-/

public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  {ι : Type*} (c : ComplexShape ι)

/-- An adjunction of additive functors descends to homotopy categories of any complex shape. -/
def mapHomotopyCategory : F.mapHomotopyCategory c ⊣ G.mapHomotopyCategory c where
  unit := Quotient.natTransLift _
    (Functor.whiskerRight (adj.mapHomologicalComplex c).unit (HomotopyCategory.quotient C c))
  counit := Quotient.natTransLift _
    (Functor.whiskerRight (adj.mapHomologicalComplex c).counit (HomotopyCategory.quotient D c))
  left_triangle_components K := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    -- The quotient lift computes componentwise; express both factors as quotient maps.
    change (HomotopyCategory.quotient D c).map _ ≫ (HomotopyCategory.quotient D c).map _ = _
    simp only [HomotopyCategory.quotient_obj_as]
    rw [← Functor.map_comp, (adj.mapHomologicalComplex c).left_triangle_components]
    exact (HomotopyCategory.quotient D c).map_id _
  right_triangle_components K := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    -- The quotient lift computes componentwise; express both factors as quotient maps.
    change (HomotopyCategory.quotient C c).map _ ≫ (HomotopyCategory.quotient C c).map _ = _
    simp only [HomotopyCategory.quotient_obj_as]
    rw [← Functor.map_comp, (adj.mapHomologicalComplex c).right_triangle_components]
    exact (HomotopyCategory.quotient C c).map_id _

/-- The unit on homotopy categories is the class of the degreewise unit on complexes. -/
@[simp]
lemma mapHomotopyCategory_unit_app (K : HomologicalComplex C c) :
    (adj.mapHomotopyCategory c).unit.app ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.quotient C c).map ((adj.mapHomologicalComplex c).unit.app K) := (rfl)

/-- The counit on homotopy categories is the class of the degreewise counit on complexes. -/
@[simp]
lemma mapHomotopyCategory_counit_app (K : HomologicalComplex D c) :
    (adj.mapHomotopyCategory c).counit.app ((HomotopyCategory.quotient D c).obj K) =
      (HomotopyCategory.quotient D c).map ((adj.mapHomologicalComplex c).counit.app K) := (rfl)

end CategoryTheory.Adjunction
