/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Acyclic
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# The bounded derived category of an exact category

Let `E` be an exact structure on an additive category `C`. A complex in the homotopy category is
**bounded acyclic** when it is isomorphic to the homotopy class of a bounded complex which is
acyclic for `E` (`TauCeti.ExactStructure.acyclic`). By Neeman's lemma
(`TauCeti.ExactStructure.acyclic_mappingCone`), and since bounded and acyclic complexes are stable
under shifts, these objects form a triangulated subcategory of the homotopy category, and so of
the bounded homotopy category `Kᵇ(C)`. The **bounded derived category** `Dᵇ(E)` is the Verdier
quotient of `Kᵇ(C)` by it, with its localized triangulated structure (Bühler, Section 10;
Neeman).

The subcategory is defined as the closure under isomorphisms of the classes of bounded acyclic
complexes. When `C` is not idempotent complete, a complex homotopy equivalent to an acyclic one
need not itself be acyclic, so this closure is the subcategory used for the localization, and
it does not change the quotient (Bühler, Remark 10.5).

## Main definitions

* `TauCeti.ExactStructure.boundedAcyclic`: the bounded acyclic objects of the homotopy category,
  characterized by `TauCeti.ExactStructure.boundedAcyclic_iff`.
* `TauCeti.ExactStructure.acyclicBounded`: the same objects in `Kᵇ(C)`
  (`TauCeti.ExactStructure.acyclicBounded_iff`).
* `TauCeti.ExactStructure.BoundedDerivedCategory`: the bounded derived category `Dᵇ(E)`, with
  the quotient functor `TauCeti.ExactStructure.BoundedDerivedCategory.Q`.

## Main results

* The bounded acyclic objects form a triangulated subcategory.
* `Dᵇ(E)` is a triangulated category and `Q` is a triangulated functor.
* `TauCeti.ExactStructure.BoundedDerivedCategory.isZero_Q_obj_of_acyclicBounded`: bounded acyclic
  complexes become zero in `Dᵇ(E)`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 10.
* Amnon Neeman, *The derived category of an exact category*, J. Algebra **135** (1990),
  388--394.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- The objects of the homotopy category isomorphic to a bounded acyclic complex. -/
def boundedAcyclic : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun X ↦
  ∃ K : CochainComplex C ℤ, CochainComplex.bounded C K ∧ E.acyclic K ∧
    Nonempty (X ≅ (HomotopyCategory.quotient C (.up ℤ)).obj K)

/-- An object of the homotopy category is bounded acyclic exactly when it is isomorphic to the class
of a bounded acyclic complex. -/
theorem boundedAcyclic_iff (X : HomotopyCategory C (.up ℤ)) :
    E.boundedAcyclic X ↔ ∃ K : CochainComplex C ℤ, CochainComplex.bounded C K ∧ E.acyclic K ∧
      Nonempty (X ≅ (HomotopyCategory.quotient C (.up ℤ)).obj K) :=
  Iff.rfl

/-- The class of a bounded acyclic complex is bounded acyclic. -/
theorem boundedAcyclic_quotient_obj {K : CochainComplex C ℤ} (hb : CochainComplex.bounded C K)
    (ha : E.acyclic K) : E.boundedAcyclic ((HomotopyCategory.quotient C (.up ℤ)).obj K) :=
  ⟨K, hb, ha, ⟨Iso.refl _⟩⟩

instance : E.boundedAcyclic.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨K, hb, ha, ⟨e'⟩⟩ ↦ ⟨K, hb, ha, ⟨e.symm ≪≫ e'⟩⟩

instance : E.boundedAcyclic.ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient C (.up ℤ)).obj 0,
    Functor.map_isZero _ (isZero_zero _), 0,
    (CochainComplex.bounded_iff C 0).2 ⟨0, 0, inferInstance, inferInstance⟩,
    E.acyclic.prop_of_isZero (isZero_zero _), ⟨Iso.refl _⟩⟩

instance : E.boundedAcyclic.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ⟨K, hb, ha, ⟨e⟩⟩ ↦ ⟨K⟦n⟧,
    (CochainComplex.bounded C).le_shift n K hb, E.acyclic.le_shift n K ha,
    ⟨(shiftFunctor _ n).mapIso e ≪≫
      ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app K⟩⟩⟩

instance : E.boundedAcyclic.IsTriangulatedClosed₃ where
  ext₃' T hT := fun ⟨K₁, hb₁, ha₁, ⟨e₁⟩⟩ ⟨K₂, hb₂, ha₂, ⟨e₂⟩⟩ ↦ by
    obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
    refine ObjectProperty.le_isoClosure _ _ ⟨CochainComplex.mappingCone f,
      CochainComplex.bounded_mappingCone f hb₁ hb₂, E.acyclic_mappingCone f ha₁ ha₂,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f) e₁ e₂ ?_)⟩⟩
    -- The goal is stated through the triangle of the mapping cone; its first morphism is the
    -- class of `f`.
    change T.mor₁ ≫ e₂.hom = e₁.hom ≫ (HomotopyCategory.quotient C (.up ℤ)).map f
    rw [hf]
    simp

instance : E.boundedAcyclic.IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The bounded acyclic complexes, as a triangulated subcategory of the bounded homotopy category
`Kᵇ(C)`. -/
def acyclicBounded : ObjectProperty (HomotopyCategory.Bounded C) :=
  E.boundedAcyclic.inverseImage (HomotopyCategory.Bounded.ι C)

/-- An object of `Kᵇ(C)` is acyclic exactly when its image in the homotopy category is. -/
@[simp]
theorem acyclicBounded_iff (X : HomotopyCategory.Bounded C) :
    E.acyclicBounded X ↔ E.boundedAcyclic ((HomotopyCategory.Bounded.ι C).obj X) :=
  Iff.rfl

instance : E.acyclicBounded.IsTriangulated := by
  dsimp only [acyclicBounded]
  infer_instance

/-- The **bounded derived category** `Dᵇ(E)` of an exact category: the Verdier quotient of the
bounded homotopy category by the bounded acyclic complexes. -/
abbrev BoundedDerivedCategory :=
  E.acyclicBounded.trW.Localization

namespace BoundedDerivedCategory

/-- The Verdier quotient functor `Kᵇ(C) ⥤ Dᵇ(E)`. -/
noncomputable def Q : HomotopyCategory.Bounded C ⥤ E.BoundedDerivedCategory :=
  E.acyclicBounded.trW.Q

instance : (Q E).IsLocalization E.acyclicBounded.trW := by
  dsimp only [Q]
  infer_instance

noncomputable instance : Preadditive E.BoundedDerivedCategory :=
  Localization.preadditive (Q E) E.acyclicBounded.trW

instance : (Q E).Additive :=
  Localization.functor_additive (Q E) E.acyclicBounded.trW

noncomputable instance : HasZeroObject E.BoundedDerivedCategory :=
  (Q E).hasZeroObject_of_additive

noncomputable instance : HasShift E.BoundedDerivedCategory ℤ :=
  HasShift.localized (Q E) E.acyclicBounded.trW ℤ

noncomputable instance : (Q E).CommShift ℤ :=
  Functor.CommShift.localized (Q E) E.acyclicBounded.trW ℤ

instance (n : ℤ) : (shiftFunctor E.BoundedDerivedCategory n).Additive := by
  rw [Localization.functor_additive_iff (Q E) E.acyclicBounded.trW]
  exact Functor.additive_of_iso ((Q E).commShiftIso n)

noncomputable instance : Pretriangulated E.BoundedDerivedCategory :=
  Triangulated.Localization.pretriangulated (Q E) E.acyclicBounded.trW

instance : (Q E).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor (Q E) E.acyclicBounded.trW

instance : IsTriangulated E.BoundedDerivedCategory :=
  Triangulated.Localization.isTriangulated (Q E) E.acyclicBounded.trW

variable {E} in
/-- A bounded acyclic complex is zero in the bounded derived category. -/
lemma isZero_Q_obj_of_acyclicBounded {X : HomotopyCategory.Bounded C}
    (hX : E.acyclicBounded X) : IsZero ((Q E).obj X) := by
  -- The map from zero to `X` has cone `X`, which is acyclic, so it becomes invertible.
  have h : E.acyclicBounded.trW (0 : 0 ⟶ X) :=
    ObjectProperty.trW.mk _ (contractible_distinguished₁ X) hX
  have := Localization.inverts (Q E) _ _ h
  exact ((Q E).map_isZero (isZero_zero _)).of_iso (asIso ((Q E).map (0 : 0 ⟶ X))).symm

end BoundedDerivedCategory

end TauCeti.ExactStructure
