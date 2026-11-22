/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.UnitDegree
public import TauCeti.CategoryTheory.Simple.Rigid

/-!
# Duality and rigidity in the universal grading group

In a finite semisimple monoidal category `C` with `[MonoidalPreadditive C]`, exact pairings invert
universal degrees (`TauCeti.universalGradingGroup.degree_classOf_of_exactPairing`,
`degree_classOf_rightDual`). Under `[RigidCategory C]`, dual simple classes have inverse degrees
without assuming `[Simple (𝟙_ C)]` (`degree_dual`), and when `𝟙_ C` is simple every element of
`universalGradingGroup C` is the degree of a simple object (`degree_surjective`), making
`universalGradingGroup C` finite whenever there are finitely many simple classes.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti.universalGradingGroup

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [IsFiniteSemisimpleCategory C]

section ExactPairing

/-- In an exact pairing of simple objects, `degree (classOf Y)` is the inverse of
`degree (classOf X)`. -/
theorem degree_classOf_of_exactPairing {X Y : C} [ExactPairing X Y] [Simple X] [Simple Y] :
    degree (SimpleClasses.classOf Y) = (degree (SimpleClasses.classOf X))⁻¹ := by
  obtain ⟨I, hf⟩ := (UnitSimpleClasses.ne_zero_iff_exists_ι_comp_ne_zero _).1
    (coevaluation_ne_zero (Y := Y) (Simple.not_isZero X))
  have h := degree_classOf_eq_mul (UnitSimpleClasses.ι I ≫ η_ X Y) hf
  rw [degree_classOf_eq_one_of_hom_to_unit_ne_zero (UnitSimpleClasses.ι_ne_zero I)] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The right dual of a simple object has inverse universal degree. -/
@[simp] theorem degree_classOf_rightDual (X : C) [HasRightDual X] [Simple X] [Simple Xᘁ] :
    degree (SimpleClasses.classOf Xᘁ) = (degree (SimpleClasses.classOf X))⁻¹ :=
  degree_classOf_of_exactPairing

end ExactPairing

section Rigid

variable [RigidCategory C] [MonoidalPreadditive C]

/-- Dual simple objects have inverse universal degrees. -/
@[simp] theorem degree_dual (S : SimpleClasses C) : degree S.dual = (degree S)⁻¹ := by
  rw [← SimpleClasses.classOf_repr S.dual,
    (SimpleClasses.classOf_eq_iff_nonempty_iso _ _).2 ⟨SimpleClasses.dualReprIso S⟩,
    degree_classOf_rightDual S.repr, SimpleClasses.classOf_repr]

variable [Simple (𝟙_ C)]

/-- Every element of the universal grading group is the degree of a simple object. Thus the
universal assignment is faithful, rather than merely generating its target group. -/
theorem degree_surjective :
    Function.Surjective (degree : SimpleClasses C → universalGradingGroup C) := by
  let H : Subgroup (universalGradingGroup C) :=
    { carrier := Set.range degree, one_mem' := ⟨SimpleClasses.classOf (𝟙_ C), degree_unit⟩
      inv_mem' := by rintro _ ⟨S, rfl⟩; exact ⟨S.dual, degree_dual S⟩
      mul_mem' := by
        rintro _ _ ⟨S, rfl⟩ ⟨T, rfl⟩
        obtain ⟨W, _, f, hf⟩ := exists_simple_hom_ne_zero
          (not_isZero_tensorObj (Simple.not_isZero S.repr) (Simple.not_isZero T.repr))
        let b := SimpleClasses.classOfReprIso W
        have hbf : b.hom ≫ f ≠ 0 := fun h ↦ hf (by simpa using b.inv ≫= h)
        exact ⟨SimpleClasses.classOf W, degree_mul S T _ _ hbf⟩ }
  exact fun x ↦ mem_subgroup_of_degree_mem (H := H) (fun S ↦ ⟨S, rfl⟩) x

/-- Finitely many simple classes give a finite universal grading group. -/
instance [Finite (SimpleClasses C)] : Finite (universalGradingGroup C) :=
  Finite.of_surjective degree degree_surjective

end Rigid

end TauCeti.universalGradingGroup
