/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Groupoid.Rigid
public import TauCeti.CategoryTheory.Monoidal.Grading.Groupoid.SingleObj
public import TauCeti.CategoryTheory.Monoidal.Grading.Universal.UnitSummands

/-!
# Duality and rigidity in the universal grading group

In a rigid category with simple tensor unit `𝟙_ C`, exact pairings and duals invert universal
degrees without assuming finite semisimplicity
(`TauCeti.universalGradingGroup.degree_classOf_of_exactPairing_of_simple_unit`,
`degree_dual_of_simple_unit`). In a finite semisimple monoidal category `C` with
`[MonoidalPreadditive C]`, exact pairings invert universal degrees without `[Simple (𝟙_ C)]`
(`degree_classOf_of_exactPairing`, `degree_classOf_rightDual`). Under `[RigidCategory C]`, dual
simple classes have inverse degrees (`degree_dual`), and when `𝟙_ C` is simple every element of
`universalGradingGroup C` is the degree of a simple object (`degree_surjective`), making
`universalGradingGroup C` finite whenever there are finitely many simple classes.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §3.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti.universalGradingGroup

section SimpleUnit

/-- In an exact pairing of simple objects when `𝟙_ C` is simple, `degree (classOf Y)` is the
inverse of `degree (classOf X)`, without requiring finite semisimplicity. -/
theorem degree_classOf_of_exactPairing_of_simple_unit {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [MonoidalCategory C] [Simple (𝟙_ C)] {X Y : C} [ExactPairing X Y]
    [Simple X] [Simple Y] :
    degree (SimpleClasses.classOf Y) = (degree (SimpleClasses.classOf X))⁻¹ :=
  degree_classOf_eq_inv_of_hom_ne_zero degree_unit
    (coevaluation_ne_zero (Y := Y) (Simple.not_isZero X))

/-- When `𝟙_ C` is simple, dual simple objects have inverse universal degrees without requiring
finite semisimplicity. -/
@[simp] theorem degree_dual_of_simple_unit {C : Type u} [Category.{v} C] [Abelian C]
    [MonoidalCategory C] [RigidCategory C] [MonoidalPreadditive C] [Simple (𝟙_ C)]
    (S : SimpleClasses C) :
    degree S.dual = (degree S)⁻¹ := by
  rw [← SimpleClasses.classOf_repr S.dual,
    (SimpleClasses.classOf_eq_iff_nonempty_iso _ _).2 ⟨SimpleClasses.dualReprIso S⟩,
    degree_classOf_of_exactPairing_of_simple_unit (X := S.repr), SimpleClasses.classOf_repr]

end SimpleUnit

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [IsFiniteSemisimpleCategory C]

section ExactPairing

/-- In an exact pairing of simple objects, `degree (classOf Y)` is the inverse of
`degree (classOf X)`. -/
theorem degree_classOf_of_exactPairing {X Y : C} [ExactPairing X Y] [Simple X] [Simple Y] :
    degree (SimpleClasses.classOf Y) = (degree (SimpleClasses.classOf X))⁻¹ := by
  obtain ⟨I, hf⟩ := (UnitSimpleClasses.ne_zero_iff_exists_ι_comp_ne_zero _).1
    (coevaluation_ne_zero (Y := Y) (Simple.not_isZero X))
  exact degree_classOf_eq_inv_of_hom_ne_zero
    (degree_classOf_eq_one_of_hom_to_unit_ne_zero (UnitSimpleClasses.ι_ne_zero I)) hf

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

/-- Every element of the universal grading group is the degree of a simple object. -/
theorem degree_surjective :
    Function.Surjective (degree : SimpleClasses C → universalGradingGroup C) := fun x ↦ by
  obtain ⟨S, hL, hR, hg⟩ := universalGradingGroupoid.exists_degree_eq
    (universalGradingGroupoid.vertexGroupMulEquiv.symm x)
  have h := congrArg universalGradingGroupoid.vertexGroupMulEquiv hg
  rw [MulEquiv.apply_symm_apply,
    Subsingleton.elim hL.symm (Subsingleton.elim _ _),
    Subsingleton.elim hR (Subsingleton.elim _ _),
    universalGradingGroupoid.vertexGroupMulEquiv_degree] at h
  exact ⟨S, h.symm⟩

/-- Finitely many simple classes give a finite universal grading group. -/
instance [Finite (SimpleClasses C)] : Finite (universalGradingGroup C) :=
  Finite.of_equiv _ (universalGradingGroupoid.vertexGroupMulEquiv (C := C)).toEquiv

end Rigid

end TauCeti.universalGradingGroup
