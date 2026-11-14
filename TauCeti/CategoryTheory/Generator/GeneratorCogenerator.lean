/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Preadditive
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic

/-!
# Generator-cogenerators

An object `M` of a category is a **generator-cogenerator** (`TauCeti.IsGeneratorCogenerator`) when
it is both a separator and a coseparator (`CategoryTheory.IsSeparator`,
`CategoryTheory.IsCoseparator`): morphisms are distinguished by their composites with morphisms
out of `M`, and by their composites with morphisms into `M`. In the category `mod A` of finitely
generated modules over an Artin algebra these are the modules `M` with `A` and `D A` in `add M`
(`TauCeti/Algebra/Category/FGModuleCat/Generator/Cogenerator.lean`); their endomorphism rings are
the subject of the Morita-Tachikawa correspondence.

In any category, separators and coseparators are invariant under isomorphism and pass to every
object having them as a direct summand, so generator-cogenerators are invariant under isomorphism
and under adding direct summands, and an equivalence of categories carries them to
generator-cogenerators. Since separators of `Cᵒᵖ` are the coseparators of `C`, the notion is
self-dual: `op M` is a generator-cogenerator of `Cᵒᵖ` exactly when `M` is one of `C`.

In a preadditive category with finite biproducts, separators and coseparators also pass up
additive closures: if a separator `G` lies in `add M`, then `M` is a separator
(`CategoryTheory.IsSeparator.of_additiveClosure`), and dually.

## Main definitions

* `TauCeti.IsGeneratorCogenerator`: a separator and coseparator.

## Main results

* `CategoryTheory.IsSeparator.of_additiveClosure` and
  `CategoryTheory.IsCoseparator.of_additiveClosure`: `M` is a separator (coseparator) as soon as
  `add M` contains one.
* `CategoryTheory.IsSeparator.of_retract` and `CategoryTheory.IsCoseparator.of_retract`: an object
  having a separator (coseparator) as a direct summand is one.
* `TauCeti.IsGeneratorCogenerator.of_retract`: adding direct summands keeps a generator-cogenerator.
* `CategoryTheory.Equivalence.isGeneratorCogenerator_functor_obj_iff`: invariance under
  equivalences of categories.
* `TauCeti.isGeneratorCogenerator_op_iff`: generator-cogenerators are self-dual.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TauCeti

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **Separators are invariant under isomorphism.** -/
theorem IsSeparator.of_iso {G M : C} (hG : IsSeparator G) (e : G ≅ M) : IsSeparator M := by
  rw [isSeparator_iff_faithful_coyoneda_obj] at hG ⊢
  exact Functor.Faithful.of_iso (coyoneda.mapIso e.symm.op)

/-- **Coseparators are invariant under isomorphism.** -/
theorem IsCoseparator.of_iso {G M : C} (hG : IsCoseparator G) (e : G ≅ M) : IsCoseparator M := by
  rw [isCoseparator_iff_faithful_yoneda_obj] at hG ⊢
  exact Functor.Faithful.of_iso (yoneda.mapIso e)

/-- **Separators pass to objects having them as retracts**: if `M` is a separator and a direct
summand of `N`, then `N` is a separator. -/
theorem IsSeparator.of_retract {M N : C} (hM : IsSeparator M) (h : Retract M N) :
    IsSeparator N := by
  rw [isSeparator_def] at hM ⊢
  exact fun X Y f g hfg ↦ hM f g fun a ↦ by
    simpa [Category.assoc] using congrArg (h.i ≫ ·) (hfg (h.r ≫ a))

/-- **Coseparators pass to objects having them as retracts**: if `M` is a coseparator and a direct
summand of `N`, then `N` is a coseparator. -/
theorem IsCoseparator.of_retract {M N : C} (hM : IsCoseparator M) (h : Retract M N) :
    IsCoseparator N := by
  rw [isCoseparator_def] at hM ⊢
  exact fun X Y f g hfg ↦ hM f g fun a ↦ by
    simpa using congrArg (· ≫ h.r) (hfg (a ≫ h.i))

section Preadditive

variable [Preadditive C] [HasFiniteBiproducts C]

/-- **A separator in an additive closure makes a separator**: if `add M` contains a separator `G`,
then `M` is a separator. Every morphism out of `G` factors through finitely many copies of `M`. -/
theorem IsSeparator.of_additiveClosure {G M : C} (hG : IsSeparator G)
    (h : additiveClosure M G) : IsSeparator M := by
  obtain ⟨n, a, b, hab⟩ := additiveClosure_iff_exists_sum_comp_eq_id.1 h
  rw [Preadditive.isSeparator_iff] at hG ⊢
  refine fun X Y f hf ↦ hG f fun g ↦ ?_
  rw [← Category.id_comp g, ← hab, Preadditive.sum_comp, Preadditive.sum_comp]
  exact Finset.sum_eq_zero fun j _ ↦ by simp only [Category.assoc, hf, Limits.comp_zero]

/-- **A coseparator in an additive closure makes a coseparator**: if `add M` contains a coseparator
`G`, then `M` is a coseparator. Every morphism into `G` factors through finitely many copies of
`M`. -/
theorem IsCoseparator.of_additiveClosure {G M : C} (hG : IsCoseparator G)
    (h : additiveClosure M G) : IsCoseparator M := by
  obtain ⟨n, a, b, hab⟩ := additiveClosure_iff_exists_sum_comp_eq_id.1 h
  rw [Preadditive.isCoseparator_iff] at hG ⊢
  refine fun X Y f hf ↦ hG f fun g ↦ ?_
  rw [← Category.comp_id g, ← hab, Preadditive.comp_sum, Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun j _ ↦ by
    rw [← Category.assoc, ← Category.assoc, Category.assoc f, hf (g ≫ a j), Limits.zero_comp]

end Preadditive

end CategoryTheory

namespace TauCeti

variable {C : Type u} [Category.{v} C]

/-- `M` is a **generator-cogenerator**: a separator and a coseparator. In `mod A` these are the
modules that generate and cogenerate the category. -/
def IsGeneratorCogenerator (M : C) : Prop :=
  IsSeparator M ∧ IsCoseparator M

theorem isGeneratorCogenerator_iff {M : C} :
    IsGeneratorCogenerator M ↔ IsSeparator M ∧ IsCoseparator M :=
  Iff.rfl

theorem IsGeneratorCogenerator.isSeparator {M : C} (hM : IsGeneratorCogenerator M) :
    IsSeparator M :=
  hM.1

theorem IsGeneratorCogenerator.isCoseparator {M : C} (hM : IsGeneratorCogenerator M) :
    IsCoseparator M :=
  hM.2

/-- **Generator-cogenerators are invariant under isomorphism.** -/
theorem IsGeneratorCogenerator.of_iso {M N : C} (hM : IsGeneratorCogenerator M) (e : M ≅ N) :
    IsGeneratorCogenerator N :=
  ⟨hM.1.of_iso e, hM.2.of_iso e⟩

/-- **Equivalences carry generator-cogenerators to generator-cogenerators.** -/
theorem IsGeneratorCogenerator.of_equivalence {D : Type u'} [Category.{v'} D] {M : C}
    (hM : IsGeneratorCogenerator M) (e : C ≌ D) : IsGeneratorCogenerator (e.functor.obj M) :=
  ⟨hM.1.of_equivalence e, hM.2.of_equivalence e⟩

/-- **Generator-cogenerators are invariant under equivalences of categories.** -/
theorem _root_.CategoryTheory.Equivalence.isGeneratorCogenerator_functor_obj_iff {D : Type u'}
    [Category.{v'} D] (e : C ≌ D) (M : C) :
    IsGeneratorCogenerator (e.functor.obj M) ↔ IsGeneratorCogenerator M :=
  ⟨fun h ↦ (h.of_equivalence e.symm).of_iso (e.unitIso.app M).symm, fun h ↦ h.of_equivalence e⟩

/-- **Generator-cogenerators are self-dual**: `op M` is a generator-cogenerator of `Cᵒᵖ` exactly
when `M` is one of `C`. -/
@[simp]
theorem isGeneratorCogenerator_op_iff (M : C) :
    IsGeneratorCogenerator (op M) ↔ IsGeneratorCogenerator M := by
  simp only [isGeneratorCogenerator_iff, isSeparator_op_iff, isCoseparator_op_iff, and_comm]

/-- **Generator-cogenerators are self-dual**: `unop M` is a generator-cogenerator of `C` exactly
when `M` is one of `Cᵒᵖ`. -/
@[simp]
theorem isGeneratorCogenerator_unop_iff (M : Cᵒᵖ) :
    IsGeneratorCogenerator (unop M) ↔ IsGeneratorCogenerator M := by
  rw [← isGeneratorCogenerator_op_iff, op_unop]

/-- **Adding direct summands keeps a generator-cogenerator**: if `M` is a generator-cogenerator and
a direct summand of `N`, then `N` is a generator-cogenerator. -/
theorem IsGeneratorCogenerator.of_retract {M N : C} (hM : IsGeneratorCogenerator M)
    (h : Retract M N) : IsGeneratorCogenerator N :=
  ⟨hM.1.of_retract h, hM.2.of_retract h⟩

variable [Preadditive C] [HasFiniteBiproducts C]

/-- **Adding objects to a generator-cogenerator**: if `add M` contains a generator-cogenerator, then
`M` is one. -/
theorem IsGeneratorCogenerator.of_additiveClosure {G M : C} (hG : IsGeneratorCogenerator G)
    (h : additiveClosure M G) : IsGeneratorCogenerator M :=
  ⟨hG.1.of_additiveClosure h, hG.2.of_additiveClosure h⟩

end TauCeti
