/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Evaluation of presheaves of modules is monoidal

Let `R` be a presheaf of commutative rings on a category `C` and `X` an object of `Cᵒᵖ`. The tensor
product of presheaves of `R`-modules is computed sectionwise, so evaluation at `X`, valued in
modules over the commutative ring `R.obj X`, is a strong monoidal functor whose unit and tensor
comparisons are identities.

Composed with the lax monoidal inclusion of sheaves of modules into presheaves of modules, this
makes taking sections over an object lax monoidal; over a terminal object this is the global
sections functor.

## Main declarations

* `TauCeti.PresheafOfModulesOfCommRing.evaluation`: evaluation at `X`, as a functor to
  `ModuleCat (R.obj X)`;
* `TauCeti.PresheafOfModulesOfCommRing.evaluationMonoidal`: its monoidal structure.
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Evaluation at `X` of presheaves of modules over a presheaf of commutative rings, valued in
modules over the commutative ring `R.obj X`. This is `PresheafOfModules.evaluation`, with its
target written as `ModuleCat (R.obj X)` so that the monoidal structure of that category applies. -/
abbrev evaluation (X : Cᵒᵖ) :
    PresheafOfModulesOfCommRing.{u} R ⥤ ModuleCat.{u} (R.obj X) :=
  PresheafOfModules.evaluation _ X

/-- Evaluation of presheaves of modules is monoidal: the tensor product of presheaves of modules
is computed sectionwise, so the unit and tensor comparisons are identities. -/
instance evaluationMonoidal (X : Cᵒᵖ) : (evaluation (R := R) X).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      associativity := fun _ _ _ ↦ by
        apply ModuleCat.MonoidalCategory.tensor_ext₃'
        intros
        rfl
      left_unitality := fun _ ↦ by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intros
        rfl
      right_unitality := fun _ ↦ by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intros
        rfl }

variable (X : Cᵒᵖ)

/-- The unit comparison of evaluation is the identity. -/
@[simp]
lemma evaluation_ε : ε (evaluation (R := R) X) = 𝟙 _ :=
  rfl

/-- The inverse unit comparison of evaluation is the identity. -/
@[simp]
lemma evaluation_η : η (evaluation (R := R) X) = 𝟙 _ :=
  rfl

/-- The tensor comparison of evaluation is the identity. -/
@[simp]
lemma evaluation_μ (M N : PresheafOfModulesOfCommRing.{u} R) :
    μ (evaluation X) M N = 𝟙 _ :=
  rfl

/-- The inverse tensor comparison of evaluation is the identity. -/
@[simp]
lemma evaluation_δ (M N : PresheafOfModulesOfCommRing.{u} R) :
    δ (evaluation X) M N = 𝟙 _ :=
  rfl

end PresheafOfModulesOfCommRing

end

end TauCeti
