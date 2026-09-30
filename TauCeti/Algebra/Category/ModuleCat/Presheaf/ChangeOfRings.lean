/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings

/-!
# Monoidal change of rings for presheaves of modules

For presheaves of commutative rings `R` and `S` and a morphism `α : R ⟶ S`, restriction of scalars
from presheaves of `S`-modules to presheaves of
`R`-modules is lax symmetric monoidal. Its unit map is `α` itself, sectionwise, and its tensor map
sends a pure tensor `m ⊗ n` to the same pure tensor, now regarded over the smaller ring.

Combining it with precomposition, the pushforward of presheaves of modules along a functor and
a morphism of presheaves of commutative rings is lax symmetric monoidal. Consequently its left
adjoint, the pullback, carries a canonical oplax tensor comparison.

## Main declarations

* `PresheafOfModules.restrictScalarsLaxMonoidal`: its lax monoidal structure;
* `PresheafOfModules.restrictScalarsLaxBraided`: compatibility with the symmetric braiding;
* `PresheafOfModules.pushforwardLaxMonoidal`: Mathlib's
  `PresheafOfModulesOfCommRing.pushforward` is lax monoidal;
* `PresheafOfModules.pushforwardLaxBraided`: it is moreover lax symmetric monoidal.

All structure maps and coherence laws are obtained sectionwise from Mathlib's lax monoidal
restriction of scalars for `ModuleCat`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u v v' w w'

noncomputable section

namespace PresheafOfModules

variable {C : Type v} {D : Type v'} [Category.{w} C] [Category.{w'} D]

variable {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (α : R ⟶ S)

/-- The unit map for restriction of scalars, given sectionwise by the coefficient morphism. -/
def restrictScalarsUnit :
    𝟙_ (PresheafOfModulesOfCommRing.{u} R) ⟶
      (PresheafOfModulesOfCommRing.restrictScalars α).obj
        (𝟙_ (PresheafOfModulesOfCommRing.{u} S)) :=
  PresheafOfModulesOfCommRing.homMk
    (fun X ↦ Functor.LaxMonoidal.ε (ModuleCat.restrictScalars (α.app X).hom))
    (fun {X Y} f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      erw [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply,
        ModuleCat.restrictScalars_η, ModuleCat.comp_apply, ModuleCat.restrictScalars_η]
      exact congr($(α.naturality f).hom r))

/-- On sections over `X`, the unit map for restriction of scalars is `α.app X`. -/
@[simp]
lemma restrictScalarsUnit_app_apply (X : Cᵒᵖ) (r : R.obj X) :
    (restrictScalarsUnit α).app' X r = α.app X r :=
  ModuleCat.restrictScalars_η (α.app X).hom r

/-- The tensor map for restriction of scalars, given sectionwise by the canonical balanced map. -/
def restrictScalarsTensor (M N : PresheafOfModulesOfCommRing.{u} S) :
    (PresheafOfModulesOfCommRing.restrictScalars α).obj M ⊗
        (PresheafOfModulesOfCommRing.restrictScalars α).obj N ⟶
      (PresheafOfModulesOfCommRing.restrictScalars α).obj (M ⊗ N) :=
  PresheafOfModulesOfCommRing.homMk
    (fun X ↦ Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (α.app X).hom)
      (M.obj X) (N.obj X))
    (fun {X Y} f ↦ by
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m n
      erw [ModuleCat.comp_apply,
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
        ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalars_μ_tmul,
        ModuleCat.comp_apply, ModuleCat.restrictScalars_μ_tmul,
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
      rfl)

/-- On sections over `X`, the tensor map for restriction of scalars sends the pure tensor
`m ⊗ₜ n` over `R.obj X` to the same pure tensor over `S.obj X`. -/
@[simp]
lemma restrictScalarsTensor_app_tmul (M N : PresheafOfModulesOfCommRing.{u} S)
    (X : Cᵒᵖ) (m : M.obj X) (n : N.obj X) :
    (restrictScalarsTensor α M N).app' X (m ⊗ₜ[R.obj X] n) =
      m ⊗ₜ[S.obj X] n :=
  ModuleCat.restrictScalars_μ_tmul (α.app X).hom (M.obj X) (N.obj X) m n

/-- Restriction of scalars for presheaves of modules is lax monoidal. -/
instance restrictScalarsLaxMonoidal :
    (PresheafOfModulesOfCommRing.restrictScalars α).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom (restrictScalarsUnit α) (restrictScalarsTensor α)
    (fun f g ↦ by
      apply _root_.PresheafOfModules.hom_ext
      intro X
      exact Functor.LaxMonoidal.μ_natural
        (F := ModuleCat.restrictScalars (α.app X).hom) (f.app' X) (g.app' X))
    (fun M N P ↦ by
      apply _root_.PresheafOfModules.hom_ext
      intro X
      exact Functor.LaxMonoidal.associativity
        (F := ModuleCat.restrictScalars (α.app X).hom) (M.obj X) (N.obj X) (P.obj X))
    (fun M ↦ by
      apply _root_.PresheafOfModules.hom_ext
      intro X
      exact Functor.LaxMonoidal.left_unitality
        (F := ModuleCat.restrictScalars (α.app X).hom) (M.obj X))
    (fun M ↦ by
      apply _root_.PresheafOfModules.hom_ext
      intro X
      exact Functor.LaxMonoidal.right_unitality
        (F := ModuleCat.restrictScalars (α.app X).hom) (M.obj X))

/-- Restriction of scalars preserves the symmetric braiding. -/
instance restrictScalarsLaxBraided :
    (PresheafOfModulesOfCommRing.restrictScalars α).LaxBraided where
  braided M N := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    exact Functor.LaxBraided.braided (F := ModuleCat.restrictScalars (α.app X).hom)
      (M.obj X) (N.obj X)

/-- Pushforward of presheaves of modules is lax monoidal. -/
instance pushforwardLaxMonoidal (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : S ⟶ F.op ⋙ R) :
    (PresheafOfModulesOfCommRing.pushforward.{u} α).LaxMonoidal :=
  inferInstanceAs (PresheafOfModulesOfCommRing.pushforward₀ F R ⋙
    PresheafOfModulesOfCommRing.restrictScalars α).LaxMonoidal

/-- On sections over `X`, the unit map for pushforward is `α.app X`. -/
@[simp]
lemma pushforward_ε_app_apply (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {S : Cᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ F.op ⋙ R) (X : Cᵒᵖ) (r : S.obj X) :
    (Functor.LaxMonoidal.ε (PresheafOfModulesOfCommRing.pushforward.{u} α)).app' X r =
      α.app X r :=
  restrictScalarsUnit_app_apply α X r

/-- On sections over `X`, the tensor map for pushforward sends the pure tensor `m ⊗ₜ n` over
`S.obj X` to the same pure tensor over `R.obj (op (F.obj X.unop))`. -/
@[simp]
lemma pushforward_μ_app_tmul (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {S : Cᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ F.op ⋙ R)
    (M N : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ)
    (m : M.obj (Opposite.op (F.obj X.unop))) (n : N.obj (Opposite.op (F.obj X.unop))) :
    (Functor.LaxMonoidal.μ (PresheafOfModulesOfCommRing.pushforward.{u} α) M N).app' X
        (m ⊗ₜ[S.obj X] n) =
      m ⊗ₜ[R.obj (Opposite.op (F.obj X.unop))] n :=
  restrictScalarsTensor_app_tmul α ((PresheafOfModulesOfCommRing.pushforward₀ F R).obj M)
    ((PresheafOfModulesOfCommRing.pushforward₀ F R).obj N) X m n

/-- Pushforward of presheaves of modules preserves the symmetric braiding. -/
instance pushforwardLaxBraided (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : S ⟶ F.op ⋙ R) :
    (PresheafOfModulesOfCommRing.pushforward.{u} α).LaxBraided where
  braided M N := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    exact Functor.LaxBraided.braided (F := ModuleCat.restrictScalars (α.app X).hom)
      (M.obj _) (N.obj _)

end PresheafOfModules

end

end TauCeti
