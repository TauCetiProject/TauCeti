/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-!
# Monoidal change of rings for presheaves of modules

For presheaves of commutative rings `R` and `S` and a morphism `α : R ⟶ S`, restriction of scalars
from presheaves of `S`-modules to presheaves of
`R`-modules is lax symmetric monoidal. Its unit map is `α` itself, sectionwise, and its tensor map
sends a pure tensor `m ⊗ n` to the same pure tensor, now regarded over the smaller ring.

This is the presheaf-level change-of-rings input for the monoidal pullback of sheaves of modules.
After combining it with precomposition, the pushforward right adjoint is lax monoidal; the
left-adjoint pullback therefore has a canonical oplax tensor comparison. Proving that comparison
invertible after sheafification is the remaining step toward strong symmetric monoidal pullback.

## Main declarations

* `PresheafOfModules.restrictScalarsLaxMonoidal`: its lax monoidal structure;
* `PresheafOfModules.restrictScalarsLaxBraided`: compatibility with the symmetric braiding;
* `PresheafOfModules.pushforward`: pushforward along a ringed-functor morphism;
* `PresheafOfModules.pushforwardLaxBraided`: pushforward is lax symmetric monoidal.

No formalization is vendored. The construction is obtained sectionwise from Mathlib's lax
monoidal restriction of scalars for `ModuleCat`.
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

private lemma component_ε_apply (X : Cᵒᵖ) (r : R.obj X) :
    Functor.LaxMonoidal.ε (ModuleCat.restrictScalars (α.app X).hom) r = α.app X r :=
  ModuleCat.restrictScalars_η (α.app X).hom r

private lemma component_μ_tmul (X : Cᵒᵖ) (M N : ModuleCat.{u} (S.obj X))
    (m : M) (n : N) :
    Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (α.app X).hom) M N
        (m ⊗ₜ[R.obj X] n) = m ⊗ₜ[S.obj X] n :=
  ModuleCat.restrictScalars_μ_tmul (α.app X).hom M N m n

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
        component_ε_apply, ModuleCat.comp_apply, component_ε_apply]
      exact congr($(α.naturality f).hom r))

@[simp]
lemma restrictScalarsUnit_app_apply (X : Cᵒᵖ) (r : R.obj X) :
    (restrictScalarsUnit α).app' X r = α.app X r :=
  component_ε_apply α X r

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
        ModuleCat.restrictScalars.map_apply, component_μ_tmul,
        ModuleCat.comp_apply, component_μ_tmul,
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
      rfl)

@[simp]
lemma restrictScalarsTensor_app_tmul (M N : PresheafOfModulesOfCommRing.{u} S)
    (X : Cᵒᵖ) (m : M.obj X) (n : N.obj X) :
    (restrictScalarsTensor α M N).app' X (m ⊗ₜ[R.obj X] n) =
      m ⊗ₜ[S.obj X] n :=
  component_μ_tmul α X (M.obj X) (N.obj X) m n

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
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl

/-- Pushforward of presheaves of modules along a functor of sites and a morphism of coefficient
presheaves, factored as precomposition followed by restriction of scalars. -/
abbrev pushforward (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : S ⟶ F.op ⋙ R) :
    PresheafOfModulesOfCommRing.{u} R ⥤ PresheafOfModulesOfCommRing.{u} S :=
  PresheafOfModulesOfCommRing.pushforward₀ F R ⋙
    PresheafOfModulesOfCommRing.restrictScalars α

/-- Pushforward of presheaves of modules is lax monoidal. -/
instance pushforwardLaxMonoidal (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : S ⟶ F.op ⋙ R) :
    (pushforward F α).LaxMonoidal := inferInstance

/-- Pushforward of presheaves of modules preserves the symmetric braiding. -/
instance pushforwardLaxBraided (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}}
    {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : S ⟶ F.op ⋙ R) :
    (pushforward F α).LaxBraided where
  braided M N := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl

end PresheafOfModules

end

end TauCeti
