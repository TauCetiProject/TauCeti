/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.CategoryTheory.Monoidal.Internal.Module

/-!
# Sections of commutative algebras of modules on schemes

A commutative monoid object in `X.Modules` has a commutative `Γ(X, U)`-algebra of sections
on each open `U`. Restriction is a ring homomorphism, giving a presheaf of commutative rings
under the structure presheaf of `X`.

These constructions use Mathlib's `Functor.mapCommMon` and the equivalence between monoid
objects in modules and algebras, applied to the lax braided sections functor.
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon X.Modules)

/-- The sections over `U` of a commutative `𝒪ₓ`-algebra, as a commutative monoid object in
`Γ(X, U)`-modules: the image of `A` under the lax braided sections functor. -/
abbrev _root_.CategoryTheory.CommMon.sectionsCommMon (U : X.Opens) :
    CommMon (ModuleCat.{u} Γ(X, U)) :=
  (Scheme.Modules.sectionsFunctor U).mapCommMon.obj A

/-- The sections of a commutative `𝒪ₓ`-algebra over an open form a commutative ring. Its
multiplication is the monoid multiplication of `A` applied to the image of `x ⊗ₜ y` in the sections
of the tensor product (`CategoryTheory.CommMon.sections_mul_def`). -/
instance _root_.CategoryTheory.CommMon.commRingSections (U : X.Opens) : CommRing Γ(A.X, U) :=
  ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing (A.sectionsCommMon U).X

/-- The sections of a commutative `𝒪ₓ`-algebra over an open `U` form a `Γ(X, U)`-algebra, whose
scalar multiplication is that of the sections of the underlying `𝒪ₓ`-module. -/
instance _root_.CategoryTheory.CommMon.algebraSections (U : X.Opens) :
    Algebra Γ(X, U) Γ(A.X, U) :=
  ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ (A.sectionsCommMon U).X

/-- The product of two sections of a commutative `𝒪ₓ`-algebra is the multiplication of `A`
applied to the image of their tensor product under the tensor map of the sections functor. -/
lemma _root_.CategoryTheory.CommMon.sections_mul_def (U : X.Opens) (x y : Γ(A.X, U)) :
    x * y = (MonObj.mul (X := A.X)).app U
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) A.X A.X (x ⊗ₜ y)) :=
  (rfl)

/-- The structure map `Γ(X, U) → Γ(A.X, U)` of a commutative `𝒪ₓ`-algebra is the unit of `A` on
sections over `U`. -/
lemma _root_.CategoryTheory.CommMon.sections_algebraMap_def (U : X.Opens) (r : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(A.X, U) r = (MonObj.one (X := A.X)).app U
      (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r) :=
  (rfl)

/-- Restriction of sections of a commutative `𝒪ₓ`-algebra along an inclusion of opens `V ≤ U`,
as a ring homomorphism. -/
def _root_.CategoryTheory.CommMon.restrictSections {U V : X.Opens} (i : V ⟶ U) :
    Γ(A.X, U) →+* Γ(A.X, V) where
  toFun := A.X.presheaf.map i.op
  map_one' := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    -- The unit of sections is `η[A.X]` applied to `1`; both maps commute with restriction.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.one (X := A.X)).val i.op
      ((Functor.LaxMonoidal.ε F).app' (op U) (1 : Γ(X, U)))
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) i.op (1 : Γ(X, U))
    exact h₁.symm.trans (congrArg _ (h₂.symm.trans
      (congrArg _ (map_one (X.presheaf.map i.op).hom))))
  map_mul' x y := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    -- The product is `μ[A.X]` applied to the tensor map of `F`; both commute with restriction,
    -- and restriction of the sectionwise tensor product sends `x ⊗ₜ y` to the pure tensor of
    -- the restrictions.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.mul (X := A.X)).val i.op
      ((Functor.LaxMonoidal.μ F A.X A.X).app' (op U) (x ⊗ₜ y))
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.μ F A.X A.X) i.op (x ⊗ₜ y)
    exact h₁.symm.trans (congrArg _ h₂.symm)
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
lemma _root_.CategoryTheory.CommMon.restrictSections_apply {U V : X.Opens} (i : V ⟶ U)
    (x : Γ(A.X, U)) :
    A.restrictSections i x = A.X.presheaf.map i.op x :=
  (rfl)

/-- The presheaf of commutative rings of sections of a commutative `𝒪ₓ`-algebra. -/
@[expose]
def _root_.CategoryTheory.CommMon.sectionsPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of Γ(A.X, U.unop)
  map i := CommRingCat.ofHom (A.restrictSections i.unop)
  map_id U := by
    ext x
    exact congr($(A.X.presheaf.map_id U) x)
  map_comp i j := by
    ext x
    exact congr($(A.X.presheaf.map_comp i j) x)

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheaf_obj (U : X.Opensᵒᵖ) :
    A.sectionsPresheaf.obj U = CommRingCat.of Γ(A.X, U.unop) :=
  (rfl)

@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheaf_map {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    A.sectionsPresheaf.map i = CommRingCat.ofHom (A.restrictSections i.unop) :=
  (rfl)

/-- The structure morphism from the structure presheaf of `X` to the presheaf of sections of a
commutative `𝒪ₓ`-algebra, given on each open by the algebra map. -/
def _root_.CategoryTheory.CommMon.toSectionsPresheaf : X.presheaf ⟶ A.sectionsPresheaf where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) Γ(A.X, U.unop))
  naturality {U V} i := by
    let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
      _root_.SheafOfModules.forget _
    let _ : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal X.sheaf
    ext r
    -- The algebra map is `η[A.X]` after the unit map of `F`; both commute with restriction.
    have h₁ := PresheafOfModules.naturality_apply (MonObj.one (X := A.X)).val i
      ((Functor.LaxMonoidal.ε F).app' U r)
    have h₂ := PresheafOfModules.naturality_apply (Functor.LaxMonoidal.ε F) i r
    exact (congrArg _ h₂).trans h₁

@[simp]
lemma _root_.CategoryTheory.CommMon.toSectionsPresheaf_app (U : X.Opensᵒᵖ) :
    A.toSectionsPresheaf.app U = CommRingCat.ofHom (algebraMap Γ(X, U.unop) Γ(A.X, U.unop)) :=
  (rfl)

end

end TauCeti
