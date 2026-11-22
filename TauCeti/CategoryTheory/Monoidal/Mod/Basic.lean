/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Basic constructions for internal module objects

This file provides isomorphism constructors and basic simp lemmas for Mathlib's `CategoryTheory.Mod`
of internal module objects, and transports internal actions along lax monoidal functors.

An isomorphism between the underlying objects of two `A`-modules whose forward morphism is
equivariant lifts to an isomorphism in `Mod D A` (`CategoryTheory.Mod.mkIso'`,
`CategoryTheory.Mod.mkIso`, following `CategoryTheory.Mon.mkIso'` and `CategoryTheory.Mon.mkIso`);
in particular, two `A`-module structures on the same object with equal action maps give isomorphic
objects of `Mod D A` via the identity (`CategoryTheory.Mod.isoOfSmulEq`), and
`CategoryTheory.Mod.comap_obj_smul` records the restricted action of `(Mod.comap f).obj M`.

A lax monoidal functor carries an action of a monoid object to an action of the image
monoid object (`CategoryTheory.Functor.modObjObj`, following `CategoryTheory.Functor.monObjObj`):
the action map is the tensorator followed by the image of the original action, and equivariant
morphisms remain equivariant (`CategoryTheory.Functor.modObjObj_isModHom`). This applies, in
particular, to passing from algebra coactions to actions on affine schemes by a monoidal spectrum
functor.
-/

public section

open CategoryTheory MonoidalCategory MonoidalLeftAction MonObj
open Functor.LaxMonoidal
open scoped Obj

namespace CategoryTheory.Mod

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]
  {A : C} [MonObj A]

/-- Construct an isomorphism of module objects from a module isomorphism between the underlying
objects. -/
def mkIso' {M N : Mod D A} (e : M.X ≅ N.X) [h : IsModHom A e.hom] : M ≅ N where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩

-- The body of `mkIso'` is not exposed, so its projections are proved with `by rfl`.
@[simp]
theorem mkIso'_hom_hom {M N : Mod D A} (e : M.X ≅ N.X) [IsModHom A e.hom] :
    (mkIso' e).hom.hom = e.hom := by
  rfl

@[simp]
theorem mkIso'_inv_hom {M N : Mod D A} (e : M.X ≅ N.X) [IsModHom A e.hom] :
    (mkIso' e).inv.hom = e.inv := by
  rfl

/-- Construct an isomorphism of module objects from an isomorphism between the underlying objects,
checking equivariance only in the forward direction. -/
def mkIso {M N : Mod D A} (e : M.X ≅ N.X)
    (smul_hom : γ[A,M.X] ≫ e.hom = A ⊴ₗ e.hom ≫ γ[A,N.X] := by cat_disch) : M ≅ N :=
  mkIso' e (h := ⟨smul_hom⟩)

@[simp]
theorem mkIso_hom_hom {M N : Mod D A} (e : M.X ≅ N.X)
    (smul_hom : γ[A,M.X] ≫ e.hom = A ⊴ₗ e.hom ≫ γ[A,N.X]) :
    (mkIso e smul_hom).hom.hom = e.hom := by
  rfl

@[simp]
theorem mkIso_inv_hom {M N : Mod D A} (e : M.X ≅ N.X)
    (smul_hom : γ[A,M.X] ≫ e.hom = A ⊴ₗ e.hom ≫ γ[A,N.X]) :
    (mkIso e smul_hom).inv.hom = e.inv := by
  rfl

/-- Two `A`-module structures on the same object `X` with equal action maps give isomorphic objects
of `Mod D A` via `𝟙 X`. -/
def isoOfSmulEq {X : D} (m₁ m₂ : ModObj A X) (h : m₁.smul = m₂.smul) :
    ({ X := X, mod := m₁ } : Mod D A) ≅ { X := X, mod := m₂ } :=
  mkIso (M := { X := X, mod := m₁ }) (N := { X := X, mod := m₂ }) (Iso.refl X) (by simp [h])

@[simp]
theorem isoOfSmulEq_hom_hom {X : D} (m₁ m₂ : ModObj A X) (h : m₁.smul = m₂.smul) :
    (isoOfSmulEq m₁ m₂ h).hom.hom = 𝟙 X := by
  simp [isoOfSmulEq]

@[simp]
theorem isoOfSmulEq_inv_hom {X : D} (m₁ m₂ : ModObj A X) (h : m₁.smul = m₂.smul) :
    (isoOfSmulEq m₁ m₂ h).inv.hom = 𝟙 X := by
  simp [isoOfSmulEq]

/-- Restricting the scalars of a `B`-module `M` along a monoid morphism `f : A ⟶ B` acts by `f`
followed by the action of `B`. -/
@[reassoc, simp]
theorem comap_obj_smul {B : C} [MonObj B] (f : A ⟶ B) [IsMonHom f] (M : Mod D B) :
    γ[A,((comap f).obj M).X] = f ⊵ₗ M.X ≫ γ[B,M.X] :=
  (rfl)

end CategoryTheory.Mod

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
  (M X : C) [MonObj M] [ModObj M X]

/-- A lax monoidal functor transports an internal action to an action of the image monoid. -/
@[instance_reducible]
def modObjObj : ModObj (F.obj M) (F.obj X) where
  smul := LaxMonoidal.μ F M X ≫ F.map γ[M, X]
  one_smul := by simp [← F.map_comp]
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight, obj.μ_def]
    simp only [comp_whiskerRight, Category.assoc, μ_natural_left_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, ModObj.mul_smul_self]
    simp

/-- The transported action is the tensorator followed by the image of the action. -/
@[simp]
theorem modObjObj_smul :
    letI := F.modObjObj M X
    γ[F.obj M, F.obj X] = LaxMonoidal.μ F M X ≫ F.map γ[M, X] := by
  rw [modObjObj]
  rfl

variable {X} {Y : C} [ModObj M Y]

/-- A lax monoidal functor transports equivariant morphisms to equivariant morphisms. -/
theorem modObjObj_isModHom (f : X ⟶ Y) [IsModHom M f] :
    letI := F.modObjObj M X
    letI := F.modObjObj M Y
    IsModHom (F.obj M) (F.map f) := by
  let := F.modObjObj M X
  let := F.modObjObj M Y
  constructor
  simp only [modObjObj_smul, selfLeftAction_actionHomRight, Category.assoc,
    μ_natural_right_assoc, ← F.map_comp]
  exact congrArg (fun k ↦ LaxMonoidal.μ F M X ≫ F.map k) (IsModHom.smul_hom (A := M) (f := f))

end CategoryTheory.Functor

namespace CategoryTheory

open CategoryTheory MonoidalCategory MonObj
open scoped Obj

/-- If `G ◁ p` is an epimorphism and `p` and `p ≫ f` are `G`-equivariant, then `f` is
`G`-equivariant. -/
theorem isModHom_of_epi_whiskerLeft_comp {C : Type*} [Category C] [MonoidalCategory C]
    {G Z X Y : C} [MonObj G] [ModObj G Z] [ModObj G X] [ModObj G Y]
    (p : Z ⟶ X) [Epi (G ◁ p)] [IsModHom G p] (f : X ⟶ Y) [IsModHom G (p ≫ f)] :
    IsModHom G f where
  smul_hom := by
    have hp := IsModHom.smul_hom (A := G) (f := p)
    have hpf := IsModHom.smul_hom (A := G) (f := p ≫ f)
    simp only [selfLeftAction_actionHomRight] at hp hpf ⊢
    rw [← cancel_epi (G ◁ p), ← Category.assoc, ← hp, Category.assoc, hpf,
      ← Category.assoc, ← whiskerLeft_comp]

end CategoryTheory
