/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.CategoryTheory.Preadditive.HomWithAction

/-!
# Endomorphisms and commuting actions in `ModuleCat`

An automorphism of a ring as a module over itself sends one to a unit. Consequently,
the scalar comparing the images of one under two isomorphisms is a unit as well.

A natural number `e` kills a module `M` exactly when the endomorphism `e • 𝟙 M` vanishes
(`ModuleCat.nsmul_id_eq_zero_iff`).

A commuting `R`-module structure on `Y : ModuleCat k` induces a ring homomorphism
`Y.endRingHomOfModule R : R →+* End Y` (`ModuleCat.endRingHomOfModule`), under which
`TauCeti.HomWithAction` identifies `R`-linearly with `X →ₗ[k] Y`
(`TauCeti.HomWithAction.moduleCatLinearEquiv`).
-/

public noncomputable section

open CategoryTheory

namespace ModuleCat

universe v u

variable {R : Type u} [Ring R]

/-- An automorphism of the rank-one free module sends one to a unit. -/
theorem isUnit_apply_one_of_isIso (f : ModuleCat.of R R ⟶ ModuleCat.of R R) [IsIso f] :
    IsUnit (f 1) :=
  (((Module.End.isUnit_iff _).2 (ConcreteCategory.bijective_of_isIso f)).map
    (RingEquiv.moduleEndSelf R).symm).unop

/-- The scalar comparing the images of one under two module isomorphisms is a unit. -/
theorem isUnit_of_apply_one_eq_smul {M : ModuleCat R}
    (f g : ModuleCat.of R R ⟶ M) [IsIso f] [IsIso g] {a : R}
    (h : g 1 = a • f 1) : IsUnit a := by
  have hu := isUnit_apply_one_of_isIso (g ≫ inv f)
  simpa only [CategoryTheory.comp_apply, h, map_smul, IsIso.hom_inv_id_apply,
    smul_eq_mul, mul_one] using hu

/-- A natural number `e` kills a module `M`, in the sense that `e • 𝟙 M = 0`, exactly when
`e • x = 0` for every element `x` of `M`. -/
theorem nsmul_id_eq_zero_iff {M : ModuleCat R} {e : ℕ} : e • 𝟙 M = 0 ↔ ∀ x : M, e • x = 0 :=
  ⟨fun h x ↦ by simpa using congr($h x), fun h ↦ by ext x; simpa using h x⟩

/-- A commuting `R`-module structure on `Y : ModuleCat k` induces `R →+* End Y` sending `r` to
scalar multiplication by `r`. -/
def endRingHomOfModule {k : Type*} [Ring k] (Y : ModuleCat.{v} k) (R : Type*) [Semiring R]
    [Module R Y] [SMulCommClass k R Y] : R →+* End Y :=
  letI := SMulCommClass.symm k R Y
  (ModuleCat.endRingEquiv Y).symm.toRingHom.comp (Module.toModuleEnd k Y)

@[simp]
lemma endRingHomOfModule_apply_asHom_apply {k : Type*} [Ring k] (Y : ModuleCat.{v} k)
    (R : Type*) [Semiring R] [Module R Y] [SMulCommClass k R Y] (r : R) (y : Y) :
    (Y.endRingHomOfModule R r).asHom.hom y = r • y := (rfl)

end ModuleCat

namespace TauCeti.HomWithAction

universe v

variable {k R : Type*} [Ring k] [Semiring R]

/-- For `X Y : ModuleCat k` with a commuting `R`-action on `Y`, `HomWithAction` for
`Y.endRingHomOfModule R` agrees `R`-linearly with `X →ₗ[k] Y` equipped with its pointwise
`R`-action. -/
def moduleCatLinearEquiv (X Y : ModuleCat.{v} k) [Module R Y] [SMulCommClass k R Y] :
    HomWithAction (Y.endRingHomOfModule R) X ≃ₗ[R] (X →ₗ[k] Y) where
  toAddEquiv := (toHom (Y.endRingHomOfModule R)).trans
    (ModuleCat.homLinearEquiv (S := R)).toAddEquiv
  map_smul' _ _ := by ext x; simp

@[simp]
lemma moduleCatLinearEquiv_apply {X Y : ModuleCat.{v} k} [Module R Y] [SMulCommClass k R Y]
    (f : HomWithAction (Y.endRingHomOfModule R) X) :
    moduleCatLinearEquiv X Y f = (toHom (Y.endRingHomOfModule R) f).hom := (rfl)

@[simp]
lemma toHom_moduleCatLinearEquiv_symm {X Y : ModuleCat.{v} k} [Module R Y] [SMulCommClass k R Y]
    (f : X →ₗ[k] Y) :
    toHom (Y.endRingHomOfModule R) ((moduleCatLinearEquiv X Y).symm f) = ModuleCat.ofHom f := by
  simp [moduleCatLinearEquiv, ModuleCat.homAddEquiv, ModuleCat.homEquiv]

end TauCeti.HomWithAction
