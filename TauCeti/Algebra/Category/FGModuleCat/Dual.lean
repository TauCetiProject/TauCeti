/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duality for finitely generated projective modules

Over a commutative ring `R` the algebraic dual of a module `M` is `Module.Dual R M`, the
hom module into `R`. Its dual `Module.Dual R (Module.Dual R M)` carries a canonical
isomorphism back to `M` as soon as `M` is finitely generated and projective, and the
isomorphism is the evaluation pairing
`Module.Dual.evalEquiv`. Over a field this is the familiar reflexivity of the category of
finite-dimensional vector spaces; over a general ring it is the reason the dual of a
finitely generated projective module is again finitely generated projective.

Because `FGModuleCat R` keeps finite generation as part of its objects, a finitely generated
projective module is an object of `FGModuleCat R` and its dual is one as well. This file
packages the algebraic dual as a contravariant operation on the objects and morphisms of
`FGModuleCat R`, so that constructions which dualize, such as the duality for matrix
factorizations, are written once at the module level.

## Main definitions

* `FGModuleCat.dual`: the dual of a finitely generated projective module, as an object of
  `FGModuleCat R`.
* `FGModuleCat.dualHom`: the transpose of a morphism, contravariantly.
* `FGModuleCat.dualEvalEquiv`: the double dual isomorphism.

## Main results

* `FGModuleCat.dualHom_id`, `FGModuleCat.dualHom_comp`, `FGModuleCat.dualHom_smul`,
  `FGModuleCat.dualHom_neg`: transposing is contravariant and compatible with the `R`-linear
  structure.
* `FGModuleCat.dualEvalEquiv`: a double dual is canonically isomorphic to the original module.
* `FGModuleCat.dualHom_dualHom_dualEvalEquiv`: the double transpose of a morphism is the original
  morphism, conjugated by the evaluation isomorphisms. This is the fact that makes double duals an
  equivalence.
-/

public section

universe u

namespace TauCeti

open CategoryTheory Module

variable (R : Type u) [CommRing R]

/-- The dual of a finitely generated projective module, as an object of `FGModuleCat R`. -/
abbrev FGModuleCat.dual (M : FGModuleCat.{u} R) [Module.Projective R M] : FGModuleCat.{u} R :=
  ⟨ModuleCat.of R (Module.Dual R M), (ModuleCat.isFG_iff _).2 inferInstance⟩

/-- The underlying module of a dual is projective. -/
instance (M : FGModuleCat.{u} R) [Module.Projective R M] :
    Module.Projective R ((FGModuleCat.dual R M).obj) :=
  inferInstanceAs (Module.Projective R (Module.Dual R M))

@[simp] theorem FGModuleCat.dual_obj (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (FGModuleCat.dual R M).obj = Module.Dual R M := rfl

/-- The transpose of a morphism of finitely generated projective modules. -/
@[expose] def FGModuleCat.dualHom {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) : FGModuleCat.dual R N ⟶ FGModuleCat.dual R M :=
  FGModuleCat.ofHom f.hom.hom.dualMap

@[simp] theorem FGModuleCat.dualHom_apply {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) (φ : Module.Dual R N) (x : M) :
    (FGModuleCat.dualHom (R := R) f).hom.hom φ x = φ (f.hom.hom x) := rfl

@[simp] theorem FGModuleCat.dualHom_id {M : FGModuleCat.{u} R} [Module.Projective R M] :
    FGModuleCat.dualHom (R := R) (𝟙 M) = 𝟙 (FGModuleCat.dual R M) := by
  apply FGModuleCat.hom_ext
  rfl

@[simp] theorem FGModuleCat.dualHom_comp {M N P : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] [Module.Projective R P] (f : M ⟶ N) (g : N ⟶ P) :
    FGModuleCat.dualHom (R := R) (f ≫ g) = FGModuleCat.dualHom (R := R) g ≫
      FGModuleCat.dualHom (R := R) f := by
  apply FGModuleCat.hom_ext
  rfl

@[simp] theorem FGModuleCat.dualHom_smul (a : R) {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualHom (R := R) (a • f) = a • FGModuleCat.dualHom (R := R) f := by
  apply FGModuleCat.hom_ext
  ext φ x
  change (Module.Dual.transpose (a • f.hom.hom) φ) x
      = (Module.Dual.transpose f.hom.hom (a • φ)) x
  rw [Module.Dual.transpose_apply, Module.Dual.transpose_apply]
  simp

/-- A double dual is canonically isomorphic to the original module, by the evaluation pairing. -/
@[expose] noncomputable def FGModuleCat.dualEvalEquiv (M : FGModuleCat.{u} R)
    [Module.Projective R M] : FGModuleCat.dual R (FGModuleCat.dual R M) ≅ M :=
  ObjectProperty.isoMk (P := ModuleCat.isFG R) (Module.evalEquiv R M).symm.toModuleIso

@[simp] theorem FGModuleCat.dualEvalEquiv_apply (M : FGModuleCat.{u} R) [Module.Projective R M]
    (φ : Module.Dual R (Module.Dual R M)) :
    (FGModuleCat.dualEvalEquiv R M).hom.hom.hom φ = (Module.evalEquiv R M).symm φ := rfl

@[simp] theorem FGModuleCat.dualHom_neg {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualHom (R := R) (-f) = -(FGModuleCat.dualHom (R := R) f) := by
  apply FGModuleCat.hom_ext
  ext φ x
  change (Module.Dual.transpose (-f.hom.hom) φ) x = -(Module.Dual.transpose f.hom.hom φ) x
  simp [Module.Dual.transpose_apply]

/-- The double transpose of a morphism is the morphism itself, up to the evaluation isomorphisms:
a double dual is not just isomorphic to the original module, the isomorphism intertwines the
morphisms. -/
@[simp] theorem FGModuleCat.dualHom_dualHom_dualEvalEquiv {M N : FGModuleCat.{u} R}
    [Module.Projective R M] [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualHom (R := R) (FGModuleCat.dualHom (R := R) f) ≫
        (FGModuleCat.dualEvalEquiv R N).hom
      = (FGModuleCat.dualEvalEquiv R M).hom ≫ f := by
  apply FGModuleCat.hom_ext
  ext Φ
  have key : (FGModuleCat.dualHom (R := R) (FGModuleCat.dualHom (R := R) f)).hom.hom Φ
      = Module.Dual.eval R N (f.hom.hom ((FGModuleCat.dualEvalEquiv R M).hom.hom.hom Φ)) := by
    have h := (Module.Dual.eval_comp_comp_evalEquiv_eq
      (R := R) (M := M) (M' := N) (f := f.hom.hom)).symm
    change f.hom.hom.dualMap.dualMap Φ = _
    rw [congrArg (fun g => g Φ) h]
    rfl
  change (Module.evalEquiv R N).symm
      ((FGModuleCat.dualHom (R := R) (FGModuleCat.dualHom (R := R) f)).hom.hom Φ)
      = f.hom.hom ((FGModuleCat.dualEvalEquiv R M).hom.hom.hom Φ)
  rw [key]
  exact (Module.evalEquiv R N).symm_apply_apply _

end TauCeti
