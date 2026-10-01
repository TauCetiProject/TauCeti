/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.CategoryTheory.Linear.FullSubcategory

/-!
# Duality for finitely generated projective modules

Over a commutative ring `R` the algebraic dual of a module `M` is `Module.Dual R M`, the
hom module into `R`. When `M` is finitely generated and projective, so is its dual, and the
evaluation pairing `Module.evalEquiv` identifies `M` with its double dual. Over a field this is
the familiar reflexivity of finite-dimensional vector spaces.

Because `FGModuleCat R` keeps finite generation as part of its objects, a finitely generated
projective module is an object of `FGModuleCat R` and its dual is one as well. This file
packages the algebraic dual as a contravariant operation on the objects and morphisms of
`FGModuleCat R`, so that constructions which dualize, such as the duality for matrix
factorizations, are written once at the module level.

The crossed-transpose calculations that dualizing a *curved pair* of maps needs are curvature
equations, and they are proved in `TauCeti.Algebra.Homology.Curved.Dual` beside the duals whose
differential equations they are.

## Main definitions

* `FGModuleCat.dual`: the dual of a finitely generated projective module, as an object of
  `FGModuleCat R`.
* `FGModuleCat.dualMap`: the transpose of a morphism, contravariantly.
* `FGModuleCat.dualEvalIso`: the isomorphism from the double dual back to the module.

The bodies of `FGModuleCat.dualMap` and `FGModuleCat.dualEvalIso` are not exposed; the results
below describe them.

## Main results

* `FGModuleCat.dualMap_hom`: the underlying module map of a transpose is the dual map of the
  underlying module map.
* `FGModuleCat.dualMap_id`, `FGModuleCat.dualMap_comp`, `FGModuleCat.dualMap_smul`,
  `FGModuleCat.dualMap_neg`, `FGModuleCat.dualMap_zero`, `FGModuleCat.dualMap_add`: transposing is
  contravariant and compatible with the additive and `R`-linear structure on morphisms.
* `FGModuleCat.dualEvalIso_hom`, `FGModuleCat.dualEvalIso_inv`: the underlying module maps of the
  double dual isomorphism and its inverse are the two halves of the evaluation pairing.
* `FGModuleCat.dualEvalIso_hom_naturality`: the double dual isomorphism is natural, i.e. it
  intertwines the double transpose of a morphism with the morphism itself.
-/

public section

universe u

open CategoryTheory Module

namespace FGModuleCat

variable (R : Type u) [CommRing R]

/-- The dual of a finitely generated projective module, as an object of `FGModuleCat R`. -/
abbrev dual (M : FGModuleCat.{u} R) [Module.Projective R M] : FGModuleCat.{u} R :=
  FGModuleCat.of R (Module.Dual R M)

/-- The underlying module of a dual is projective. -/
instance (M : FGModuleCat.{u} R) [Module.Projective R M] : Module.Projective R (dual R M) :=
  inferInstanceAs (Module.Projective R (Module.Dual R M))

/-- The underlying module of a dual is the module dual `Module.Dual R M`. -/
@[simp] theorem dual_obj (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (dual R M).obj = Module.Dual R M := rfl

variable {R}

/-- The transpose of a morphism of finitely generated projective modules. -/
def dualMap {M N : FGModuleCat.{u} R} [Module.Projective R M] [Module.Projective R N]
    (f : M ⟶ N) : dual R N ⟶ dual R M :=
  ofHom f.hom.hom.dualMap

/-- The underlying module map of a transpose is the dual map of the underlying module map. -/
@[simp] theorem dualMap_hom {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) : (dualMap f).hom.hom = f.hom.hom.dualMap := (rfl)

/-- The transpose of the identity is the identity. -/
@[simp] theorem dualMap_id {M : FGModuleCat.{u} R} [Module.Projective R M] :
    dualMap (𝟙 M) = 𝟙 (dual R M) := by
  ext; simp

/-- The transpose of a composite is the composite of the transposes in the opposite order. -/
@[simp] theorem dualMap_comp {M N P : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] [Module.Projective R P] (f : M ⟶ N) (g : N ⟶ P) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  ext; simp

/-- The transpose of a scalar multiple of a morphism is the same scalar multiple of the
transpose. -/
@[simp] theorem dualMap_smul (a : R) {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) : dualMap (a • f) = a • dualMap f := by
  ext; simp

/-- The transpose of a negated morphism is the negation of the transpose. -/
@[simp] theorem dualMap_neg {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) : dualMap (-f) = -dualMap f := by
  ext; simp

/-- The transpose of the zero morphism is the zero morphism. -/
@[simp] theorem dualMap_zero {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] : dualMap (0 : M ⟶ N) = 0 := by
  ext; simp

/-- The transpose of a sum of morphisms is the sum of the transposes. -/
@[simp] theorem dualMap_add {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f g : M ⟶ N) : dualMap (f + g) = dualMap f + dualMap g := by
  ext; simp

/-- A double dual is canonically isomorphic to the original module, by the evaluation pairing. -/
noncomputable def dualEvalIso (M : FGModuleCat.{u} R) [Module.Projective R M] :
    dual R (dual R M) ≅ M :=
  ObjectProperty.isoMk (P := ModuleCat.isFG R) (Module.evalEquiv R M).symm.toModuleIso

/-- The underlying module map of the double dual isomorphism is the inverse of the evaluation
pairing. -/
@[simp] theorem dualEvalIso_hom (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (dualEvalIso M).hom.hom.hom = (Module.evalEquiv R M).symm.toLinearMap := (rfl)

/-- The underlying module map of the inverse of the double dual isomorphism is the evaluation
pairing itself. -/
@[simp] theorem dualEvalIso_inv (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (dualEvalIso M).inv.hom.hom = (Module.evalEquiv R M).toLinearMap := (rfl)

/-- The double dual isomorphism is natural: it intertwines the double transpose of a morphism
with the morphism itself. -/
@[reassoc (attr := simp)]
theorem dualEvalIso_hom_naturality {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    dualMap (dualMap f) ≫ (dualEvalIso N).hom = (dualEvalIso M).hom ≫ f := by
  ext Φ
  simp [← Module.Dual.eval_comp_comp_evalEquiv_eq, ← Module.evalEquiv_apply]

end FGModuleCat
