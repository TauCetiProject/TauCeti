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
isomorphism is the evaluation pairing `Module.evalEquiv`. Over a field this is the familiar
reflexivity of the category of finite-dimensional vector spaces; over a general ring it is
the reason the dual of a finitely generated projective module is again finitely generated
projective.

Because `FGModuleCat R` keeps finite generation as part of its objects, a finitely generated
projective module is an object of `FGModuleCat R` and its dual is one as well. This file
packages the algebraic dual as a contravariant operation on the objects and morphisms of
`FGModuleCat R`, so that constructions which dualize, such as the duality for matrix
factorizations, are written once at the module level.

The operations this file contributes are those of the category of finitely generated projective
modules alone; the crossed-transpose calculations that dualizing a *curved pair* of maps needs are
curvature equations, and they are proved in `TauCeti.Algebra.Homology.Curved.Dual` beside the duals
whose differential equations they are.

## Main definitions

* `FGModuleCat.dual`: the dual of a finitely generated projective module, as an object of
  `FGModuleCat R`.
* `FGModuleCat.dualMap`: the transpose of a morphism, contravariantly.
* `FGModuleCat.dualEvalIso`: the double dual isomorphism.

The bodies of `FGModuleCat.dualMap` and `FGModuleCat.dualEvalIso` are not exposed; the results
below describe them.

## Main results

* `FGModuleCat.dualMap_hom`: the underlying module map of a transpose is the dual map of the
  underlying module map, the component form of `FGModuleCat.dualMap`.
* `FGModuleCat.dualMap_id`, `FGModuleCat.dualMap_comp`, `FGModuleCat.dualMap_smul`,
  `FGModuleCat.dualMap_neg`, `FGModuleCat.dualMap_zero`, `FGModuleCat.dualMap_add`: transposing is
  contravariant and compatible with the additive and `R`-linear structure on morphisms.
* `FGModuleCat.dualEvalIso`, `FGModuleCat.dualEvalIso_hom`, `FGModuleCat.dualEvalIso_inv`: a
  double dual is canonically isomorphic to the original module, and the underlying module maps of
  that isomorphism and its inverse are the two halves of the evaluation pairing.
* `FGModuleCat.dualMap_dualMap_dualEvalIso`: the double transpose of a morphism is the original
  morphism, conjugated by the evaluation isomorphisms. This is the fact that makes double duals an
  equivalence.
-/

public section

universe u

open CategoryTheory Module Preadditive

namespace FGModuleCat

variable (R : Type u) [CommRing R]

/-- The dual of a finitely generated projective module, as an object of `FGModuleCat R`. -/
abbrev dual (M : FGModuleCat.{u} R) [Module.Projective R M] : FGModuleCat.{u} R :=
  ⟨ModuleCat.of R (Module.Dual R M), (ModuleCat.isFG_iff _).2 inferInstance⟩

/-- The underlying module of a dual is projective. -/
instance (M : FGModuleCat.{u} R) [Module.Projective R M] :
    Module.Projective R ((FGModuleCat.dual R M).obj) :=
  inferInstanceAs (Module.Projective R (Module.Dual R M))

/-- The underlying module of a dual is the module dual `Module.Dual R M`. -/
@[simp] theorem dual_obj (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (FGModuleCat.dual R M).obj = Module.Dual R M := rfl

/-- The transpose of a morphism of finitely generated projective modules. -/
def dualMap {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) : FGModuleCat.dual R N ⟶ FGModuleCat.dual R M :=
  FGModuleCat.ofHom f.hom.hom.dualMap

/-- The underlying module map of a transpose is the dual map of the underlying module map. -/
@[simp] theorem dualMap_hom {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    (FGModuleCat.dualMap (R := R) f).hom.hom = f.hom.hom.dualMap := (rfl)

private theorem smul_hom_apply (a : R) {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (a • f).hom.hom = a • f.hom.hom := rfl

private theorem neg_hom_apply {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (-f).hom.hom = -f.hom.hom := rfl

private theorem zero_hom_apply {M N : FGModuleCat.{u} R} : (0 : M ⟶ N).hom.hom = 0 := rfl

private theorem add_hom_apply {M N : FGModuleCat.{u} R} (f g : M ⟶ N) :
    (f + g).hom.hom = f.hom.hom + g.hom.hom := rfl

/-- Dualization is contravariant on morphisms: the transpose of the identity is the
identity. -/
@[simp] theorem dualMap_id {M : FGModuleCat.{u} R} [Module.Projective R M] :
    FGModuleCat.dualMap (R := R) (𝟙 M) = 𝟙 (FGModuleCat.dual R M) := by
  apply FGModuleCat.hom_ext
  simp only [FGModuleCat.dualMap_hom, FGModuleCat.hom_hom_id]
  exact LinearMap.dualMap_id

/-- Dualization is contravariant on morphisms: the transpose of a composite is the composite
of the transposes in the opposite order. -/
@[simp] theorem dualMap_comp {M N P : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] [Module.Projective R P] (f : M ⟶ N) (g : N ⟶ P) :
    FGModuleCat.dualMap (R := R) (f ≫ g) = FGModuleCat.dualMap (R := R) g ≫
      FGModuleCat.dualMap (R := R) f := by
  apply FGModuleCat.hom_ext
  simp only [FGModuleCat.dualMap_hom, FGModuleCat.hom_hom_comp]
  exact (LinearMap.dualMap_comp_dualMap f.hom.hom g.hom.hom).symm

/-- Transposing is compatible with the `R`-linear structure on morphisms: the transpose of a
scalar multiple of a morphism is the same scalar multiple of the transpose. -/
@[simp] theorem dualMap_smul (a : R) {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualMap (R := R) (a • f) = a • FGModuleCat.dualMap (R := R) f := by
  apply FGModuleCat.hom_ext
  ext φ x
  rw [smul_hom_apply, FGModuleCat.dualMap_hom, smul_hom_apply, FGModuleCat.dualMap_hom]
  simp

/-- A double dual is canonically isomorphic to the original module, by the evaluation pairing. -/
noncomputable def dualEvalIso (M : FGModuleCat.{u} R)
    [Module.Projective R M] : FGModuleCat.dual R (FGModuleCat.dual R M) ≅ M :=
  ObjectProperty.isoMk (P := ModuleCat.isFG R) (Module.evalEquiv R M).symm.toModuleIso

/-- The underlying module map of the double dual isomorphism is the inverse of the evaluation
pairing. -/
@[simp] theorem dualEvalIso_hom (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (FGModuleCat.dualEvalIso R M).hom.hom.hom = (Module.evalEquiv R M).symm.toLinearMap := (rfl)

/-- The underlying module map of the inverse of the double dual isomorphism is the evaluation
pairing itself, the other half of `FGModuleCat.dualEvalIso_hom`. -/
@[simp] theorem dualEvalIso_inv (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (FGModuleCat.dualEvalIso R M).inv.hom.hom = (Module.evalEquiv R M).toLinearMap := (rfl)

/-- Transposing is compatible with the additive structure on morphisms: the transpose of a
negated morphism is the negation of the transpose. -/
@[simp] theorem dualMap_neg {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualMap (R := R) (-f) = -(FGModuleCat.dualMap (R := R) f) := by
  apply FGModuleCat.hom_ext
  ext φ x
  rw [neg_hom_apply, FGModuleCat.dualMap_hom, neg_hom_apply, FGModuleCat.dualMap_hom]
  simp

/-- Transposing is compatible with the additive structure on morphisms: the transpose of the
zero morphism is the zero morphism. -/
@[simp] theorem dualMap_zero {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] : FGModuleCat.dualMap (R := R) (0 : M ⟶ N) = 0 := by
  apply FGModuleCat.hom_ext
  simp only [FGModuleCat.dualMap_hom, zero_hom_apply]
  ext φ x
  simp

/-- Transposing is compatible with the additive structure on morphisms: the transpose of a sum of
morphisms is the sum of the transposes. -/
@[simp] theorem dualMap_add {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f g : M ⟶ N) :
    FGModuleCat.dualMap (R := R) (f + g) = FGModuleCat.dualMap R f + FGModuleCat.dualMap R g := by
  apply FGModuleCat.hom_ext
  simp only [FGModuleCat.dualMap_hom, add_hom_apply]
  ext φ x
  simp

/-- The double transpose of a morphism is the morphism itself, up to the evaluation isomorphisms:
a double dual is not just isomorphic to the original module, the isomorphism intertwines the
morphisms. -/
@[simp] theorem dualMap_dualMap_dualEvalIso {M N : FGModuleCat.{u} R}
    [Module.Projective R M] [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualMap (R := R) (FGModuleCat.dualMap (R := R) f) ≫
        (FGModuleCat.dualEvalIso R N).hom
      = (FGModuleCat.dualEvalIso R M).hom ≫ f := by
  apply FGModuleCat.hom_ext
  ext Φ
  -- `dualMap` is on the nose the transpose of the underlying module map and `dualEvalIso` is
  -- `(Module.evalEquiv R M).symm`, so after unfolding the two composites the goal reads
  -- `(Module.evalEquiv R N).symm (f.dualMap.dualMap Φ) = f ((Module.evalEquiv R M).symm Φ)`.
  rw [InducedCategory.comp_hom, ModuleCat.hom_comp, FGModuleCat.dualMap_hom,
    FGModuleCat.dualEvalIso_hom, FGModuleCat.dualMap_hom,
    InducedCategory.comp_hom, ModuleCat.hom_comp, FGModuleCat.dualEvalIso_hom,
    LinearMap.comp_apply]
  -- `Module.Dual.eval_comp_comp_evalEquiv_eq` says the double transpose is
  -- `Module.Dual.eval R N ∘ₗ f ∘ₗ (Module.evalEquiv R M).symm`, and
  -- `Module.evalEquiv R N` inverts that evaluation pairing.
  have key := congrArg (fun g => g Φ) (Module.Dual.eval_comp_comp_evalEquiv_eq
    (R := R) (M := M) (M' := N) (f := f.hom.hom))
  simp only [LinearMap.comp_apply, ← Module.evalEquiv_toLinearMap,
    LinearEquiv.coe_toLinearMap] at key ⊢
  rw [← key, (Module.evalEquiv R N).symm_apply_apply]

end FGModuleCat
