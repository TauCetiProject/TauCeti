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

## Main definitions

* `FGModuleCat.dual`: the dual of a finitely generated projective module, as an object of
  `FGModuleCat R`.
* `FGModuleCat.dualHom`: the transpose of a morphism, contravariantly.
* `FGModuleCat.dualEvalIso`: the double dual isomorphism.

The bodies of `FGModuleCat.dualHom` and `FGModuleCat.dualEvalIso` are not exposed; the results
below describe them.

## Main results

* `FGModuleCat.dualHom_hom`: the underlying module map of a transpose is the dual map of the
  underlying module map, the component form of `FGModuleCat.dualHom`.
* `FGModuleCat.dualHom_id`, `FGModuleCat.dualHom_comp`, `FGModuleCat.dualHom_smul`,
  `FGModuleCat.dualHom_neg`: transposing is contravariant and compatible with the `R`-linear
  structure.
* `FGModuleCat.dualEvalIso`, `FGModuleCat.dualEvalIso_hom`, `FGModuleCat.dualEvalIso_inv`: a
  double dual is canonically isomorphic to the original module, and the underlying module maps of
  that isomorphism and its inverse are the two halves of the evaluation pairing.
* `FGModuleCat.dualHom_dualHom_dualEvalIso`: the double transpose of a morphism is the original
  morphism, conjugated by the evaluation isomorphisms. This is the fact that makes double duals an
  equivalence.
* `FGModuleCat.negDualHom_comp_dualHom`,
  `FGModuleCat.negDualHom_dualHom_comp_negDualHom_dualHom`: the composite of a crossed pair of
  transposes of a curved pair of maps is the negated curvature, and the same holds for the
  composite of the two negated double transposes, which is the original curvature again.
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

@[simp] theorem dual_obj (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (FGModuleCat.dual R M).obj = Module.Dual R M := rfl

/-- The transpose of a morphism of finitely generated projective modules. -/
def dualHom {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) : FGModuleCat.dual R N ⟶ FGModuleCat.dual R M :=
  FGModuleCat.ofHom f.hom.hom.dualMap

/-- The underlying module map of a transpose is the dual map of the underlying module map. -/
@[simp] theorem dualHom_hom {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    (FGModuleCat.dualHom (R := R) f).hom.hom = f.hom.hom.dualMap := (rfl)

private theorem smul_hom_apply (a : R) {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (a • f).hom.hom = a • f.hom.hom := rfl

private theorem neg_hom_apply {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (-f).hom.hom = -f.hom.hom := rfl

@[simp] theorem dualHom_id {M : FGModuleCat.{u} R} [Module.Projective R M] :
    FGModuleCat.dualHom (R := R) (𝟙 M) = 𝟙 (FGModuleCat.dual R M) := by
  apply FGModuleCat.hom_ext
  rfl

@[simp] theorem dualHom_comp {M N P : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] [Module.Projective R P] (f : M ⟶ N) (g : N ⟶ P) :
    FGModuleCat.dualHom (R := R) (f ≫ g) = FGModuleCat.dualHom (R := R) g ≫
      FGModuleCat.dualHom (R := R) f := by
  apply FGModuleCat.hom_ext
  rfl

@[simp] theorem dualHom_smul (a : R) {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualHom (R := R) (a • f) = a • FGModuleCat.dualHom (R := R) f := by
  apply FGModuleCat.hom_ext
  ext φ x
  rw [smul_hom_apply, FGModuleCat.dualHom_hom, smul_hom_apply, FGModuleCat.dualHom_hom]
  simp

/-- A double dual is canonically isomorphic to the original module, by the evaluation pairing. -/
noncomputable def dualEvalIso (M : FGModuleCat.{u} R)
    [Module.Projective R M] : FGModuleCat.dual R (FGModuleCat.dual R M) ≅ M :=
  ObjectProperty.isoMk (P := ModuleCat.isFG R) (Module.evalEquiv R M).symm.toModuleIso

/-- The underlying module map of the double dual isomorphism is the inverse of the evaluation
pairing. -/
@[simp] theorem dualEvalIso_hom (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (FGModuleCat.dualEvalIso R M).hom.hom.hom = (Module.evalEquiv R M).symm.toLinearMap := (rfl)

@[simp] theorem dualEvalIso_inv (M : FGModuleCat.{u} R) [Module.Projective R M] :
    (FGModuleCat.dualEvalIso R M).inv.hom.hom = (Module.evalEquiv R M).toLinearMap := (rfl)

@[simp] theorem dualHom_neg {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualHom (R := R) (-f) = -(FGModuleCat.dualHom (R := R) f) := by
  apply FGModuleCat.hom_ext
  ext φ x
  rw [neg_hom_apply, FGModuleCat.dualHom_hom, neg_hom_apply, FGModuleCat.dualHom_hom]
  simp

/-- The double transpose of a morphism is the morphism itself, up to the evaluation isomorphisms:
a double dual is not just isomorphic to the original module, the isomorphism intertwines the
morphisms. -/
@[simp] theorem dualHom_dualHom_dualEvalIso {M N : FGModuleCat.{u} R}
    [Module.Projective R M] [Module.Projective R N] (f : M ⟶ N) :
    FGModuleCat.dualHom (R := R) (FGModuleCat.dualHom (R := R) f) ≫
        (FGModuleCat.dualEvalIso R N).hom
      = (FGModuleCat.dualEvalIso R M).hom ≫ f := by
  apply FGModuleCat.hom_ext
  ext Φ
  -- `dualHom` is on the nose the transpose of the underlying module map and `dualEvalIso` is
  -- `(Module.evalEquiv R M).symm`, so after unfolding the two composites the goal reads
  -- `(Module.evalEquiv R N).symm (f.dualMap.dualMap Φ) = f ((Module.evalEquiv R M).symm Φ)`.
  rw [InducedCategory.comp_hom, ModuleCat.hom_comp, FGModuleCat.dualHom_hom,
    FGModuleCat.dualEvalIso_hom, FGModuleCat.dualHom_hom,
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

/-- For a curved pair of maps `f` and `g` with `f ≫ g = w • 𝟙`, the composite of the negated
transpose of `g` with the transpose of `f` is multiplication by `-w` on the dual. This is the
computation behind the two differential equations of a dual of curvature `-w`. -/
theorem negDualHom_comp_dualHom {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (w : R) (f : M ⟶ N) (g : N ⟶ M) (h : f ≫ g = w • 𝟙 M) :
    ((-FGModuleCat.dualHom R g) ≫ FGModuleCat.dualHom R f) = -w • 𝟙 (FGModuleCat.dual R M) := by
  calc (-FGModuleCat.dualHom R g) ≫ FGModuleCat.dualHom R f
      = -(FGModuleCat.dualHom R g ≫ FGModuleCat.dualHom R f) := by simp only [neg_comp]
    _ = -FGModuleCat.dualHom R (f ≫ g) := by
      rw [FGModuleCat.dualHom_comp (f := f) (g := g)]
    _ = -FGModuleCat.dualHom R (w • 𝟙 M) := by rw [h]
    _ = -(w • FGModuleCat.dualHom R (𝟙 M)) := by rw [FGModuleCat.dualHom_smul]
    _ = -(w • 𝟙 (FGModuleCat.dual R M)) := by rw [FGModuleCat.dualHom_id]
    _ = -w • 𝟙 (FGModuleCat.dual R M) := by rw [neg_smul]

/-- The same computation one dual further: the composite of the two negated double transposes of
a curved pair of maps is multiplication by the original `w` on the double dual. This is the
computation behind the two differential equations of a double dual, and the reason a double dual
has the same curvature as its source. -/
theorem negDualHom_dualHom_comp_negDualHom_dualHom {M N : FGModuleCat.{u} R}
    [Module.Projective R M] [Module.Projective R N] (w : R) (f : M ⟶ N) (g : N ⟶ M)
    (h : f ≫ g = w • 𝟙 M) :
    ((-FGModuleCat.dualHom R (FGModuleCat.dualHom R f)) ≫
      (-FGModuleCat.dualHom R (FGModuleCat.dualHom R g)))
      = w • 𝟙 (FGModuleCat.dual R (FGModuleCat.dual R M)) := by
  calc (-FGModuleCat.dualHom R (FGModuleCat.dualHom R f)) ≫
        (-FGModuleCat.dualHom R (FGModuleCat.dualHom R g))
      = FGModuleCat.dualHom R (FGModuleCat.dualHom R f) ≫
          FGModuleCat.dualHom R (FGModuleCat.dualHom R g) := by
            rw [Preadditive.neg_comp_neg]
    _ = FGModuleCat.dualHom R (FGModuleCat.dualHom R (f ≫ g)) := by
      rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp]
    _ = FGModuleCat.dualHom R (FGModuleCat.dualHom R (w • 𝟙 M)) := by rw [h]
    _ = w • FGModuleCat.dualHom R (FGModuleCat.dualHom R (𝟙 M)) := by
      simp only [FGModuleCat.dualHom_smul]
    _ = w • 𝟙 (FGModuleCat.dual R (FGModuleCat.dual R M)) := by
      rw [FGModuleCat.dualHom_id, FGModuleCat.dualHom_id]

end FGModuleCat
