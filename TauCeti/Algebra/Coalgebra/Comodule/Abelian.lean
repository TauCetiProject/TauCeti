/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Limits
public import TauCeti.Algebra.Coalgebra.Comodule.Product
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The abelian category of comodules over a flat coalgebra

The forgetful functor to modules preserves kernels and cokernels and reflects isomorphisms.
Consequently the coimage-to-image comparison is an isomorphism, making comodules an abelian
category. In particular this applies to any coalgebra over a field, providing the exact-category
structure used in the representation theory of affine groups.

The comparison argument follows Mathlib's `FGModuleCat` abelian-category construction.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ComoduleCat

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

noncomputable section

/-- A comodule morphism whose underlying module map is an isomorphism is an isomorphism. -/
instance : (forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    let F := forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)
    have hbij : Function.Bijective f.toLinearMap := ConcreteCategory.bijective_of_isIso (F.map f)
    let e := LinearEquiv.ofBijective f.toLinearMap hbij
    let i : M ≅ N := isoOfLinearEquiv (R := R) (C := C) e f.map_coact
    have hi : i.hom = f := by
      ext x
      exact isoOfLinearEquiv_hom_apply (R := R) (C := C) e _ x
    rw [← hi]
    infer_instance

variable [Module.Flat R C]

instance {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison f) := by
  let F := forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)
  have := IsIso.of_isIso_fac_right
    (Abelian.PreservesCoimage.hom_coimageImageComparison F f).symm
  exact isIso_of_reflects_iso _ F

/-- Comodules over a flat coalgebra over a commutative ring form an abelian category. -/
instance : Abelian (ComoduleCat.{u, v, w} R C) :=
  Abelian.ofCoimageImageComparisonIsIso

/-- Forgetting a comodule to its underlying module preserves finite limits. -/
instance : PreservesFiniteLimits
    (forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

omit [Module.Flat R C] in
/-- Forgetting a comodule to its underlying module preserves finite colimits. -/
instance : PreservesFiniteColimits
    (forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)) :=
  by
    let : HasFiniteBiproducts (ComoduleCat.{u, v, w} R C) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    let : HasCoequalizers (ComoduleCat.{u, v, w} R C) :=
      Preadditive.hasCoequalizers_of_hasCokernels
    exact Functor.preservesFiniteColimits_of_preservesCokernels _

end

end TauCeti.ComoduleCat
