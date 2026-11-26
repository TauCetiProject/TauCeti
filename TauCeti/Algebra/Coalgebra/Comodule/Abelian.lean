/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Limits
public import TauCeti.Algebra.Coalgebra.Comodule.Product
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The abelian category of comodules over a flat coalgebra

The forgetful functor to modules preserves kernels and cokernels and reflects isomorphisms.
Consequently the coimage-to-image comparison is an isomorphism, making comodules an abelian
category. In particular this applies to any coalgebra over a field, providing the exact-category
structure used in the representation theory of affine groups. Since the forgetful functor is
exact, exactness of a short complex of comodules can be read off from the underlying linear maps,
and a short exact sequence of comodules can be built from exact, injective and surjective
underlying maps (`TauCeti.ComoduleCat.shortComplex_shortExact`).

The comparison argument follows Mathlib's `FGModuleCat` abelian-category construction.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ComoduleCat

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

noncomputable section

/-- Forgetting a comodule to its underlying module preserves finite colimits. -/
instance : PreservesFiniteColimits
    (forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)) := by
  have : HasBinaryBiproducts (ComoduleCat.{u, v, w} R C) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : HasFiniteBiproducts (ComoduleCat.{u, v, w} R C) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasCoequalizers (ComoduleCat.{u, v, w} R C) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

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

end

end TauCeti.ComoduleCat

namespace CategoryTheory.ShortComplex

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable {S : ShortComplex (TauCeti.ComoduleCat.{u, v, w} R C)}

variable (S) in
/-- A short complex of comodules over a flat coalgebra is exact exactly when its underlying
linear maps are exact. -/
theorem comoduleCat_exact_iff_function_exact : S.Exact ↔ Function.Exact S.f S.g :=
  (S.exact_map_iff_of_faithful (forget₂ _ (ModuleCat.{w} R))).symm.trans
    (ShortExact.moduleCat_exact_iff_function_exact (S.map (forget₂ _ (ModuleCat.{w} R))))

/-- The first map of a short exact sequence of comodules over a flat coalgebra is injective. -/
theorem ShortExact.comoduleCat_injective_f (hS : S.ShortExact) : Function.Injective S.f :=
  (hS.map_of_exact (forget₂ _ (ModuleCat.{w} R))).moduleCat_injective_f

/-- The second map of a short exact sequence of comodules over a flat coalgebra is surjective. -/
theorem ShortExact.comoduleCat_surjective_g (hS : S.ShortExact) : Function.Surjective S.g :=
  (hS.map_of_exact (forget₂ _ (ModuleCat.{w} R))).moduleCat_surjective_g

end CategoryTheory.ShortComplex

namespace TauCeti.ComoduleCat

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]

/-- A short complex of comodules over a flat coalgebra whose underlying linear maps are exact is
exact. -/
theorem shortComplex_exact (S : ShortComplex (ComoduleCat.{u, v, w} R C))
    (exac : Function.Exact S.f S.g) : S.Exact :=
  S.comoduleCat_exact_iff_function_exact.2 exac

/-- A short complex of comodules over a flat coalgebra is short exact when its underlying linear
maps are exact, the first injective and the second surjective. -/
theorem shortComplex_shortExact (S : ShortComplex (ComoduleCat.{u, v, w} R C))
    (exac : Function.Exact S.f S.g) (inj : Function.Injective S.f)
    (surj : Function.Surjective S.g) : S.ShortExact where
  exact := shortComplex_exact S exac
  mono_f :=
    (forget₂ _ (ModuleCat.{w} R)).mono_of_mono_map ((ModuleCat.mono_iff_injective _).2 inj)
  epi_g :=
    (forget₂ _ (ModuleCat.{w} R)).epi_of_epi_map ((ModuleCat.epi_iff_surjective _).2 surj)

end TauCeti.ComoduleCat
