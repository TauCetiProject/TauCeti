/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Product
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# The abelian category of finite comodules

Finitely generated comodules over a flat coalgebra over a Noetherian commutative ring form
an abelian category. Their kernels and cokernels are computed in the category of all comodules.
In particular, finite-dimensional comodules over a field form an abelian category, with an
exact forgetful functor to vector spaces. Hence epimorphisms and monomorphisms of finite
comodules are surjective and injective (`TauCeti.FGComoduleCat.surjective_of_epi`,
`TauCeti.FGComoduleCat.injective_of_mono`). For coordinate Hopf algebras this supplies the
abelian and exact structures of the Tannakian representation category.

The full-subcategory argument shows that finite generation is closed under kernels and
cokernels; closure under finite products is in
`TauCeti.Algebra.Coalgebra.Comodule.Finite.Product`. Mathlib's `ObjectProperty`
abelian-subcategory instance then makes finite comodules abelian, and
`CategoryTheory.ObjectProperty.preservesFiniteLimits_ι` and
`CategoryTheory.ObjectProperty.preservesFiniteColimits_ι` make their inclusion into all comodules
exact.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

noncomputable section

namespace ComoduleCat

/-- Cokernels of morphisms between finite comodules are finite. -/
instance isFG_isClosedUnderCokernels :
    (isFG.{u, v, w} R C).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, s, hs, _, hN⟩
    let : Module.Finite R _ := hN
    exact Module.Finite.equiv (isoToLinearEquiv (R := R) (C := C)
      ((cokernelIsoRangeQuotient f).symm ≪≫ colimit.isoColimitCocone ⟨s, hs⟩))

variable [IsNoetherianRing R] [Module.Flat R C]

/-- Kernels of morphisms between finite comodules are finite over a Noetherian base. -/
instance isFG_isClosedUnderKernels :
    (isFG.{u, v, w} R C).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, s, hs, hM, _⟩
    let : Module.Finite R _ := hM
    have : Module.Finite R f.ker := f.ker.finite
    exact Module.Finite.equiv (isoToLinearEquiv (R := R) (C := C)
      ((kernelIsoKer f).symm ≪≫ limit.isoLimitCone ⟨s, hs⟩))

end ComoduleCat

namespace FGComoduleCat

variable [IsNoetherianRing R] [Module.Flat R C]

/-- The underlying-module functor on finite comodules preserves finite limits. -/
instance : PreservesFiniteLimits
    (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)) :=
  inferInstanceAs (PreservesFiniteLimits
    (incl ⋙ forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)))

omit [IsNoetherianRing R] [Module.Flat R C] in
/-- The underlying-module functor on finite comodules preserves finite colimits. -/
instance : PreservesFiniteColimits
    (forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)) :=
  inferInstanceAs (PreservesFiniteColimits
    (incl ⋙ forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)))

omit [IsNoetherianRing R] [Module.Flat R C] in
/-- An epimorphism of finite comodules is surjective. -/
theorem surjective_of_epi {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) [Epi f] :
    Function.Surjective f :=
  (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).map f))

/-- A monomorphism of finite comodules over a flat coalgebra over a Noetherian ring is
injective. -/
theorem injective_of_mono {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) [Mono f] :
    Function.Injective f :=
  (ModuleCat.mono_iff_injective _).1
    (inferInstance : Mono ((forget₂ (FGComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)).map f))

end FGComoduleCat

end

end TauCeti
