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
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import TauCeti.CategoryTheory.ObjectProperty

/-!
# The abelian category of finite comodules

Finitely generated comodules over a flat coalgebra over a Noetherian commutative ring form
an abelian category. Their kernels and cokernels are computed in the category of all comodules.
In particular, finite-dimensional comodules over a field form an abelian category, with an
exact forgetful functor to vector spaces. For coordinate Hopf algebras this supplies the
abelian and exact structures of the Tannakian representation category.

The full-subcategory argument shows that finite generation is closed under kernels, cokernels and
finite products. Mathlib's `ObjectProperty` abelian-subcategory instance then makes finite
comodules abelian, and `CategoryTheory.ObjectProperty.preservesFiniteLimits_ι` and
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

/-- Finite comodules are closed under binary products. -/
instance isFG_isClosedUnderBinaryProducts :
    (isFG.{u, v, w} R C).IsClosedUnderBinaryProducts :=
  have : HasBinaryBiproducts (ComoduleCat.{u, v, w} R C) := .of_hasBinaryProducts
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    let F := forget₂ (ComoduleCat.{u, v, w} R C) (ModuleCat.{w} R)
    have := preservesBinaryBiproducts_of_preservesBiproducts F
    let : Module.Finite R (F.obj M) := hM
    let : Module.Finite R (F.obj N) := hN
    exact Module.Finite.equiv
      ((F.mapBiprod M N ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv.symm)

/-- Finite comodules are closed under finite products. -/
instance isFG_isClosedUnderFiniteProducts :
    (isFG.{u, v, w} R C).IsClosedUnderFiniteProducts :=
  .mk'

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

end FGComoduleCat

end

end TauCeti
