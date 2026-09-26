/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Product
public import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The abelian category of finite comodules

Finitely generated comodules over a flat coalgebra over a Noetherian commutative ring form
an abelian category. Their kernels and cokernels are computed in the category of all comodules.
In particular, finite-dimensional comodules over a field form an abelian category, with an
exact forgetful functor to vector spaces. For coordinate Hopf algebras this supplies the
abelian and exact structures of the Tannakian representation category.

The full-subcategory argument uses Mathlib's `ObjectProperty` kernel and cokernel closure API.
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

/-- Finite comodules over a flat coalgebra over a Noetherian commutative ring are abelian. -/
instance : Abelian (FGComoduleCat.{u, v, w} R C) where

instance {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (incl (R := R) (C := C)) :=
  (ComoduleCat.isFG R C).preservesKernels_ι f

omit [IsNoetherianRing R] [Module.Flat R C] in
instance {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (incl (R := R) (C := C)) :=
  (ComoduleCat.isFG R C).preservesCokernels_ι f

/-- Inclusion of finite comodules preserves finite limits. -/
instance : PreservesFiniteLimits (incl (R := R) (C := C) :
    FGComoduleCat.{u, v, w} R C ⥤ _) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

omit [IsNoetherianRing R] [Module.Flat R C] in
/-- Inclusion of finite comodules preserves finite colimits. -/
instance : PreservesFiniteColimits (incl (R := R) (C := C) :
    FGComoduleCat.{u, v, w} R C ⥤ _) :=
  by
    let : HasCoequalizers (FGComoduleCat.{u, v, w} R C) :=
      Preadditive.hasCoequalizers_of_hasCokernels
    exact Functor.preservesFiniteColimits_of_preservesCokernels _

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
