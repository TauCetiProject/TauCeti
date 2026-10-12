/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Forgetting the scalars of a topological module

A topological module over a topological ring `R` is in particular a topological abelian group,
that is a topological `ℤ`-module for the canonical action of `ℤ`, and a continuous `R`-linear map
is a continuous `ℤ`-linear map. This file packages that observation as the functor
`TopModuleCat.restrictScalarsInt : TopModuleCat R ⥤ TopModuleCat ℤ` and proves that it preserves
homology: the kernel of a continuous linear map and the cokernel with its quotient topology do not
see the scalars, so the functor preserves kernels and cokernels, hence homology.

The target ring is `ℤ` and not an arbitrary ring `S` with a ring homomorphism `S →+* R`: only for
`ℤ` does every topological `R`-module carry a *canonical* `S`-module structure, the one every
statement about topological abelian groups already uses, and restricting scalars along
`Int.castRingHom R` would produce the structure `Module.compHom`, which agrees with the canonical
one only propositionally. The application is continuous cohomology: Mathlib's
`continuousCohomology n X` for `X : TopRep R G` is the homology of a complex of topological
`R`-modules, and forgetting the scalars identifies it with the cohomology of the underlying
topological representation over `ℤ`, on which the explicit low-degree descriptions are stated.

## Main definitions

* `TopModuleCat.restrictScalarsInt`: the functor forgetting the scalars, with its instances
  `Additive` and `PreservesHomology`.
* `TopModuleCat.restrictScalarsInt.kerEquiv`, `TopModuleCat.restrictScalarsInt.cokerEquiv`: the
  kernel and the cokernel of a continuous linear map, computed after forgetting the scalars, are
  the kernel and the cokernel computed before.

## Main results

* `TopModuleCat.restrictScalarsInt.preservesHomology`: forgetting the scalars preserves homology,
  so that `CategoryTheory.ShortComplex.mapHomologyIso` identifies the homology computed after
  forgetting the scalars with the underlying topological abelian group of the homology.
-/

public section

open CategoryTheory Limits

namespace TopModuleCat

universe v u

variable {R : Type u} [Ring R] [TopologicalSpace R]

/-! ### The functor -/

/-- Forgetting the scalars of a topological `R`-module: the underlying topological abelian group,
as a topological `ℤ`-module for the canonical action of `ℤ`, with a continuous `R`-linear map read
as a continuous `ℤ`-linear map. The body is exposed because a consumer must see that the
underlying type of `restrictScalarsInt.obj M` is that of `M` before it can name its elements. -/
@[expose] def restrictScalarsInt : TopModuleCat.{v} R ⥤ TopModuleCat.{v} ℤ where
  obj M := of ℤ M
  map f := ofHom (f.hom.restrictScalars ℤ)

/-- The object underlying `M` after forgetting the scalars is `M` as a topological `ℤ`-module. -/
@[simp]
theorem restrictScalarsInt_obj (M : TopModuleCat.{v} R) : restrictScalarsInt.obj M = of ℤ M :=
  (rfl)

/-- Forgetting the scalars of a morphism restricts its scalars to `ℤ`. -/
theorem restrictScalarsInt_map_hom {M N : TopModuleCat.{v} R} (f : M ⟶ N) :
    (restrictScalarsInt.map f).hom = f.hom.restrictScalars ℤ :=
  (rfl)

/-- Forgetting the scalars does not change the underlying function of a morphism. -/
@[simp]
theorem restrictScalarsInt_map_apply {M N : TopModuleCat.{v} R} (f : M ⟶ N) (x : M) :
    restrictScalarsInt.map f x = f x :=
  (rfl)

instance : restrictScalarsInt.{v} (R := R).Additive where
  map_add := (rfl)

namespace restrictScalarsInt

variable {M N : TopModuleCat.{v} R} (f : M ⟶ N)

/-! ### Kernels -/

/-- The kernel of `f`, computed after forgetting the scalars, is the kernel of `f` computed before,
as a topological `ℤ`-module. -/
def kerEquiv : ker (restrictScalarsInt.map f) ≃L[ℤ] restrictScalarsInt.obj (ker f) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 continuous_subtype_val

/-- `kerEquiv` is the identity on the underlying elements. -/
@[simp]
theorem coe_kerEquiv_apply (x : ker (restrictScalarsInt.map f)) :
    (kerEquiv f x).1 = x.1 :=
  (rfl)

/-- The kernel of `f`, computed after forgetting the scalars, is the kernel of `f` computed
before, as an isomorphism in `TopModuleCat ℤ`. -/
noncomputable def kerIso : ker (restrictScalarsInt.map f) ≅ restrictScalarsInt.obj (ker f) :=
  ofIso (kerEquiv f)

/-- `kerIso` is compatible with the inclusions of the kernels. -/
@[reassoc (attr := simp)]
theorem kerIso_hom_comp_map_kerι :
    (kerIso f).hom ≫ restrictScalarsInt.map (kerι f) = kerι (restrictScalarsInt.map f) := by
  ext x
  rfl

instance preservesKernel : PreservesLimit (parallelPair f 0) restrictScalarsInt.{v} :=
  preservesLimit_of_preserves_limit_cone (isLimitKer f) <|
    (isLimitMapConeForkEquiv' restrictScalarsInt (kerι_comp f)).symm <|
      IsLimit.ofIsoLimit (isLimitKer (restrictScalarsInt.map f))
        (Fork.ext (kerIso f) (kerIso_hom_comp_map_kerι f))

/-! ### Cokernels -/

/-- The cokernel of `f`, computed after forgetting the scalars, is the cokernel of `f` computed
before, as a topological `ℤ`-module. Both carry the quotient topology of `N`. -/
noncomputable def cokerEquiv :
    coker (restrictScalarsInt.map f) ≃L[ℤ] restrictScalarsInt.obj (coker f) :=
  { Submodule.Quotient.restrictScalarsEquiv ℤ (LinearMap.range (f.hom : M →ₗ[R] N)) with
    continuous_toFun :=
      (Submodule.isOpenQuotientMap_mkQ
        ((LinearMap.range (f.hom : M →ₗ[R] N)).restrictScalars ℤ)).isQuotientMap.continuous_iff.2
          continuous_quot_mk
    continuous_invFun :=
      (Submodule.isOpenQuotientMap_mkQ
        (LinearMap.range (f.hom : M →ₗ[R] N))).isQuotientMap.continuous_iff.2 continuous_quot_mk }

/-- `cokerEquiv` sends the class of `x` to the class of `x`. -/
@[simp]
theorem cokerEquiv_mk (x : N) :
    cokerEquiv f (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  (rfl)

/-- The cokernel of `f`, computed after forgetting the scalars, is the cokernel of `f` computed
before, as an isomorphism in `TopModuleCat ℤ`. -/
noncomputable def cokerIso : coker (restrictScalarsInt.map f) ≅ restrictScalarsInt.obj (coker f) :=
  ofIso (cokerEquiv f)

/-- `cokerIso` is compatible with the projections onto the cokernels. -/
@[reassoc (attr := simp)]
theorem cokerπ_comp_cokerIso_hom :
    cokerπ (restrictScalarsInt.map f) ≫ (cokerIso f).hom = restrictScalarsInt.map (cokerπ f) := by
  ext x
  rfl

instance preservesCokernel : PreservesColimit (parallelPair f 0) restrictScalarsInt.{v} :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCoker f) <|
    (isColimitMapCoconeCoforkEquiv' restrictScalarsInt (comp_cokerπ f)).symm <|
      IsColimit.ofIsoColimit (isColimitCoker (restrictScalarsInt.map f))
        (Cofork.ext (cokerIso f) (cokerπ_comp_cokerIso_hom f))

instance preservesHomology : restrictScalarsInt.{v} (R := R).PreservesHomology where

end restrictScalarsInt

end TopModuleCat
