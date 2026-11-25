/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Biprod
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Direct sums of `𝒪ₓ`-modules

The site-level closure properties of direct sums of sheaves of modules
(`TauCeti/Algebra/Category/ModuleCat/Sheaf/Quasicoherent/Biprod.lean`) specialize to a scheme `X`
by taking the sheaf of rings to be the structure sheaf of `X`. Since `X.Modules` carries its own
category and abelian structures, instance search does not find the site-level instances for
`M ⊞ N`, and they are restated here. This file also records the finite-biproduct decomposition
`freeTensorIsoBiproduct` in `X.Modules` and specializes the zero and finite-product closure
instances for finite presentation. These specializations pre-elaborate the ringed-site hypotheses
to stay within the default typeclass search-size bound.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.instHasFiniteBiproducts`: `X.Modules` has finite biproducts.
* `AlgebraicGeometry.Scheme.Modules.freeTensorIsoBiproduct`: `𝒪_X^{⊕I} ⊗ L ≅ ⨁_{I} L` for finite
  `I`.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biprod`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_biprod`,
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_biprod` and
  `AlgebraicGeometry.Scheme.Modules.isLocallyFree_biprod`: the direct sum of two quasi-coherent
  (respectively finite type, finitely presented, locally free) `𝒪ₓ`-modules is again so. In
  particular, direct sums of finite locally free `𝒪ₓ`-modules are finite locally free.
* `AlgebraicGeometry.Scheme.Modules.containsZero_isFinitePresentation`,
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderBinaryProducts_isFinitePresentation` and
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderFiniteProducts_isFinitePresentation`:
  finitely presented sheaves contain zero and are closed under binary and finite products.
-/

public section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TauCeti

universe u

/-- The category of `𝒪_X`-modules has finite biproducts. -/
instance instHasFiniteBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  Abelian.hasFiniteBiproducts

/-- Tensoring the free `𝒪_X`-module on a finite type `I` with `L` gives the biproduct of `I`
copies of `L`. -/
noncomputable def freeTensorIsoBiproduct {X : Scheme.{u}} (I : Type u) [Finite I] (L : X.Modules) :
    ((SheafOfModules.free I : X.Modules) ⊗ L : X.Modules) ≅ ⨁ fun _ : I ↦ L :=
  have : Fintype I := .ofFinite I
  (tensorRight L).mapIso
      ((biproduct.isColimit (C := X.Modules)
        (fun _ : I ↦ (𝟙_ X.Modules : X.Modules))).coconePointUniqueUpToIso
        (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)).symm ≪≫
    (tensorRight L).mapBiproduct (fun _ : I ↦ (𝟙_ X.Modules : X.Modules)) ≪≫
    biproduct.mapIso fun _ : I ↦ λ_ L

/-- On the `i`-th summand, the inverse of `freeTensorIsoBiproduct` is `(λ_ L).inv` followed by
`(tensorRight L).map (ιFree i)`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_freeTensorIsoBiproduct_inv {X : Scheme.{u}} {I : Type u} [Finite I]
    (L : X.Modules) (i : I) :
    biproduct.ι (fun _ : I ↦ L) i ≫ (freeTensorIsoBiproduct I L).inv =
      (λ_ L).inv ≫ (tensorRight L).map
        (SheafOfModules.ιFree i : (𝟙_ X.Modules : X.Modules) ⟶
          (SheafOfModules.free I : X.Modules)) :=
  letI : Fintype I := .ofFinite I
  (Category.assoc _ _ _).trans <| (Category.assoc _ _ _).trans <|
    (biproduct.ι_map_assoc (fun _ : I ↦ (λ_ L).inv) i _).trans <|
      congrArg ((λ_ L).inv ≫ ·) <|
        (biproduct.ι_desc_assoc _ i _).trans <|
          ((tensorRight L).map_comp _ _).symm.trans <|
            congrArg (tensorRight L).map <|
              (biproduct.isColimit (C := X.Modules)
                (fun _ : I ↦ (𝟙_ X.Modules : X.Modules))).comp_coconePointUniqueUpToIso_hom
                (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I) ⟨i⟩

/-- On the `i`-th basis summand, `freeTensorIsoBiproduct` applies `λ_ L` followed by the `i`-th
coprojection into `⨁_I L`. -/
@[reassoc (attr := simp)]
theorem map_ιFree_freeTensorIsoBiproduct_hom {X : Scheme.{u}} {I : Type u} [Finite I]
    (L : X.Modules) (i : I) :
    (tensorRight L).map
        (SheafOfModules.ιFree i : (𝟙_ X.Modules : X.Modules) ⟶
          (SheafOfModules.free I : X.Modules)) ≫
      (freeTensorIsoBiproduct I L).hom =
      (λ_ L).hom ≫ biproduct.ι (fun _ : I ↦ L) i := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  exact (biproduct_ι_freeTensorIsoBiproduct_inv L i).symm

variable {X : Scheme.{u}} (M N : X.Modules)

/-- The direct sum of two quasi-coherent `𝒪ₓ`-modules is quasi-coherent. -/
instance isQuasicoherent_biprod [M.IsQuasicoherent]
    [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_biprod (M := M) (N := N)

/-- The direct sum of two `𝒪ₓ`-modules of finite type is of finite type. -/
instance isFiniteType_biprod [M.IsFiniteType]
    [N.IsFiniteType] : (M ⊞ N).IsFiniteType :=
  SheafOfModules.isFiniteType_biprod (M := M) (N := N)

/-- The direct sum of two finitely presented `𝒪ₓ`-modules is finitely presented. -/
instance isFinitePresentation_biprod
    [M.IsFinitePresentation] [N.IsFinitePresentation] : (M ⊞ N).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_biprod (M := M) (N := N)

/-- The direct sum of two locally free `𝒪ₓ`-modules is locally free. -/
instance isLocallyFree_biprod [M.IsLocallyFree]
    [N.IsLocallyFree] : (M ⊞ N).IsLocallyFree :=
  SheafOfModules.isLocallyFree_biprod (M := M) (N := N)

-- These specializations pre-elaborate the ringed-site hypotheses: synthesizing the site-level
-- instances directly for `X.ringCatSheaf` exceeds the default typeclass search size (128).
/-- The zero module sheaf is finitely presented. -/
instance containsZero_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero :=
  TauCeti.SheafOfModules.containsZero_isFinitePresentation (R := X.ringCatSheaf)

/-- Finitely presented sheaves are closed under binary products, computed as direct sums. -/
instance isClosedUnderBinaryProducts_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderBinaryProducts :=
  TauCeti.SheafOfModules.isClosedUnderBinaryProducts_isFinitePresentation (R := X.ringCatSheaf)

/-- Finitely presented sheaves are closed under finite products. -/
instance isClosedUnderFiniteProducts_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := .mk'

end AlgebraicGeometry.Scheme.Modules
