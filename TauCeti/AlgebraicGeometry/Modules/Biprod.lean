/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Biprod

/-!
# Direct sums of `𝒪ₓ`-modules

The site-level closure properties of direct sums of sheaves of modules
(`TauCeti/Algebra/Category/ModuleCat/Sheaf/Quasicoherent/Biprod.lean`) specialize to a scheme `X`
by taking the sheaf of rings to be the structure sheaf of `X`. Since `X.Modules` carries its own
category and abelian structures, instance search does not find the site-level instances for
`M ⊞ N`, and they are restated here. This file also specializes the zero and finite-product
closure instances for finite presentation. These specializations pre-elaborate the ringed-site
hypotheses to stay within the default typeclass search-size bound.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biprod`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_biprod`,
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_biprod` and
  `AlgebraicGeometry.Scheme.Modules.isLocallyFree_biprod`: the direct sum of two quasi-coherent
  (respectively finite type, finitely presented, locally free) `𝒪ₓ`-modules is again so. In
  particular, direct sums of finite locally free `𝒪ₓ`-modules are finite locally free.
* `AlgebraicGeometry.Scheme.Modules.containsZero_isQuasicoherent`,
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderBinaryProducts_isQuasicoherent`,
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderFiniteProducts_isQuasicoherent`,
  `AlgebraicGeometry.Scheme.Modules.containsZero_isFinitePresentation`,
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderBinaryProducts_isFinitePresentation` and
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderFiniteProducts_isFinitePresentation`:
  quasi-coherent and finitely presented sheaves contain zero and are closed under binary and finite
  products.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct` and
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_biproduct`: a finite biproduct of
  quasi-coherent (respectively finitely presented) `𝒪ₓ`-modules is again so.
-/

public section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Limits TauCeti

universe u

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
/-- The zero module sheaf is quasi-coherent. -/
instance containsZero_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero where
  exists_zero := ⟨_, TauCeti.SheafOfModules.isZero_free (S := X.ringCatSheaf) PEmpty.{u + 1},
    inferInstance⟩

/-- Quasi-coherent sheaves are closed under binary products, computed as direct sums. -/
instance isClosedUnderBinaryProducts_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun A B hA hB ↦ by
    let := hA
    let := hB
    exact isQuasicoherent_biprod A B

/-- Quasi-coherent sheaves are closed under finite products. -/
instance isClosedUnderFiniteProducts_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteProducts := .mk'

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

/-- A finite biproduct of quasi-coherent `𝒪ₓ`-modules is quasi-coherent. -/
instance isQuasicoherent_biproduct {J : Type*} [Finite J] (F : J → X.Modules)
    [HasBiproduct F] [∀ j, (F j).IsQuasicoherent] :
    (⨁ F).IsQuasicoherent := by
  have := Fintype.ofFinite J
  have : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let G : Fin (Fintype.card J) → X.Modules := fun i ↦ F (e i)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((biproduct.isoProduct G).symm ≪≫
      biproduct.whiskerEquiv (f := G) (g := F) e fun _ ↦ Iso.refl _)
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_pi G fun _ ↦ inferInstance)

/-- A finite biproduct of finitely presented `𝒪ₓ`-modules is finitely presented. -/
instance isFinitePresentation_biproduct {J : Type*} [Finite J] (F : J → X.Modules)
    [HasBiproduct F] [∀ j, (F j).IsFinitePresentation] :
    (⨁ F).IsFinitePresentation := by
  have := Fintype.ofFinite J
  have : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let G : Fin (Fintype.card J) → X.Modules := fun i ↦ F (e i)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((biproduct.isoProduct G).symm ≪≫
      biproduct.whiskerEquiv (f := G) (g := F) e fun _ ↦ Iso.refl _)
    ((SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_pi G fun _ ↦ inferInstance)

end AlgebraicGeometry.Scheme.Modules
