/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import TauCeti.AlgebraicGeometry.Sites.Etale.Constructible
public import TauCeti.AlgebraicGeometry.Sites.Etale.Monoidal.Pullback

/-!
# Tensor products of constructible étale sheaves

Let `X` be a scheme and `Λ` a commutative ring. This file shows that finite lisse and
constructible étale sheaves of `Λ`-modules on `X` are closed under tensor products and contain the
unit, the constant sheaf `Λ`. For constructible sheaves, a common refinement of the two
stratifications reduces the statement to finite lisse sheaves on each stratum, since the inverse
image along a stratum commutes with tensor products
(`AlgebraicGeometry.Scheme.Hom.smallEtalePullbackTensorIso`).

## Main declarations

* `CategoryTheory.Sheaf.isFiniteLisse_tensorUnit`: the unit `𝟙_` is finite lisse.
* `CategoryTheory.Sheaf.IsConstructibleOn.tensor`: if `F` and `G` are constructible on an open
  `U`, so is `F ⊗ G`.
* `AlgebraicGeometry.Scheme.constructibleSheaf_tensor`: the tensor product of two constructible
  sheaves is constructible.
* The instances `CategoryTheory.Sheaf.isMonoidal_isFiniteLisse` and
  `AlgebraicGeometry.Scheme.isMonoidal_constructibleSheaf`: finite lisse sheaves and
  constructible sheaves form monoidal subcategories (`CategoryTheory.ObjectProperty.IsMonoidal`).

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §§2–3.
* The Stacks Project, Sections 59.71–59.74.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Scheme
  TauCeti.AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- The unit of the tensor product of étale sheaves of `Λ`-modules, the sheafification of the
constant presheaf `Λ`, is the constant sheaf `Λ`. -/
noncomputable def tensorUnitIsoConstantSheaf :
    𝟙_ (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) ≅
      (constantSheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)).obj (𝟙_ (ModuleCat.{u} Λ)) :=
  Functor.Monoidal.εIso (presheafToSheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) ≪≫
    (presheafToSheaf _ _).mapIso (NatIso.ofComponents fun _ ↦ Iso.refl _)

/-- The unit of the tensor product of étale sheaves of `Λ`-modules is finite lisse. -/
theorem isFiniteLisse_tensorUnit :
    (𝟙_ (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))).IsFiniteLisse :=
  haveI : Module.Finite Λ (𝟙_ (ModuleCat.{u} Λ)) := inferInstanceAs (Module.Finite Λ Λ)
  (isFiniteLisse_constantSheaf _).of_iso tensorUnitIsoConstantSheaf.symm

/-- Finite lisse étale sheaves of `Λ`-modules form a monoidal subcategory. -/
instance isMonoidal_isFiniteLisse :
    (ObjectProperty.IsMonoidal fun F : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ) ↦
      F.IsFiniteLisse) where
  prop_unit := isFiniteLisse_tensorUnit
  prop_tensor _ _ hF hG := hF.tensor hG

variable {F G : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)} {U : X.Opens}

/-- **Tensor products of constructible sheaves.** If `F` and `G` are constructible on an open
`U`, so is `F ⊗ G`: on the strata of a common refinement of the two stratifications both are
finite lisse, and the inverse image along a stratum commutes with tensor products. -/
theorem IsConstructibleOn.tensor (hF : F.IsConstructibleOn U) (hG : G.IsConstructibleOn U) :
    (F ⊗ G).IsConstructibleOn U := by
  obtain ⟨S, hS⟩ := isConstructibleOn_iff.mp hF
  obtain ⟨T, hT⟩ := isConstructibleOn_iff.mp hG
  refine isConstructibleOn_iff.mpr ⟨S.inf T, fun p ↦ ?_⟩
  exact (((S.inf_refines_left T).isFiniteLisse hS p).tensor
    ((S.inf_refines_right T).isFiniteLisse hT p)).of_iso
      (((S.inf T).f p).smallEtalePullbackTensorIso Λ F G).symm

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Sheaf

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]
  {F G : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)}

/-- **Tensor products of constructible sheaves.** The tensor product of two constructible étale
sheaves of `Λ`-modules is constructible. -/
theorem constructibleSheaf_tensor (hF : X.constructibleSheaf Λ F)
    (hG : X.constructibleSheaf Λ G) : X.constructibleSheaf Λ (F ⊗ G) :=
  constructibleSheaf_iff.mpr fun U hU ↦
    (constructibleSheaf_iff.mp hF U hU).tensor (constructibleSheaf_iff.mp hG U hU)

/-- Constructible étale sheaves of `Λ`-modules form a monoidal subcategory. -/
instance isMonoidal_constructibleSheaf : (X.constructibleSheaf Λ).IsMonoidal where
  prop_unit := constructibleSheaf_of_isFiniteLisse isFiniteLisse_tensorUnit
  prop_tensor _ _ hF hG := constructibleSheaf_tensor hF hG

end AlgebraicGeometry.Scheme
