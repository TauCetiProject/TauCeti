/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.Over.Sheafify
public import TauCeti.CategoryTheory.Sites.LocallyConstant.Tensor
public import TauCeti.CategoryTheory.Sites.Monoidal

/-!
# The tensor product of étale sheaves of modules and its stalks

Let `S` be a scheme and `Λ` a commutative ring. The category of sheaves of `Λ`-modules on the
small étale site of `S` is symmetric monoidal: the tensor product of two sheaves is the
sheafification of their sectionwise tensor product, and the unit is the constant sheaf `Λ`.
This is Mathlib's `CategoryTheory.Sheaf.monoidalCategory`, which applies because the small étale
site has enough points, so that sheafification is compatible with tensor products
(`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W`).

The stalk `TauCeti.AlgebraicGeometry.Scheme.etaleStalk Λ s` at a geometric point `s` is a monoidal
functor, because fibre functors of points commute with sheafification and with filtered colimits,
which commute with tensor products of modules. In particular the stalk of `F ⊗ G` is the tensor
product of the stalks (`CategoryTheory.Functor.Monoidal.μIso`), and the stalk of the unit is `Λ`
(`CategoryTheory.Functor.Monoidal.εIso`).

Change of coefficients also commutes with stalks: for restriction of scalars this is Mathlib's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso`, and for extension of scalars,
the sheafification of the sectionwise extension of scalars, it is
`CategoryTheory.GrothendieckTopology.Point.composeAndSheafifyCompSheafFiberIso`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.monoidalCategorySheafModuleCat`,
  `TauCeti.AlgebraicGeometry.Scheme.symmetricCategorySheafModuleCat`: the symmetric monoidal
  structure on `Sheaf (smallEtaleTopology S) (ModuleCat Λ)`.
* `TauCeti.AlgebraicGeometry.Scheme.isMonoidal_W_smallEtaleTopology`: sheafification of
  presheaves of `Λ`-modules on the small étale site is compatible with tensor products.
* `TauCeti.AlgebraicGeometry.Scheme.monoidalEtaleStalk`: the stalk functor
  `TauCeti.AlgebraicGeometry.Scheme.etaleStalk Λ s` is monoidal.
* `CategoryTheory.Sheaf.IsFiniteLisse.tensor`: the tensor product of two finite lisse sheaves is
  finite lisse.
* `CategoryTheory.Sheaf.isFiniteLisse_tensorUnit`: the unit, the constant sheaf `Λ`
  (`CategoryTheory.Sheaf.tensorUnitIsoConstantSheaf`), is finite lisse, so that finite lisse
  sheaves form a monoidal subcategory (`CategoryTheory.Sheaf.isMonoidal_isFiniteLisse`).

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IV, §12, for the tensor product of
  sheaves of modules, and Exposé VIII, §3, for stalks at geometric points.
* The Stacks Project, Section 59.29, Stalks of étale sheaves.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (Λ : Type u) [CommRing Λ]

/-- Sheafification of presheaves of `Λ`-modules on the small étale site is compatible with tensor
products, because the small étale site has enough points. -/
instance isMonoidal_W_smallEtaleTopology :
    ((smallEtaleTopology S).W (A := ModuleCat.{u} Λ)).IsMonoidal :=
  have : PreservesLimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u} Λ)) :=
    (ModuleCat.adj.{u} Λ).rightAdjoint_preservesLimits
  have : (smallEtaleTopology S).HasSheafCompose (forget (ModuleCat.{u} Λ)) :=
    hasSheafCompose_of_preservesMulticospan _ _
  instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints.{u}
    (C := S.Etale) (J := smallEtaleTopology S) (ModuleCat.{u} Λ)

/-- The monoidal structure on étale sheaves of `Λ`-modules: the tensor product is the
sheafification of the sectionwise tensor product. -/
noncomputable instance monoidalCategorySheafModuleCat :
    MonoidalCategory (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :=
  Sheaf.monoidalCategory _ _

noncomputable instance symmetricCategorySheafModuleCat :
    SymmetricCategory (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :=
  Sheaf.symmetricCategory _ _

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The stalk functor at a geometric point is monoidal. -/
noncomputable instance monoidalEtaleStalk : (etaleStalk Λ s).Monoidal :=
  inferInstanceAs (pointSmallEtale s).sheafFiber.Monoidal

end TauCeti.AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf

open MonoidalCategory

variable {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- **Tensor products of finite lisse sheaves.** The tensor product of two finite lisse étale
sheaves of `Λ`-modules is finite lisse: étale locally it is the tensor product of two constant
sheaves on finitely generated modules, which is the constant sheaf on their tensor product. -/
theorem IsFiniteLisse.tensor {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) : (F ⊗ G).IsFiniteLisse :=
  IsLocallyConstantIn.tensor (R := fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M)
    (fun (M N : ModuleCat.{u} Λ) (_ : Module.Finite Λ M) (_ : Module.Finite Λ N) ↦
      inferInstanceAs (Module.Finite Λ (TensorProduct Λ M N))) hF hG

/-- The unit of the tensor product of étale sheaves of `Λ`-modules is finite lisse. -/
theorem isFiniteLisse_tensorUnit :
    (𝟙_ (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))).IsFiniteLisse :=
  haveI : Module.Finite Λ (𝟙_ (ModuleCat.{u} Λ)) := inferInstanceAs (Module.Finite Λ Λ)
  (isFiniteLisse_constantSheaf _).of_iso (tensorUnitIsoConstantSheaf _ _).symm

/-- Finite lisse étale sheaves of `Λ`-modules form a monoidal subcategory. -/
instance isMonoidal_isFiniteLisse :
    (ObjectProperty.IsMonoidal fun F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ) ↦
      F.IsFiniteLisse) where
  prop_unit := isFiniteLisse_tensorUnit
  prop_tensor _ _ hF hG := hF.tensor hG

end CategoryTheory.Sheaf
