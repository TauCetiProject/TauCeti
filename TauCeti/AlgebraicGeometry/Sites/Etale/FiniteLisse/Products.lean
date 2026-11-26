/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.CategoryTheory.Sites.LocallyConstant.FiniteProducts

/-!
# Finite products of finite lisse sheaves

Let `S` be a scheme and `Λ` a ring. The finite lisse étale sheaves of `Λ`-modules on `S`
(`CategoryTheory.Sheaf.IsFiniteLisse`) form a property of objects of
`Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)` which contains the zero sheaf and is closed under
isomorphisms and finite products, hence under finite biproducts. For two finite lisse sheaves
trivialized over two étale covers, the product is trivialized over their common refinement, with
value the product of the two finitely generated modules
(`CategoryTheory.Sheaf.IsLocallyConstantIn.prod`).

## Main declarations

* The instances `ContainsZero` and `IsClosedUnderFiniteProducts` for the object property
  `CategoryTheory.Sheaf.IsFiniteLisse`; it is closed under isomorphisms by the instance for
  `CategoryTheory.Sheaf.IsLocallyConstantIn`. Binary products, binary biproducts and zero sheaves
  are then finite lisse by the generic lemmas `ObjectProperty.prop_prod`,
  `ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts` and `ObjectProperty.prop_of_isZero`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe u

open CategoryTheory Limits ZeroObject AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

instance containsZero_isFiniteLisse :
    ObjectProperty.ContainsZero
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  exists_zero :=
    ⟨0, isZero_zero _, .of_isTerminal (ModuleCat.isFG Λ).prop_terminal (isZero_zero _).isTerminal⟩

instance isClosedUnderFiniteProducts_isFiniteLisse :
    ObjectProperty.IsClosedUnderFiniteProducts
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) :=
  inferInstanceAs (ObjectProperty.IsClosedUnderFiniteProducts
    (IsLocallyConstantIn (smallEtaleTopology S) (ModuleCat.isFG Λ)))

end CategoryTheory.Sheaf
