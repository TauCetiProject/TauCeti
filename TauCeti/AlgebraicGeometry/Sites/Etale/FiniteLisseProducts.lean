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

* `CategoryTheory.Sheaf.IsFiniteLisse.prod`, `CategoryTheory.Sheaf.IsFiniteLisse.biprod`,
  `CategoryTheory.Sheaf.IsFiniteLisse.of_isZero`: binary products, binary biproducts and zero
  sheaves.
* The instances `ContainsZero` and `IsClosedUnderFiniteProducts` for the object property
  `CategoryTheory.Sheaf.IsFiniteLisse`; it is closed under isomorphisms by the instance for
  `CategoryTheory.Sheaf.IsLocallyConstantIn`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe u

open CategoryTheory Limits ZeroObject AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- **Binary products of finite lisse sheaves.** The product of two finite lisse étale sheaves of
`Λ`-modules is finite lisse. -/
theorem IsFiniteLisse.prod {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) : (F ⨯ G).IsFiniteLisse :=
  IsLocallyConstantIn.prod hF hG

/-- **Binary biproducts of finite lisse sheaves.** The direct sum of two finite lisse étale sheaves
of `Λ`-modules is finite lisse. -/
theorem IsFiniteLisse.biprod {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) : (F ⊞ G).IsFiniteLisse :=
  ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts _ hF hG

/-- **Zero sheaves are finite lisse.** A zero étale sheaf of `Λ`-modules is the constant sheaf on
the zero module. -/
theorem IsFiniteLisse.of_isZero {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : IsZero F) : F.IsFiniteLisse :=
  .of_isTerminal (ModuleCat.isFG Λ).prop_terminal hF.isTerminal

instance containsZero_isFiniteLisse :
    ObjectProperty.ContainsZero
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  exists_zero := ⟨0, isZero_zero _, .of_isZero (isZero_zero _)⟩

instance isClosedUnderFiniteProducts_isFiniteLisse :
    ObjectProperty.IsClosedUnderFiniteProducts
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) :=
  inferInstanceAs (ObjectProperty.IsClosedUnderFiniteProducts
    (IsLocallyConstantIn (smallEtaleTopology S) (ModuleCat.isFG Λ)))

end CategoryTheory.Sheaf
