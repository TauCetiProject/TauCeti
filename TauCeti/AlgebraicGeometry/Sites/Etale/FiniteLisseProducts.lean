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

* `CategoryTheory.Sheaf.isFiniteLisse_eq_isLocallyConstantIn_isFG`,
  `CategoryTheory.Sheaf.isFiniteLisse_iff_isLocallyConstantIn_isFG`: finite lisse sheaves are the
  sheaves which are locally constant with values in Mathlib's `ModuleCat.isFG Λ`.
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

/-- The finite lisse étale sheaves of `Λ`-modules are the sheaves which are locally constant with
values in the finitely generated `Λ`-modules, expressed through Mathlib's `ModuleCat.isFG Λ`. -/
theorem isFiniteLisse_eq_isLocallyConstantIn_isFG :
    (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) =
      IsLocallyConstantIn (smallEtaleTopology S) (ModuleCat.isFG Λ) :=
  congrArg (IsLocallyConstantIn (smallEtaleTopology S))
    (funext fun M : ModuleCat.{u} Λ ↦ propext M.isFG_iff).symm

/-- An étale sheaf of `Λ`-modules is finite lisse if and only if it is locally constant with values
in the finitely generated `Λ`-modules, expressed through Mathlib's `ModuleCat.isFG Λ`. -/
theorem isFiniteLisse_iff_isLocallyConstantIn_isFG
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :
    F.IsFiniteLisse ↔ F.IsLocallyConstantIn (smallEtaleTopology S) (ModuleCat.isFG Λ) :=
  iff_of_eq (congrFun isFiniteLisse_eq_isLocallyConstantIn_isFG F)

/-- **Binary products of finite lisse sheaves.** The product of two finite lisse étale sheaves of
`Λ`-modules is finite lisse. -/
theorem IsFiniteLisse.prod {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) : (F ⨯ G).IsFiniteLisse := by
  rw [isFiniteLisse_iff_isLocallyConstantIn_isFG] at hF hG ⊢
  exact hF.prod hG

/-- **Binary biproducts of finite lisse sheaves.** The direct sum of two finite lisse étale sheaves
of `Λ`-modules is finite lisse. -/
theorem IsFiniteLisse.biprod {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (hG : G.IsFiniteLisse) : (F ⊞ G).IsFiniteLisse :=
  (hF.prod hG).of_iso (biprod.isoProd F G).symm

/-- **Zero sheaves are finite lisse.** A zero étale sheaf of `Λ`-modules is the constant sheaf on
the zero module. -/
theorem IsFiniteLisse.of_isZero {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : IsZero F) : F.IsFiniteLisse := by
  rw [isFiniteLisse_iff_isLocallyConstantIn_isFG]
  exact .of_isTerminal (ModuleCat.isFG Λ).prop_terminal hF.isTerminal

instance containsZero_isFiniteLisse :
    ObjectProperty.ContainsZero
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) where
  exists_zero := ⟨0, isZero_zero _, .of_isZero (isZero_zero _)⟩

instance isClosedUnderFiniteProducts_isFiniteLisse :
    ObjectProperty.IsClosedUnderFiniteProducts
      (IsFiniteLisse : ObjectProperty (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))) := by
  rw [isFiniteLisse_eq_isLocallyConstantIn_isFG]
  infer_instance

end CategoryTheory.Sheaf
