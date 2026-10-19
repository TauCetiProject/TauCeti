/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Associator
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Coproducts
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Unit
public import TauCeti.Algebra.Homology.HomotopyCategory.Bifunctor

/-!
# The graded bimodule action on homotopy categories

For graded algebras `A` and `B`, the balanced tensor product `M ⊗_B N` of a graded
`(A, B)`-bimodule `M` and a graded left `B`-module `N`
(`TauCeti.GradedModuleCat.bimoduleModuleTensor`) totalizes to cochain complexes and descends to a
bifunctor

```text
K(grBimod (A, B)) ⥤ K(grMod B) ⥤ K(grMod A)
```

on homotopy categories of unbounded cochain complexes
(`CategoryTheory.Functor.map₂HomotopyCategory`).
The required total complexes exist because graded modules have all coproducts, and the action
preserves coproducts in each variable, which supplies the hypotheses of Mathlib's associator for
totalized bifunctors.

This file records the two structure isomorphisms of this action on homotopy categories:

* the regular graded bimodule `A`, placed in cohomological degree zero, acts as the identity
  functor of `K(grMod A)`;
* acting by the total tensor product `K₁ ⊗_B K₂` of two complexes of graded bimodules is
  isomorphic to acting by `K₂` and then by `K₁`.

Together with the invariance of the action under homotopy equivalences of complexes of bimodules,
these isomorphisms let a complex of bimodules with a two-sided tensor inverse up to homotopy act by
an autoequivalence of the homotopy category of graded modules
(`TauCeti.GradedModuleCat.bimoduleModuleTensorHomotopyEquivalence`), as the braid complexes of a
zigzag algebra do.

## Main definitions

* `TauCeti.GradedModuleCat.bimoduleModuleTensorHomotopy`: the action bifunctor on homotopy
  categories.
* `TauCeti.GradedModuleCat.bimoduleModuleTensorHomotopyLeftUnitor`: the regular bimodule in degree
  zero acts as the identity.
* `TauCeti.GradedModuleCat.bimoduleModuleTensorHomotopyAssociator`: acting by a total tensor
  product of complexes of bimodules is acting by its two factors in turn.
* `TauCeti.GradedModuleCat.bimoduleModuleTensorHomotopyEquivalence`: a complex of bimodules with a
  two-sided tensor inverse up to homotopy acts by an autoequivalence.

## References

* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*, J. Amer. Math.
  Soc. 15 (2002), Section 2, for the action of complexes of bimodules on homotopy categories of
  modules by tensor product.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex

namespace TauCeti.GradedModuleCat

universe w vM vN uk uA uB uC

variable {k : Type uk} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing k] [Ring A] [Ring B] [Ring C] [Algebra k A] [Algebra k B] [Algebra k C]

section Action

variable (Γ : InternalGrading k A) (Δ : InternalGrading k B)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece]

/-- The action of complexes of graded `(A, B)`-bimodules on the homotopy category of cochain
complexes of graded `B`-modules: the totalized balanced tensor product `K ⊗_B L`, which only depends
on `K` and `L` up to homotopy. -/
-- Reducible so that the lemmas about `Functor.map₂HomotopyCategory` apply to it.
abbrev bimoduleModuleTensorHomotopy :
    HomotopyCategory (GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece) (.up ℤ) ⥤
      HomotopyCategory (GradedModuleCat.{vN} Δ.piece) (.up ℤ) ⥤
        HomotopyCategory (GradedModuleCat.{max vM vN} Γ.piece) (.up ℤ) :=
  (bimoduleModuleTensor Γ Δ).map₂HomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)

end Action

section LeftUnitor

variable (Γ : InternalGrading k A) [GradedAlgebra Γ.piece]

/-- The regular graded bimodule, placed in cohomological degree zero, acts as the identity functor
on the homotopy category of cochain complexes of graded modules. -/
-- Reducible so that the component lemmas of `Functor.map₂HomotopyCategoryLeftUnitor` apply.
abbrev bimoduleModuleTensorHomotopyLeftUnitor :
    (bimoduleModuleTensorHomotopy.{max w uA, max w uA} Γ Γ).obj
        ((HomotopyCategory.quotient _ _).obj
          ((single _ (.up ℤ) 0).obj (bimoduleUnit.{w} Γ))) ≅
      𝟭 (HomotopyCategory (GradedModuleCat.{max w uA} Γ.piece) (.up ℤ)) :=
  Functor.map₂HomotopyCategoryLeftUnitor _ _ (bimoduleModuleTensorLeftUnitorNatIso.{w} Γ) _

end LeftUnitor

section Associator

variable (Γ : InternalGrading k A) (Δ : InternalGrading k B) (Θ : InternalGrading k C)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece]

/-- Acting by the total tensor product of two complexes of graded bimodules is isomorphic, on the
homotopy category of graded modules, to acting by the second complex and then by the first. -/
-- Reducible so that the component lemmas of `Functor.map₂HomotopyCategoryAssociator` apply.
abbrev bimoduleModuleTensorHomotopyAssociator
    (K₁ : CochainComplex (GradedModuleCat.{w} (Γ.tensorProduct Δ.opposite).piece) ℤ)
    (K₂ : CochainComplex (GradedModuleCat.{w} (Δ.tensorProduct Θ.opposite).piece) ℤ) :
    (bimoduleModuleTensorHomotopy.{w, w} Γ Θ).obj
        ((HomotopyCategory.quotient _ _).obj
          (mapBifunctor K₁ K₂ (bimoduleTensor.{w, w} Γ Δ Θ) (.up ℤ))) ≅
      (bimoduleModuleTensorHomotopy.{w, w} Δ Θ).obj ((HomotopyCategory.quotient _ _).obj K₂) ⋙
        (bimoduleModuleTensorHomotopy.{w, w} Γ Δ).obj ((HomotopyCategory.quotient _ _).obj K₁) :=
  Functor.map₂HomotopyCategoryAssociator (bimoduleModuleTensorAssociatorNatIso.{w, w, w} Γ Δ Θ)
    _ _ _ _ _ _ K₁ K₂

end Associator

section Equivalence

variable (Γ : InternalGrading k A) [GradedAlgebra Γ.piece]
  (K K' : CochainComplex (GradedModuleCat.{max w uA} (Γ.tensorProduct Γ.opposite).piece) ℤ)

/-- A complex `K` of graded `A`-bimodules whose tensor products with a complex `K'` in both orders
are homotopy equivalent to the regular bimodule in degree zero acts by an autoequivalence of the
homotopy category of graded `A`-modules, with inverse the action of `K'`. -/
-- Exposed so that its functor and inverse are the two actions definitionally, as required to
-- compare composites of such autoequivalences.
@[expose]
def bimoduleModuleTensorHomotopyEquivalence
    (e : HomotopyEquiv (mapBifunctor K K' (bimoduleTensor Γ Γ Γ) (.up ℤ))
      ((single _ (.up ℤ) 0).obj (bimoduleUnit.{w} Γ)))
    (e' : HomotopyEquiv (mapBifunctor K' K (bimoduleTensor Γ Γ Γ) (.up ℤ))
      ((single _ (.up ℤ) 0).obj (bimoduleUnit.{w} Γ))) :
    HomotopyCategory (GradedModuleCat.{max w uA} Γ.piece) (.up ℤ) ≌
      HomotopyCategory (GradedModuleCat.{max w uA} Γ.piece) (.up ℤ) :=
  CategoryTheory.Equivalence.mk
    ((bimoduleModuleTensorHomotopy Γ Γ).obj ((HomotopyCategory.quotient _ _).obj K))
    ((bimoduleModuleTensorHomotopy Γ Γ).obj ((HomotopyCategory.quotient _ _).obj K'))
    ((bimoduleModuleTensorHomotopyLeftUnitor.{w} Γ).symm ≪≫
      (bimoduleModuleTensorHomotopy Γ Γ).mapIso (HomotopyCategory.isoOfHomotopyEquiv e').symm ≪≫
      bimoduleModuleTensorHomotopyAssociator Γ Γ Γ K' K)
    ((bimoduleModuleTensorHomotopyAssociator Γ Γ Γ K K').symm ≪≫
      (bimoduleModuleTensorHomotopy Γ Γ).mapIso (HomotopyCategory.isoOfHomotopyEquiv e) ≪≫
      bimoduleModuleTensorHomotopyLeftUnitor.{w} Γ)

variable (e : HomotopyEquiv (mapBifunctor K K' (bimoduleTensor Γ Γ Γ) (.up ℤ))
      ((single _ (.up ℤ) 0).obj (bimoduleUnit.{w} Γ)))
    (e' : HomotopyEquiv (mapBifunctor K' K (bimoduleTensor Γ Γ Γ) (.up ℤ))
      ((single _ (.up ℤ) 0).obj (bimoduleUnit.{w} Γ)))

/-- The autoequivalence attached to `K` is the action of `K`. -/
@[simp]
lemma bimoduleModuleTensorHomotopyEquivalence_functor :
    (bimoduleModuleTensorHomotopyEquivalence Γ K K' e e').functor =
      (bimoduleModuleTensorHomotopy Γ Γ).obj ((HomotopyCategory.quotient _ _).obj K) :=
  (rfl)

/-- The inverse of the autoequivalence attached to `K` is the action of `K'`. -/
@[simp]
lemma bimoduleModuleTensorHomotopyEquivalence_inverse :
    (bimoduleModuleTensorHomotopyEquivalence Γ K K' e e').inverse =
      (bimoduleModuleTensorHomotopy Γ Γ).obj ((HomotopyCategory.quotient _ _).obj K') :=
  (rfl)

end Equivalence

end TauCeti.GradedModuleCat
