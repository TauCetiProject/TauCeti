/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor

/-!
# Duals of tensor coinvariants and group cohomology with coefficients in an internal hom

Let `A` be a `k`-linear representation of `G` and `N` a `k`-module. For a representation `X`,
`Rep.coinvariantsTensorHomLinearEquiv` identifies the `k`-linear maps `(A ⊗ X)_G ⟶ N` with the
morphisms of representations `X ⟶ Homₖ(A, N)` into the internal hom, naturally in `X`.

Applied degreewise to a chain complex `P` of representations, it identifies the cochain complex
`Hom((A ⊗ P)_G, N)` with `Hom_G(P, Homₖ(A, N))`
(`HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso`). When `P` is a projective
resolution of the trivial representation `k`, the cohomology of the second complex is group
cohomology, so

`Hⁿ(G, Homₖ(A, N)) ≅ Hⁿ(Hom((A ⊗ P)_G, N))`

(`Rep.groupCohomologyIhomIso`). The complex `(A ⊗ P)_G` is the one whose homology is Mathlib's
group homology `Hₙ(G, A)` (`groupHomologyIso`), so this is the cochain-level form of the duality
between the group homology of `A` and the group cohomology of `Homₖ(A, N)`. It is how cohomology
with local coefficients, computed from twisted chains of the form `(A ⊗ P)_G`, is compared with
group cohomology.

## Main definitions

* `HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso`: the isomorphism of cochain
  complexes `Hom((A ⊗ P)_G, N) ≅ Hom_G(P, Homₖ(A, N))`.
* `Rep.groupCohomologyIhomIso`: `Hⁿ(G, Homₖ(A, N)) ≅ Hⁿ(Hom((A ⊗ P)_G, N))` for a projective
  resolution `P` of `k`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section III.2 and
  Proposition VI.7.1.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G]

namespace HomologicalComplex

variable {α : Type*} [AddRightCancelSemigroup α] [One α] (A : Rep.{u} k G)
  (P : ChainComplex (Rep.{u} k G) α) (N : Type u) [AddCommGroup N] [Module k N]

/-- **Duals of tensor coinvariants of a complex**: for a chain complex `P` of representations of
`G`, a representation `A` and a `k`-module `N`, the cochain complex `Hom((A ⊗ P)_G, N)` is
isomorphic to the complex `Hom_G(P, Homₖ(A, N))` of morphisms into the internal hom, by
`Rep.coinvariantsTensorHomLinearEquiv` in each degree. -/
def coinvariantsTensorObjLinearYonedaObjIso :
    (P.coinvariantsTensorObj A).linearYonedaObj k (ModuleCat.of k N) ≅
      P.linearYonedaObj k ((Rep.ihom A).obj (Rep.trivial k G N)) :=
  Hom.isoOfComponents (fun i ↦ (Rep.coinvariantsTensorHomLinearEquiv A N (P.X i)).toModuleIso)
    fun i j _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun f ↦
      (Rep.coinvariantsTensorHomLinearEquiv_comp (P.d j i) f).symm

/-- The isomorphism is `Rep.coinvariantsTensorHomLinearEquiv` in each degree. -/
@[simp]
theorem coinvariantsTensorObjLinearYonedaObjIso_hom_f_apply (i : α)
    (f : ((P.coinvariantsTensorObj A).linearYonedaObj k (ModuleCat.of k N)).X i) :
    (P.coinvariantsTensorObjLinearYonedaObjIso A N).hom.f i f =
      Rep.coinvariantsTensorHomLinearEquiv A N (P.X i) f :=
  (rfl)

/-- The inverse isomorphism is the inverse of `Rep.coinvariantsTensorHomLinearEquiv` in each
degree. -/
@[simp]
theorem coinvariantsTensorObjLinearYonedaObjIso_inv_f_apply (i : α)
    (φ : (P.linearYonedaObj k ((Rep.ihom A).obj (Rep.trivial k G N))).X i) :
    (P.coinvariantsTensorObjLinearYonedaObjIso A N).inv.f i φ =
      (Rep.coinvariantsTensorHomLinearEquiv A N (P.X i)).symm φ :=
  (rfl)

end HomologicalComplex

namespace Rep

variable (A : Rep.{u} k G) (N : Type u) [AddCommGroup N] [Module k N]

/-- **Group cohomology with coefficients in an internal hom, from tensor coinvariants**: for a
projective resolution `P` of the trivial representation `k`, a representation `A` and a
`k`-module `N`, the group cohomology `Hⁿ(G, Homₖ(A, N))` is the cohomology of the cochain complex
`Hom((A ⊗ P)_G, N)` dual to the complex computing the group homology of `A`. -/
def groupCohomologyIhomIso (n : ℕ) (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupCohomology ((Rep.ihom A).obj (Rep.trivial k G N)) n ≅
      ((P.complex.coinvariantsTensorObj A).linearYonedaObj k (ModuleCat.of k N)).homology n :=
  groupCohomologyIso _ n P ≪≫ (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (P.complex.coinvariantsTensorObjLinearYonedaObjIso A N).symm

end Rep
