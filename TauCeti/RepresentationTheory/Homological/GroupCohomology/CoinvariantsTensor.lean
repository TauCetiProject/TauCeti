/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups
public import TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups

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
between the group homology of `A` and the group cohomology of `Homₖ(A, N)`.

Both identifications commute with change of group: a homomorphism `f : G →* H`, a compatible
coefficient map `φ : A ⟶ Rep.res f B` and an augmentation-preserving chain map between resolutions
induce the same map on cohomology as Mathlib's `groupCohomology.map`, with precomposition by `φ`
on the internal-hom coefficients (`MonoidHom.groupCohomologyIhomIso_inv_naturality`).
This is how cohomology with local coefficients, computed from twisted chains of the form
`(A ⊗ P)_G`, is compared with group cohomology.

## Main definitions

* `HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso`: the isomorphism of cochain
  complexes `Hom((A ⊗ P)_G, N) ≅ Hom_G(P, Homₖ(A, N))`.
* `Rep.groupCohomologyIhomIso`: `Hⁿ(G, Homₖ(A, N)) ≅ Hⁿ(Hom((A ⊗ P)_G, N))` for a projective
  resolution `P` of `k`.
* `MonoidHom.coinvariantsTensorObjLinearYonedaObjIso_hom_naturality`: change of group commutes
  with the cochain isomorphism.
* `MonoidHom.groupCohomologyIhomIso_inv_naturality` and
  `MonoidHom.groupCohomologyIhomIso_hom_naturality`: naturality of the cohomology comparison.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section III.2 and
  Proposition VI.7.1; Chapter III, §8 for change of group.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Rep

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

namespace MonoidHom

variable {H : Type u} [Group H]
  {A : Rep.{u} k G} {B : Rep.{u} k H} (f : G →* H) (φ : A ⟶ res f B)
  (N : Type u) [AddCommGroup N] [Module k N]

variable {P : ChainComplex (Rep.{u} k G) ℕ} {Q : ChainComplex (Rep.{u} k H) ℕ}
  (α : P ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q)

/-- The isomorphism from dual tensor coinvariants to morphisms into the internal hom commutes
with the cochain maps induced by change of group. -/
@[reassoc]
theorem coinvariantsTensorObjLinearYonedaObjIso_hom_naturality :
    (TauCeti.ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
        (f.coinvariantsTensorChainMap φ α).op ≫
        (P.coinvariantsTensorObjLinearYonedaObjIso A N).hom =
      (Q.coinvariantsTensorObjLinearYonedaObjIso B N).hom ≫
        f.linearYonedaObjMap (f.ihomTrivialPrecomp N φ) α := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun ℓ ↦ ?_
  -- The functor presents its values as morphism complexes; use its evaluation lemma
  -- before comparing with the degreewise adjunction.
  exact (congrArg (coinvariantsTensorHomLinearEquiv A N (P.X n))
    (TauCeti.ChainComplex.linearYonedaFunctor_map_f_hom_apply k (ModuleCat.of k N)
      (f.coinvariantsTensorChainMap φ α).op n ℓ)).trans <|
    (congrArg (fun v ↦ coinvariantsTensorHomLinearEquiv A N (P.X n) (v ≫ ℓ))
      (f.coinvariantsTensorChainMap_f φ α n)).trans <|
    (f.coinvariantsTensorHomLinearEquiv_naturality φ N (α.f n) ℓ).trans
      (f.linearYonedaObjMap_f_apply (f.ihomTrivialPrecomp N φ) α n
        (coinvariantsTensorHomLinearEquiv B N (Q.X n) ℓ)).symm

variable (P₀ : ProjectiveResolution (Rep.trivial k G k))
  (Q₀ : ProjectiveResolution (Rep.trivial k H k))
  (α₀ : P₀.complex ⟶ ((resFunctor f).mapHomologicalComplex _).obj Q₀.complex)
  (hα : α₀.f 0 ≫ (resFunctor f).map (Q₀.π.f 0) = P₀.π.f 0)

include hα in
/-- The comparison of the cohomology of dual tensor coinvariants with group cohomology is
natural under any group homomorphism and any compatible map of coefficient representations.
Only preservation of the augmentation is required of the chain map between resolutions. -/
@[reassoc]
theorem groupCohomologyIhomIso_inv_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
          (f.coinvariantsTensorChainMap φ α₀).op) n ≫
        (Rep.groupCohomologyIhomIso A N n P₀).inv =
      (Rep.groupCohomologyIhomIso B N n Q₀).inv ≫
        groupCohomology.map f (f.ihomTrivialPrecomp N φ) n := by
  let t : (Q₀.complex.coinvariantsTensorObj B).linearYonedaObj k (ModuleCat.of k N) ⟶
      (P₀.complex.coinvariantsTensorObj A).linearYonedaObj k (ModuleCat.of k N) :=
    (TauCeti.ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
      (f.coinvariantsTensorChainMap φ α₀).op
  let sA := (P₀.complex.coinvariantsTensorObjLinearYonedaObjIso A N).hom
  let sB := (Q₀.complex.coinvariantsTensorObjLinearYonedaObjIso B N).hom
  let c := f.linearYonedaObjMap (f.ihomTrivialPrecomp N φ) α₀
  have h : CommSq t sB sA c :=
    ⟨f.coinvariantsTensorObjLinearYonedaObjIso_hom_naturality φ N α₀⟩
  have h' := (HomologicalComplex.homologyFunctor _ _ n).map_commSq h
  have h'' : CommSq (HomologicalComplex.homologyMap c n)
      (groupCohomologyIso _ n Q₀).inv (groupCohomologyIso _ n P₀).inv
      (groupCohomology.map f (f.ihomTrivialPrecomp N φ) n) :=
    ⟨f.groupCohomologyIso_inv_naturality (f.ihomTrivialPrecomp N φ) P₀ Q₀ α₀ hα n⟩
  exact (h'.vert_comp h'').w

include hα in
/-- The forward comparison from group cohomology to the cohomology of dual tensor coinvariants
also commutes with change of group. -/
@[reassoc]
theorem groupCohomologyIhomIso_hom_naturality (n : ℕ) :
    groupCohomology.map f (f.ihomTrivialPrecomp N φ) n ≫
        (Rep.groupCohomologyIhomIso A N n P₀).hom =
      (Rep.groupCohomologyIhomIso B N n Q₀).hom ≫
        HomologicalComplex.homologyMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
            (f.coinvariantsTensorChainMap φ α₀).op) n :=
  (CommSq.horiz_inv (f := (Rep.groupCohomologyIhomIso B N n Q₀).symm)
    (i := (Rep.groupCohomologyIhomIso A N n P₀).symm)
    ⟨(f.groupCohomologyIhomIso_inv_naturality φ N P₀ Q₀ α₀ hα n).symm⟩).w.symm

end MonoidHom
