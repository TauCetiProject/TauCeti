/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.GroupHomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.CoinvariantsTensor

/-!
# Twisted cohomology of the base of a contractible free cover is group cohomology

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, let `k` be a commutative ring, `A` a `k`-linear representation
of `G` and `N` a `k`-module. The twisted singular cohomology
`TauCeti.LocalCoefficientSystem.twistedCohomology` of `B` with coefficients in the local system
`L_A` associated to `A` (`IsQuotientCoveringMap.associatedLocalSystem`) and values in `N` is the
cohomology of `Hom(C(B; L_A), N)`. The twisted chains are the coinvariants `(A ⊗ C(E; k))_G`
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`), and a map
`(A ⊗ C(E; k))_G ⟶ N` is a morphism of representations `C(E; k) ⟶ Homₖ(A, N)`
(`HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso`). So the twisted cochains of `B` are
the complex `Hom_G(C(E; k), Homₖ(A, N))`.

If `E` is contractible, its singular chains are a projective resolution of the trivial
representation (`TauCeti.singularChainsResolution`), so the twisted cohomology of `B` is the group
cohomology of `G` with coefficients in the internal hom `Homₖ(A, N)`
(`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`):

`Hⁿ(B; L_A, N) ≅ Hⁿ(G, Homₖ(A, N))`.

The internal hom appears because Tau Ceti's twisted cochains with values in `N` are maps out of
the twisted chains, that is, cochains with coefficients in the dual system `Homₖ(L_A, N)`. For the
trivial representation `A = k` the fibres `(k ⊗ k[p⁻¹ x])_G` of `L_A` are copies of `k` and
`Homₖ(k, N)` is the trivial representation `N`, so this is the twisted form of the comparison
`IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology` of untwisted singular cohomology.
This is the cohomological counterpart of `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology`.

The identification is natural in both coefficient variables. A linear map `g : N →ₗ[k] N'` acts on
twisted cochains by postcomposition and on `Hⁿ(G, Homₖ(A, -))` through the induced map of internal
homs (`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_right`). A
morphism of representations `f : A ⟶ A'` induces a morphism of associated local systems
`L_A ⟶ L_A'` (`IsQuotientCoveringMap.associatedLocalSystemMap`), hence a map
`Hⁿ(B; L_A', N) ⟶ Hⁿ(B; L_A, N)`, which corresponds to the map on `Hⁿ(G, Homₖ(-, N))` given by
precomposition with `f`
(`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_left`).

## Main definitions

* `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`: for contractible `E`, the twisted
  cohomology `Hⁿ(B; L_A, N)` is the group cohomology `Hⁿ(G, Homₖ(A, N))`.

## Main results

* `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_right`,
  `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_left`: the
  identification is natural in the module of values and in the representation.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory TauCeti TauCeti.LocalCoefficientSystem

universe u

namespace IsQuotientCoveringMap

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] (A : Rep.{u} k G) (N : Type u)
  [AddCommGroup N] [Module k N]

/-- **The twisted cohomology of the base of a contractible free cover is group cohomology**: for
the quotient covering map `p : E ⟶ B` of an action of `G` with contractible total space, a
representation `A` of `G` and a `k`-module `N`, the cohomology of `B` with coefficients in the
local system associated to `A` and values in `N` is Mathlib's group cohomology
`Hⁿ(G, Homₖ(A, N))` of the internal hom into the trivial representation `N`. The singular chains
of `E` form a free resolution of `k` over `k[G]`, the twisted chains of `B` are the coinvariants
`(A ⊗ C(E; k))_G`, and maps from these to `N` are morphisms `C(E; k) ⟶ Homₖ(A, N)`. -/
def twistedCohomologyIsoGroupCohomology [ContractibleSpace E] (n : ℕ) :
    (hG.associatedLocalSystem k A).twistedCohomology k (ModuleCat.of k N) n ≅
      groupCohomology ((Rep.ihom A).obj (Rep.trivial k G N)) n :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  letI := Classical.decEq G
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).mapIso
        (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).op) ≪≫
    (Rep.groupCohomologyIhomIso A N n (singularChainsResolution k E G)).symm

/-- The comparison `Hⁿ(B; L_A, N) ≅ Hⁿ(G, Homₖ(A, N))` is the cohomology of the comparison of
cochains induced by `IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`, followed
by the inverse of `Rep.groupCohomologyIhomIso` for the resolution by singular chains of `E`. -/
lemma twistedCohomologyIsoGroupCohomology_hom_eq [ContractibleSpace E] (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    haveI := hG.isCancelSMul
    (hG.twistedCohomologyIsoGroupCohomology k A N n).hom =
      HomologicalComplex.homologyMap ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
          (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom.op) n ≫
        (Rep.groupCohomologyIhomIso A N n (singularChainsResolution k E G)).inv :=
  (rfl)

variable {N' : Type u} [AddCommGroup N'] [Module k N']

/-- **The twisted cohomology of the base of a contractible free cover is naturally group
cohomology, in the module of values**: for a `k`-linear map `g : N →ₗ[k] N'`, the identifications
`Hⁿ(B; L_A, N) ≅ Hⁿ(G, Homₖ(A, N))` and `Hⁿ(B; L_A, N') ≅ Hⁿ(G, Homₖ(A, N'))` carry the map on
twisted cohomology given by postcomposing cochains with `g` to Mathlib's map
`groupCohomology.map (MonoidHom.id G)` induced by the map `Homₖ(A, N) ⟶ Homₖ(A, N')` of internal
homs. -/
@[reassoc]
theorem twistedCohomologyIsoGroupCohomology_hom_naturality_right [ContractibleSpace E]
    (g : N →ₗ[k] N') (n : ℕ) :
    HomologicalComplex.homologyMap ((hG.associatedLocalSystem k A).twistedChainComplex
        |>.linearYonedaObjMap k (ModuleCat.ofHom g)) n ≫
        (hG.twistedCohomologyIsoGroupCohomology k A N' n).hom =
      (hG.twistedCohomologyIsoGroupCohomology k A N n).hom ≫ groupCohomology.map (MonoidHom.id G)
        ((Rep.ihom A).map ((Rep.trivialFunctor k G).map (ModuleCat.ofHom g))) n := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  -- Postcomposition with `g` commutes with precomposition with the comparison of chains, and
  -- `Rep.groupCohomologyIhomIso` is natural in the module.
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map k
        (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom (ModuleCat.ofHom g))).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [twistedCohomologyIsoGroupCohomology_hom_eq, twistedCohomologyIsoGroupCohomology_hom_eq]
  -- The complex of `singularChainsResolution k E G` is `singularChainsRep k E G` only by
  -- unfolding, so the two squares are pasted in term mode.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Rep.groupCohomologyIhomIso_inv_naturality_right A N g n
      (singularChainsResolution k E G))).trans (Category.assoc _ _ _).symm

variable {A} {A' : Rep.{u} k G}

/-- **The twisted cohomology of the base of a contractible free cover is naturally group
cohomology, in the representation**: for a morphism of representations `f : A ⟶ A'`, the
identifications `Hⁿ(B; L_A', N) ≅ Hⁿ(G, Homₖ(A', N))` and `Hⁿ(B; L_A, N) ≅ Hⁿ(G, Homₖ(A, N))`
carry the map on twisted cohomology induced by the morphism of associated local systems
`IsQuotientCoveringMap.associatedLocalSystemMap` to Mathlib's map
`groupCohomology.map (MonoidHom.id G)` induced by precomposition with `f`,
`Homₖ(A', N) ⟶ Homₖ(A, N)`. -/
@[reassoc]
theorem twistedCohomologyIsoGroupCohomology_hom_naturality_left [ContractibleSpace E]
    (f : A ⟶ A') (n : ℕ) :
    twistedCohomologyCoefficientMap k (ModuleCat.of k N) (hG.associatedLocalSystemMap k f) n ≫
        (hG.twistedCohomologyIsoGroupCohomology k A N n).hom =
      (hG.twistedCohomologyIsoGroupCohomology k A' N n).hom ≫
        groupCohomology.map (MonoidHom.id G) ((MonoidalClosed.pre f).app (Rep.trivial k G N))
          n := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  -- Dualizing the naturality of the comparison of chains: precomposition with the map of
  -- coinvariant chains induced by `f` corresponds to precomposition with the map of twisted
  -- chains induced by the morphism of associated local systems.
  have hchains := congrArg (fun φ ↦ (ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
    φ.op) (hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality k f)
  simp only [op_comp, Functor.map_comp] at hchains
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n) hchains.symm).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [twistedCohomologyIsoGroupCohomology_hom_eq, twistedCohomologyIsoGroupCohomology_hom_eq]
  -- As above, the two squares are pasted in term mode.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Rep.groupCohomologyIhomIso_inv_naturality_left A N f n
      (singularChainsResolution k E G))).trans (Category.assoc _ _ _).symm

end IsQuotientCoveringMap
