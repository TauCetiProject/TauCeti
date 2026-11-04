/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Bockstein
public import TauCeti.AlgebraicTopology.Singular.Twisted.EquivariantMap
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.CoinvariantsTensor
public import TauCeti.RepresentationTheory.Rep.Ihom
public import TauCeti.RepresentationTheory.Rep.Trivial

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

The identification is natural in both coefficient variables and in the group. A linear map
`g : N →ₗ[k] N'` acts on twisted cochains by postcomposition and on `Hⁿ(G, Homₖ(A, -))` through the
induced map of internal homs
(`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_right`). A morphism of
representations `f : A ⟶ A'` induces `L_A ⟶ L_A'`
(`IsQuotientCoveringMap.associatedLocalSystemMap`), hence `Hⁿ(B; L_A', N) ⟶ Hⁿ(B; L_A, N)`, which
corresponds to precomposition with `f` on `Hⁿ(G, Homₖ(-, N))`
(`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_left`). More generally,
for a second quotient covering `q : F ⟶ C` of a group `H`, an equivariant map `f : E ⟶ F` along
`φ : G →* H` over `b : B ⟶ C`, and a compatible morphism `ξ : A ⟶ Rep.res φ D`, pulling twisted
cohomology back along `b` and changing local coefficients along
`IsQuotientCoveringMap.associatedLocalSystemMapOver` corresponds to
`groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ)`
(`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_over`).

If the underlying module of `A` is projective over `k`, the fibres of `L_A` are projective, so a
short exact sequence `0 ⟶ N₁ ⟶ N₂ ⟶ N₃ ⟶ 0` of `k`-modules has a Bockstein homomorphism
`Hⁿ(B; L_A, N₃) ⟶ Hⁿ⁺¹(B; L_A, N₁)` (`TauCeti.LocalCoefficientSystem.twistedCohomologyBockstein`),
and `0 ⟶ Homₖ(A, N₁) ⟶ Homₖ(A, N₂) ⟶ Homₖ(A, N₃) ⟶ 0` is a short exact sequence of representations
(`Rep.shortExact_map_ihom`). The identification carries the first connecting map to Mathlib's
`groupCohomology.δ` of the second
(`IsQuotientCoveringMap.twistedCohomologyBockstein_comp_twistedCohomologyIsoGroupCohomology_hom`):
the comparison of cochains is natural in the module of values, so it is a morphism of short exact
sequences of cochain complexes, and `groupCohomologyIso` respects connecting maps
(`TauCeti.Rep.δ_comp_groupCohomologyIso_inv`).

## Main definitions

* `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`: for contractible `E`, the twisted
  cohomology `Hⁿ(B; L_A, N)` is the group cohomology `Hⁿ(G, Homₖ(A, N))`.

## Main results

* `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_right`,
  `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_left`: the
  identification is natural in the module of values and in the representation.
* `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_hom_naturality_over`,
  `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology_inv_pullback`: the identification is
  natural with respect to equivariant maps of quotient covers along arbitrary group homomorphisms.
* `IsQuotientCoveringMap.twistedCohomologyBockstein_comp_twistedCohomologyIsoGroupCohomology_hom`:
  for `k`-projective `A`, the identification respects the long exact sequences in the module of
  values.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4, III.1, and III.8.
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

section LongExactSequence

variable (A)

/-- The comparison of twisted cochains with `Hom_G(C(E; k), Homₖ(A, -))` underlying
`IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology` commutes with postcomposition by a
linear map of modules of values. -/
private lemma twistedCochainComparison_naturality {N N' : Type u} [AddCommGroup N] [Module k N]
    [AddCommGroup N'] [Module k N'] (g : N →ₗ[k] N') :
    haveI := hG.toContinuousConstSMul
    (hG.associatedLocalSystem k A).twistedChainComplex.linearYonedaObjMap k (ModuleCat.ofHom g) ≫
        (ChainComplex.linearYonedaFunctor k (ModuleCat.of k N')).map
          (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom.op ≫
        ((singularChainsRep k E G).coinvariantsTensorObjLinearYonedaObjIso A N').hom =
      ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map
          (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom.op ≫
        ((singularChainsRep k E G).coinvariantsTensorObjLinearYonedaObjIso A N).hom) ≫
        (singularChainsRep k E G).linearYonedaObjMap k
          ((Rep.ihom A).map ((Rep.trivialFunctor k G).map (ModuleCat.ofHom g))) := by
  have := hG.toContinuousConstSMul
  -- Postcomposition with `g` commutes with precomposition with the comparison of chains, and the
  -- duality `coinvariantsTensorObjLinearYonedaObjIso` is natural in the module. The first square
  -- is stated between `linearYonedaFunctor` and `linearYonedaObj` complexes, which agree only by
  -- unfolding, so the squares are pasted in term mode.
  exact (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map_assoc k
      (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom (ModuleCat.ofHom g) _).trans <|
    (congrArg (_ ≫ ·)
      (HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso_hom_naturality_right A
        (singularChainsRep k E G) N g)).trans (Category.assoc _ _ _).symm

/-- **The twisted cohomology of the base of a contractible free cover is group cohomology,
compatibly with the long exact sequences in the module of values**: for the quotient covering map
`p : E ⟶ B` of an action of `G` with contractible total space, a representation `A` of `G` whose
underlying module is projective over `k`, and a short exact sequence `0 ⟶ N₁ ⟶ N₂ ⟶ N₃ ⟶ 0` of
`k`-modules, the isomorphisms `Hⁿ(B; L_A, Nᵢ) ≅ Hⁿ(G, Homₖ(A, Nᵢ))` carry the Bockstein homomorphism
`Hⁿ(B; L_A, N₃) ⟶ Hᵐ(B; L_A, N₁)`, `n + 1 = m`, of twisted cohomology to Mathlib's connecting map
`groupCohomology.δ` of the short exact sequence of representations
`0 ⟶ Homₖ(A, N₁) ⟶ Homₖ(A, N₂) ⟶ Homₖ(A, N₃) ⟶ 0`. -/
@[reassoc]
theorem twistedCohomologyBockstein_comp_twistedCohomologyIsoGroupCohomology_hom
    [ContractibleSpace E] [Module.Projective k A] {S : ShortComplex (ModuleCat.{u} k)}
    (hS : S.ShortExact) (n m : ℕ) (h : n + 1 = m := by lia) :
    LocalCoefficientSystem.twistedCohomologyBockstein.{u, u, u, u} k
        (hG.associatedLocalSystem k A) hS n m h ≫
        (hG.twistedCohomologyIsoGroupCohomology k A S.X₁ m).hom =
      (hG.twistedCohomologyIsoGroupCohomology k A S.X₃ n).hom ≫
        groupCohomology.δ (Rep.shortExact_map_ihom A (Rep.shortExact_map_trivialFunctor hS))
          n m h := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  -- The comparisons of cochains, natural in the module of values, form a morphism from the short
  -- exact sequence of twisted cochain complexes of `B` with values in `S` to that of the complexes
  -- `Hom_G(C(E; k), Homₖ(A, Nᵢ))`. Its naturality for connecting maps is pasted with that of
  -- `groupCohomologyIso` for the resolution by singular chains of `E`.
  let c := fun N : ModuleCat.{u} k ↦
    (ChainComplex.linearYonedaFunctor k N).map
        (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom.op ≫
      ((singularChainsRep k E G).coinvariantsTensorObjLinearYonedaObjIso A N).hom
  let ψ : (hG.associatedLocalSystem k A).twistedCochainComplexValueShortComplex k S ⟶
      ((S.map (Rep.trivialFunctor k G)).map (Rep.ihom A)).map
        ((singularChainsRep k E G).linearYonedaObjFunctor k) :=
    { τ₁ := c S.X₁
      τ₂ := c S.X₂
      τ₃ := c S.X₃
      comm₁₂ := (hG.twistedCochainComparison_naturality k A S.f.hom).symm
      comm₂₃ := (hG.twistedCochainComparison_naturality k A S.g.hom).symm }
  have hcochains := HomologicalComplex.HomologySequence.δ_naturality ψ
    ((hG.associatedLocalSystem k A).shortExact_twistedCochainComplexValueShortComplex k hS)
    ((singularChainsResolution k E G).complex.shortExact_map_linearYonedaObjFunctor k
      (Rep.shortExact_map_ihom A (Rep.shortExact_map_trivialFunctor hS))) n m h
  have hδ := TauCeti.Rep.δ_comp_groupCohomologyIso_inv
    (Rep.shortExact_map_ihom A (Rep.shortExact_map_trivialFunctor hS))
    (singularChainsResolution k E G) n m h
  -- Each comparison `Hⁿ(B; L_A, N) ≅ Hⁿ(G, Homₖ(A, N))` is the cohomology of `c N` followed by the
  -- inverse of `groupCohomologyIso`.
  have hc (N : Type u) [AddCommGroup N] [Module k N] (j : ℕ) :
      (hG.twistedCohomologyIsoGroupCohomology k A N j).hom =
        HomologicalComplex.homologyMap (c (ModuleCat.of k N)) j ≫
          (groupCohomologyIso ((Rep.ihom A).obj (Rep.trivial k G N)) j
            (singularChainsResolution k E G)).inv := by
    rw [twistedCohomologyIsoGroupCohomology_hom_eq, Rep.groupCohomologyIhomIso_inv]
    exact (HomologicalComplex.homologyMap_comp_assoc _ _ j _).symm
  rw [LocalCoefficientSystem.twistedCohomologyBockstein_eq_δ k _ hS n m h, hc, hc]
  -- As in `twistedCohomologyIsoGroupCohomology_hom_naturality_right`, the squares are pasted in
  -- term mode: the complex of `singularChainsResolution k E G` is `singularChainsRep k E G` only by
  -- unfolding.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hδ).trans (Category.assoc _ _ _).symm

end LongExactSequence

section ChangeOfGroups

variable {F C : _root_.TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)

/-- **The twisted cohomology of the base of a contractible free cover is naturally group
cohomology, in the covering and the group**: for quotient covering maps `p : E ⟶ B` and
`q : F ⟶ C` with contractible total spaces, an equivariant map `f : E ⟶ F` along any group
homomorphism `φ : G →* H` lying over `b : B ⟶ C`, and a compatible morphism `ξ : A ⟶ Rep.res φ D`,
the identifications `Hⁿ(C; L_D, N) ≅ Hⁿ(H, Homₖ(D, N))` and `Hⁿ(B; L_A, N) ≅ Hⁿ(G, Homₖ(A, N))`
carry the composite of `b^*` with `associatedLocalSystemMapOver` on twisted cohomology to
Mathlib's change-of-group map `groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ)`. -/
@[reassoc]
theorem twistedCohomologyIsoGroupCohomology_hom_naturality_over [ContractibleSpace E]
    [ContractibleSpace F] {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    twistedCohomologyMap k (ModuleCat.of k N) b (hH.associatedLocalSystem k D) n ≫
        twistedCohomologyCoefficientMap k (ModuleCat.of k N)
          (hG.associatedLocalSystemMapOver k hH f hf b hb ξ) n ≫
        (hG.twistedCohomologyIsoGroupCohomology k A N n).hom =
      (hH.twistedCohomologyIsoGroupCohomology k D N n).hom ≫
        groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  -- Dualize the change-of-groups naturality of `coinvariantsTensorSingularChainsRepIsoTwisted`,
  -- noting that `linearYonedaFunctor` reverses composition, and paste with
  -- `MonoidHom.groupCohomologyIhomIso_inv_naturality`.
  have hchain := (hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality_over hH k f hf b
    hb ξ).trans (congrArg ((hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom ≫ ·)
      (hG.associatedTwistedChainMap_def hH k f hf b hb ξ))
  have hchains := congrArg
    (fun t ↦ (ChainComplex.linearYonedaFunctor k (ModuleCat.of k N)).map t.op) hchain
  simp only [op_comp, Functor.map_comp, Category.assoc] at hchains
  have hcochains := ((congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n).symm).trans
    (HomologicalComplex.homologyMap_comp _ _ n).symm).trans <|
    (congrArg (HomologicalComplex.homologyMap · n) hchains.symm).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [twistedCohomologyIsoGroupCohomology_hom_eq, twistedCohomologyIsoGroupCohomology_hom_eq]
  -- `singularChainsResolution` and `singularChainsRep` agree only by unfolding, so the cochain
  -- and resolution squares are pasted in term mode.
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (φ.groupCohomologyIhomIso_inv_naturality ξ N (singularChainsResolution k E G)
        (singularChainsResolution k F H) (singularChainsRepResMap k f hf)
        (singularChainsRepResMap_f_zero_comp_augmentation k f hf) n)).trans
      (Category.assoc _ _ _).symm

/-- The inverse identification of group cohomology with twisted cohomology on a contractible free
cover is natural for equivariant maps and compatible coefficient maps. -/
@[reassoc]
theorem twistedCohomologyIsoGroupCohomology_inv_naturality_over [ContractibleSpace E]
    [ContractibleSpace F] {D : Rep.{u} k H} (ξ : A ⟶ Rep.res φ D) (n : ℕ) :
    groupCohomology.map φ (φ.ihomTrivialPrecomp N ξ) n ≫
        (hG.twistedCohomologyIsoGroupCohomology k A N n).inv =
      (hH.twistedCohomologyIsoGroupCohomology k D N n).inv ≫
        twistedCohomologyMap k (ModuleCat.of k N) b (hH.associatedLocalSystem k D) n ≫
        twistedCohomologyCoefficientMap k (ModuleCat.of k N)
          (hG.associatedLocalSystemMapOver k hH f hf b hb ξ) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Category.assoc,
    hG.twistedCohomologyIsoGroupCohomology_hom_naturality_over k N hH f hf b hb ξ n,
    Iso.inv_hom_id_assoc]

/-- Pulling twisted cohomology back along `b : B ⟶ C` from `L_D` to `b^* L_D` corresponds, via
`IsQuotientCoveringMap.associatedLocalSystemPullbackIso`, to the change-of-group map
`groupCohomology.map φ (φ.ihomTrivialPrecomp N (𝟙 (Rep.res φ D)))` in group cohomology. -/
@[reassoc]
theorem twistedCohomologyIsoGroupCohomology_inv_pullback [ContractibleSpace E]
    [ContractibleSpace F] (D : Rep.{u} k H) (n : ℕ) :
    (hH.twistedCohomologyIsoGroupCohomology k D N n).inv ≫
        twistedCohomologyMap k (ModuleCat.of k N) b (hH.associatedLocalSystem k D) n =
      groupCohomology.map φ (φ.ihomTrivialPrecomp N (𝟙 (Rep.res φ D))) n ≫
        (hG.twistedCohomologyIsoGroupCohomology k (Rep.res φ D) N n).inv ≫
        twistedCohomologyCoefficientMap k (ModuleCat.of k N)
          (hG.associatedLocalSystemPullbackIso k hH f hf b hb D).inv n := by
  have h := hG.twistedCohomologyIsoGroupCohomology_inv_naturality_over k N hH f hf b hb
    (𝟙 (Rep.res φ D)) n
  rw [← associatedLocalSystemPullbackIso_hom] at h
  simp only [← Category.assoc] at h
  calc
    (hH.twistedCohomologyIsoGroupCohomology k D N n).inv ≫
        twistedCohomologyMap k (ModuleCat.of k N) b (hH.associatedLocalSystem k D) n
      = (hH.twistedCohomologyIsoGroupCohomology k D N n).inv ≫
        twistedCohomologyMap k (ModuleCat.of k N) b (hH.associatedLocalSystem k D) n ≫
        (twistedCohomologyCoefficientMap k (ModuleCat.of k N)
            (hG.associatedLocalSystemPullbackIso k hH f hf b hb D).hom n ≫
          twistedCohomologyCoefficientMap k (ModuleCat.of k N)
            (hG.associatedLocalSystemPullbackIso k hH f hf b hb D).inv n) := by
      rw [← twistedCohomologyCoefficientMap_comp, Iso.inv_hom_id,
        twistedCohomologyCoefficientMap_id, Category.comp_id]
    _ = _ := by
      simp only [← Category.assoc]
      rw [← h]

end ChangeOfGroups

end IsQuotientCoveringMap
