/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.EquivariantMap
public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative

/-!
# Relative twisted chains of the base of a quotient cover of pairs

Let a group `G` act on both spaces of a topological pair `(E, E₀)`, with an equivariant embedding,
and let a map of pairs `(E, E₀) ⟶ (B, A)` restrict to quotient covering maps `E ⟶ B` and
`E₀ ⟶ A` of the two actions, in the sense of Mathlib's `IsQuotientCoveringMap`. For a commutative
ring `k` and a representation `D` of `G`, let `L_D` be the local system on `B` associated to `D`
(`IsQuotientCoveringMap.associatedLocalSystem`), whose fibre over `x` is `(D ⊗ k[p⁻¹ x])_G`.

The relative singular chains of `(E, E₀)` form a complex of representations of `G`
(`TopPair.singularChainsRep`), and this file identifies its tensor coinvariants with the relative
chains of `(B, A)` twisted by `L_D`:

`(D ⊗ C(E, E₀; k))_G ≅ C(B, A; L_D)`

(`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`). This is the relative form of
`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`, and it is compatible with
it through the quotient maps from the chains of `E` and of `B`
(`TopPair.singularChainsRepπ_coinvariantsTensorSingularChainsRepIsoTwisted_hom`). Tensor
coinvariants preserve cokernels (`Rep.preservesColimits_coinvariantsTensor_obj`), and the absolute
identifications for `E ⟶ B` and `E₀ ⟶ A` are compatible with the inclusions
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality_over`), up to
the comparison of `L_D` restricted to `A` with the local system associated to `D` on `A`, which is
an isomorphism (`IsQuotientCoveringMap.isIso_associatedLocalSystemMapOver_id`).

The identification lets equivariant chain maps compute twisted homology. The action on `E` is free,
so the relative chains are projective representations (`TopPair.projective_singularChainsRep_X`),
and a quasi-isomorphism between `ℕ`-graded complexes of projectives is a chain homotopy equivalence
(`ChainComplex.quasiIso_iff_of_projective`), which every additive functor preserves. So an
equivariant quasi-isomorphism `C(E, E₀; k) ⟶ K` to a complex of projective representations
identifies the relative twisted homology `Hₙ(B, A; L_D)` with the homology of `(D ⊗ K)_G`
(`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`).

## Main definitions

* `TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`: the isomorphism
  `(D ⊗ C(E, E₀; k))_G ≅ C(B, A; L_D)`.
* `TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`: an equivariant quasi-isomorphism from
  the relative chains to a complex of projective representations computes the relative twisted
  homology of the base.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti TauCeti.LocalCoefficientSystem

universe u

namespace TopPair

variable (P' : TopPair.{u}) {P : TopPair.{u}} {k : Type u} [CommRing k] {G : Type u} [Group G]
  [MulAction G P'.fst] [MulAction G P'.snd] {φ : P' ⟶ P}
  (hfst : IsQuotientCoveringMap (Hom.fst φ) G) (hsnd : IsQuotientCoveringMap (Hom.snd φ) G)
  (hP : ∀ (g : G) x, P'.map (g • x) = g • P'.map x)

variable (k) (D : Rep.{u} k G)

/-- The comparison of the restriction of `L_D` to the subspace with the local system associated to
`D` on the subspace, as an isomorphism of twisted chain complexes. -/
private def subspaceTwistedChainComplexIso :
    LocalCoefficientSystem.twistedChainComplex.{u, u, u} (hsnd.associatedLocalSystem k D) ≅
      LocalCoefficientSystem.twistedChainComplex.{u, u, u}
        (P.subspaceSystem (hfst.associatedLocalSystem k D)) :=
  haveI : IsIso (hsnd.associatedLocalSystemMapOver k hfst (φ := MonoidHom.id G) P'.map hP P.map
      (Hom.w φ) (𝟙 D)) :=
    hsnd.isIso_associatedLocalSystemMapOver_id k hfst P'.map hP P.map (Hom.w φ) D
  asIso (LocalCoefficientSystem.twistedChainComplexCoefficientMap
    (hsnd.associatedLocalSystemMapOver k hfst (φ := MonoidHom.id G) P'.map hP P.map (Hom.w φ)
      (𝟙 D)))

/-- The tensor coinvariants of the inclusion of the chains of `E₀` into those of `E` are the
inclusion of the twisted chains of `A` into those of `B`, through the absolute identifications. -/
private theorem coinvariantsTensor_map_comp_coinvariantsTensorSingularChainsRepIsoTwisted_hom :
    haveI := hfst.toContinuousConstSMul
    haveI := hsnd.toContinuousConstSMul
    (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map
        (P'.singularChainsRepι k G hP) ≫
      (hfst.coinvariantsTensorSingularChainsRepIsoTwisted k D).hom =
    ((hsnd.coinvariantsTensorSingularChainsRepIsoTwisted k D) ≪≫
        subspaceTwistedChainComplexIso P' k hfst hsnd hP D).hom ≫
      LocalCoefficientSystem.twistedChainComplexMap P.map (hfst.associatedLocalSystem k D) := by
  have := hfst.toContinuousConstSMul
  have := hsnd.toContinuousConstSMul
  -- Through the identity of `G`, the inclusion `E₀ ⟶ E` is a map of quotient covers over `A ⟶ B`.
  refine Eq.trans ?_
    ((IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality_over hsnd
      hfst k (φ := MonoidHom.id G) P'.map hP P.map (Hom.w φ) (𝟙 D)).trans ?_)
  · rw [singularChainsRepι_def]
    exact congrArg (· ≫ _) (MonoidHom.coinvariantsTensorChainMap_id (A := D) _).symm
  · rw [IsQuotientCoveringMap.associatedTwistedChainMap_def, Iso.trans_hom, Category.assoc,
      subspaceTwistedChainComplexIso, asIso_hom]

/-- **Relative twisted chains of the base of a quotient cover of pairs are coinvariant chains.**
Let `G` act on a pair `(E, E₀)` with an equivariant embedding, and let a map of pairs
`(E, E₀) ⟶ (B, A)` restrict to quotient covering maps `E ⟶ B` and `E₀ ⟶ A`. For a representation
`D` of `G`, the tensor coinvariants `(D ⊗ C(E, E₀; k))_G` of the relative singular chains are the
relative chains of `(B, A)` twisted by the local system associated to `D`. -/
def coinvariantsTensorSingularChainsRepIsoTwisted :
    haveI := hfst.toContinuousConstSMul
    haveI := hsnd.toContinuousConstSMul
    (P'.singularChainsRep k G hP).coinvariantsTensorObj D ≅
      P.twistedChainComplex (hfst.associatedLocalSystem k D) :=
  haveI := hfst.toContinuousConstSMul
  haveI := hsnd.toContinuousConstSMul
  (CokernelCofork.mapIsColimit _ (P'.isColimitCokernelCoforkSingularChainsRep k G hP)
      (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _)).coconePointUniqueUpToIso
      (cokernelIsCokernel _) ≪≫
    cokernel.mapIso _ _ _ _
      (coinvariantsTensor_map_comp_coinvariantsTensorSingularChainsRepIsoTwisted_hom P' k hfst hsnd
        hP D) ≪≫
    (cokernelIsCokernel _).coconePointUniqueUpToIso
      (P.isColimitCokernelCoforkTwistedChainComplexπ (hfst.associatedLocalSystem k D))

/-- The relative identification is the absolute identification for `E ⟶ B`, read through the
quotient maps from the chains of `E` and of `B`. -/
@[reassoc]
theorem singularChainsRepπ_coinvariantsTensorSingularChainsRepIsoTwisted_hom :
    haveI := hfst.toContinuousConstSMul
    haveI := hsnd.toContinuousConstSMul
    (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map
        (P'.singularChainsRepπ k G hP) ≫
      (P'.coinvariantsTensorSingularChainsRepIsoTwisted k hfst hsnd hP D).hom =
    (hfst.coinvariantsTensorSingularChainsRepIsoTwisted k D).hom ≫
      P.twistedChainComplexπ (hfst.associatedLocalSystem k D) := by
  have := hfst.toContinuousConstSMul
  have := hsnd.toContinuousConstSMul
  -- The two colimit comparisons send the quotient maps to the quotient maps.
  have h₁ : (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map
        (P'.singularChainsRepπ k G hP) ≫
      ((CokernelCofork.mapIsColimit _ (P'.isColimitCokernelCoforkSingularChainsRep k G hP)
        (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _)).coconePointUniqueUpToIso
          (cokernelIsCokernel _)).hom =
        cokernel.π ((((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map
          (P'.singularChainsRepι k G hP)) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (CokernelCofork.mapIsColimit _
      (P'.isColimitCokernelCoforkSingularChainsRep k G hP)
        (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _)) (cokernelIsCokernel _)
          WalkingParallelPair.one
  have h₃ : cokernel.π (LocalCoefficientSystem.twistedChainComplexMap P.map
        (hfst.associatedLocalSystem k D)) ≫
      ((cokernelIsCokernel _).coconePointUniqueUpToIso
        (P.isColimitCokernelCoforkTwistedChainComplexπ (hfst.associatedLocalSystem k D))).hom =
        P.twistedChainComplexπ (hfst.associatedLocalSystem k D) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
      (P.isColimitCokernelCoforkTwistedChainComplexπ (hfst.associatedLocalSystem k D))
        WalkingParallelPair.one
  rw [coinvariantsTensorSingularChainsRepIsoTwisted, Iso.trans_hom, Iso.trans_hom, reassoc_of% h₁,
    cokernel.mapIso_hom, cokernel.π_desc_assoc, Category.assoc, h₃]

/-- **Equivariant quasi-isomorphisms compute relative twisted homology.** Let `G` act on a pair
`(E, E₀)` with an equivariant embedding, and let a map of pairs `(E, E₀) ⟶ (B, A)` restrict to
quotient covering maps `E ⟶ B` and `E₀ ⟶ A`. If `f : C(E, E₀; k) ⟶ K` is an equivariant
quasi-isomorphism from the relative singular chains to a complex of projective representations,
then for every representation `D` the homology of `(D ⊗ K)_G` is the relative homology of
`(B, A)` twisted by the local system associated to `D`. -/
def twistedHomologyIsoHomologyCoinvariantsTensorObj {K : ChainComplex (Rep.{u} k G) ℕ}
    [∀ n, Projective (K.X n)] (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶ K) [QuasiIso f] (n : ℕ) :
    P.twistedHomology (hfst.associatedLocalSystem k D) n ≅ (K.coinvariantsTensorObj D).homology n :=
  haveI := hfst.toContinuousConstSMul
  haveI := hsnd.toContinuousConstSMul
  haveI := hfst.isCancelSMul
  -- A quasi-isomorphism of complexes of projectives is a chain homotopy equivalence, so it stays a
  -- quasi-isomorphism after applying the additive functor of tensor coinvariants.
  haveI : QuasiIso ((((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map f) :=
    homotopyEquivalences_le_quasiIso _ _ _
      (Functor.homotopyEquivalences_mapHomologicalComplex_map _ f
        ((ChainComplex.quasiIso_iff_of_projective f).1 ‹_›))
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (P'.coinvariantsTensorSingularChainsRepIsoTwisted k hfst hsnd hP D).symm ≪≫
    asIso (HomologicalComplex.homologyMap
      ((((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map f) n)

/-- The isomorphism `twistedHomologyIsoHomologyCoinvariantsTensorObj` is induced by `f` after the
relative identification of `(D ⊗ C(E, E₀; k))_G` with `C(B, A; L_D)`. -/
theorem twistedHomologyIsoHomologyCoinvariantsTensorObj_hom {K : ChainComplex (Rep.{u} k G) ℕ}
    [∀ n, Projective (K.X n)] (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶ K) [QuasiIso f] (n : ℕ) :
    haveI := hfst.toContinuousConstSMul
    haveI := hsnd.toContinuousConstSMul
    (P'.twistedHomologyIsoHomologyCoinvariantsTensorObj k hfst hsnd hP D f n).hom =
      HomologicalComplex.homologyMap
          (P'.coinvariantsTensorSingularChainsRepIsoTwisted k hfst hsnd hP D).inv n ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map f) n :=
  (rfl)

end TopPair
