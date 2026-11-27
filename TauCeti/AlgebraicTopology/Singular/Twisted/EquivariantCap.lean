/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.Embedding.LinearYoneda
public import TauCeti.Algebra.Homology.Embedding.MapExtend
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Cap
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Coordinates
public import TauCeti.AlgebraicTopology.Singular.Twisted.QuotientCovering
public import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor

/-!
# Twisted homology of a quotient pair from an equivariant cap product

Let a group `G` act on a pair `(X, A)` with an equivariant embedding and on a space `Y`, let
`p₀ : X ⟶ Y` be equivariant, and let `φ` be a relative cocycle of degree `n` of `(X, A)` which is
semi-invariant for a character `χ : G →* kˣ` (`TopPair.IsSemiInvariantCocycle`). Capping with `φ`
and pushing forward along `p₀` is a chain map of complexes of representations

`C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]`

(`TopPair.singularChainsRepCap`). Suppose that `(X, A)` maps to a pair `(Q, Q₀)` by quotient
covering maps `X ⟶ Q` and `A ⟶ Q₀`, and that `Y ⟶ Z` is a quotient covering map, all for the
action of `G`. This file shows that any quasi-isomorphism `C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` of
complexes of representations, such as the equivariant cap product when it is one, computes for
every representation `D` of `G` the homology of `(Q, Q₀)` twisted by the local system `L_D`
associated to `D` as the homology of `Z` twisted by the local system associated to `D ⊗ k_χ`,
shifted by `n`:

`H_{q + n}(Q, Q₀; L_D) ≅ H_q(Z; L_{D ⊗ k_χ})`

(`TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso`). For the trivial representation `D = k`
the local system `L_D` is the constant system `k`, which gives
`H_{q + n}(Q, Q₀; k) ≅ H_q(Z; L_{k_χ})`
(`TopPair.singularHomologyIsoTwistedHomologyOfQuasiIso`).

Both come from one chain map. Applying the tensor coinvariants `(D ⊗ -)_G` to any chain map
`f : C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` gives a chain map
`C(Q, Q₀; L_D) ⟶ C(Z; L_{D ⊗ k_χ})[n]` (`TopPair.coinvariantsTwistedChainMap`). On the source the
coinvariants are the relative chains of `(Q, Q₀)` twisted by `L_D`
(`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`). On the target they commute with the shift
(`HomologicalComplex.mapExtendIso`), and `(D ⊗ (k_χ ⊗ C(Y; k)))_G ≅ ((D ⊗ k_χ) ⊗ C(Y; k))_G` by the
associator (`Rep.tensorLeftCompCoinvariantsTensorObjIso`), which is the chain complex of `Z` twisted
by the local system associated to `D ⊗ k_χ`
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`). The free actions make both
complexes of representations projective, so when `f` is a quasi-isomorphism its tensor coinvariants
are a chain homotopy equivalence (`TopPair.homotopyEquivalences_coinvariantsTensor_map`), and so is
the chain map (`TopPair.homotopyEquivalences_coinvariantsTwistedChainMap`). The isomorphisms in
homology are induced by it, followed by the removal of the shift
(`HomologicalComplex.extendHomologyIso`). Since `Hom(-, N)` preserves chain homotopy equivalences,
the same chain map also gives, for every `k`-module `N`, the isomorphism in cohomology
`Hᵖ⁺ⁿ(Q, Q₀; L_D, N) ≅ Hᵖ(Z; L_{D ⊗ k_χ}, N)`
(`TopPair.twistedCohomologyIsoTwistedCohomologyOfQuasiIso`), with the shift removed by
`ChainComplex.linearYonedaObjExtendHomologyIso`.

The intended use is the Thom pair of a vector bundle `E' → B'` pulled back to the orientation double
cover `B'` of a real vector bundle `E → B`, with `G = ℤˣ` acting by the deck involution, `χ` the
sign character, `p₀` the projection, and `φ` a cocycle representing a Thom class of `E'` which the
deck involution negates. The equivariant cap product with `φ` is then a quasi-isomorphism
(`TauCeti.quasiIso_singularChainsRepCap_thomPair`), `(Q, Q₀)` is the Thom pair of `E` and `Z` is
`B`, and the isomorphism here with `D` trivial identifies `H_{q + r}(E, E₀; k)` with the homology of
`B` with coefficients in the local system associated to the representation
`Rep.of (Representation.ofLinearCharacter sign)` of `ℤˣ`. The orientation local system of `E` is
the local system associated to `Rep.ofDistribMulAction k ℤˣ k`
(`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`), so this becomes the Thom
isomorphism of `E` with orientation-twisted coefficients, over any commutative ring, once these two
sign representations are identified. Neither that identification nor the production of such a
cocycle `φ` is done in this file.

## Main definitions

* `TopPair.coinvariantsTwistedChainMap`: a chain map `C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` of
  complexes of representations gives a chain map `C(Q, Q₀; L_D) ⟶ C(Z; L_{D ⊗ k_χ})[n]`, which is
  a chain homotopy equivalence when the first one is a quasi-isomorphism
  (`TopPair.homotopyEquivalences_coinvariantsTwistedChainMap`).
* `TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso`: a quasi-isomorphism
  `C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` identifies `H_{q + n}(Q, Q₀; L_D)` with
  `H_q(Z; L_{D ⊗ k_χ})`.
* `TopPair.singularHomologyIsoTwistedHomologyOfQuasiIso`: the case of the trivial
  representation, `H_{q + n}(Q, Q₀; k) ≅ H_q(Z; L_{k_χ})`.
* `TopPair.twistedCohomologyIsoTwistedCohomologyOfQuasiIso`: a quasi-isomorphism
  `C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` identifies `Hᵖ⁺ⁿ(Q, Q₀; L_D, N)` with
  `Hᵖ(Z; L_{D ⊗ k_χ}, N)` for every `k`-module `N`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory TauCeti TauCeti.LocalCoefficientSystem

universe u

namespace TopPair

variable {P' P : TopPair.{u}} {k : Type u} [CommRing k] {G : Type u} [Group G]
  [MulAction G P'.fst] [MulAction G P'.snd] {π : P' ⟶ P}
  (hfst : IsQuotientCoveringMap (Hom.fst π) G) (hsnd : IsQuotientCoveringMap (Hom.snd π) G)
  (hP : ∀ (g : G) x, P'.map (g • x) = g • P'.map x)
  {Y Z : TopCat.{u}} [MulAction G Y] {p : Y ⟶ Z} (hY : IsQuotientCoveringMap p G)
  (χ : G →* kˣ) {n : ℕ} (D : Rep.{u} k G)

/-- **The twisted chain map of a quotient pair induced by a shifted equivariant chain map.** Let
`G` act on a pair `(X, A)` and on a space `Y`, let `(X, A) ⟶ (Q, Q₀)` restrict to quotient covering
maps `X ⟶ Q` and `A ⟶ Q₀` and let `Y ⟶ Z` be a quotient covering map, all for the action of `G`. A
chain map `f : C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` of complexes of representations, for a character
`χ : G →* kˣ`, gives for every representation `D` of `G` a chain map
`C(Q, Q₀; L_D) ⟶ C(Z; L_{D ⊗ k_χ})[n]`, where `L_D` and `L_{D ⊗ k_χ}` are the local systems
associated to `D` and to `D ⊗ k_χ`. It is the tensor coinvariants `(D ⊗ f)_G`, read through the
identification of `(D ⊗ C(X, A; k))_G` with `C(Q, Q₀; L_D)`
(`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`), the commutation of the coinvariants with
the shift (`HomologicalComplex.mapExtendIso`), the associator
(`Rep.tensorLeftCompCoinvariantsTensorObjIso`) and the identification of
`((D ⊗ k_χ) ⊗ C(Y; k))_G` with `C(Z; L_{D ⊗ k_χ})`
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`). The main example of `f`
is the equivariant cap product `TopPair.singularChainsRepCap` with a semi-invariant relative
cocycle. -/
def coinvariantsTwistedChainMap
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n)) :
    P.twistedChainComplex (hfst.associatedLocalSystem k D) ⟶
      (LocalCoefficientSystem.twistedChainComplex
        (hY.associatedLocalSystem k (D ⊗ Rep.of (Representation.ofLinearCharacter χ)))).extend
        (ComplexShape.embeddingDownNatAdd n) :=
  haveI := hfst.toContinuousConstSMul
  haveI := hsnd.toContinuousConstSMul
  haveI := hY.toContinuousConstSMul
  (P'.coinvariantsTensorSingularChainsRepIsoTwisted k hfst hsnd hP D).inv ≫
    (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map f ≫
    (HomologicalComplex.mapExtendIso _ _ (ComplexShape.embeddingDownNatAdd n)).hom ≫
    ((ComplexShape.embeddingDownNatAdd n).extendFunctor _).map
      ((Functor.mapHomologicalComplexCompIso
          (Rep.tensorLeftCompCoinvariantsTensorObjIso D
            (Rep.of (Representation.ofLinearCharacter χ))) _).app
          (TauCeti.singularChainsRep k Y G) ≪≫
        hY.coinvariantsTensorSingularChainsRepIsoTwisted k
          (D ⊗ Rep.of (Representation.ofLinearCharacter χ))).hom

/-- The chain map `coinvariantsTwistedChainMap` is the tensor coinvariants `(D ⊗ f)_G`, between the
identification of `(D ⊗ C(X, A; k))_G` with `C(Q, Q₀; L_D)` and the identification of
`(D ⊗ (k_χ ⊗ C(Y; k))[n])_G` with `C(Z; L_{D ⊗ k_χ})[n]`. -/
theorem coinvariantsTwistedChainMap_def
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n)) :
    haveI := hfst.toContinuousConstSMul
    haveI := hsnd.toContinuousConstSMul
    haveI := hY.toContinuousConstSMul
    coinvariantsTwistedChainMap hfst hsnd hP hY χ D f =
      (P'.coinvariantsTensorSingularChainsRepIsoTwisted k hfst hsnd hP D).inv ≫
        (((Rep.coinvariantsTensor k G).obj D).mapHomologicalComplex _).map f ≫
        (HomologicalComplex.mapExtendIso _ _ (ComplexShape.embeddingDownNatAdd n)).hom ≫
        ((ComplexShape.embeddingDownNatAdd n).extendFunctor _).map
          ((Functor.mapHomologicalComplexCompIso
              (Rep.tensorLeftCompCoinvariantsTensorObjIso D
                (Rep.of (Representation.ofLinearCharacter χ))) _).app
              (TauCeti.singularChainsRep k Y G) ≪≫
            hY.coinvariantsTensorSingularChainsRepIsoTwisted k
              (D ⊗ Rep.of (Representation.ofLinearCharacter χ))).hom :=
  (rfl)

/-- **A shifted equivariant quasi-isomorphism induces a twisted chain homotopy equivalence.** Under
the hypotheses of `TopPair.coinvariantsTwistedChainMap`, if `f` is a quasi-isomorphism then the
chain map `C(Q, Q₀; L_D) ⟶ C(Z; L_{D ⊗ k_χ})[n]` is a chain homotopy equivalence: the free actions
make both complexes projective, so the tensor coinvariants of `f` are a chain homotopy equivalence
(`TopPair.homotopyEquivalences_coinvariantsTensor_map`), and the other factors are isomorphisms. -/
theorem homotopyEquivalences_coinvariantsTwistedChainMap
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] :
    HomologicalComplex.homotopyEquivalences _ _
      (coinvariantsTwistedChainMap hfst hsnd hP hY χ D f) := by
  have := hY.toContinuousConstSMul
  have := hY.isCancelSMul
  exact MorphismProperty.comp_mem _ _ _ (.of_isIso _) <| MorphismProperty.comp_mem _ _ _
    (P'.homotopyEquivalences_coinvariantsTensor_map k hfst hsnd hP D f) <|
      MorphismProperty.comp_mem _ _ _ (.of_isIso _) (.of_isIso _)

/-- **Twisted homology of a quotient pair from a shifted twisted quasi-isomorphism.** Let `G` act
on a pair `(X, A)` and on a space `Y`, let `(X, A) ⟶ (Q, Q₀)` restrict to quotient covering maps
`X ⟶ Q` and `A ⟶ Q₀` and let `Y ⟶ Z` be a quotient covering map, all for the action of `G`. A
quasi-isomorphism `f : C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` of complexes of representations, for a
character `χ : G →* kˣ`, gives for every representation `D` of `G`
`H_{q + n}(Q, Q₀; L_D) ≅ H_q(Z; L_{D ⊗ k_χ})`, where `L_D` and `L_{D ⊗ k_χ}` are the local systems
associated to `D` and to `D ⊗ k_χ`. It is induced by the chain homotopy equivalence
`TopPair.coinvariantsTwistedChainMap`. The main example of `f` is the equivariant cap product
`TopPair.singularChainsRepCap` with a semi-invariant relative cocycle. -/
def twistedHomologyIsoTwistedHomologyOfQuasiIso
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] (q : ℕ) :
    P.twistedHomology (hfst.associatedLocalSystem k D) (q + n) ≅
      LocalCoefficientSystem.twistedHomology
        (hY.associatedLocalSystem k (D ⊗ Rep.of (Representation.ofLinearCharacter χ))) q :=
  haveI : QuasiIso (coinvariantsTwistedChainMap hfst hsnd hP hY χ D f) :=
    homotopyEquivalences_le_quasiIso _ _ _
      (homotopyEquivalences_coinvariantsTwistedChainMap hfst hsnd hP hY χ D f)
  asIso (HomologicalComplex.homologyMap (coinvariantsTwistedChainMap hfst hsnd hP hY χ D f)
      (q + n)) ≪≫
    HomologicalComplex.extendHomologyIso _ (ComplexShape.embeddingDownNatAdd n)
      (ComplexShape.embeddingDownNatAdd_f n q)

/-- The isomorphism `twistedHomologyIsoTwistedHomologyOfQuasiIso` is the map induced in homology
by `coinvariantsTwistedChainMap`, followed by the removal of the shift. -/
theorem twistedHomologyIsoTwistedHomologyOfQuasiIso_hom
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] (q : ℕ) :
    (twistedHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hY χ D f q).hom =
      HomologicalComplex.homologyMap (coinvariantsTwistedChainMap hfst hsnd hP hY χ D f) (q + n) ≫
        (HomologicalComplex.extendHomologyIso _ (ComplexShape.embeddingDownNatAdd n)
          (ComplexShape.embeddingDownNatAdd_f n q)).hom :=
  (rfl)

/-- **Homology of a quotient pair from a shifted twisted quasi-isomorphism.** Under the hypotheses
of `TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso`, the relative singular homology of
`(Q, Q₀)` with coefficients in `k` is the homology of `Z` twisted by the local system associated to
the one-dimensional representation `k_χ`, shifted by `n`: `H_{q + n}(Q, Q₀; k) ≅ H_q(Z; L_{k_χ})`.
It is the case of the trivial representation `D = k`, whose associated local system is the constant
system `k` (`IsQuotientCoveringMap.associatedLocalSystemTrivialIso`). -/
def singularHomologyIsoTwistedHomologyOfQuasiIso
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] (q : ℕ) :
    P.singularHomology (ModuleCat.of k k) (q + n) ≅
      LocalCoefficientSystem.twistedHomology
        (hY.associatedLocalSystem k (Rep.of (Representation.ofLinearCharacter χ))) q :=
  (P.twistedHomologyConstantIso (ModuleCat.of k k) (q + n)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (q + n)).mapIso
      (P.twistedChainComplexCoefficientIso (hfst.associatedLocalSystemTrivialIso k k).symm) ≪≫
    twistedHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hY χ (Rep.trivial k G k) f q ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      (LocalCoefficientSystem.twistedChainComplexCoefficientIso
        ((hY.associatedLocalSystemFunctor k).mapIso
          (λ_ (Rep.of (Representation.ofLinearCharacter χ)))))

/-- The isomorphism `singularHomologyIsoTwistedHomologyOfQuasiIso` is
`twistedHomologyIsoTwistedHomologyOfQuasiIso` for the trivial representation `k`, between the
identification of the constant system `k` with the local system associated to `k` and the left
unitor `k ⊗ k_χ ≅ k_χ`. -/
theorem singularHomologyIsoTwistedHomologyOfQuasiIso_def
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] (q : ℕ) :
    singularHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hY χ f q =
      (P.twistedHomologyConstantIso (ModuleCat.of k k) (q + n)).symm ≪≫
        (HomologicalComplex.homologyFunctor _ _ (q + n)).mapIso
          (P.twistedChainComplexCoefficientIso (hfst.associatedLocalSystemTrivialIso k k).symm) ≪≫
        twistedHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hY χ (Rep.trivial k G k) f q ≪≫
        (HomologicalComplex.homologyFunctor _ _ q).mapIso
          (LocalCoefficientSystem.twistedChainComplexCoefficientIso
            ((hY.associatedLocalSystemFunctor k).mapIso
              (λ_ (Rep.of (Representation.ofLinearCharacter χ))))) :=
  (rfl)

/-- **Twisted cohomology of a quotient pair from a shifted twisted quasi-isomorphism.** Under the
hypotheses of `TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso`, a quasi-isomorphism
`f : C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` of complexes of representations gives for every
representation `D` of `G` and every `k`-module `N` the isomorphism
`Hᵖ⁺ⁿ(Q, Q₀; L_D, N) ≅ Hᵖ(Z; L_{D ⊗ k_χ}, N)` of cohomology with values in `N`. The chain map
`TopPair.coinvariantsTwistedChainMap` is a chain homotopy equivalence, and `Hom(-, N)` preserves
chain homotopy equivalences, so no hypothesis on `N` is needed; the shift is removed by
`ChainComplex.linearYonedaObjExtendHomologyIso`. -/
def twistedCohomologyIsoTwistedCohomologyOfQuasiIso
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] (N : ModuleCat.{u} k) (q : ℕ) :
    P.twistedCohomology (hfst.associatedLocalSystem k D) k N (q + n) ≅
      LocalCoefficientSystem.twistedCohomology k N
        (hY.associatedLocalSystem k (D ⊗ Rep.of (Representation.ofLinearCharacter χ))) q :=
  haveI : QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k N).map
      (coinvariantsTwistedChainMap hfst hsnd hP hY χ D f).op) :=
    homotopyEquivalences_le_quasiIso _ _ _
      (TauCeti.ChainComplex.homotopyEquivalences_linearYonedaFunctor_map k N
        (homotopyEquivalences_coinvariantsTwistedChainMap hfst hsnd hP hY χ D f))
  (asIso (HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k N).map
      (coinvariantsTwistedChainMap hfst hsnd hP hY χ D f).op) (q + n))).symm ≪≫
    _root_.ChainComplex.linearYonedaObjExtendHomologyIso N _ (ComplexShape.embeddingDownNatAdd n)
      (ComplexShape.embeddingDownNatAdd_f n q)

/-- The inverse of `twistedCohomologyIsoTwistedCohomologyOfQuasiIso` is the removal of the shift,
followed by the map induced in cohomology by precomposition with `coinvariantsTwistedChainMap`. -/
theorem twistedCohomologyIsoTwistedCohomologyOfQuasiIso_inv
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] (N : ModuleCat.{u} k) (q : ℕ) :
    (twistedCohomologyIsoTwistedCohomologyOfQuasiIso hfst hsnd hP hY χ D f N q).inv =
      (_root_.ChainComplex.linearYonedaObjExtendHomologyIso N _
        (ComplexShape.embeddingDownNatAdd n) (ComplexShape.embeddingDownNatAdd_f n q)).inv ≫
        HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k N).map
          (coinvariantsTwistedChainMap hfst hsnd hP hY χ D f).op) (q + n) :=
  (rfl)

end TopPair
