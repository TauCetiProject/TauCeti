/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.Embedding.MapExtend
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

The free actions make both complexes projective, so applying the tensor coinvariants `(D ⊗ -)_G`
to the quasi-isomorphism gives a quasi-isomorphism
(`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`). On the source the coinvariants are the
relative chains of `(Q, Q₀)` twisted by `L_D`. On the target they commute with the shift
(`HomologicalComplex.mapExtendIso`, `HomologicalComplex.extendHomologyIso`), and
`(D ⊗ (k_χ ⊗ C(Y; k)))_G ≅ ((D ⊗ k_χ) ⊗ C(Y; k))_G` by the associator
(`Rep.tensorLeftCompCoinvariantsTensorObjIso`), which is the chain complex of `Z` twisted by the
local system associated to `D ⊗ k_χ`
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`).

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

* `TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso`: a quasi-isomorphism
  `C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` identifies `H_{q + n}(Q, Q₀; L_D)` with
  `H_q(Z; L_{D ⊗ k_χ})`.
* `TopPair.singularHomologyIsoTwistedHomologyOfQuasiIso`: the case of the trivial
  representation, `H_{q + n}(Q, Q₀; k) ≅ H_q(Z; L_{k_χ})`.

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

/-- **Twisted homology of a quotient pair from a shifted twisted quasi-isomorphism.** Let `G` act
on a pair `(X, A)` and on a space `Y`, let `(X, A) ⟶ (Q, Q₀)` restrict to quotient covering maps
`X ⟶ Q` and `A ⟶ Q₀` and let `Y ⟶ Z` be a quotient covering map, all for the action of `G`. A
quasi-isomorphism `f : C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]` of complexes of representations, for a
character `χ : G →* kˣ`, gives for every representation `D` of `G`
`H_{q + n}(Q, Q₀; L_D) ≅ H_q(Z; L_{D ⊗ k_χ})`, where `L_D` and `L_{D ⊗ k_χ}` are the local systems
associated to `D` and to `D ⊗ k_χ`. The main example of `f` is the equivariant cap product
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
  haveI := hfst.toContinuousConstSMul
  haveI := hsnd.toContinuousConstSMul
  haveI := hY.toContinuousConstSMul
  haveI := hY.isCancelSMul
  P'.twistedHomologyIsoHomologyCoinvariantsTensorObj k hfst hsnd hP D f (q + n) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (q + n)).mapIso
      (HomologicalComplex.mapExtendIso _ _ (ComplexShape.embeddingDownNatAdd n)) ≪≫
    HomologicalComplex.extendHomologyIso _ (ComplexShape.embeddingDownNatAdd n)
      (ComplexShape.embeddingDownNatAdd_f n q) ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      ((Functor.mapHomologicalComplexCompIso
          (Rep.tensorLeftCompCoinvariantsTensorObjIso D
            (Rep.of (Representation.ofLinearCharacter χ))) _).app
          (TauCeti.singularChainsRep k Y G) ≪≫
        hY.coinvariantsTensorSingularChainsRepIsoTwisted k
          (D ⊗ Rep.of (Representation.ofLinearCharacter χ)))

/-- The isomorphism `twistedHomologyIsoTwistedHomologyOfQuasiIso` is the identification of
`H_{q + n}(Q, Q₀; L_D)` with the homology of `(D ⊗ (k_χ ⊗ C(Y; k))[n])_G` induced by `f`, followed
by the commutation of the coinvariants with the shift, the removal of the shift, the associator and
the identification of `((D ⊗ k_χ) ⊗ C(Y; k))_G` with the chains of `Z` twisted by the local system
associated to `D ⊗ k_χ`. -/
theorem twistedHomologyIsoTwistedHomologyOfQuasiIso_def
    (f : haveI := hfst.toContinuousConstSMul
      haveI := hsnd.toContinuousConstSMul
      haveI := hY.toContinuousConstSMul
      P'.singularChainsRep k G hP ⟶
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n))
    [QuasiIso f] (q : ℕ) :
    haveI := hfst.toContinuousConstSMul
    haveI := hsnd.toContinuousConstSMul
    haveI := hY.toContinuousConstSMul
    haveI := hY.isCancelSMul
    twistedHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hY χ D f q =
      P'.twistedHomologyIsoHomologyCoinvariantsTensorObj k hfst hsnd hP D f (q + n) ≪≫
        (HomologicalComplex.homologyFunctor _ _ (q + n)).mapIso
          (HomologicalComplex.mapExtendIso _ _ (ComplexShape.embeddingDownNatAdd n)) ≪≫
        HomologicalComplex.extendHomologyIso _ (ComplexShape.embeddingDownNatAdd n)
          (ComplexShape.embeddingDownNatAdd_f n q) ≪≫
        (HomologicalComplex.homologyFunctor _ _ q).mapIso
          ((Functor.mapHomologicalComplexCompIso
              (Rep.tensorLeftCompCoinvariantsTensorObjIso D
                (Rep.of (Representation.ofLinearCharacter χ))) _).app
              (TauCeti.singularChainsRep k Y G) ≪≫
            hY.coinvariantsTensorSingularChainsRepIsoTwisted k
              (D ⊗ Rep.of (Representation.ofLinearCharacter χ))) :=
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

end TopPair
