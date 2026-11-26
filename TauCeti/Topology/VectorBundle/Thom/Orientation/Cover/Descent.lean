/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.LinearYoneda
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Coordinates
public import TauCeti.AlgebraicTopology.Singular.Twisted.QuotientCovering
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.Cover.SignRepresentation
public import TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.ChainMap
public import TauCeti.Topology.VectorBundle.Thom.EquivariantCap
public import TauCeti.Topology.VectorBundle.Thom.Orientation.TwistedLift
import TauCeti.Topology.VectorBundle.ModelFiber

/-!
# The Thom isomorphism with orientation-twisted coefficients over every ring

Let `E → B` be a real vector bundle of rank `r` with Thom pair `(E, E₀)`, let `B'` be its
orientation double cover, whose points are the pairs of a point of `B` and an orientation of the
fibre there, and let `E'` be the pull-back of `E` to `B'`. The units `ℤˣ` act on the Thom pair
`(E', E'₀)`, with `-1` acting by the lift `δ` of the deck involution (`deckThomPairMap`), and the
map of Thom pairs `(E', E'₀) ⟶ (E, E₀)` is the quotient of this free action on both spaces
(`isQuotientCoveringMap_pullbackThomPairMap_fst`, `isQuotientCoveringMap_pullbackThomPairMap_snd`).
For a commutative ring `k`, `ℤ` included, this file descends the homology Thom isomorphism of the
bundle `E'` to the Thom isomorphism of `E` with coefficients in its orientation local system
`o(E)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`):

`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)`

(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology`). Its input is a
relative cocycle `φ` of degree `r` of `(E', E'₀)` which `δ` negates exactly, in the sense of
`TopPair.IsSemiInvariantCocycle` for the sign character `ℤˣ →* kˣ`, and whose class is a Thom class
of `E'`. No orientation of `E` and no hypothesis on `2` in `k` are needed. Over a ring in which `2`
is invertible the same groups are identified through the transfer instead
(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`); over `ℤ` the
transfer does not suffice, and the descent here is the argument of Milnor–Stasheff §12 and
Spanier, Chapter 5, Section 7, at the level of equivariant chains.

The isomorphism is induced by a chain map `C(E, E₀; k) ⟶ C(B; o(E) ⊗ k)[r]`
(`TauCeti.VectorBundleOrientationCover.thomPairTwistedChainMap`), the chain map that the general
descent of shifted equivariant chain maps (`TopPair.coinvariantsTwistedChainMap`) gives for the
equivariant cap product. It is composed of three pieces.

* The equivariant cap product with `φ` is a quasi-isomorphism
  `C(E', E'₀; k) ⟶ (k_sign ⊗ C(B'; k))[r]` of complexes of representations of `ℤˣ`
  (`TauCeti.quasiIso_singularChainsRepCap_thomPair`). The actions on `E'` and `B'` are free, so both
  are complexes of projective representations and it is a chain homotopy equivalence.
* Taking coinvariants against the trivial representation, the source becomes the relative chains of
  `(E, E₀)` with coefficients in the local system associated to the trivial representation
  (`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`), which is constant
  (`IsQuotientCoveringMap.associatedLocalSystemTrivialIso`), so it is `C(E, E₀; k)`.
* The target becomes the coinvariants `(k ⊗ (k_sign ⊗ C(B'; k)))_{ℤˣ}`, placed `r` degrees higher,
  which are the chains of `B` with coefficients in the local system associated to `k ⊗ k_sign`
  (`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`). That local system is
  `o(E)` (`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`).

Coinvariants form an additive functor, so the chain map is a chain homotopy equivalence
(`TopPair.homotopyEquivalences_coinvariantsTwistedChainMap`,
`TauCeti.VectorBundleOrientationCover.homotopyEquivalences_thomPairTwistedChainMap`). Hence
`Hom(-, N)` turns it into a cochain homotopy equivalence for every `k`-module `N`, which gives the
Thom isomorphism in cohomology with values in `N`,

`Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)`

(`TauCeti.VectorBundleOrientationCover.thomPairSingularCohomologyIsoTwistedCohomology`), with no
hypothesis on `N`: over `ℤ` it holds with integral values, not only with values in an injective
module such as `ℚ`, for which the universal coefficient theorem would suffice.

Such cocycles come from classes of `(E, E₀)` with coefficients in the pulled-back orientation
system `π^*o(E)`. The deck involution negates every lifted cochain on the nose
(`thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap`), so the lift of a twisted
cocycle is semi-invariant
(`TauCeti.VectorBundleOrientationCover.isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`, in
`TauCeti.Topology.VectorBundle.Thom.Orientation.TwistedLift`).
Hence, whenever the lift of a class `U ∈ Hʳ(E, E₀; π^*o(E), k)` to `(E', E'₀)` is a Thom class of
`E'`, `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` and `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` in every
degree
(`TauCeti.VectorBundleOrientationCover.nonempty_singularHomology_thomPair_iso_twistedHomology` and
`TauCeti.VectorBundleOrientationCover.nonempty_singularCohomology_thomPair_iso_twistedCohomology`).
The natural class `U` is the Thom class with coefficients in the orientation system
(`TauCeti.twistedThomClass`), which takes the value `1` on the fibre class over every point. Its
lift is a Thom class of `E'` (`isThomClass_thomPairSignCohomologyMap_twistedThomClass`), so
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` holds for every bundle, over any base, and every commutative
ring `k` (`nonempty_singularHomology_thomPair_iso_twistedHomology_signLocalSystem`, in the
namespace `TauCeti.VectorBundleOrientationCover`), and so does
`Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` for every `k`-module `N`
(`nonempty_singularCohomology_thomPair_iso_twistedCohomology_signLocalSystem`, in the same
namespace).

The base, the fibres and the ring lie in any common universe `w`, and the orientations are indexed
by a type `ι : Type`, such as `Fin r`. Representations, their associated local systems and the
equivariant cap product need the acting group in the universe `w`, so `ℤˣ` acts through its copy
`ULift ℤˣ` there (`IsQuotientCoveringMap.ulift`). The descent also needs the model fibre in the
universe `w`. For the final theorems the model fibre may lie in any universe, such as
`Fin r → ℝ : Type`: the bundle is read with the model fibre `ULift (ι → ℝ)` instead
(`VectorBundle.exists_modelFiber_of_continuousLinearEquiv`), which changes neither its Thom pair
(`TauCeti.thomPairModelFiberIso`) nor its orientation local system.

## Main definitions and results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `thomPairTwistedChainMap`: the chain map `C(E, E₀; k) ⟶ C(B; o(E) ⊗ k)[r]` from a
  semi-invariant cocycle of `E'`, and `homotopyEquivalences_thomPairTwistedChainMap`: it is a
  chain homotopy equivalence when the cocycle represents a Thom class of `E'`.
* `thomPairSingularHomologyIsoTwistedHomology`: `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` from a
  semi-invariant Thom cocycle of `E'`.
* `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass`: the same from a cocycle of
  `(E, E₀)` with coefficients in `π^*o(E)` whose lifted class is a Thom class of `E'`, and
  `nonempty_singularHomology_thomPair_iso_twistedHomology`: the same from a class of
  `Hʳ(E, E₀; π^*o(E), k)` whose lift is a Thom class of `E'`.
* `nonempty_singularHomology_thomPair_iso_twistedHomology_signLocalSystem`:
  `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` for every bundle and every commutative ring `k`.
* `thomPairSingularCohomologyIsoTwistedCohomology`: `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)`
  for every `k`-module `N`, from a semi-invariant Thom cocycle of `E'`.
* `thomPairSingularCohomologyIsoTwistedCohomologyOfIsThomClass`: the same from a cocycle of
  `(E, E₀)` with coefficients in `π^*o(E)` whose lifted class is a Thom class of `E'`, and
  `nonempty_singularCohomology_thomPair_iso_twistedCohomology`: the same from a class of
  `Hʳ(E, E₀; π^*o(E), k)` whose lift is a Thom class of `E'`.
* `nonempty_singularCohomology_thomPair_iso_twistedCohomology_signLocalSystem`:
  `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` for every bundle, every commutative ring `k` and every
  `k`-module `N`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover and twisted
  coefficients).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Sections II.4 and III.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H.
-/

public section

noncomputable section

open Bundle CategoryTheory Module MonoidalCategory TauCeti.LocalCoefficientSystem

namespace TauCeti.VectorBundleOrientationCover

universe w

section Descent

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type w) [CommRing k]

/-- The action of `ℤˣ` on the total space of the Thom pair of the orientation cover, lifted from the
deck involution (`TauCeti.VectorBundleOrientationCover.thomPairFstMulAction`). -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction

/-- The action of `ℤˣ` on the nonzero vectors of the Thom pair of the orientation cover
(`TauCeti.VectorBundleOrientationCover.thomPairSndMulAction`). -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
  thomPairSndMulAction

/-- The units act continuously on the total space of the Thom pair of the orientation cover
(`TauCeti.VectorBundleOrientationCover.thomPairFstMulAction_continuousConstSMul`). -/
local instance : ContinuousConstSMul ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction_continuousConstSMul

/-- The units act continuously on the nonzero vectors of the Thom pair of the orientation cover
(`TauCeti.VectorBundleOrientationCover.thomPairSndMulAction_continuousConstSMul`). -/
local instance : ContinuousConstSMul ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
  thomPairSndMulAction_continuousConstSMul

/-! ### Descent of the equivariant Thom isomorphism -/

variable (F E) in
/-- **The chain-level Thom map with coefficients in the orientation system.** Let `E → B` be a real
vector bundle of rank `r`, `B'` its orientation double cover, `E'` the pull-back of `E` to `B'`
and `k` a commutative ring. A relative cocycle `φ` of degree `r` of `(E', E'₀)` which the deck
involution negates (`TopPair.IsSemiInvariantCocycle` for the sign character) gives a chain map
`C(E, E₀; k) ⟶ C(B; o(E) ⊗ k)[r]` from the relative singular chains of the Thom pair to the chains
of `B` with coefficients in the orientation local system `o(E)`, placed `r` degrees higher. It is
the chain map `TopPair.coinvariantsTwistedChainMap` of the equivariant cap product with `φ`
(`TopPair.singularChainsRepCap`) for the trivial representation, between the identification of the
constant system `k` on `E` with the local system of the trivial representation and the
identification of the local system of the sign representation with `o(E)`
(`thomPairTwistedChainMap_def`). When the class of `φ` is a Thom class of `E'` it is a chain
homotopy equivalence (`homotopyEquivalences_thomPairTwistedChainMap`). -/
def thomPairTwistedChainMap
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ) :
    (thomPair F E).singularChainComplex (ModuleCat.of k k) ⟶
      (twistedChainComplex (signLocalSystem F E k hι)).extend
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) :=
  ((thomPair F E).twistedChainComplexConstantIso (ModuleCat.of k k)).inv ≫
    ((thomPair F E).twistedChainComplexCoefficientIso
      ((isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift.associatedLocalSystemTrivialIso
        k k)).inv ≫
    TopPair.coinvariantsTwistedChainMap (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift
      (isQuotientCoveringMap_coverThomPairMap_snd F E ι hι).ulift (fun _ ↦ thomPair_map_smul _)
      (Y := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
      (isQuotientCoveringMap_proj hι).ulift (uliftIntUnitsSign k) (Rep.trivial k (ULift.{w} ℤˣ) k)
      -- the pair and `p₀` are explicit so that the cap map is the one of the actions above:
      -- `thomPairProj_smul` reads the zeros of the fibres through `pullbackFiberZero` instead
      (TopPair.singularChainsRepCap
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (p₀ := thomPairProj F _) (fun _ ↦ thomPairProj_smul _) (uliftIntUnitsSign k) hφ
        (fun _ ↦ thomPair_map_smul _)) ≫
    ((ComplexShape.embeddingDownNatAdd (finrank ℝ F)).extendFunctor _).map
      (twistedChainComplexCoefficientIso
        ((((isQuotientCoveringMap_proj hι).ulift.associatedLocalSystemFunctor
            (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
            k).mapIso
          (λ_ _ ≪≫ Rep.mkIso (Representation.ofLinearCharacterEquivOfDistribMulAction
            (uliftIntUnitsSign k) fun _ _ ↦ by simp [Units.smul_def]))) ≪≫
          associatedLocalSystemSignIso hι k)).hom

variable (F E) in
/-- The chain map `thomPairTwistedChainMap` is `TopPair.coinvariantsTwistedChainMap` for the
equivariant cap product with `φ` and the trivial representation `k`, after the identification of
the constant system `k` on `E` with the local system associated to `k`, and followed by the
identification of the local system associated to `k ⊗ k_sign` with the orientation local system
`o(E)`. -/
theorem thomPairTwistedChainMap_def
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ) :
    thomPairTwistedChainMap F E hι k hφ =
      ((thomPair F E).twistedChainComplexConstantIso (ModuleCat.of k k)).inv ≫
        ((thomPair F E).twistedChainComplexCoefficientIso
          ((isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift
            |>.associatedLocalSystemTrivialIso k k)).inv ≫
        TopPair.coinvariantsTwistedChainMap
          (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift
          (isQuotientCoveringMap_coverThomPairMap_snd F E ι hι).ulift (fun _ ↦ thomPair_map_smul _)
          (Y := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
          (isQuotientCoveringMap_proj hι).ulift (uliftIntUnitsSign k)
          (Rep.trivial k (ULift.{w} ℤˣ) k)
          (TopPair.singularChainsRepCap
            (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
            (p₀ := thomPairProj F _) (fun _ ↦ thomPairProj_smul _) (uliftIntUnitsSign k) hφ
            (fun _ ↦ thomPair_map_smul _)) ≫
        ((ComplexShape.embeddingDownNatAdd (finrank ℝ F)).extendFunctor _).map
          (twistedChainComplexCoefficientIso
            ((((isQuotientCoveringMap_proj hι).ulift.associatedLocalSystemFunctor
                (E := TopCat.of (VectorBundleOrientationCover F E ι))
                (p := TopCat.ofHom projection) k).mapIso
              (λ_ _ ≪≫ Rep.mkIso (Representation.ofLinearCharacterEquivOfDistribMulAction
                (uliftIntUnitsSign k) fun _ _ ↦ by simp [Units.smul_def]))) ≪≫
              associatedLocalSystemSignIso hι k)).hom :=
  (rfl)

variable (F E) in
/-- **The chain-level Thom map is a chain homotopy equivalence.** If the class of the
semi-invariant cocycle `φ` is a Thom class of the pull-back `E'` of `E` to the orientation double
cover, the chain map `C(E, E₀; k) ⟶ C(B; o(E) ⊗ k)[r]` of `thomPairTwistedChainMap` is a chain
homotopy equivalence, over every commutative ring `k`. The equivariant cap product with `φ` is a
quasi-isomorphism of complexes of projective representations of `ℤˣ`
(`TauCeti.quasiIso_singularChainsRepCap_thomPair`), hence a chain homotopy equivalence, which the
additive functor of sign coinvariants preserves. -/
theorem homotopyEquivalences_thomPairTwistedChainMap
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ)
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ (finrank ℝ F) φ)) :
    HomologicalComplex.homotopyEquivalences _ _ (thomPairTwistedChainMap F E hι k hφ) := by
  have := quasiIso_singularChainsRepCap_thomPair (F := F)
    (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) (G := ULift.{w} ℤˣ)
    (B := VectorBundleOrientationCover F E ι) (fun _ ↦ thomPair_map_smul _)
    (fun _ ↦ thomPairProj_smul _) (uliftIntUnitsSign k) hφ hu
  -- every factor but the coinvariants of the cap product is an isomorphism, and that factor is a
  -- chain homotopy equivalence because the cap product is a quasi-isomorphism
  exact MorphismProperty.comp_mem _ _ _ (.of_isIso _) <| MorphismProperty.comp_mem _ _ _
    (.of_isIso _) <| MorphismProperty.comp_mem _ _ _
      (TopPair.homotopyEquivalences_coinvariantsTwistedChainMap _ _ _ _ _ _ _) (.of_isIso _)

variable (F E) in
/-- **The Thom isomorphism with coefficients in the orientation system, from a semi-invariant Thom
cocycle on the orientation cover.** Let `E → B` be a real vector bundle of rank `r`, `B'` its
orientation double cover and `E'` the pull-back of `E` to `B'`, and let `k` be a commutative ring.
A relative cocycle `φ` of degree `r` of `(E', E'₀)` which the deck involution negates
(`TopPair.IsSemiInvariantCocycle` for the sign character of `ℤˣ`, acting through its copy
`ULift ℤˣ`: `TauCeti.uliftIntUnitsSign`) and whose class is a Thom class of `E'` gives
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)`, with coefficients in the orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`). -/
def thomPairSingularHomologyIsoTwistedHomology
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ)
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ (finrank ℝ F) φ))
    (p : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of k k) (p + finrank ℝ F) ≅
      twistedHomology (signLocalSystem F E k hι) p :=
  haveI : QuasiIso (thomPairTwistedChainMap F E hι k hφ) :=
    homotopyEquivalences_le_quasiIso _ _ _
      (homotopyEquivalences_thomPairTwistedChainMap F E hι k hφ hu)
  asIso (HomologicalComplex.homologyMap (thomPairTwistedChainMap F E hι k hφ) (p + finrank ℝ F)) ≪≫
    HomologicalComplex.extendHomologyIso _ _ (ComplexShape.embeddingDownNatAdd_f _ p)

variable (F E) in
/-- The isomorphism `thomPairSingularHomologyIsoTwistedHomology` is the map induced in homology by
the chain-level Thom map `thomPairTwistedChainMap`, followed by the removal of the shift. -/
theorem thomPairSingularHomologyIsoTwistedHomology_hom
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ)
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ (finrank ℝ F) φ))
    (p : ℕ) :
    (thomPairSingularHomologyIsoTwistedHomology F E hι k hφ hu p).hom =
      HomologicalComplex.homologyMap (thomPairTwistedChainMap F E hι k hφ) (p + finrank ℝ F) ≫
        (HomologicalComplex.extendHomologyIso _ _ (ComplexShape.embeddingDownNatAdd_f _ p)).hom :=
  (rfl)

variable (F E) in
/-- **The Thom isomorphism in cohomology with coefficients in the orientation system, from a
semi-invariant Thom cocycle on the orientation cover.** Let `E → B` be a real vector bundle of rank
`r`, `E'` its pull-back to the orientation double cover and `k` a commutative ring. A relative
cocycle `φ` of degree `r` of `(E', E'₀)` which the deck involution negates and whose class is a
Thom class of `E'` gives `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` for every `k`-module `N`, with
coefficients in the orientation local system `o(E)`. The chain map `thomPairTwistedChainMap` is a
chain homotopy equivalence, and `Hom(-, N)` preserves chain homotopy equivalences, so no hypothesis
on `N` is needed. This is the construction of the general
`TopPair.twistedCohomologyIsoTwistedCohomologyOfQuasiIso`, applied to `thomPairTwistedChainMap`,
which already contains the identifications of the trivial and sign local systems. -/
def thomPairSingularCohomologyIsoTwistedCohomology
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ)
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ (finrank ℝ F) φ))
    (N : ModuleCat.{w} k) (p : ℕ) :
    (thomPair F E).singularCohomology (ModuleCat.of k k) k N (p + finrank ℝ F) ≅
      (signLocalSystem F E k hι).twistedCohomology k N p :=
  haveI : QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k N).map
      (thomPairTwistedChainMap F E hι k hφ).op) :=
    homotopyEquivalences_le_quasiIso _ _ _
      (TauCeti.ChainComplex.homotopyEquivalences_linearYonedaFunctor_map k N
        (homotopyEquivalences_thomPairTwistedChainMap F E hι k hφ hu))
  (asIso (HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k N).map
      (thomPairTwistedChainMap F E hι k hφ).op) (p + finrank ℝ F))).symm ≪≫
    ChainComplex.linearYonedaObjExtendHomologyIso N _
      (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) (ComplexShape.embeddingDownNatAdd_f _ p)

variable (F E) in
/-- The inverse of `thomPairSingularCohomologyIsoTwistedCohomology` is the removal of the shift,
followed by the map induced in cohomology by precomposition with the chain-level Thom map
`thomPairTwistedChainMap`. -/
theorem thomPairSingularCohomologyIsoTwistedCohomology_inv
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ)
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ (finrank ℝ F) φ))
    (N : ModuleCat.{w} k) (p : ℕ) :
    (thomPairSingularCohomologyIsoTwistedCohomology F E hι k hφ hu N p).inv =
      (ChainComplex.linearYonedaObjExtendHomologyIso N _
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F))
        (ComplexShape.embeddingDownNatAdd_f _ p)).inv ≫
        HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k N).map
          (thomPairTwistedChainMap F E hι k hφ).op) (p + finrank ℝ F) :=
  (rfl)

variable (F E) in
/-- **The Thom isomorphism with orientation-twisted coefficients over every ring, from a lifted
Thom cocycle.** Let `E → B` be a real vector bundle of rank `r`, `E'` its pull-back to the
orientation double cover and `k` any commutative ring, for instance `ℤ`. A relative cocycle `ψ` of
`(E, E₀)` of degree `r` with coefficients in `π^*o(E)` whose lifted class
(`TauCeti.VectorBundleOrientationCover.thomPairSignCohomologyMap`) is a Thom class of `E'` gives
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)`, over any base and with no orientation of `E`. It is
`thomPairSingularHomologyIsoTwistedHomology` for the lift of `ψ`, which is semi-invariant
(`isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`) and whose class is a Thom class
(`isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap`). -/
def thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass
    (ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles (finrank ℝ F))
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F)
        (((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
          (ModuleCat.of k k)).homologyπ (finrank ℝ F) ψ)))
    (p : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of k k) (p + finrank ℝ F) ≅
      twistedHomology (signLocalSystem F E k hι) p :=
  thomPairSingularHomologyIsoTwistedHomology F E hι k
    (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι k ψ)
    (isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap hι k hu) p

/-- **The Thom isomorphism with coefficients in the orientation system, from a twisted class whose
lift is a Thom class.** Let `E → B` be a real vector bundle of rank `r`, `E'` its pull-back to the
orientation double cover and `k` a commutative ring. If the lift to `(E', E'₀)`
(`TauCeti.VectorBundleOrientationCover.thomPairSignCohomologyMap`) of a class
`U ∈ Hʳ(E, E₀; π^*o(E), k)` is a Thom class of `E'`, then `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` in
every degree `p`: `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass` applies to any
cocycle representing `U`. -/
theorem nonempty_singularHomology_thomPair_iso_twistedHomology
    (U : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)
      (finrank ℝ F))
    (hU : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F) U)) (p : ℕ) :
    Nonempty ((thomPair F E).singularHomology (ModuleCat.of k k) (p + finrank ℝ F) ≅
      twistedHomology (signLocalSystem F E k hι) p) := by
  obtain ⟨ψ, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (HomologicalComplex.homologyπ _ (finrank ℝ F))) U
  exact ⟨thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass F E hι k ψ hU p⟩

variable (F E) in
/-- **The Thom isomorphism in cohomology with orientation-twisted coefficients over every ring,
from a lifted Thom cocycle.** Let `E → B` be a real vector bundle of rank `r`, `E'` its pull-back to
the orientation double cover and `k` any commutative ring, for instance `ℤ`. A relative cocycle `ψ`
of `(E, E₀)` of degree `r` with coefficients in `π^*o(E)` whose lifted class
(`TauCeti.VectorBundleOrientationCover.thomPairSignCohomologyMap`) is a Thom class of `E'` gives
`Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` for every `k`-module `N`, over any base and with no
orientation of `E`. It is `thomPairSingularCohomologyIsoTwistedCohomology` for the lift of `ψ`,
which is semi-invariant (`isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`) and whose class
is a Thom class (`isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap`). -/
def thomPairSingularCohomologyIsoTwistedCohomologyOfIsThomClass
    (ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles (finrank ℝ F))
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F)
        (((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
          (ModuleCat.of k k)).homologyπ (finrank ℝ F) ψ)))
    (N : ModuleCat.{w} k) (p : ℕ) :
    (thomPair F E).singularCohomology (ModuleCat.of k k) k N (p + finrank ℝ F) ≅
      (signLocalSystem F E k hι).twistedCohomology k N p :=
  thomPairSingularCohomologyIsoTwistedCohomology F E hι k
    (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι k ψ)
    (isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap hι k hu) N p

/-- **The Thom isomorphism in cohomology with coefficients in the orientation system, from a
twisted class whose lift is a Thom class.** Let `E → B` be a real vector bundle of rank `r`, `E'`
its pull-back to the orientation double cover and `k` a commutative ring. If the lift to
`(E', E'₀)` (`TauCeti.VectorBundleOrientationCover.thomPairSignCohomologyMap`) of a class
`U ∈ Hʳ(E, E₀; π^*o(E), k)` is a Thom class of `E'`, then `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)`
for every `k`-module `N` and every degree `p`:
`thomPairSingularCohomologyIsoTwistedCohomologyOfIsThomClass` applies to any cocycle representing
`U`. -/
theorem nonempty_singularCohomology_thomPair_iso_twistedCohomology
    (U : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)
      (finrank ℝ F))
    (hU : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F) U))
    (N : ModuleCat.{w} k) (p : ℕ) :
    Nonempty ((thomPair F E).singularCohomology (ModuleCat.of k k) k N (p + finrank ℝ F) ≅
      (signLocalSystem F E k hι).twistedCohomology k N p) := by
  obtain ⟨ψ, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (HomologicalComplex.homologyπ _ (finrank ℝ F))) U
  exact ⟨thomPairSingularCohomologyIsoTwistedCohomologyOfIsThomClass F E hι k ψ hU N p⟩

end Descent

section ModelFiber

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type w) [CommRing k]

/-- **The Thom isomorphism with coefficients in the orientation system, over every ring.** Let
`E → B` be a real vector bundle of rank `r` over any base, orientable or not, with orientation
local system `o(E)`, and let `k` be a commutative ring, `ℤ` included. Then
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` in every degree `p`. For the Möbius line over the circle and
`k = ℤ` this gives `H₁(E, E₀; ℤ) ≅ H₀(S¹; o(E)) ≅ ℤ/2`, where constant coefficients would give
`ℤ`. The model fibre may lie in any universe, for instance `Fin r → ℝ : Type` for a base in a
higher universe. -/
theorem nonempty_singularHomology_thomPair_iso_twistedHomology_signLocalSystem (p : ℕ) :
    Nonempty ((thomPair F E).singularHomology (ModuleCat.of k k) (p + finrank ℝ F) ≅
      twistedHomology (signLocalSystem F E k hι) p) := by
  classical
  -- Read `E` with the model fibre `F' = ULift (ι → ℝ)`, which lies in the universe of `B` and of
  -- the fibres, with the topology on its total space induced along the identity of points.
  let L : F ≃L[ℝ] ULift.{w} (ι → ℝ) :=
    (ContinuousLinearEquiv.ofFinrankEq (by simp [hι])).trans ContinuousLinearEquiv.ulift.symm
  obtain ⟨_, h_ind, _, _⟩ := VectorBundle.exists_modelFiber_of_continuousLinearEquiv F (E := E) L
  have hι' : Fintype.card ι = finrank ℝ (ULift.{w} (ι → ℝ)) := hι.trans L.toLinearEquiv.finrank_eq
  -- For the model fibre `F'`, the lift to the orientation cover of the Thom class with
  -- coefficients in the orientation system, normalized by any orientation of `F'`, is a Thom
  -- class.
  let ω : Orientation ℝ (ULift.{w} (ι → ℝ)) ι :=
    ((Module.finBasis ℝ _).reindex (Fintype.equivFinOfCardEq hι').symm).orientation
  obtain ⟨e⟩ := nonempty_singularHomology_thomPair_iso_twistedHomology hι' k _
    (isThomClass_thomPairSignCohomologyMap_twistedThomClass (E := E) hι' ω) p
  -- The identity of points identifies the Thom pairs and the orientation systems of the two
  -- readings of `E`.
  exact ⟨(thomPair F E).singularHomologyMapIso (ModuleCat.of k k)
      (thomPairModelFiberIso h_ind).symm _ ≪≫
    eqToIso (by rw [L.toLinearEquiv.finrank_eq]) ≪≫ e ≪≫
    asIso (twistedHomologyCoefficientMap (signLocalSystemIsoOfFiberwise k hι hι'
      (φ := fun b ↦ .refl ℝ (E b)) (by simpa using h_ind.continuous)).inv p)⟩

variable (F E) in
/-- **The Thom isomorphism in cohomology with orientation-twisted coefficients.** Let `E → B` be a
real vector bundle of rank `r` over any base, orientable or not, with orientation local system
`o(E)`, let `k` be any commutative ring and `N` any `k`-module, for instance `k = N = ℤ`. Then
`Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` in every degree `p`. The model fibre may lie in any
universe. -/
theorem nonempty_singularCohomology_thomPair_iso_twistedCohomology_signLocalSystem
    (N : ModuleCat.{w} k) (p : ℕ) :
    Nonempty ((thomPair F E).singularCohomology (ModuleCat.of k k) k N (p + finrank ℝ F) ≅
      (signLocalSystem F E k hι).twistedCohomology k N p) := by
  classical
  -- As in homology, read `E` with the model fibre `F' = ULift (ι → ℝ)`, for which the lift of
  -- the Thom class with coefficients in the orientation system is a Thom class of the pull-back
  -- to the orientation cover.
  let L : F ≃L[ℝ] ULift.{w} (ι → ℝ) :=
    (ContinuousLinearEquiv.ofFinrankEq (by simp [hι])).trans ContinuousLinearEquiv.ulift.symm
  obtain ⟨_, h_ind, _, _⟩ := VectorBundle.exists_modelFiber_of_continuousLinearEquiv F (E := E) L
  have hι' : Fintype.card ι = finrank ℝ (ULift.{w} (ι → ℝ)) := hι.trans L.toLinearEquiv.finrank_eq
  let ω : Orientation ℝ (ULift.{w} (ι → ℝ)) ι :=
    ((Module.finBasis ℝ _).reindex (Fintype.equivFinOfCardEq hι').symm).orientation
  obtain ⟨e⟩ := nonempty_singularCohomology_thomPair_iso_twistedCohomology hι' k _
    (isThomClass_thomPairSignCohomologyMap_twistedThomClass (E := E) hι' ω) N p
  -- The identity of points identifies the Thom pairs and the orientation systems of the two
  -- readings of `E`.
  exact ⟨TopPair.singularCohomologyMapIso (ModuleCat.of k k) k N (thomPairModelFiberIso h_ind) _ ≪≫
    eqToIso (by rw [L.toLinearEquiv.finrank_eq]) ≪≫ e ≪≫
    twistedCohomologyCoefficientIso k N (signLocalSystemIsoOfFiberwise k hι hι'
      (φ := fun b ↦ .refl ℝ (E b)) (by simpa using h_ind.continuous)) p⟩

end ModelFiber

end TauCeti.VectorBundleOrientationCover
