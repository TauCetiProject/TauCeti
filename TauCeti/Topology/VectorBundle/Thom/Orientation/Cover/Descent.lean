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
(`TauCeti.VectorBundleOrientationCover.thomPairTwistedChainMap`), composed of three pieces.

* The equivariant cap product with `φ` is a quasi-isomorphism
  `C(E', E'₀; k) ⟶ (k_sign ⊗ C(B'; k))[r]` of complexes of representations of `ℤˣ`
  (`TauCeti.quasiIso_singularChainsRepCap_thomPair`). The actions on `E'` and `B'` are free, so both
  are complexes of projective representations and it is a chain homotopy equivalence.
* Taking coinvariants against the trivial representation, the source becomes the relative chains of
  `(E, E₀)` with coefficients in the local system associated to the trivial representation
  (`TopPair.coinvariantsTensorSingularChainsRepIsoTwisted`), which is constant
  (`IsQuotientCoveringMap.associatedLocalSystemTrivialIso`), so it is `C(E, E₀; k)`.
* The target becomes the sign coinvariants `(k_sign ⊗ C(B'; k))_{ℤˣ}`, placed `r` degrees higher,
  which are the chains of `B` with coefficients in `o(E)`
  (`TauCeti.VectorBundleOrientationCover.coinvariantsTensorSingularChainsRepIsoTwisted`).

Coinvariants form an additive functor, so the chain map is a chain homotopy equivalence
(`TauCeti.VectorBundleOrientationCover.homotopyEquivalences_thomPairTwistedChainMap`). Hence
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
(`TauCeti.twistedThomClass`, over a compact base), which takes the value `1` on the fibre class
over every point. Its lift is a Thom class of `E'`
(`isThomClass_thomPairSignCohomologyMap_twistedThomClass`), so over a compact base
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` holds for every bundle and every commutative ring `k`
(`nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`, in the namespace
`TauCeti.VectorBundleOrientationCover`), and so does `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` for
every `k`-module `N` (`nonempty_singularCohomology_thomPair_iso_twistedCohomology_of_compactSpace`,
in the same namespace).

The base, the fibres and the ring lie in any common universe `w`, and the orientations are indexed
by a type `ι : Type`, such as `Fin r`. Representations, their associated local systems and the
equivariant cap product need the acting group in the universe `w`, so `ℤˣ` acts through its copy
`ULift ℤˣ` there (`IsQuotientCoveringMap.ulift`).

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
* `nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`: over a compact base,
  `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` for every bundle and every commutative ring `k`.
* `thomPairSingularCohomologyIsoTwistedCohomology`: `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)`
  for every `k`-module `N`, from a semi-invariant Thom cocycle of `E'`, and
  `nonempty_singularCohomology_thomPair_iso_twistedCohomology`: the same from a class of
  `Hʳ(E, E₀; π^*o(E), k)` whose lift is a Thom class of `E'`.
* `nonempty_singularCohomology_thomPair_iso_twistedCohomology_of_compactSpace`: over a compact
  base, `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` for every bundle, every commutative ring `k` and
  every `k`-module `N`.

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
the sign coinvariants of the equivariant cap product with `φ`
(`TopPair.singularChainsRepCap`), read through the identifications of the coinvariants of the
chains of `(E', E'₀)` with the relative chains of `(E, E₀)` and of the sign coinvariants of the
chains of `B'` with the orientation-twisted chains of `B`. When the class of `φ` is a Thom class of
`E'` it is a chain homotopy equivalence (`homotopyEquivalences_thomPairTwistedChainMap`). -/
def thomPairTwistedChainMap
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (uliftIntUnitsSign.{w} k) φ) :
    (thomPair F E).singularChainComplex (ModuleCat.of k k) ⟶
      (twistedChainComplex (signLocalSystem F E k hι)).extend
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) :=
  haveI := (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift.{w}.toContinuousConstSMul
  haveI := (isQuotientCoveringMap_coverThomPairMap_snd F E ι hι).ulift.{w}.toContinuousConstSMul
  ((thomPair F E).twistedChainComplexConstantIso (ModuleCat.of k k)).inv ≫
    ((thomPair F E).twistedChainComplexCoefficientIso
      ((isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift.associatedLocalSystemTrivialIso
        k k)).inv ≫
    ((thomPair F _).coinvariantsTensorSingularChainsRepIsoTwisted k
      (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift
      (isQuotientCoveringMap_coverThomPairMap_snd F E ι hι).ulift (fun _ ↦ thomPair_map_smul _)
      (Rep.trivial k (ULift.{w} ℤˣ) k)).inv ≫
    (((Rep.coinvariantsTensor k (ULift.{w} ℤˣ)).obj
      (Rep.trivial k (ULift.{w} ℤˣ) k)).mapHomologicalComplex _).map (TopPair.singularChainsRepCap
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (p₀ := thomPairProj F _) (fun _ ↦ thomPairProj_smul _) (uliftIntUnitsSign k) hφ
        (fun _ ↦ thomPair_map_smul _)) ≫
    (HomologicalComplex.mapExtendIso _ _ _).hom ≫
    ((ComplexShape.embeddingDownNatAdd (finrank ℝ F)).extendFunctor _).map
      ((NatIso.mapHomologicalComplex (Rep.tensorLeftCompCoinvariantsTensorTrivialIso _ ≪≫
        (Rep.coinvariantsTensor k (ULift.{w} ℤˣ)).mapIso
          (Rep.mkIso (Representation.ofLinearCharacterEquivOfDistribMulAction
            (uliftIntUnitsSign k) fun _ _ ↦ by simp [Units.smul_def]))) _).app _ ≪≫
        coinvariantsTensorSingularChainsRepIsoTwisted hι k).hom

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
  have := (isQuotientCoveringMap_proj (F := F) (E := E) hι).ulift.{w}.isCancelSMul
  have := (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift.{w}.toContinuousConstSMul
  have := (isQuotientCoveringMap_coverThomPairMap_snd F E ι hι).ulift.{w}.toContinuousConstSMul
  have := (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift.{w}.isCancelSMul
  have := quasiIso_singularChainsRepCap_thomPair (F := F)
    (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) (G := ULift.{w} ℤˣ)
    (B := VectorBundleOrientationCover F E ι) (fun _ ↦ thomPair_map_smul _)
    (fun _ ↦ thomPairProj_smul _) (uliftIntUnitsSign k) hφ hu
  -- every factor but the coinvariants of the cap product is an isomorphism, and that factor is the
  -- image of a chain homotopy equivalence between complexes of projective representations
  refine MorphismProperty.comp_mem _ _ _ (.of_isIso _) <| MorphismProperty.comp_mem _ _ _
    (.of_isIso _) <| MorphismProperty.comp_mem _ _ _ (.of_isIso _) <|
      MorphismProperty.comp_mem _ _ _ ?_ <| MorphismProperty.comp_mem _ _ _ (.of_isIso _)
        (.of_isIso _)
  have : ∀ n, Projective ((TopPair.singularChainsRep
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) k
      (ULift.{w} ℤˣ) (fun _ ↦ thomPair_map_smul _)).X n) :=
    fun n ↦ TopPair.projective_singularChainsRep_X _ k _ _ n
  exact Functor.homotopyEquivalences_mapHomologicalComplex_map _ _
    ((ChainComplex.quasiIso_iff_of_projective _).1 ‹_›)


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
/-- **The Thom isomorphism in cohomology with coefficients in the orientation system, from a
semi-invariant Thom cocycle on the orientation cover.** Let `E → B` be a real vector bundle of rank
`r`, `E'` its pull-back to the orientation double cover and `k` a commutative ring. A relative
cocycle `φ` of degree `r` of `(E', E'₀)` which the deck involution negates and whose class is a
Thom class of `E'` gives `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` for every `k`-module `N`, with
coefficients in the orientation local system `o(E)`. The chain map `thomPairTwistedChainMap` is a
chain homotopy equivalence, and `Hom(-, N)` preserves chain homotopy equivalences, so no hypothesis
on `N` is needed. -/
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
    ChainComplex.linearYonedaObjExtendHomologyIso N _ (finrank ℝ F) p

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

/-- **The Thom isomorphism with coefficients in the orientation system over a compact base, over
every ring.** Let `E → B` be a real vector bundle of rank `r` over a compact base, orientable or
not, with orientation local system `o(E)`, and let `k` be a commutative ring, `ℤ` included. Then
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` in every degree `p`. For the Möbius line over the circle and
`k = ℤ` this gives `H₁(E, E₀; ℤ) ≅ H₀(S¹; o(E)) ≅ ℤ/2`, where constant coefficients would give
`ℤ`. -/
theorem nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace [CompactSpace B]
    (p : ℕ) :
    Nonempty ((thomPair F E).singularHomology (ModuleCat.of k k) (p + finrank ℝ F) ≅
      twistedHomology (signLocalSystem F E k hι) p) := by
  classical
  -- The lift to the orientation cover of the Thom class with coefficients in the orientation
  -- system, normalized by any orientation of the model fibre, is a Thom class.
  let ω : Orientation ℝ F ι :=
    ((Module.finBasis ℝ F).reindex (Fintype.equivFinOfCardEq hι).symm).orientation
  exact nonempty_singularHomology_thomPair_iso_twistedHomology hι k _
    (isThomClass_thomPairSignCohomologyMap_twistedThomClass hι ω) p

/-- **The Thom isomorphism in cohomology with coefficients in the orientation system, from a
twisted class whose lift is a Thom class.** Let `E → B` be a real vector bundle of rank `r`, `E'`
its pull-back to the orientation double cover and `k` a commutative ring. If the lift to
`(E', E'₀)` (`TauCeti.VectorBundleOrientationCover.thomPairSignCohomologyMap`) of a class
`U ∈ Hʳ(E, E₀; π^*o(E), k)` is a Thom class of `E'`, then `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)`
for every `k`-module `N` and every degree `p`: `thomPairSingularCohomologyIsoTwistedCohomology`
applies to the lift of any cocycle representing `U`. -/
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
  exact ⟨thomPairSingularCohomologyIsoTwistedCohomology F E hι k
    (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι k ψ)
    (isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap hι k hU) N p⟩

variable (F E) in
/-- **The Thom isomorphism in cohomology with orientation-twisted coefficients over a compact
base.** Let `E → B` be a real vector bundle of rank `r` over a compact base, orientable or not, with
orientation local system `o(E)`, let `k` be any commutative ring and `N` any `k`-module, for
instance `k = N = ℤ`. Then `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` in every degree `p`. -/
theorem nonempty_singularCohomology_thomPair_iso_twistedCohomology_of_compactSpace
    [CompactSpace B] (N : ModuleCat.{w} k) (p : ℕ) :
    Nonempty ((thomPair F E).singularCohomology (ModuleCat.of k k) k N (p + finrank ℝ F) ≅
      (signLocalSystem F E k hι).twistedCohomology k N p) := by
  classical
  -- As in homology, the lift of the Thom class with coefficients in the orientation system is a
  -- Thom class of the pull-back to the orientation cover.
  let ω : Orientation ℝ F ι :=
    ((Module.finBasis ℝ F).reindex (Fintype.equivFinOfCardEq hι).symm).orientation
  exact nonempty_singularCohomology_thomPair_iso_twistedCohomology hι k _
    (isThomClass_thomPairSignCohomologyMap_twistedThomClass hι ω) N p

end TauCeti.VectorBundleOrientationCover
