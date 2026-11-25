/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.MapExtend
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

The isomorphism is composed of three identifications.

* The equivariant cap product with `φ` is a quasi-isomorphism
  `C(E', E'₀; k) ⟶ (k_sign ⊗ C(B'; k))[r]` of complexes of representations of `ℤˣ`
  (`TauCeti.quasiIso_singularChainsRepCap_thomPair`). The action on `B'` is free, so the target is
  a complex of projective representations.
* Taking coinvariants against the trivial representation, the source becomes the relative chains of
  `(E, E₀)` with coefficients in the local system associated to the trivial representation
  (`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`), which is constant
  (`IsQuotientCoveringMap.associatedLocalSystemTrivialIso`), so its homology is `Hₘ(E, E₀; k)`.
* The target becomes the sign coinvariants `(k_sign ⊗ C(B'; k))_{ℤˣ}`, placed `r` degrees higher,
  which are the chains of `B` with coefficients in `o(E)`
  (`TauCeti.VectorBundleOrientationCover.coinvariantsTensorSingularChainsRepIsoTwisted`).

Such cocycles come from classes of `(E, E₀)` with coefficients in the pulled-back orientation
system `π^*o(E)`. The deck involution negates every lifted cochain on the nose
(`thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap`), so the lift of a twisted
cocycle is semi-invariant
(`TauCeti.VectorBundleOrientationCover.isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`, in
`TauCeti.Topology.VectorBundle.Thom.Orientation.TwistedLift`).
Hence, whenever the lift of a class `U ∈ Hʳ(E, E₀; π^*o(E), k)` to `(E', E'₀)` is a Thom class of
`E'`, `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` in every degree
(`TauCeti.VectorBundleOrientationCover.nonempty_singularHomology_thomPair_iso_twistedHomology`).
The natural class `U` is the Thom class with coefficients in the orientation system
(`TauCeti.twistedThomClass`, over a compact base), which takes the value `1` on the fibre class
over every point. Over a compact base this gives the Thom isomorphism with orientation-twisted
coefficients for every bundle and every ring
(`nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`).

The lifts of cochains to the orientation cover are stated with the orientations indexed by a type
`ι : Type`, so the base, the fibres and the ring live in `Type` here.

## Main definitions and results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `thomPairSingularHomologyIsoTwistedHomology`: `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` from a
  semi-invariant Thom cocycle of `E'`.
* `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass`: the same from a cocycle of
  `(E, E₀)` with coefficients in `π^*o(E)` whose lifted class is a Thom class of `E'`, and
  `nonempty_singularHomology_thomPair_iso_twistedHomology`: the same from a class of
  `Hʳ(E, E₀; π^*o(E), k)` whose lift is a Thom class of `E'`.
* `nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`: the same for every
  bundle over a compact base.

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

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type) [CommRing k]

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
/-- **The Thom isomorphism with coefficients in the orientation system, from a semi-invariant Thom
cocycle on the orientation cover.** Let `E → B` be a real vector bundle of rank `r`, `B'` its
orientation double cover and `E'` the pull-back of `E` to `B'`, and let `k` be a commutative ring.
A relative cocycle `φ` of degree `r` of `(E', E'₀)` which the deck involution negates
(`TopPair.IsSemiInvariantCocycle` for the sign character of `ℤˣ`) and whose class is a Thom class of
`E'` gives `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)`, with coefficients in the orientation local system
`o(E)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`). -/
def thomPairSingularHomologyIsoTwistedHomology
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle (Units.map (Int.castRingHom k).toMonoidHom) φ)
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ (finrank ℝ F) φ))
    (p : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of k k) (p + finrank ℝ F) ≅
      twistedHomology (signLocalSystem F E k hι) p :=
  haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).isCancelSMul
  haveI := quasiIso_singularChainsRepCap_thomPair (F := F)
    (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) (G := ℤˣ)
    (B := VectorBundleOrientationCover F E ι) thomPair_map_smul thomPairProj_smul
    (Units.map (Int.castRingHom k).toMonoidHom) hφ hu
  ((thomPair F E).twistedHomologyConstantIso (ModuleCat.of k k) _).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso
      ((thomPair F E).twistedChainComplexCoefficientIso
        ((isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).associatedLocalSystemTrivialIso k
          k)).symm ≪≫
    (thomPair F _).twistedHomologyIsoHomologyCoinvariantsTensorObj k
      (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι)
      (isQuotientCoveringMap_coverThomPairMap_snd F E ι hι) thomPair_map_smul
      -- the pair and `p₀` are explicit so that the cap map is the one of the instance above:
      -- `thomPairProj_smul` reads the zeros of the fibres through `pullbackFiberZero` instead
      (Rep.trivial k ℤˣ k) (TopPair.singularChainsRepCap
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (p₀ := thomPairProj F _) thomPairProj_smul (Units.map (Int.castRingHom k).toMonoidHom) hφ
        thomPair_map_smul)
      (p + finrank ℝ F) ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso (HomologicalComplex.mapExtendIso _ _ _) ≪≫
    HomologicalComplex.extendHomologyIso _ _ (ComplexShape.embeddingDownNatAdd_f _ p) ≪≫
    (HomologicalComplex.homologyFunctor _ _ p).mapIso
      ((NatIso.mapHomologicalComplex (Rep.tensorLeftCompCoinvariantsTensorTrivialIso _ ≪≫
        (Rep.coinvariantsTensor k ℤˣ).mapIso
          (Rep.mkIso Representation.ofLinearCharacterIntCastEquivOfDistribMulAction)) _).app _) ≪≫
    (HomologicalComplex.homologyFunctor _ _ p).mapIso
      (coinvariantsTensorSingularChainsRepIsoTwisted hι k)

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
/-- **The Thom isomorphism with coefficients in the orientation system over a compact base.** Let
`E → B` be a real vector bundle of rank `r` over a compact base, orientable or not, and `k` a
commutative ring, `ℤ` included. Then `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` in every degree `p`, where
`o(E)` is the orientation local system of `E`. -/
theorem nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace [CompactSpace B]
    (p : ℕ) :
    Nonempty ((thomPair F E).singularHomology (ModuleCat.of k k) (p + finrank ℝ F) ≅
      twistedHomology (signLocalSystem F E k hι) p) := by
  classical
  -- An orientation of the model fibre normalizes the Thom class with coefficients in `o(E)`.
  let ω : Orientation ℝ F ι :=
    ((Module.finBasis ℝ F).reindex (Fintype.equivFinOfCardEq hι).symm).orientation
  exact nonempty_singularHomology_thomPair_iso_twistedHomology hι k (twistedThomClass F E k hι ω)
    (isThomClass_thomPairSignCohomologyMap_twistedThomClass hι ω) p

end TauCeti.VectorBundleOrientationCover
