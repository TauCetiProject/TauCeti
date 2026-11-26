/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.MapExtend
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Kronecker
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
over every point. Its lift is a Thom class of `E'`
(`isThomClass_thomPairSignCohomologyMap_twistedThomClass`), so over a compact base
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` holds for every bundle and every commutative ring `k`
(`nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`, in the namespace
`TauCeti.VectorBundleOrientationCover`). By the universal coefficient theorem it transposes to
cohomology with values in any injective module
(`nonempty_singularCohomology_thomPair_iso_twistedCohomology_of_compactSpace`, in the same
namespace).

The base, the fibres and the ring lie in any common universe `w`, and the orientations are indexed
by a type `ι : Type`, such as `Fin r`. Representations, their associated local systems and the
equivariant cap product need the acting group in the universe `w`, so `ℤˣ` acts through its copy
`ULift ℤˣ` there (`IsQuotientCoveringMap.ulift`). The descent also needs the model fibre in the
universe `w`. Over a compact base the model fibre may lie in any universe, such as
`Fin r → ℝ : Type`: the bundle is read with the model fibre `ULift (ι → ℝ)` instead
(`VectorBundle.exists_modelFiber_of_continuousLinearEquiv`), which changes neither its Thom pair
(`TauCeti.thomPairModelFiberIso`) nor its orientation local system.

## Main definitions and results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `thomPairSingularHomologyIsoTwistedHomology`: `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` from a
  semi-invariant Thom cocycle of `E'`.
* `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass`: the same from a cocycle of
  `(E, E₀)` with coefficients in `π^*o(E)` whose lifted class is a Thom class of `E'`, and
  `nonempty_singularHomology_thomPair_iso_twistedHomology`: the same from a class of
  `Hʳ(E, E₀; π^*o(E), k)` whose lift is a Thom class of `E'`.
* `nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`: over a compact base,
  `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` for every bundle and every commutative ring `k`.
* `nonempty_singularCohomology_thomPair_iso_twistedCohomology_of_compactSpace`: its transpose
  `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` in cohomology, for injective values `N`.

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
  haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).ulift.{w}.isCancelSMul
  -- `ℤˣ` acts through its copy `ULift ℤˣ` in the universe of the spaces, as representations and
  -- associated local systems require.
  haveI := quasiIso_singularChainsRepCap_thomPair (F := F)
    (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) (G := ULift.{w} ℤˣ)
    (B := VectorBundleOrientationCover F E ι) (fun _ ↦ thomPair_map_smul _)
    (fun _ ↦ thomPairProj_smul _) (uliftIntUnitsSign k) hφ hu
  ((thomPair F E).twistedHomologyConstantIso (ModuleCat.of k k) _).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso
      ((thomPair F E).twistedChainComplexCoefficientIso
        ((isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift.associatedLocalSystemTrivialIso
          k k)).symm ≪≫
    (thomPair F _).twistedHomologyIsoHomologyCoinvariantsTensorObj k
      (isQuotientCoveringMap_coverThomPairMap_fst F E ι hι).ulift
      (isQuotientCoveringMap_coverThomPairMap_snd F E ι hι).ulift (fun _ ↦ thomPair_map_smul _)
      -- the pair and `p₀` are explicit so that the cap map is the one of the instance above:
      -- `thomPairProj_smul` reads the zeros of the fibres through `pullbackFiberZero` instead
      (Rep.trivial k (ULift.{w} ℤˣ) k) (TopPair.singularChainsRepCap
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (p₀ := thomPairProj F _) (fun _ ↦ thomPairProj_smul _) (uliftIntUnitsSign k) hφ
        (fun _ ↦ thomPair_map_smul _))
      (p + finrank ℝ F) ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso (HomologicalComplex.mapExtendIso _ _ _) ≪≫
    HomologicalComplex.extendHomologyIso _ _ (ComplexShape.embeddingDownNatAdd_f _ p) ≪≫
    (HomologicalComplex.homologyFunctor _ _ p).mapIso
      ((NatIso.mapHomologicalComplex (Rep.tensorLeftCompCoinvariantsTensorTrivialIso _ ≪≫
        (Rep.coinvariantsTensor k (ULift.{w} ℤˣ)).mapIso
          (Rep.mkIso (Representation.ofLinearCharacterEquivOfDistribMulAction
            (uliftIntUnitsSign k) fun _ _ ↦ by simp [Units.smul_def]))) _).app _) ≪≫
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

end Descent

section CompactSpace

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type w) [CommRing k]

/-- **The Thom isomorphism with coefficients in the orientation system over a compact base, over
every ring.** Let `E → B` be a real vector bundle of rank `r` over a compact base, orientable or
not, with orientation local system `o(E)`, and let `k` be a commutative ring, `ℤ` included. Then
`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` in every degree `p`. For the Möbius line over the circle and
`k = ℤ` this gives `H₁(E, E₀; ℤ) ≅ H₀(S¹; o(E)) ≅ ℤ/2`, where constant coefficients would give
`ℤ`. The model fibre may lie in any universe, for instance `Fin r → ℝ : Type` for a base in a
higher universe. -/
theorem nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace [CompactSpace B]
    (p : ℕ) :
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
/-- **The Thom isomorphism in cohomology with orientation-twisted coefficients over a compact
base.** Let `E → B` be a real vector bundle of rank `r` over a compact base, orientable or not, with
orientation local system `o(E)`, let `k` be any commutative ring and `N` an injective `k`-module,
for instance `k = ℤ` and `N = ℚ`. Then `Hᵖ⁺ʳ(E, E₀; k, N) ≅ Hᵖ(B; o(E) ⊗ k, N)` in every degree `p`.
The model fibre may lie in any universe.

It is the transpose of `nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`:
with injective values both cohomologies are the duals `Hom(-, N)` of the corresponding homologies,
by the universal coefficient theorem (`TopPair.singularKronecker_bijective` and
`TauCeti.LocalCoefficientSystem.twistedKronecker_bijective`). -/
theorem nonempty_singularCohomology_thomPair_iso_twistedCohomology_of_compactSpace
    [CompactSpace B] (N : ModuleCat.{w} k) [Injective N] (p : ℕ) :
    Nonempty ((thomPair F E).singularCohomology (ModuleCat.of k k) k N (p + finrank ℝ F) ≅
      (signLocalSystem F E k hι).twistedCohomology k N p) := by
  obtain ⟨e⟩ := nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace
    (F := F) (E := E) hι k p
  exact ⟨((LinearEquiv.ofBijective _ ((thomPair F E).singularKronecker_bijective k _)).trans
    ((Linear.homCongr k e (Iso.refl N)).trans
      ((signLocalSystem F E k hι).twistedKroneckerEquiv k p).symm)).toModuleIso⟩

end CompactSpace

end TauCeti.VectorBundleOrientationCover
