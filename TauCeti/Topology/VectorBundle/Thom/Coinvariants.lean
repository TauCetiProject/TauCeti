/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.MapExtend
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Coordinates
public import TauCeti.AlgebraicTopology.Singular.Twisted.QuotientCovering
public import TauCeti.Topology.VectorBundle.Orientation.Cover.SignRepresentation
public import TauCeti.Topology.VectorBundle.Thom.CoverChainMap
public import TauCeti.Topology.VectorBundle.Thom.EquivariantCap

/-!
# The twisted Thom isomorphism over every ring, by descent from the orientation cover

Let `E → B` be a real vector bundle of rank `r`, with Thom pair `(E, E₀)` and orientation local
system `o(E)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`), and let `k` be a commutative
ring, `ℤ` included. Let `B'` be the orientation double cover of `E`, `E'` the pull-back of `E` to
`B'`, and `δ` the lift of the deck involution to the Thom pair `(E', E'₀)`
(`TauCeti.VectorBundleOrientationCover.deckThomPairMap`). A relative cocycle `ψ` of `(E, E₀)` with
coefficients in `π^*o(E)` lifts to a relative cocycle `φ` of `(E', E'₀)` with coefficients in `k`
(`TauCeti.VectorBundleOrientationCover.thomPairSignCochainMap`). This file proves that if `φ`
represents a Thom class of the tautologically oriented bundle `E'`, then capping with `φ` gives
the Thom isomorphism with orientation-twisted coefficients

`Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)`

(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass`),
over any base and with no orientation of `E`. Unlike
`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`, which passes
through the transfer of the double cover, nothing here asks `2` to be invertible in `k`: the
isomorphism descends a chain-level quasi-isomorphism along the coinvariants of `ℤˣ`.

The group `ℤˣ` acts freely on `(E', E'₀)` and on `B'`, with quotients `(E, E₀)` and `B`
(`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_pullbackThomPairMap_fst`,
`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_proj`), and `-1` acts on `E'` by `δ`.
The lifted cocycle is negated by `δ` exactly, at the level of cochains: in the namespace
`TauCeti.VectorBundleOrientationCover`, this is
`thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap`. So `φ` is semi-invariant
for the sign character `ℤˣ →* kˣ` (`TopPair.IsSemiInvariantCocycle`), and the cap product with `φ`
is a quasi-isomorphism of complexes of representations of `ℤˣ`,

`C(E', E'₀; k) ⟶ (k_sign ⊗ C(B'; k))[r]`

(`TauCeti.quasiIso_singularChainsRepCap_thomPair`). Both complexes consist of projective
representations, as the actions are free, so this quasi-isomorphism is a chain homotopy
equivalence and survives taking coinvariants
(`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`).
The coinvariants of the relative chains of `(E', E'₀)` are the relative chains of `(E, E₀)` with
constant coefficients (`IsQuotientCoveringMap.associatedLocalSystemTrivialIso`), and the
coinvariants of `k_sign ⊗ C(B'; k)` are the chains of `B` twisted by `o(E)`
(`TauCeti.VectorBundleOrientationCover.coinvariantsTensorSingularChainsRepIsoTwisted`).

Exact anti-invariance of the cocycle is what the equivariant cap product needs; a representative
of a cohomology class which `δ^*` negates need not be negated by `δ^*` itself when `2` is not
invertible in `k`. This is why the cocycle is lifted from orientation-twisted cochains of `E`.

## Main definitions and results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass`: the isomorphism
  `Hₚ₊ᵣ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` given by an orientation-twisted cocycle of `(E, E₀)` whose
  lift to the orientation cover represents a Thom class, with
  `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass_hom` describing it step by step.
* `isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`: the lift of an orientation-twisted
  cocycle of `(E, E₀)` is semi-invariant for the sign character.
* `coinvariantsTensorSingularChainsRepExtendIsoTwisted`: the coinvariants of the shifted chains
  of `B'` twisted by the sign character are the shifted chains of `B` twisted by `o(E)`, with
  `coinvariantsTensorSingularChainsRepExtendIsoTwisted_hom_f_mk` computing it on the class of
  `1 ⊗ (a ⊗ τ)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module MonoidalCategory

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type} [Fintype ι]
  (hι : Fintype.card ι = finrank ℝ F) (k : Type) [CommRing k]

-- The zeros of the fibres of the pull-back are read as in `TauCeti.pullbackThomPairMap`, so that
-- the Thom pair of the pull-back here is the source of that map and carries the actions of `ℤˣ`.
attribute [local instance] pullbackFiberZero thomPairFstMulAction thomPairSndMulAction

/-- The representation of the sign character `ℤˣ →* kˣ` is the action of `ℤˣ` on `k`. -/
private def signCharacterRepIso :
    Rep.of (Representation.ofLinearCharacter (Units.map (Int.castRingHom k : ℤ →* k))) ≅
      Rep.ofDistribMulAction k ℤˣ k :=
  eqToIso (congrArg Rep.of Representation.ofLinearCharacter_unitsMap_intCastRingHom)

variable (F E ι) in
/-- The coinvariants of the chains of the orientation cover twisted by the sign character and
shifted up by `n` are the chains of the base twisted by the orientation local system, shifted up
by `n`. In degree `q + n`, the class of `1 ⊗ (a ⊗ τ)` goes to the simplex `p ∘ τ` with the
coefficient of `o(E)` whose value at the initial orientation of `τ` is `a`
(`coinvariantsTensorSingularChainsRepExtendIsoTwisted_hom_f_mk`). -/
def coinvariantsTensorSingularChainsRepExtendIsoTwisted (n : ℕ) :
    haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
    (((((tensorLeft (Rep.of (Representation.ofLinearCharacter
        (Units.map (Int.castRingHom k : ℤ →* k))))).mapHomologicalComplex _).obj
        (singularChainsRep k (TopCat.of (VectorBundleOrientationCover F E ι)) ℤˣ)).extend
          (ComplexShape.embeddingDownNatAdd n)).coinvariantsTensorObj (Rep.trivial k ℤˣ k)) ≅
      (LocalCoefficientSystem.twistedChainComplex (signLocalSystem F E k hι)).extend
        (ComplexShape.embeddingDownNatAdd n) :=
  haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
  HomologicalComplex.mapExtendIso _ _ _ ≪≫
    ((ComplexShape.embeddingDownNatAdd n).extendFunctor _).mapIso
      ((Functor.mapHomologicalComplexCompIso
          (Rep.tensorLeftCompCoinvariantsTensorTrivialIso k ℤˣ _ ≪≫
            (Rep.coinvariantsTensor k ℤˣ).mapIso (signCharacterRepIso k)) _).app _ ≪≫
        coinvariantsTensorSingularChainsRepIsoTwisted hι k)

open scoped Simplicial TensorProduct in
open LocalCoefficientSystem in
variable (F E ι) in
/-- In the degree `q + n` of the shifted complexes,
`coinvariantsTensorSingularChainsRepExtendIsoTwisted` sends the class of `1 ⊗ (a ⊗ τ)` to the
simplex `p ∘ τ` of `B` with the coefficient of `o(E)` whose value at the initial orientation of `τ`
is `a`, as `coinvariantsTensorSingularChainsRepIsoTwisted` does in degree `q`. -/
theorem coinvariantsTensorSingularChainsRepExtendIsoTwisted_hom_f_mk (n : ℕ) {q j : ℕ}
    (h : (ComplexShape.embeddingDownNatAdd n).f q = j) (a : k)
    (τ : (TopCat.toSSet.obj (TopCat.of (VectorBundleOrientationCover F E ι))) _⦋q⦌) :
    haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
    ((coinvariantsTensorSingularChainsRepExtendIsoTwisted F E ι hι k n).hom.f j).hom
      ((((Rep.coinvariantsTensor k ℤˣ).obj (Rep.trivial k ℤˣ k)).map
        (((((tensorLeft (Rep.of (Representation.ofLinearCharacter
          (Units.map (Int.castRingHom k : ℤ →* k))))).mapHomologicalComplex _).obj
          (singularChainsRep k (TopCat.of (VectorBundleOrientationCover F E ι)) ℤˣ)).extendXIso
            (ComplexShape.embeddingDownNatAdd n) h).inv)).hom
        (Rep.coinvariantsTensorMk (Rep.trivial k ℤˣ k) _ 1 (a ⊗ₜ simplexChain τ 1))) =
      (((twistedChainComplex (signLocalSystem F E k hι)).extendXIso
          (ComplexShape.embeddingDownNatAdd n) h).inv).hom
        ((ιTwistedChainComplex (signLocalSystem F E k hι) q
          ((TopCat.toSSet.map (TopCat.ofHom projection)).app _ τ)).hom
            ((signLocalSystemObjEquiv hι _).symm
              ((signFiberEquiv deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h)
                (initialSheet τ)).symm a))) := by
  have := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
  -- both extensions conjugate the component in degree `q` by `extendXIso`
  rw [coinvariantsTensorSingularChainsRepExtendIsoTwisted, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex.mapExtendIso_hom_f _ _ _ h, Functor.mapIso_hom,
    ComplexShape.Embedding.extendFunctor_map, HomologicalComplex.extendMap_f _ _ h,
    Category.assoc, Iso.inv_hom_id_assoc, ← ModuleCat.comp_apply, Iso.inv_hom_id_map_assoc,
    ModuleCat.comp_apply, Iso.trans_hom, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    Iso.app_hom, Functor.mapHomologicalComplexCompIso_hom_app_f]
  refine congrArg _ ?_
  rw [← coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk hι k q a τ]
  refine congrArg _ ?_
  rw [Iso.trans_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    Rep.tensorLeftCompCoinvariantsTensorTrivialIso_hom_app, Functor.mapIso_hom]
  have heqToIso : ∀ {ρ σ : Representation k ℤˣ k} (hρ : ρ = σ) (x : k),
      (eqToIso (congrArg Rep.of hρ)).hom.hom x = x := by
    rintro _ _ rfl x
    rfl
  -- by definition, the left unitor sends `1 ⊗ (a ⊗ τ)` to `(1 • a) ⊗ τ`, and
  -- `signCharacterRepIso` is the `eqToIso` of `ofLinearCharacter_unitsMap_intCastRingHom`
  exact congrArg (fun b ↦ Rep.coinvariantsTensorMk (Rep.ofDistribMulAction k ℤˣ k)
    (Rep.of (singularChainsRepresentation k (TopCat.of (VectorBundleOrientationCover F E ι)) ℤˣ q))
    b (simplexChain τ (1 : k)))
      ((heqToIso Representation.ofLinearCharacter_unitsMap_intCastRingHom ((1 : k) • a)).trans
        (one_smul k a))

include hι in
/-- The action of `ℤˣ` on the total space of the pull-back of `E` to the orientation cover is by
homeomorphisms, as that total space is a quotient covering space of the total space of `E`. -/
private theorem continuousConstSMul_thomPairFst :
    ContinuousConstSMul ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul

/-- A relative cocycle of the Thom pair of the orientation cover which the lifted deck involution
negates is semi-invariant for the sign character of `ℤˣ`, since `-1` acts by the lifted deck
involution. -/
private theorem isSemiInvariantCocycle_of_anti_invariant {n : ℕ}
    {φ : (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n}
    (hφ : (TopPair.singularCochainComplexMap (deckThomPairMap F E ι)).f n
        (HomologicalComplex.iCycles (TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of k k) k (ModuleCat.of k k)) n φ) =
      -HomologicalComplex.iCycles (TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of k k) k (ModuleCat.of k k)) n φ) :
    haveI := continuousConstSMul_thomPairFst (E := E) hι
    TopPair.IsSemiInvariantCocycle (Units.map (Int.castRingHom k : ℤ →* k)) φ := by
  have := continuousConstSMul_thomPairFst (E := E) hι
  refine (TopPair.isSemiInvariantCocycle_iff _ _).2 fun g ↦ ?_
  rcases Int.units_eq_one_or g with rfl | rfl
  · have h : TopCat.ofHom ⟨((1 : ℤˣ) • · :
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst →
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst),
        continuous_const_smul _⟩ = 𝟙 _ :=
      ConcreteCategory.hom_ext _ _ fun x ↦ one_smul ℤˣ x
    rw [h, CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.id_comp, map_one,
      Units.val_one, one_smul]
    -- the two sides differ in the instances of the modules of morphisms, which agree only after
    -- unfolding, beyond the reducible unfolding with which `rw` tries `rfl`
    rfl
  · have h : TopCat.ofHom ⟨((-1 : ℤˣ) • · :
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst →
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst),
        continuous_const_smul _⟩ = TopPair.Hom.fst (deckThomPairMap F E ι) :=
      ConcreteCategory.hom_ext _ _ neg_one_smul_eq_deckThomPairMap_fst
    -- the lifted deck involution passes from the ambient chains to the relative chains
    have hπ : ((singularChains k).map (TopPair.Hom.fst (deckThomPairMap F E ι))).f n ≫
        (TopPair.singularChainComplexπ
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of k k)).f n =
        (TopPair.singularChainComplexπ
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of k k)).f n ≫
          (TopPair.singularChainComplexMap (deckThomPairMap F E ι) (ModuleCat.of k k)).f n :=
      (HomologicalComplex.comp_f _ _ n).symm.trans (congrArg (fun c ↦ HomologicalComplex.Hom.f c n)
        (TopPair.singularChainComplexπ_pair_naturality (deckThomPairMap F E ι)
          (ModuleCat.of k k)))
    -- `hφ`, with the pulled-back cochain written as a composite: the cochain map `Hom(-, k)` acts
    -- by precomposition by definition (`TauCeti.ChainComplex.linearYonedaFunctor_map_f_hom_apply`)
    have hφ' : (TopPair.singularChainComplexMap (deckThomPairMap F E ι) (ModuleCat.of k k)).f n ≫
        HomologicalComplex.iCycles (TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of k k) k (ModuleCat.of k k)) n φ =
        -HomologicalComplex.iCycles (TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of k k) k (ModuleCat.of k k)) n φ := hφ
    have hχ : ((Units.map (Int.castRingHom k : ℤ →* k) (-1) : kˣ) : k) = -1 := by simp
    rw [h, hχ, neg_one_smul]
    -- the composites live in modules of morphisms whose instances agree with those of the goal
    -- only after unfolding, so the rewriting steps are assembled in term mode
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hπ).trans
      (Category.assoc _ _ _))).trans ((congrArg (_ ≫ ·) hφ').trans (Preadditive.comp_neg _ _))

-- The cochains of the Thom pair of `E'` in the statements below and in `thomPairSignCochainMap`
-- read the zeros of the fibres through different instances, which agree only after unfolding, so
-- the lifted cocycle is given its type here by ascription and the identities relating the two
-- readings are assembled in term mode.

/-- The lift of an orientation-twisted cocycle of `(E, E₀)` to the Thom pair of the orientation
cover is semi-invariant for the sign character of `ℤˣ`. -/
theorem isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap {n : ℕ}
    (ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles n) :
    haveI :=
      (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
    TopPair.IsSemiInvariantCocycle
      (P := thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (Units.map (Int.castRingHom k : ℤ →* k))
      (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι k k (ModuleCat.of k k)) n ψ :
        (TopPair.singularCochainComplex
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n) := by
  refine isSemiInvariantCocycle_of_anti_invariant hι k ?_
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (thomPairSignCochainMap F E hι k k (ModuleCat.of k k)) n) ψ
  have hδ := congr(($(thomPairSignCochainMap_comp_singularCochainComplexMap_deckThomPairMap
    (F := F) (E := E) hι k k (ModuleCat.of k k))).f n
      (HomologicalComplex.iCycles ((thomPair F E).twistedCochainComplex
        (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)) n ψ))
  simp only [ConcreteCategory.comp_apply, HomologicalComplex.comp_f,
    HomologicalComplex.neg_f_apply] at hi hδ
  exact (congrArg ((TopPair.singularCochainComplexMap (deckThomPairMap F E ι)).f n) hi).trans
    (hδ.trans (congrArg Neg.neg hi.symm))

omit [FiniteDimensional ℝ F] in
/-- If the class of the lift of an orientation-twisted cocycle of `(E, E₀)` to the Thom pair of the
orientation cover is a Thom class, then so is the class of the lifted cocycle, read in the
cochains of the Thom pair of the cover. -/
private theorem isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap
    {ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles (finrank ℝ F)}
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F)).hom
        (HomologicalComplex.homologyπ ((thomPair F E).twistedCochainComplex
          (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)) (finrank ℝ F) ψ))) :
    IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (HomologicalComplex.homologyπ (TopPair.singularCochainComplex
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (ModuleCat.of k k) k (ModuleCat.of k k)) (finrank ℝ F)
        (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι k k (ModuleCat.of k k))
          (finrank ℝ F) ψ)) := by
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
    (thomPairSignCochainMap F E hι k k (ModuleCat.of k k)) (finrank ℝ F)) ψ
  simp only [ConcreteCategory.comp_apply] at hπ
  rw [thomPairSignCohomologyMap_def] at hu
  exact (congrArg (IsThomClass F _) hπ).mp hu

/-- **The Thom isomorphism with orientation-twisted coefficients over every ring.** Let `E → B` be
a real vector bundle of rank `r`, `o(E)` its orientation local system, and `k` any commutative
ring, for instance `ℤ`. Let `ψ` be a relative cocycle of the Thom pair `(E, E₀)` of degree `r` with
coefficients in `π^*o(E)` whose lift to the pull-back `E'` of `E` to the orientation double cover
(`TauCeti.VectorBundleOrientationCover.thomPairSignCochainMap`) represents a Thom class of `E'`.
Then `Hₘ(E, E₀; k) ≅ Hₚ(B; o(E) ⊗ k)` for `m = p + r`, over any base and with no orientation of
`E`.

The isomorphism is the equivariant cap product with the lift of `ψ`
(`TopPair.singularChainsRepCap`), a quasi-isomorphism of complexes of projective representations
of `ℤˣ` from the relative chains of `(E', E'₀)` to the chains of the cover twisted by the sign
character and shifted up by `r`, after taking coinvariants, which turns the first complex into the
relative chains of `(E, E₀)` and the second into the shifted chains of `B` twisted by `o(E)`. -/
def thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass
    (ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles (finrank ℝ F))
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F)).hom
        (HomologicalComplex.homologyπ ((thomPair F E).twistedCochainComplex
          (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)) (finrank ℝ F) ψ)))
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    (thomPair F E).singularHomology (ModuleCat.of k k) m ≅
      LocalCoefficientSystem.twistedHomology (signLocalSystem F E k hι) p :=
  haveI := continuousConstSMul_thomPairFst (E := E) hι
  haveI : ContinuousConstSMul ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
    (isQuotientCoveringMap_pullbackThomPairMap_snd (F := F) (E := E) hι).toContinuousConstSMul
  haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
  haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).isCancelSMul
  have hP : ∀ (u : ℤˣ)
      (x : (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd),
      (thomPair F _).map (u • x) = u • (thomPair F _).map x :=
    thomPair_map_smul
  have hφ := isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι k ψ
  -- the equivariant cap product is a quasi-isomorphism, as the cap product with a Thom cocycle is
  haveI := (TopPair.quasiIso_singularChainsRepCap_iff
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
    (thomPairProj_smul (F := F) (E := E)) _ hφ hP).2
      (quasiIso_pushforwardCapChainMap_thomPair _
        (isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap hι k hu))
  ((thomPair F E).twistedHomologyConstantIso (ModuleCat.of k k) m).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ m).mapIso
      ((thomPair F E).twistedChainComplexCoefficientIso
        (IsQuotientCoveringMap.associatedLocalSystemTrivialIso
          (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι) k k).symm) ≪≫
    TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) k
      (isQuotientCoveringMap_pullbackThomPairMap_fst hι)
      (isQuotientCoveringMap_pullbackThomPairMap_snd hι) hP (Rep.trivial k ℤˣ k)
      ((thomPair F _).singularChainsRepCap (thomPairProj_smul (F := F) (E := E)) _ hφ hP) m ≪≫
    (HomologicalComplex.homologyFunctor _ _ m).mapIso
      (coinvariantsTensorSingularChainsRepExtendIsoTwisted F E ι hι k (finrank ℝ F)) ≪≫
    HomologicalComplex.extendHomologyIso _ _ (h ▸ ComplexShape.embeddingDownNatAdd_f _ p)

/-- **The twisted Thom isomorphism over every ring, step by step.** The isomorphism
`thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass` reads a class of `Hₘ(E, E₀; k)` in the
relative chains of `(E, E₀)` with constant coefficients, lifts it to the coinvariants of the
relative chains of `(E', E'₀)`, caps it there with the lift of `ψ` (`TopPair.singularChainsRepCap`),
and reads the result in the shifted chains of `B` twisted by `o(E)`
(`coinvariantsTensorSingularChainsRepExtendIsoTwisted`). -/
theorem thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass_hom
    (ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles (finrank ℝ F))
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F)).hom
        (HomologicalComplex.homologyπ ((thomPair F E).twistedCochainComplex
          (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)) (finrank ℝ F) ψ)))
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    haveI :=
      (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
    haveI :=
      (isQuotientCoveringMap_pullbackThomPairMap_snd (F := F) (E := E) hι).toContinuousConstSMul
    haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
    (thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass hι k ψ hu h).hom =
      ((thomPair F E).twistedHomologyConstantIso (ModuleCat.of k k) m).inv ≫
        HomologicalComplex.homologyMap ((thomPair F E).twistedChainComplexCoefficientIso
          (IsQuotientCoveringMap.associatedLocalSystemTrivialIso
            (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι) k k).symm).hom m ≫
        HomologicalComplex.homologyMap (TopPair.coinvariantsTensorSingularChainsRepIsoTwisted
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) k
          (isQuotientCoveringMap_pullbackThomPairMap_fst hι)
          (isQuotientCoveringMap_pullbackThomPairMap_snd hι) thomPair_map_smul
          (Rep.trivial k ℤˣ k)).inv m ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor k ℤˣ).obj (Rep.trivial k ℤˣ k)).mapHomologicalComplex _).map
            ((thomPair F _).singularChainsRepCap (thomPairProj_smul (F := F) (E := E)) _
              (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι k ψ)
              thomPair_map_smul)) m ≫
        HomologicalComplex.homologyMap
          (coinvariantsTensorSingularChainsRepExtendIsoTwisted F E ι hι k (finrank ℝ F)).hom m ≫
        (HomologicalComplex.extendHomologyIso _ _
          (h ▸ ComplexShape.embeddingDownNatAdd_f _ p)).hom := by
  simp only [thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj_hom, Category.assoc]

end TauCeti.VectorBundleOrientationCover
