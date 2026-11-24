/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

`H_{q + r}(E, E₀; k) ≅ H_q(B; o(E) ⊗ k)`

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

(`TauCeti.quasiIso_singularChainsRepCap_thomPair`). Taking coinvariants turns it into the Thom
isomorphism of the quotient (`TauCeti.quotientSingularHomologyThomIso`),
`H_{q + r}(E, E₀; k) ≅ H_q(B; L_{k_sign})`, where `L_{k_sign}` is the local system associated to the
sign representation; that local system is `o(E)`
(`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`), once the representation of
the sign character is read as the action of `ℤˣ` on `k`
(`Representation.ofLinearCharacter_unitsMap_intCastRingHom`).

Exact anti-invariance of the cocycle is what the equivariant cap product needs; a representative
of a cohomology class which `δ^*` negates need not be negated by `δ^*` itself when `2` is not
invertible in `k`. This is why the cocycle is lifted from orientation-twisted cochains of `E`.

## Main definitions and results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass`: the isomorphism
  `H_{q + r}(E, E₀; k) ≅ H_q(B; o(E) ⊗ k)` given by an orientation-twisted cocycle of `(E, E₀)`
  whose lift to the orientation cover represents a Thom class, with
  `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass_def` describing it as the Thom
  isomorphism of the quotient followed by the identification of the sign local system with `o(E)`.
* `isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`: the lift of an orientation-twisted
  cocycle of `(E, E₀)` is semi-invariant for the sign character.
* `isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap`: if the lifted class is a Thom class,
  so is the class of the lifted cocycle, read in the cochains of the Thom pair of the cover.

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

section Lift

-- The zeros of the fibres of the pull-back are read as in `TauCeti.pullbackThomPairMap`, so that
-- the Thom pair of the pull-back here is the source of that map and carries the actions of `ℤˣ`.
attribute [local instance] pullbackFiberZero thomPairFstMulAction thomPairSndMulAction

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
theorem isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap
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

end Lift

-- `TauCeti.quotientSingularHomologyThomIso` reads the zeros of the fibres of the pull-back through
-- their additive structure, unlike `thomPairFstMulAction` and the quotient covering maps, which use
-- `TauCeti.pullbackFiberZero`. The two readings agree only after unfolding, so the actions of `ℤˣ`
-- are supplied below for both readings of the Thom pair of the pull-back.

/-- **The Thom isomorphism with orientation-twisted coefficients over every ring.** Let `E → B` be
a real vector bundle of rank `r`, `o(E)` its orientation local system, and `k` any commutative
ring, for instance `ℤ`. Let `ψ` be a relative cocycle of the Thom pair `(E, E₀)` of degree `r` with
coefficients in `π^*o(E)` whose lift to the pull-back `E'` of `E` to the orientation double cover
(`TauCeti.VectorBundleOrientationCover.thomPairSignCochainMap`) represents a Thom class of `E'`.
Then `H_{q + r}(E, E₀; k) ≅ H_q(B; o(E) ⊗ k)`, over any base and with no orientation of `E`.

It is the Thom isomorphism of the quotient `(E, E₀)` of `(E', E'₀)` by `ℤˣ`
(`TauCeti.quotientSingularHomologyThomIso`), given by the equivariant cap product with the lift of
`ψ`, which is semi-invariant for the sign character
(`isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`), followed by the identification of the
local system of the sign character with `o(E)` (`associatedLocalSystemSignIso`). -/
def thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass
    (ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles (finrank ℝ F))
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F)).hom
        (HomologicalComplex.homologyπ ((thomPair F E).twistedCochainComplex
          (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)) (finrank ℝ F) ψ)))
    (q : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of k k) (q + finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology (signLocalSystem F E k hι) q :=
  letI := thomPairFstMulAction (F := F) (E := E) (ι := ι)
  letI := thomPairSndMulAction (F := F) (E := E) (ι := ι)
  letI : MulAction ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
    thomPairFstMulAction
  letI : MulAction ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
    thomPairSndMulAction
  haveI : ContinuousConstSMul ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
    (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
  haveI : ContinuousConstSMul ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
    (isQuotientCoveringMap_pullbackThomPairMap_snd (F := F) (E := E) hι).toContinuousConstSMul
  haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
  quotientSingularHomologyThomIso (F := F)
      (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (isQuotientCoveringMap_pullbackThomPairMap_fst hι)
      (isQuotientCoveringMap_pullbackThomPairMap_snd hι) (isQuotientCoveringMap_proj hι)
      thomPair_map_smul (thomPairProj_smul (F := F) (E := E)) _
      (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι k ψ)
      (isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap hι k hu) q ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      (LocalCoefficientSystem.twistedChainComplexCoefficientIso
        (((isQuotientCoveringMap_proj hι).associatedLocalSystemFunctor k).mapIso
            (eqToIso
              (congrArg Rep.of Representation.ofLinearCharacter_unitsMap_intCastRingHom)) ≪≫
          associatedLocalSystemSignIso hι k))

/-- The isomorphism `thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass` is the Thom
isomorphism `TauCeti.quotientSingularHomologyThomIso` of the quotient of the Thom pair of the
orientation cover by `ℤˣ`, for the lift of `ψ`, followed by the identification of the local system
of the sign character with the orientation local system. -/
theorem thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass_def
    (ψ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E k hι) k
      (ModuleCat.of k k)).cycles (finrank ℝ F))
    (hu : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      ((thomPairSignCohomologyMap F E hι k k (ModuleCat.of k k) (finrank ℝ F)).hom
        (HomologicalComplex.homologyπ ((thomPair F E).twistedCochainComplex
          (thomPairSignLocalSystem F E k hι) k (ModuleCat.of k k)) (finrank ℝ F) ψ)))
    (q : ℕ) :
    letI := thomPairFstMulAction (F := F) (E := E) (ι := ι)
    letI := thomPairSndMulAction (F := F) (E := E) (ι := ι)
    letI : MulAction ℤˣ
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
      thomPairFstMulAction
    letI : MulAction ℤˣ
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
      thomPairSndMulAction
    haveI : ContinuousConstSMul ℤˣ
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
      (isQuotientCoveringMap_pullbackThomPairMap_fst (F := F) (E := E) hι).toContinuousConstSMul
    haveI : ContinuousConstSMul ℤˣ
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
      (isQuotientCoveringMap_pullbackThomPairMap_snd (F := F) (E := E) hι).toContinuousConstSMul
    haveI := (isQuotientCoveringMap_proj (F := F) (E := E) hι).toContinuousConstSMul
    thomPairSingularHomologyIsoTwistedHomologyOfIsThomClass hι k ψ hu q =
      quotientSingularHomologyThomIso (F := F)
          (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
          (isQuotientCoveringMap_pullbackThomPairMap_fst hι)
          (isQuotientCoveringMap_pullbackThomPairMap_snd hι) (isQuotientCoveringMap_proj hι)
          thomPair_map_smul (thomPairProj_smul (F := F) (E := E)) _
          (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι k ψ)
          (isThomClass_homologyπ_cyclesMap_thomPairSignCochainMap hι k hu) q ≪≫
        (HomologicalComplex.homologyFunctor _ _ q).mapIso
          (LocalCoefficientSystem.twistedChainComplexCoefficientIso
            (((isQuotientCoveringMap_proj hι).associatedLocalSystemFunctor k).mapIso
                (eqToIso
                  (congrArg Rep.of Representation.ofLinearCharacter_unitsMap_intCastRingHom)) ≪≫
              associatedLocalSystemSignIso hι k)) :=
  (rfl)

end TauCeti.VectorBundleOrientationCover
