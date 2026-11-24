/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Thom.CoverChainMap
public import TauCeti.Topology.VectorBundle.Thom.EquivariantCap

/-!
# Lifted orientation-twisted cocycles and the equivariant Thom quasi-isomorphism

Let `E → B` be a real vector bundle of rank `r`, `B'` its orientation double cover, whose points
are the pairs `p = (b, o)` of a point `b` of `B` and an orientation `o` of `E_b`, and `E'` the
pull-back of `E` to `B'`. The units `ℤˣ` act on `B'`, `-1` reversing the orientation, and on the
Thom pair `(E', E'₀)`, `-1` acting by the lift `δ` of the deck involution
(`neg_one_smul_eq_deckThomPairMap_fst`). Let `R` be any commutative ring, `ℤ` included. Twisted
cochains of `(E, E₀)` with coefficients in the orientation system `π^*o(E)` lift to cochains of
`(E', E'₀)` (`thomPairSignCochainMap`). This file shows that the lifted cocycles are the input of
the equivariant form of the homology Thom isomorphism of `E'`
(`TauCeti.quasiIso_singularChainsRepCap_thomPair`):

* **Lifted cocycles are semi-invariant.** The lift of any twisted cocycle `φ` is negated by `δ` at
  the level of cochains, so `u ∈ ℤˣ` multiplies it by `u`
  (`isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`). This holds on the nose, not only in
  cohomology, which is what the equivariant cap product needs.
* **The equivariant Thom quasi-isomorphism.** Consequently, for a twisted cocycle `φ` whose lifted
  class is a Thom class of `E'`, the equivariant cap product with the lift of `φ`,
  `C(E', E'₀; R) ⟶ (R_sign ⊗ C(B'; R))[r]`, is a quasi-isomorphism of complexes of representations
  of `ℤˣ` (`quasiIso_singularChainsRepCap_cyclesMap_thomPairSignCochainMap`).

The action of `ℤˣ` on `(E', E'₀)` is free, and `(E, E₀)` is its quotient
(`isQuotientCoveringMap_pullbackThomPairMap_fst`), so the relative chains of `(E', E'₀)` and the
chains of `B'` twisted by the sign representation are complexes of projective representations.
Taking coinvariants of this quasi-isomorphism therefore identifies the relative homology of
`(E, E₀)` with the homology of `B` with coefficients in the local system of the sign
representation (`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`), which is `o(E)`
(`associatedLocalSystemSignIso`). That identification is not carried out here. Over a ring in
which `2` is invertible the twisted Thom isomorphism is proved by a transfer instead
(`thomPairSingularHomologyEquivTwistedHomology`); the argument here needs no such hypothesis.

The lifted cocycles are those of `TauCeti.Topology.VectorBundle.Thom.CoverChainMap`, whose index
type of orientations lies in `Type`, so the base, the fibres and the ring live in `Type` here.

## Main results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap`: lifted cocycles are semi-invariant
  for the sign character of `ℤˣ`.
* `quasiIso_singularChainsRepCap_cyclesMap_thomPairSignCochainMap`: the equivariant cap product
  with the lift of a twisted cocycle whose lifted class is a Thom class is a quasi-isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (local
  coefficients and the orientation double cover).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) (R : Type) [CommRing R]

/-- The lift of a cocycle `φ` of `(E, E₀)` with coefficients in the orientation system is `φ`
precomposed with the chain map to orientation-twisted chains. -/
theorem iCycles_cyclesMap_thomPairSignCochainMap {n : ℕ}
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R)).cycles n) :
    (TopPair.singularCochainComplex
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
        (ModuleCat.of R R) R (ModuleCat.of R R)).iCycles n
        (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R)) n φ) =
      (thomPairSignChainMap F E hι R).f n ≫
        ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
          (ModuleCat.of R R)).iCycles n φ :=
  (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ _) φ).trans
    (thomPairSignCochainMap_f_apply hι R R (ModuleCat.of R R) _ _)

section SemiInvariant

/-- The action `thomPairFstMulAction` of `ℤˣ` on the total space of the Thom pair of the bundle
pulled back to the orientation cover. -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction

/-- The action `thomPairSndMulAction` of `ℤˣ` on the nonzero vectors of the Thom pair of the bundle
pulled back to the orientation cover. -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
  thomPairSndMulAction

-- The same actions on the Thom pair of `TauCeti.pullbackThomPairMap`, whose fibres read their zeros
-- through `TauCeti.pullbackFiberZero`, as in
-- `TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient`.
attribute [local instance] thomPairFstMulAction thomPairSndMulAction

omit [Fintype ι] in
/-- The unit `-1` acts on the total space of the pulled-back bundle by the lift of the deck
involution. -/
theorem neg_one_smul_eq_deckThomPairMap_fst_apply
    (v : (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst) :
    (-1 : ℤˣ) • v = TopPair.Hom.fst (deckThomPairMap F E ι) v :=
  Pullback.totalSpace_ext ((neg_one_smul_eq_deck v.proj).trans (deckThomPairMap_fst_proj v).symm)
    ((lift_smul _ v).trans (lift_deckThomPairMap_fst v).symm)

/-- The continuity `thomPairFstMulAction_continuousConstSMul` of the action of `ℤˣ` on the total
space of the Thom pair of the bundle pulled back to the orientation cover. -/
local instance : ContinuousConstSMul ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction_continuousConstSMul

/-- The continuity `thomPairSndMulAction_continuousConstSMul` of the action of `ℤˣ` on the nonzero
vectors of the Thom pair of the bundle pulled back to the orientation cover. -/
local instance : ContinuousConstSMul ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
  thomPairSndMulAction_continuousConstSMul

omit [Fintype ι] in
/-- The unit `-1` acts on the total space of the pulled-back bundle by the lift of the deck
involution, as a morphism of topological spaces. -/
theorem neg_one_smul_eq_deckThomPairMap_fst :
    TopCat.ofHom ⟨((-1 : ℤˣ) • · : (thomPair F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst → _),
      continuous_const_smul _⟩ =
      TopPair.Hom.fst (deckThomPairMap F E ι) :=
  TopCat.ext neg_one_smul_eq_deckThomPairMap_fst_apply

/-- **Lifted cocycles are semi-invariant for the sign character.** A relative cocycle `φ` of
`(E, E₀)` with coefficients in the orientation system lifts to a cocycle of the Thom pair
`(E', E'₀)` of the orientation cover (`thomPairSignCochainMap`) on which the unit `u` of `ℤˣ`
acts by multiplication by `u`: the lifted deck involution negates it at the level of cochains. -/
theorem isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap {n : ℕ}
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R)).cycles n) :
    TopPair.IsSemiInvariantCocycle (P := thomPair F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (Units.map (Int.castRingHom R : ℤ →* R))
      (HomologicalComplex.cyclesMap (thomPairSignCochainMap F E hι R R (ModuleCat.of R R)) n
        φ) := by
  refine (TopPair.isSemiInvariantCocycle_iff _ _).2 fun g ↦ ?_
  rw [iCycles_cyclesMap_thomPairSignCochainMap]
  rcases Int.units_eq_one_or g with rfl | rfl
  · have h1 : TopCat.ofHom ⟨((1 : ℤˣ) • · : (thomPair F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst → _),
        continuous_const_smul _⟩ = 𝟙 _ := TopCat.ext fun v ↦ one_smul ℤˣ v
    rw [h1, CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.id_comp, map_one,
      Units.val_one, one_smul]
    -- The two sides differ only in the instance composing the quotient onto the relative chains:
    -- the category of chain complexes of the singular simplicial set or of `singularChains R`.
    rfl
  · -- `-1` acts by the lifted deck involution `δ`, which commutes with the quotient onto the
    -- relative chains and negates the chain map `Λ` to twisted chains: `δ_* ≫ Λ = -Λ`.
    have hd := HomologicalComplex.congr_hom
      (TopPair.singularChainComplexπ_pair_naturality (deckThomPairMap F E ι) (ModuleCat.of R R)) n
    have hΛ := HomologicalComplex.congr_hom
      (singularChainComplexMap_deckThomPairMap_comp_thomPairSignChainMap (F := F) (E := E) hι R) n
    rw [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply] at hΛ
    -- `erw`: the composite in `hd` is formed in the category of chain complexes of the singular
    -- simplicial set, as above.
    erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hd
    rw [neg_one_smul_eq_deckThomPairMap_fst, show ((Units.map (Int.castRingHom R : ℤ →* R) (-1) :
      Rˣ) : R) = -1 by simp, neg_one_smul]
    erw [reassoc_of% hd, reassoc_of% hΛ, Preadditive.neg_comp, Preadditive.comp_neg]
    -- As in the case `1`, the two sides differ only in the instances of the composites.
    rfl

/-- **The equivariant Thom quasi-isomorphism of the orientation cover.** Let `φ` be a relative
cocycle of `(E, E₀)` of degree `r` with coefficients in the orientation system, whose lifted class
`thomPairSignCohomologyMap [φ]` is a Thom class of the bundle `E'` pulled back to the orientation
cover. Its lift to `(E', E'₀)` is a semi-invariant cocycle, so the equivariant cap product with it,
`C(E', E'₀; R) ⟶ (R_sign ⊗ C(B'; R))[r]`, is a quasi-isomorphism of complexes of representations
of `ℤˣ`. -/
theorem quasiIso_singularChainsRepCap_cyclesMap_thomPairSignCochainMap
    (φ : ((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
      (ModuleCat.of R R)).cycles (finrank ℝ F))
    (hφ : IsThomClass F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
      (thomPairSignCohomologyMap F E hι R R (ModuleCat.of R R) (finrank ℝ F)
        (((thomPair F E).twistedCochainComplex (thomPairSignLocalSystem F E R hι) R
          (ModuleCat.of R R)).homologyπ (finrank ℝ F) φ))) :
    QuasiIso (TopPair.singularChainsRepCap
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
      (G := ℤˣ) (p₀ := thomPairProj F _) (fun u v ↦
        (thomPairProj_apply F _ (u • v)).trans <| (proj_smul_totalSpace u v).trans <|
          congrArg (u • ·) (thomPairProj_apply F _ v).symm)
      (Units.map (Int.castRingHom R : ℤ →* R))
      (isSemiInvariantCocycle_cyclesMap_thomPairSignCochainMap hι R φ) (fun _ _ ↦ rfl)) := by
  refine quasiIso_singularChainsRepCap_thomPair _ _ _ _ ?_
  -- The class of the lifted cocycle is the lift of the class of `φ`.
  rwa [← ConcreteCategory.comp_apply, thomPairSignCohomologyMap_def,
    HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply] at hφ

end SemiInvariant

end TauCeti.VectorBundleOrientationCover
