/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Invariants
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Kronecker
public import TauCeti.AlgebraicTopology.Singular.Invariants
public import TauCeti.AlgebraicTopology.Singular.Transfer.Sign
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.Thom.OrientationCover

/-!
# The Thom isomorphism with coefficients in the orientation local system

Let `E → B` be a real vector bundle of rank `r`, with Thom pair `(E, E₀)`, and let `o(E)` be its
orientation local system (`TauCeti.VectorBundleOrientationCover.signLocalSystem`). For a
commutative ring `K` in which `2` is invertible, for instance `ℚ` or any field of characteristic
other than `2`, this file proves the Thom isomorphism with orientation-twisted coefficients

`Hₚ₊ᵣ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)`

(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`), with no
orientation of `E` and over any base. For a non-orientable bundle the twist cannot be dropped: for
the Möbius line over the circle, `H₁(E, E₀; ℚ) = 0` while `H₀(S¹; ℚ) = ℚ`. When `2 = 0` in `K`,
as for `ZMod 2`, the twist disappears and the untwisted Thom isomorphism holds instead
(`TauCeti.exists_isThomClass_of_two_eq_zero` with `TauCeti.homologyThomIso`).

The proof passes through the orientation double cover `B'` of `E`, with its deck involution `σ`
reversing orientations, and the pull-back `E'` of `E` to `B'`, oriented by the tautological
orientation. It composes three isomorphisms.

* The relative transfer. The Thom pair `(E', E'₀)` is a double cover of `(E, E₀)`, the quotient by
  the action of `ℤˣ` whose element `-1` acts by the lift `δ` of `σ`
  (`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_lift`). Its relative transfer
  `t : Hₘ(E, E₀; K) ⟶ Hₘ(E', E'₀; K)` (`TauCeti.VectorBundleOrientationCover.thomPairTransfer`)
  sends a relative simplex to the sum of its two lifts; writing `q` for the map of Thom pairs
  induced by the covering, it satisfies `q_* ∘ t = 2`, `t ∘ q_* = 1 + δ_*` and `δ_* ∘ t = t`. With
  `2` invertible, the transfer identifies `Hₘ(E, E₀; K)` with the classes of `Hₘ(E', E'₀; K)` fixed
  by `δ_*`
  (`IsQuotientCoveringMap.isLimitHomologyMapConePairTransferCone`); this is
  `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivDeckInvariants`.
* The Thom isomorphism of the oriented bundle `E'` anticommutes with the involutions, so it carries
  the `δ_*`-fixed classes onto the classes of `Hₚ(B'; K)` negated by `σ_*`
  (`TauCeti.VectorBundleOrientationCover.homologyThomMapDeckEquiv`).
* With `2` invertible, the classes of `Hₚ(B'; K)` negated by `σ_*` are the homology of `B` with
  coefficients in the sign local system of `σ` (`IsCoveringMap.signHomologyLinearEquiv`), which is
  `o(E)` by definition.

Dually, for an injective `K`-module `N`, for instance any vector space over a field of
characteristic other than `2`, the universal coefficient theorem identifies both cohomologies with
the duals `Hom(-, N)` of the homologies above, so the twisted Thom isomorphism transposes to
cohomology: `Hᵖ⁺ʳ(E, E₀; K, N) ≃ Hᵖ(B; o(E) ⊗ K, N)`
(`TauCeti.VectorBundleOrientationCover.thomPairSingularCohomologyEquivTwistedCohomology`).

## Main definitions

* `TauCeti.VectorBundleOrientationCover.thomPairTransfer`: the relative transfer of the double cover
  `(E', E'₀) → (E, E₀)`, with the transfer relations
  `thomPairTransfer_comp_singularHomologyMap_pullbackThomPairMap` (`q_* ∘ t = 2`),
  `singularHomologyMap_pullbackThomPairMap_comp_thomPairTransfer` (`t ∘ q_* = 1 + δ_*`) and
  `thomPairTransfer_comp_singularHomologyMap_deckThomPairMap` (`δ_* ∘ t = t`); with `2` invertible
  it is injective (`injective_thomPairTransfer`) with range the `δ_*`-fixed classes
  (`range_thomPairTransfer`).
* `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivDeckInvariants`: the transfer
  `Hₘ(E, E₀; K) ≃ {x ∈ Hₘ(E', E'₀; K) | δ_* x = x}`, for a ring `K` in which `2` is invertible.
* `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`: the twisted
  Thom isomorphism `Hₚ₊ᵣ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)` for a commutative ring `K` in which `2` is
  invertible.
* `TauCeti.VectorBundleOrientationCover.thomPairSingularCohomologyEquivTwistedCohomology`: its
  transpose `Hᵖ⁺ʳ(E, E₀; K, N) ≃ Hᵖ(B; o(E) ⊗ K, N)` for an injective `K`-module `N`, characterized
  by `twistedKronecker_thomPairSingularCohomologyEquivTwistedCohomology`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover and twisted
  coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.G (the transfer,
  Proposition 3G.1), Section 3.H (local coefficients and the orientation double cover) and
  Section 4.D (the Thom isomorphism).
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Module

universe w

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type}

attribute [local instance] pullbackMulAction

variable (F E ι) in
/-- The map from the total space of the pull-back of `E` to its orientation cover to the total
space of `E`, as a morphism of topological spaces. -/
abbrev liftHom :
    TopCat.of (TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) ⟶
      TopCat.of (TotalSpace F E) :=
  TopCat.ofHom ⟨Pullback.lift _, Pullback.continuous_lift F E _⟩

variable (F E ι) in
/-- The preimage of the nonzero vectors of `E` in the pull-back is the set of its nonzero vectors,
so the pair it forms is the Thom pair of the pull-back. -/
def preimageThomPairIso :
    TopPair.ofSubset (liftHom F E ι ⁻¹' zeroSectionCompl F E) ≅
      thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun v ↦ by
    rw [Homeomorph.refl_apply]
    exact Set.ext_iff.1 (preimage_pullbackLift_zeroSectionCompl (F := F) (E := E) _) v

/-- The isomorphism `preimageThomPairIso` is the identity on total spaces. -/
-- Not `@[simp]`: simp rewrites the coercion of the continuous map on the left-hand side, so the
-- statement is not in simp normal form.
theorem preimageThomPairIso_hom_fst_apply
    (v : (TopPair.ofSubset (liftHom F E ι ⁻¹' zeroSectionCompl F E)).fst) :
    TopPair.Hom.fst (preimageThomPairIso F E ι).hom v = v := by
  simp only [preimageThomPairIso, TopPair.ofSubsetIso_hom, Homeomorph.coe_refl, TopCat.ofHom_id,
    TopPair.ofSubsetMap_fst_apply, TopCat.hom_id, ContinuousMap.coe_id]
  exact id_eq v

/-- The underlying map of the inverse of `preimageThomPairIso` is the identity. -/
private theorem preimageThomPairIso_inv_fst :
    TopPair.Hom.fst (preimageThomPairIso F E ι).inv = 𝟙 _ :=
  (congrArg TopPair.Hom.fst (TopPair.ofSubsetIso_inv _ _)).trans (TopPair.ofSubsetMap_fst _ _)

/-- The map of pairs induced by the covering is `TauCeti.pullbackThomPairMap`, read through
`preimageThomPairIso`. -/
private theorem pullbackThomPairMap_eq_preimageThomPairIso_inv_comp :
    pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)) =
      (preimageThomPairIso F E ι).inv ≫
        TopPair.ofSubsetMap (liftHom F E ι) (Set.mapsTo_preimage _ (zeroSectionCompl F E)) := by
  -- Pointwise, both sides are `Pullback.lift`. The steps are terms: the two sides read the zero of
  -- the fibres of the pull-back through two instances that agree only up to unfolding.
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  exact (pullbackThomPairMap_fst_apply F E _ v).trans
    ((TopPair.ofSubsetMap_fst_apply (liftHom F E ι)
      (Set.mapsTo_preimage _ (zeroSectionCompl F E)) v).symm.trans
      (congrArg (fun φ ↦ TopPair.Hom.fst (TopPair.ofSubsetMap (liftHom F E ι)
        (Set.mapsTo_preimage _ (zeroSectionCompl F E))) (φ v)) preimageThomPairIso_inv_fst.symm))

variable [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)

variable (F E) in
include hι in
/-- The pull-back of `E` to its orientation cover is the quotient of its total space by the action
of `ℤˣ` (`isQuotientCoveringMap_lift`), read on `liftHom`. -/
theorem isQuotientCoveringMap_liftHom :
    IsQuotientCoveringMap (liftHom F E ι) ℤˣ :=
  isQuotientCoveringMap_lift hι

/-- The unit `-1` acts on the pair `(E', p⁻¹ E₀)` by the lift of the deck involution to the Thom
pair `(E', E'₀)`. -/
private theorem ofSubsetMap_neg_one_comp_preimageThomPairIso_hom :
    TopPair.ofSubsetMap (TopCat.ofHom ⟨((-1 : ℤˣ) • · :
        TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) → _),
          (isQuotientCoveringMap_liftHom F E hι).continuous_const_smul (-1)⟩)
        ((isQuotientCoveringMap_liftHom F E hι).mapsTo_smul_preimage (zeroSectionCompl F E) (-1)) ≫
      (preimageThomPairIso F E ι).hom =
    (preimageThomPairIso F E ι).hom ≫ deckThomPairMap F E ι := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  simp only [TopPair.Hom.fst_comp, CategoryTheory.comp_apply]
  rw [preimageThomPairIso_hom_fst_apply, preimageThomPairIso_hom_fst_apply,
    TopPair.ofSubsetMap_fst_apply]
  refine Eq.trans ?_ (deckThomPairMap_fst_apply (F := F) (E := E) (ι := ι) v).symm
  -- The left side `TopCat.ofHom ⟨((-1 : ℤˣ) • ·), _⟩ v` is `(-1 : ℤˣ) • v` by definition.
  exact Pullback.totalSpace_ext ((neg_one_smul_eq_deck v.proj).trans (deck_apply _)) rfl

section CommRing

variable {K : Type w} [CommRing K]

variable (E K) in
/-- **The transfer of the orientation double cover on Thom pairs.** The relative transfer
`Hₘ(E, E₀; K) ⟶ Hₘ(E', E'₀; K)` of the double cover of the Thom pair of `E` by the Thom pair of its
pull-back `E'` to the orientation cover: it sends a relative singular simplex to the sum of its two
lifts. -/
def thomPairTransfer (m : ℕ) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ⟶
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).singularHomology
        (ModuleCat.of K K) m :=
  HomologicalComplex.homologyMap
    ((isQuotientCoveringMap_liftHom F E hι).isCoveringMap.singularPairTransfer
      (isQuotientCoveringMap_liftHom F E hι).finite_fiber (zeroSectionCompl F E)
      (ModuleCat.of K K)) m ≫
    TopPair.singularHomologyMap (preimageThomPairIso F E ι).hom (ModuleCat.of K K) m

/-- **The transfer formula on Thom pairs.** The transfer of the orientation double cover followed by
the map of Thom pairs `(E', E'₀) ⟶ (E, E₀)` is multiplication by `2`. -/
theorem thomPairTransfer_comp_singularHomologyMap_pullbackThomPairMap (m : ℕ) :
    thomPairTransfer E hι K m ≫ TopPair.singularHomologyMap
      (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
      (ModuleCat.of K K) m = 2 • 𝟙 _ := by
  have hG := isQuotientCoveringMap_liftHom F E hι
  -- Term-mode steps: the zero of the fibres of the pull-back enters the source of
  -- `pullbackThomPairMap` and the target of the transfer as two instances that agree only up to
  -- unfolding, so `rw` cannot work on this goal.
  calc thomPairTransfer E hι K m ≫ TopPair.singularHomologyMap
        (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
        (ModuleCat.of K K) m
      = HomologicalComplex.homologyMap (hG.isCoveringMap.singularPairTransfer hG.finite_fiber
          (zeroSectionCompl F E) (ModuleCat.of K K)) m ≫ TopPair.singularHomologyMap
          ((preimageThomPairIso F E ι).hom ≫ (preimageThomPairIso F E ι).inv ≫
            TopPair.ofSubsetMap (liftHom F E ι) (Set.mapsTo_preimage _ (zeroSectionCompl F E)))
          (ModuleCat.of K K) m :=
        (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((TopPair.singularHomologyMap_comp _ _ _ _).symm.trans
          (congrArg (TopPair.singularHomologyMap · _ m)
            (congrArg (_ ≫ ·) pullbackThomPairMap_eq_preimageThomPairIso_inv_comp))))
    _ = 2 • 𝟙 _ := by
      rw [Iso.hom_inv_id_assoc]
      exact hG.isCoveringMap.homologyMap_singularPairTransfer_comp_singularHomologyMap
        hG.finite_fiber (zeroSectionCompl F E) (ModuleCat.of K K) m fun b ↦
          (hG.natCard_fiber b).trans (Nat.card_eq_fintype_card.trans Fintype.card_units_int)

/-- **The transfer of a projected class is its symmetrization.** The map of Thom pairs
`(E', E'₀) ⟶ (E, E₀)` followed by the transfer of the orientation double cover is `1 + δ_*`, for
the lift `δ` of the deck involution. -/
theorem singularHomologyMap_pullbackThomPairMap_comp_thomPairTransfer (m : ℕ) :
    TopPair.singularHomologyMap
      (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
      (ModuleCat.of K K) m ≫ thomPairTransfer E hι K m =
      𝟙 _ + TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m := by
  have hG := isQuotientCoveringMap_liftHom F E hι
  set e := preimageThomPairIso F E ι
  have h₁ : TopPair.ofSubsetMap (TopCat.ofHom ⟨((1 : ℤˣ) • · :
      TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) → _),
      hG.continuous_const_smul _⟩) (hG.mapsTo_smul_preimage (zeroSectionCompl F E) 1) = 𝟙 _ :=
    TopPair.hom_ext_of_fst _ (by
      simp only [TopPair.ofSubsetMap_fst, TopPair.Hom.fst_id]
      exact TopCat.ext fun v ↦ Pullback.totalSpace_ext (one_smul ℤˣ v.proj) rfl)
  -- On relative chains of the preimage pair, the projection followed by the transfer is the sum of
  -- the actions of `1` and `-1`.
  have h := hG.singularChainComplexMap_comp_singularPairTransfer (zeroSectionCompl F E)
    (ModuleCat.of K K)
  rw [UnitsInt.univ, Finset.sum_pair (by decide), h₁] at h
  have h' := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ m) h
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_add,
    TopPair.singularChainComplexMap_id, HomologicalComplex.homologyMap_id] at h'
  -- Conjugated by `e`, the action of `-1` is the lift of the deck involution.
  have key : TopPair.singularHomologyMap e.inv (ModuleCat.of K K) m ≫
      (TopPair.singularHomologyMap (TopPair.ofSubsetMap (liftHom F E ι)
        (Set.mapsTo_preimage _ (zeroSectionCompl F E))) (ModuleCat.of K K) m ≫
        HomologicalComplex.homologyMap (hG.isCoveringMap.singularPairTransfer hG.finite_fiber
          (zeroSectionCompl F E) (ModuleCat.of K K)) m) ≫
        TopPair.singularHomologyMap e.hom (ModuleCat.of K K) m =
      𝟙 _ + TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m := by
    rw [h', Preadditive.add_comp, Preadditive.comp_add, Category.id_comp,
      ← TopPair.singularHomologyMap_comp, e.inv_hom_id, TopPair.singularHomologyMap_id,
      ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
      ofSubsetMap_neg_one_comp_preimageThomPairIso_hom hι, e.inv_hom_id_assoc]
  -- Term-mode steps, as in `thomPairTransfer_comp_singularHomologyMap_pullbackThomPairMap`.
  refine Eq.trans ?_ key
  refine (congrArg (· ≫ _) ((congrArg (TopPair.singularHomologyMap · _ m)
    pullbackThomPairMap_eq_preimageThomPairIso_inv_comp).trans
      (TopPair.singularHomologyMap_comp _ _ _ _))).trans ?_
  -- `thomPairTransfer` unfolds to the composite with `preimageThomPairIso`, which is `e`.
  simp only [thomPairTransfer, Category.assoc]
  rfl

/-- **The transfer is invariant under the deck involution.** The transfer of the orientation
double cover followed by the lift `δ` of the deck involution is the transfer. -/
theorem thomPairTransfer_comp_singularHomologyMap_deckThomPairMap (m : ℕ) :
    thomPairTransfer E hι K m ≫ TopPair.singularHomologyMap (deckThomPairMap F E ι)
      (ModuleCat.of K K) m = thomPairTransfer E hι K m := by
  have hG := isQuotientCoveringMap_liftHom F E hι
  rw [thomPairTransfer, Category.assoc, ← TopPair.singularHomologyMap_comp,
    ← ofSubsetMap_neg_one_comp_preimageThomPairIso_hom hι, TopPair.singularHomologyMap_comp,
    ← Category.assoc,
    hG.isCoveringMap.homologyMap_singularPairTransfer_comp_singularHomologyMap_of_comp_eq
      hG.finite_fiber (zeroSectionCompl F E) (ModuleCat.of K K) m (MulAction.bijective _)
      (TopCat.ext fun _ ↦ hG.map_smul _)]

variable [Invertible (2 : K)]

/-- **The transfer is injective when `2` is invertible**, since projecting a transferred class
back multiplies it by `2`. -/
theorem injective_thomPairTransfer (m : ℕ) :
    Function.Injective (thomPairTransfer E hι K m).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- Term-mode steps: the zero of the fibres of the pull-back enters the source of
  -- `pullbackThomPairMap` and the target of the transfer as two instances that agree only up to
  -- unfolding, so `rw` cannot rewrite `hx` inside `h`.
  have h : (TopPair.singularHomologyMap
      (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
      (ModuleCat.of K K) m).hom ((thomPairTransfer E hι K m).hom x) = (2 : ℕ) • x :=
    congr($(thomPairTransfer_comp_singularHomologyMap_pullbackThomPairMap hι m).hom x)
  have h₂ : (2 : ℕ) • x = 0 := h.symm.trans ((congrArg _ hx).trans (map_zero _))
  rw [← one_smul K x, ← invOf_mul_self (2 : K), mul_smul, ofNat_smul_eq_nsmul K 2, h₂, smul_zero]

/-- **The transferred classes are the deck-invariant classes when `2` is invertible.** A class
`c ∈ Hₘ(E', E'₀; K)` is the transfer of a class of `Hₘ(E, E₀; K)` exactly when `δ_* c = c` for the
lift `δ` of the deck involution: such a class is the transfer of half its projection. -/
theorem range_thomPairTransfer (m : ℕ) :
    LinearMap.range (thomPairTransfer E hι K m).hom =
      LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K)
        m).hom - LinearMap.id) := by
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, rfl⟩
    have h : (TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom
        ((thomPairTransfer E hι K m).hom x) = (thomPairTransfer E hι K m).hom x :=
      congr($(thomPairTransfer_comp_singularHomologyMap_deckThomPairMap hι m).hom x)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, h, sub_self]
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
    refine ⟨⅟(2 : K) • (TopPair.singularHomologyMap
      (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
      (ModuleCat.of K K) m).hom y, ?_⟩
    have h : (thomPairTransfer E hι K m).hom ((TopPair.singularHomologyMap
        (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
        (ModuleCat.of K K) m).hom y) =
          y + (TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom y :=
      congr($(singularHomologyMap_pullbackThomPairMap_comp_thomPairTransfer hι m).hom y)
    rw [map_smul, h, hy, ← two_smul K y, smul_smul, invOf_mul_self, one_smul]

variable (K) in
/-- **The transfer lands on the classes fixed by the lifted deck involution.** Let `δ` be the lift
of the deck involution to the Thom pair `(E', E'₀)` and `K` a ring in which `2` is invertible. The
isomorphism of the pair `(E', p⁻¹ E₀)` with `(E', E'₀)` (`preimageThomPairIso`) carries the range of
the relative transfer `Hₘ(E, E₀; K) ⟶ Hₘ(E', p⁻¹ E₀; K)` onto the classes of `Hₘ(E', E'₀; K)` fixed
by `δ_*`. -/
theorem map_range_pairTransfer_eq_ker_sub_id (m : ℕ) :
    (LinearMap.range (((HomologicalComplex.homologyFunctor _ _ m).mapCone
        ((isQuotientCoveringMap_liftHom F E hι).pairTransferCone (zeroSectionCompl F E)
          (ModuleCat.of K K))).π.app (SingleObj.star ℤˣ)).hom).map
        (TopPair.singularHomologyMapIso (ModuleCat.of K K) (preimageThomPairIso F E ι) m).hom.hom =
      LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K)
        m).hom - LinearMap.id) := by
  have : IsIso (Fintype.card ℤˣ • 𝟙 (ModuleCat.of K K)) :=
    Linear.isIso_nsmul_id (by simpa using isUnit_of_invertible (2 : K))
  have hc := (isQuotientCoveringMap_liftHom F E hι).isLimitHomologyMapConePairTransferCone
    (zeroSectionCompl F E) (ModuleCat.of K K) m
  let e := (TopPair.singularHomologyMapIso (ModuleCat.of K K) (preimageThomPairIso F E ι)
    m).toLinearEquiv
  -- The isomorphism `e` of the pair `(E', p⁻¹ E₀)` with the Thom pair `(E', E'₀)` conjugates the
  -- action of `-1` to the lifted deck involution `δ`.
  have hconj (x) := congr($(congrArg (TopPair.singularHomologyMap · (ModuleCat.of K K) m)
    (ofSubsetMap_neg_one_comp_preimageThomPairIso_hom (F := F) (E := E) hι)).hom x)
  simp only [TopPair.singularHomologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hconj
  rw [ModuleCat.range_π_app_star_of_isLimit hc]
  ext y
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hconj x).symm.trans (congrArg _ (ModuleCat.mem_invariants_iff.1 hx (-1)))
  · intro hy
    refine ⟨e.symm y, ModuleCat.mem_invariants_iff.2 fun u ↦ ?_, e.apply_symm_apply y⟩
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [← SingleObj.id_as_one, CategoryTheory.Functor.map_id, ModuleCat.hom_id]
      exact LinearMap.id_apply _
    · refine e.injective ((hconj (e.symm y)).trans ?_)
      exact (congrArg _ (e.apply_symm_apply y)).trans (hy.trans (e.apply_symm_apply y).symm)

variable (F E ι K) in
/-- **The relative transfer of the orientation cover.** Let `E'` be the pull-back of `E` to its
orientation double cover, `δ` the lift to its Thom pair of the deck involution, and `K` a ring in
which `2` is invertible. The transfer of the double cover `(E', E'₀) → (E, E₀)` identifies
`Hₘ(E, E₀; K)` with the classes of `Hₘ(E', E'₀; K)` fixed by `δ_*`. -/
def thomPairSingularHomologyEquivDeckInvariants (m : ℕ) :
    ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K) ≃ₗ[K]
      LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K)
        m).hom - LinearMap.id) :=
  have : IsIso (Fintype.card ℤˣ • 𝟙 (ModuleCat.of K K)) :=
    Linear.isIso_nsmul_id (by simpa using isUnit_of_invertible (2 : K))
  (LinearEquiv.ofInjective _ (ModuleCat.injective_π_app_star_of_isLimit
    ((isQuotientCoveringMap_liftHom F E hι).isLimitHomologyMapConePairTransferCone
      (zeroSectionCompl F E) (ModuleCat.of K K) m))).trans
    (LinearEquiv.ofSubmodules
      (TopPair.singularHomologyMapIso (ModuleCat.of K K) (preimageThomPairIso F E ι)
        m).toLinearEquiv _ _ (map_range_pairTransfer_eq_ker_sub_id hι K m))

/-- **The relative transfer of the orientation cover, as a value.** The class
`thomPairSingularHomologyEquivDeckInvariants F E ι hι K m x` is the transfer `thomPairTransfer` of
`x`: the leg of the transfer cone (`IsQuotientCoveringMap.pairTransferCone`) to
`Hₘ(E', p⁻¹ E₀; K)`, carried to `Hₘ(E', E'₀; K)` by the isomorphism of pairs
`preimageThomPairIso`. -/
theorem coe_thomPairSingularHomologyEquivDeckInvariants_apply {m : ℕ}
    (x : ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K)) :
    (thomPairSingularHomologyEquivDeckInvariants F E ι hι K m x :
        ((thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          |>.singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K)) =
      (thomPairTransfer E hι K m).hom x :=
  -- The leg of the transfer cone is the relative transfer (`pairTransferπ_app`), whose definition
  -- is not exposed here, so the two sides agree only through this lemma.
  have h := (isQuotientCoveringMap_liftHom F E hι).pairTransferπ_app (zeroSectionCompl F E)
    (ModuleCat.of K K) (SingleObj.star ℤˣ)
  congr((TopPair.singularHomologyMap (preimageThomPairIso F E ι).hom (ModuleCat.of K K) m).hom
    ((HomologicalComplex.homologyMap $h m).hom x))

variable (ω : Orientation ℝ F ι)
  {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
    (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)} (hg : Submodule.span K {g} = ⊤)
  {p m : ℕ} (h : finrank ℝ F + p = m)

/-- **The Thom isomorphism with coefficients in the orientation local system.** Let `E → B` be a
real vector bundle of rank `r`, `o(E)` its orientation local system, and `K` a commutative ring in
which `2` is invertible, for instance `ℚ`. Then `Hₘ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)` for `m = r + p`,
with no orientation of `E` and over any base.

The isomorphism passes through the orientation double cover `B'` of `E` and the pull-back `E'` of
`E` to it: it is the relative transfer onto the deck-invariant classes of `Hₘ(E', E'₀; K)`
(`thomPairSingularHomologyEquivDeckInvariants`), followed by the Thom isomorphism of the
tautologically oriented bundle `E'`, normalized by an orientation `ω` of the model fibre and a
generator `g` of `Hʳ(F, F ∖ {0}; K)`, onto the deck-anti-invariant classes of `Hₚ(B'; K)`
(`homologyThomMapDeckEquiv`), which are the classes of `Hₚ(B; o(E) ⊗ K)`
(`IsCoveringMap.signHomologyLinearEquiv`). -/
def thomPairSingularHomologyEquivTwistedHomology :
    ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K) ≃ₗ[K]
      LocalCoefficientSystem.twistedHomology (signLocalSystem F E K hι) p :=
  (thomPairSingularHomologyEquivDeckInvariants F E ι hι K m).trans
    ((homologyThomMapDeckEquiv (E := E) hι ω hg h).trans
      (IsCoveringMap.signHomologyLinearEquiv (E := TopCat.of (VectorBundleOrientationCover F E ι))
        (p := TopCat.ofHom projection) (isCoveringMap_proj hι) K
        (σ := (deck (F := F) (E := E) (ι := ι) :
          C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)))
        proj_comp_deck (fun q ↦ deck_deck q) (isQuotientCoveringMap_proj hι).finite_fiber p).symm)

/-- **The twisted Thom isomorphism read on the orientation cover.** Reading a class of
`Hₚ(B; o(E) ⊗ K)` on the orientation cover `B'` (`IsCoveringMap.signHomologyToCover`), the image
of `x ∈ Hₘ(E, E₀; K)` under `thomPairSingularHomologyEquivTwistedHomology` is the homology Thom
map of the tautological Thom class of the pull-back `E'`, applied to the transfer of `x`
(`thomPairTransfer`). -/
theorem signHomologyToCover_thomPairSingularHomologyEquivTwistedHomology
    (x : ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K)) :
    (IsCoveringMap.signHomologyToCover (E := TopCat.of (VectorBundleOrientationCover F E ι))
        (p := TopCat.ofHom projection) (isCoveringMap_proj hι) K
        (σ := (deck (F := F) (E := E) (ι := ι) :
          C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)))
        proj_comp_deck (isQuotientCoveringMap_proj hι).finite_fiber p).hom
        (thomPairSingularHomologyEquivTwistedHomology hι ω hg h x) =
      (homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (ModuleCat.of K K) (finrank ℝ F) p m h
        ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g)).hom
        ((thomPairTransfer E hι K m).hom x) :=
  -- Reading the inverse of `IsCoveringMap.signHomologyLinearEquiv` on the cover returns the
  -- anti-invariant class itself, which is the image of the homology Thom map.
  (IsCoveringMap.coe_signHomologyLinearEquiv_apply
    (E := TopCat.of (VectorBundleOrientationCover F E ι)) (p := TopCat.ofHom projection)
    (isCoveringMap_proj hι) K
    (σ := (deck (F := F) (E := E) (ι := ι) :
      C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)))
    proj_comp_deck (fun q ↦ deck_deck q) (isQuotientCoveringMap_proj hι).finite_fiber p
    _).symm.trans
    ((congrArg Subtype.val (LinearEquiv.apply_symm_apply _ _)).trans
      ((coe_homologyThomMapDeckEquiv_apply hι ω hg h _).trans
        (congrArg _ (coe_thomPairSingularHomologyEquivDeckInvariants_apply hι x))))

variable (F E K) in
include h in
/-- **The Thom isomorphism with coefficients in the orientation local system, unnormalized.** Let
`E → B` be a real vector bundle of rank `r`, `o(E)` its orientation local system, and `K` a
commutative ring in which `2` is invertible. Then `Hₘ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)` for
`m = r + p`, with no orientation of `E` and over any base. This forgets the normalization of
`thomPairSingularHomologyEquivTwistedHomology` by an orientation of the model fibre and a generator
of `Hʳ(F, F ∖ {0}; K)`, both of which always exist. -/
theorem nonempty_singularHomology_thomPair_linearEquiv_twistedHomology :
    Nonempty (((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K) ≃ₗ[K]
      LocalCoefficientSystem.twistedHomology (signLocalSystem F E K hι) p) := by
  obtain ⟨u, hu⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (Set.mem_univ 0)
  classical
  exact ⟨thomPairSingularHomologyEquivTwistedHomology hι
    ((Module.finBasisOfFinrankEq ℝ F hι.symm).reindex (Fintype.equivFin ι).symm).orientation hu h⟩

variable (F E K) in
include h in
/-- **The dimension of the homology of the Thom pair is a twisted Betti number of the base.** For a
real vector bundle `E → B` of rank `r`, orientable or not, and a commutative ring `K` in which `2`
is invertible, `dim Hₘ(E, E₀; K) = dim Hₚ(B; o(E) ⊗ K)` whenever `r + p = m`, where `o(E)` is the
orientation local system of `E`. -/
theorem finrank_singularHomology_thomPair_eq_finrank_twistedHomology :
    finrank K ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K) =
      finrank K (LocalCoefficientSystem.twistedHomology (signLocalSystem F E K hι) p) :=
  (nonempty_singularHomology_thomPair_linearEquiv_twistedHomology F E hι K h).some.finrank_eq

/-! ### The dual isomorphism in cohomology -/

variable (N : ModuleCat.{w} K) [Injective N]

/-- **The Thom isomorphism in cohomology with coefficients in the orientation local system.** Let
`E → B` be a real vector bundle of rank `r`, `o(E)` its orientation local system, `K` a commutative
ring in which `2` is invertible and `N` an injective `K`-module, for instance any vector space over
a field of characteristic other than `2` (`Module.injective_of_isSemisimpleRing`). Then
`Hᵐ(E, E₀; K, N) ≃ Hᵖ(B; o(E) ⊗ K, N)` for `m = r + p`, with no orientation of `E` and over any
base.

It is the transpose of the twisted Thom isomorphism in homology
(`thomPairSingularHomologyEquivTwistedHomology`): with injective values both cohomologies are the
duals `Hom(-, N)` of the corresponding homologies, by the universal coefficient theorem
(`TopPair.singularKronecker_bijective` and
`TauCeti.LocalCoefficientSystem.twistedKronecker_bijective`). -/
def thomPairSingularCohomologyEquivTwistedCohomology :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K N m ≃ₗ[K]
      (signLocalSystem F E K hι).twistedCohomology K N p :=
  (LinearEquiv.ofBijective _ ((thomPair F E).singularKronecker_bijective K m)).trans
    ((Linear.homCongr K (thomPairSingularHomologyEquivTwistedHomology hι ω hg h).toModuleIso
      (Iso.refl N)).trans ((signLocalSystem F E K hι).twistedKroneckerEquiv K p).symm)

/-- **The twisted Thom isomorphism in cohomology is dual to the one in homology**: evaluating the
image of `α ∈ Hᵐ(E, E₀; K, N)` in `Hᵖ(B; o(E) ⊗ K, N)` on a twisted class is evaluating `α` on the
class of `Hₘ(E, E₀; K)` that `thomPairSingularHomologyEquivTwistedHomology` sends to it. This
characterizes `thomPairSingularCohomologyEquivTwistedCohomology`, since the twisted Kronecker map
is injective for injective values. -/
@[simp]
theorem twistedKronecker_thomPairSingularCohomologyEquivTwistedCohomology
    (α : (thomPair F E).singularCohomology (ModuleCat.of K K) K N m) :
    (signLocalSystem F E K hι).twistedKronecker K p
        (thomPairSingularCohomologyEquivTwistedCohomology hι ω hg h N α) =
      ModuleCat.ofHom (thomPairSingularHomologyEquivTwistedHomology hι ω hg h).symm.toLinearMap ≫
        (thomPair F E).singularKronecker K m α := by
  rw [← LocalCoefficientSystem.twistedKroneckerEquiv_apply]
  simp [thomPairSingularCohomologyEquivTwistedCohomology, Linear.homCongr_apply,
    -LocalCoefficientSystem.twistedKroneckerEquiv_apply]

end CommRing

end TauCeti.VectorBundleOrientationCover
