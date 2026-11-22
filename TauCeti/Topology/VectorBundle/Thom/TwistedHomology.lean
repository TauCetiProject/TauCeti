/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Invariants
public import TauCeti.AlgebraicTopology.Singular.Transfer.Sign
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.Thom.OrientationCover

/-!
# The Thom isomorphism with orientation-twisted coefficients when `2` is invertible

Let `E → B` be a real vector bundle of rank `r`, `o(E)` its orientation local system
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), and `K` a commutative ring in which `2`
is invertible, for instance `ℚ` or any field of characteristic other than `2`. This file proves the
Thom isomorphism with coefficients twisted by the orientation,

`Hₚ₊ᵣ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)`,

in every degree `p`, over an arbitrary base and with no orientation of `E`
(`TauCeti.thomPairSingularHomologyLinearEquivTwistedHomology`). For an orientable bundle `o(E)` is
trivial and this is the ordinary Thom isomorphism. For a non-orientable one the twist cannot be
dropped: for the Möbius line over the circle, `H₁(E, E₀; ℚ) = 0` while `H₀(S¹; ℚ) = ℚ`.

The proof goes through the orientation double cover `π : B' → B`, with deck involution `σ`, and the
pull-back `E'` of `E` to `B'`, oriented by the tautological orientation. The map `E' → E` is the
quotient covering map of the action of `ℤˣ` lifted from `B'`
(`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_lift`), and it carries `E'₀` onto
`E₀`. Its relative transfer `t : Hₘ(E, E₀; K) ⟶ Hₘ(E', E'₀; K)`
(`TauCeti.VectorBundleOrientationCover.thomPairTransfer`) sends a relative simplex to the sum of its
two lifts. Writing `q : Hₘ(E', E'₀) ⟶ Hₘ(E, E₀)` for the map induced by the covering and `δ` for
the lift of `σ` to the Thom pair (`TauCeti.VectorBundleOrientationCover.deckThomPairMap`), the
transfer satisfies `q ∘ t = 2` and `t ∘ q = 1 + δ_*`. So when `2` is invertible, `t` identifies
`Hₘ(E, E₀; K)` with the classes fixed by `δ_*`
(`TauCeti.VectorBundleOrientationCover.thomPairTransferLinearEquiv`).

The Thom isomorphism of the oriented bundle `E'` carries the classes fixed by `δ_*` onto the classes
of `Hₚ(B'; K)` negated by `σ_*` (`TauCeti.VectorBundleOrientationCover.homologyThomMapDeckEquiv`),
because `δ` reverses the tautological orientation. Finally, the classes negated by `σ_*` are the
homology of `B` with coefficients in the sign local system of `σ`, which is `o(E) ⊗ K`
(`IsCoveringMap.signHomologyLinearEquiv`). The composite of the three identifications is the
twisted Thom isomorphism. It is normalized by an orientation `ω` of the model fibre `F` and a
generator `g` of `Hʳ(F, F ∖ {0}; K)`: read on the cover, it sends a class `x` to the image under the
Thom map of `E'` of the transfer of `x`
(`TauCeti.signHomologyToCover_thomPairSingularHomologyLinearEquivTwistedHomology`).

## Main definitions and results

* `TauCeti.VectorBundleOrientationCover.thomPairTransfer`: the relative transfer of the double cover
  `(E', E'₀) → (E, E₀)`, with the transfer relations
  `thomPairTransfer_comp_singularHomologyMap_pullbackThomPairMap` (`q ∘ t = 2`),
  `singularHomologyMap_pullbackThomPairMap_comp_thomPairTransfer` (`t ∘ q = 1 + δ_*`) and
  `thomPairTransfer_comp_singularHomologyMap_deckThomPairMap` (`δ_* ∘ t = t`).
* `TauCeti.VectorBundleOrientationCover.thomPairTransferLinearEquiv`: when `2` is invertible, the
  transfer identifies `Hₘ(E, E₀; K)` with the classes of `Hₘ(E', E'₀; K)` fixed by the lifted deck
  involution.
* `TauCeti.thomPairSingularHomologyLinearEquivTwistedHomology`: the Thom isomorphism
  `Hₚ₊ᵣ(E, E₀; K) ≃ₗ[K] Hₚ(B; o(E) ⊗ K)` when `2` is invertible in `K`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.G
  (Proposition 3G.1, the transfer of a finite cover), Section 3.H (the orientation double cover and
  homology with local coefficients) and Section 4.D (the Thom isomorphism).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover).
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Module

universe w

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] [FiniteDimensional ℝ F] {K : Type w} [CommRing K]
  (hι : Fintype.card ι = finrank ℝ F)

attribute [local instance] pullbackMulAction

section Transfer

variable (F E ι) in
/-- The map from the total space of the pull-back of `E` to its orientation cover to the total space
of `E`, as a morphism of spaces. -/
private abbrev liftHom :
    TopCat.of (TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) ⟶
      TopCat.of (TotalSpace F E) :=
  TopCat.ofHom ⟨Pullback.lift (projection : VectorBundleOrientationCover F E ι → B),
    Pullback.continuous_lift F E _⟩

include hι in
/-- The map `liftHom` is the quotient covering map of the action of `ℤˣ`. -/
private theorem isQuotientCoveringMap_liftHom : IsQuotientCoveringMap (liftHom F E ι) ℤˣ :=
  isQuotientCoveringMap_lift hι

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The preimage of the nonzero vectors of `E` is the set of nonzero vectors of the pull-back. -/
private theorem preimage_liftHom_zeroSectionCompl :
    liftHom F E ι ⁻¹' zeroSectionCompl F E =
      zeroSectionCompl F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) :=
  preimage_pullbackLift_zeroSectionCompl _

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The pair of the preimage of the nonzero vectors of `E`, in which the relative transfer of the
covering lands, is the Thom pair of the pull-back, through the identity of the total space. -/
private def preimageThomPairIso :
    TopPair.ofSubset (liftHom F E ι ⁻¹' zeroSectionCompl F E) ≅
      thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) where
  hom := TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
    preimage_liftHom_zeroSectionCompl (F := F) (E := E) (ι := ι) ▸ hv
  inv := TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
    (preimage_liftHom_zeroSectionCompl (F := F) (E := E) (ι := ι)).symm ▸ hv
  hom_inv_id := (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hv ↦ hv)
    (Category.id_comp _)).trans (TopPair.ofSubsetMap_id _)
  inv_hom_id := (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hv ↦ hv)
    (Category.id_comp _)).trans (TopPair.ofSubsetMap_id _)

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The underlying map of `preimageThomPairIso` is the identity. -/
private theorem preimageThomPairIso_hom_fst :
    TopPair.Hom.fst (preimageThomPairIso (F := F) (E := E) (ι := ι)).hom = 𝟙 _ :=
  TopPair.ofSubsetMap_fst _ _

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The underlying map of the inverse of `preimageThomPairIso` is the identity. -/
private theorem preimageThomPairIso_inv_fst :
    TopPair.Hom.fst (preimageThomPairIso (F := F) (E := E) (ι := ι)).inv = 𝟙 _ :=
  TopPair.ofSubsetMap_fst _ _

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The map of pairs induced by the covering is `TauCeti.pullbackThomPairMap`, read through
`preimageThomPairIso`. -/
private theorem pullbackThomPairMap_eq_preimageThomPairIso_inv_comp :
    pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)) =
      (preimageThomPairIso (F := F) (E := E) (ι := ι)).inv ≫
        TopPair.ofSubsetMap (liftHom F E ι) (Set.mapsTo_preimage _ (zeroSectionCompl F E)) := by
  -- Pointwise, both sides are `Pullback.lift`. The steps are terms: the two sides read the zero of
  -- the fibres of the pull-back through two instances that agree only up to unfolding.
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  exact (pullbackThomPairMap_fst_apply F E _ v).trans
    ((TopPair.ofSubsetMap_fst_apply (liftHom F E ι)
      (Set.mapsTo_preimage _ (zeroSectionCompl F E)) v).symm.trans
      (congrArg (fun φ ↦ TopPair.Hom.fst (TopPair.ofSubsetMap (liftHom F E ι)
        (Set.mapsTo_preimage _ (zeroSectionCompl F E))) (φ v)) preimageThomPairIso_inv_fst.symm))

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The lift of the deck involution to the pull-back is the action of `-1`. -/
private theorem deckThomPairMap_fst_apply_eq_neg_one_smul
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    TopPair.Hom.fst (deckThomPairMap F E ι) v = (-1 : ℤˣ) • v :=
  Pullback.totalSpace_ext ((deckThomPairMap_fst_proj v).trans (neg_one_smul_eq_deck _).symm)
    (lift_deckThomPairMap_fst v)

/-- Read through `preimageThomPairIso`, the action of `-1` is the lift of the deck involution. -/
private theorem preimageThomPairIso_hom_comp_deckThomPairMap :
    (preimageThomPairIso (F := F) (E := E) (ι := ι)).hom ≫ deckThomPairMap F E ι =
      TopPair.ofSubsetMap (TopCat.ofHom ⟨((-1 : ℤˣ) • · :
        TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) → _),
        (isQuotientCoveringMap_liftHom hι).continuous_const_smul _⟩)
      ((isQuotientCoveringMap_liftHom hι).mapsTo_smul_preimage (zeroSectionCompl F E) (-1)) ≫
        preimageThomPairIso.hom := by
  set S := TopPair.ofSubsetMap (TopCat.ofHom ⟨((-1 : ℤˣ) • · :
    TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) → _),
    (isQuotientCoveringMap_liftHom hι).continuous_const_smul _⟩)
    ((isQuotientCoveringMap_liftHom hι).mapsTo_smul_preimage (zeroSectionCompl F E) (-1)) with hS
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ ?_)
  -- Both underlying maps of `preimageThomPairIso` are identities, so both sides are computed on `v`
  -- directly: the lift of the deck involution and the action of `-1` agree.
  refine (congrArg (fun φ ↦ TopPair.Hom.fst (deckThomPairMap F E ι) (φ v))
    preimageThomPairIso_hom_fst).trans ((deckThomPairMap_fst_apply_eq_neg_one_smul v).trans ?_)
  refine (hS ▸ TopPair.ofSubsetMap_fst_apply _ _ v).symm.trans ?_
  exact congrArg (fun φ ↦ φ (TopPair.Hom.fst S v)) preimageThomPairIso_hom_fst.symm

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
    ((isQuotientCoveringMap_liftHom hι).isCoveringMap.singularPairTransfer
      (isQuotientCoveringMap_liftHom hι).finite_fiber (zeroSectionCompl F E)
      (ModuleCat.of K K)) m ≫
    TopPair.singularHomologyMap preimageThomPairIso.hom (ModuleCat.of K K) m

/-- **The transfer formula on Thom pairs.** The transfer of the orientation double cover followed by
the map of Thom pairs `(E', E'₀) ⟶ (E, E₀)` is multiplication by `2`. -/
theorem thomPairTransfer_comp_singularHomologyMap_pullbackThomPairMap (m : ℕ) :
    thomPairTransfer E K hι m ≫ TopPair.singularHomologyMap
      (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
      (ModuleCat.of K K) m = 2 • 𝟙 _ := by
  have hG := isQuotientCoveringMap_liftHom (F := F) (E := E) (ι := ι) hι
  -- Term-mode steps: the zero of the fibres of the pull-back enters the source of
  -- `pullbackThomPairMap` and the target of the transfer as two instances that agree only up to
  -- unfolding, so `rw` cannot work on this goal.
  calc thomPairTransfer E K hι m ≫ TopPair.singularHomologyMap
        (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
        (ModuleCat.of K K) m
      = HomologicalComplex.homologyMap (hG.isCoveringMap.singularPairTransfer hG.finite_fiber
          (zeroSectionCompl F E) (ModuleCat.of K K)) m ≫ TopPair.singularHomologyMap
          (preimageThomPairIso.hom ≫ preimageThomPairIso.inv ≫
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
      (ModuleCat.of K K) m ≫ thomPairTransfer E K hι m =
      𝟙 _ + TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m := by
  have hG := isQuotientCoveringMap_liftHom (F := F) (E := E) (ι := ι) hι
  set e := preimageThomPairIso (F := F) (E := E) (ι := ι)
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
      ← preimageThomPairIso_hom_comp_deckThomPairMap hι, e.inv_hom_id_assoc]
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
    thomPairTransfer E K hι m ≫ TopPair.singularHomologyMap (deckThomPairMap F E ι)
      (ModuleCat.of K K) m = thomPairTransfer E K hι m := by
  have hG := isQuotientCoveringMap_liftHom (F := F) (E := E) (ι := ι) hι
  rw [thomPairTransfer, Category.assoc, ← TopPair.singularHomologyMap_comp,
    preimageThomPairIso_hom_comp_deckThomPairMap hι, TopPair.singularHomologyMap_comp,
    ← Category.assoc,
    hG.isCoveringMap.homologyMap_singularPairTransfer_comp_singularHomologyMap_of_comp_eq
      hG.finite_fiber (zeroSectionCompl F E) (ModuleCat.of K K) m (MulAction.bijective _)
      (TopCat.ext fun _ ↦ hG.map_smul _)]

variable [Invertible (2 : K)]

/-- **The transfer is injective when `2` is invertible**, since projecting a transferred class
back multiplies it by `2`. -/
theorem injective_thomPairTransfer (m : ℕ) :
    Function.Injective (thomPairTransfer E K hι m).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- Term-mode steps: the zero of the fibres of the pull-back enters the source of
  -- `pullbackThomPairMap` and the target of the transfer as two instances that agree only up to
  -- unfolding, so `rw` cannot rewrite `hx` inside `h`.
  have h : (TopPair.singularHomologyMap
      (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
      (ModuleCat.of K K) m).hom ((thomPairTransfer E K hι m).hom x) = (2 : ℕ) • x :=
    congr($(thomPairTransfer_comp_singularHomologyMap_pullbackThomPairMap hι m).hom x)
  have h₂ : (2 : ℕ) • x = 0 := h.symm.trans ((congrArg _ hx).trans (map_zero _))
  rw [← one_smul K x, ← invOf_mul_self (2 : K), mul_smul, ofNat_smul_eq_nsmul K 2, h₂, smul_zero]

/-- **The transferred classes are the deck-invariant classes when `2` is invertible.** A class
`c ∈ Hₘ(E', E'₀; K)` is the transfer of a class of `Hₘ(E, E₀; K)` exactly when `δ_* c = c` for the
lift `δ` of the deck involution: such a class is the transfer of half its projection. -/
theorem range_thomPairTransfer (m : ℕ) :
    LinearMap.range (thomPairTransfer E K hι m).hom =
      LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K)
        m).hom - LinearMap.id) := by
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, rfl⟩
    have h : (TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom
        ((thomPairTransfer E K hι m).hom x) = (thomPairTransfer E K hι m).hom x :=
      congr($(thomPairTransfer_comp_singularHomologyMap_deckThomPairMap hι m).hom x)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, h, sub_self]
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
    refine ⟨⅟(2 : K) • (TopPair.singularHomologyMap
      (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
      (ModuleCat.of K K) m).hom y, ?_⟩
    have h : (thomPairTransfer E K hι m).hom ((TopPair.singularHomologyMap
        (pullbackThomPairMap F E (projection : C(VectorBundleOrientationCover F E ι, B)))
        (ModuleCat.of K K) m).hom y) =
          y + (TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom y :=
      congr($(singularHomologyMap_pullbackThomPairMap_comp_thomPairTransfer hι m).hom y)
    rw [map_smul, h, hy, ← two_smul K y, smul_smul, invOf_mul_self, one_smul]

/-- **The relative homology of the Thom pair is the deck-invariant part upstairs.** When `2` is
invertible in `K`, the transfer of the orientation double cover identifies `Hₘ(E, E₀; K)` with the
classes of `Hₘ(E', E'₀; K)` fixed by the lift of the deck involution. -/
def thomPairTransferLinearEquiv (m : ℕ) :
    (thomPair F E).singularHomology (C := ModuleCat.{w} K) (ModuleCat.of K K) m ≃ₗ[K]
      LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K)
        m).hom - LinearMap.id) :=
  (LinearEquiv.ofInjective _ (injective_thomPairTransfer hι m)).trans
    (LinearEquiv.ofEq _ _ (range_thomPairTransfer hι m))

/-- The identification of the relative homology of the Thom pair with the deck-invariant classes
upstairs is `TauCeti.VectorBundleOrientationCover.thomPairTransfer`. -/
@[simp]
theorem coe_thomPairTransferLinearEquiv_apply {m : ℕ}
    (x : (thomPair F E).singularHomology (C := ModuleCat.{w} K) (ModuleCat.of K K) m) :
    (thomPairTransferLinearEquiv hι m x : (thomPair F
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).singularHomology
        (C := ModuleCat.{w} K) (ModuleCat.of K K) m) = (thomPairTransfer E K hι m).hom x :=
  (rfl)

end Transfer

end TauCeti.VectorBundleOrientationCover

namespace TauCeti

open VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} [Fintype ι] [FiniteDimensional ℝ F] {K : Type w} [CommRing K] [Invertible (2 : K)]
  (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
  {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
    (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)} (hg : Submodule.span K {g} = ⊤)
  {p m : ℕ} (h : finrank ℝ F + p = m)

/-- **The Thom isomorphism with orientation-twisted coefficients.** Let `E → B` be a real vector
bundle of rank `r`, over any base and not necessarily orientable, and let `K` be a commutative ring
in which `2` is invertible. Then `Hₚ₊ᵣ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)`, the homology of `B` with
coefficients in the orientation local system of `E`. The isomorphism is normalized by an orientation
`ω` of the model fibre `F` and a generator `g` of `Hʳ(F, F ∖ {0}; K)`. -/
def thomPairSingularHomologyLinearEquivTwistedHomology :
    (thomPair F E).singularHomology (C := ModuleCat.{w} K) (ModuleCat.of K K) m ≃ₗ[K]
      LocalCoefficientSystem.twistedHomology.{w, w, w} (signLocalSystem F E K hι) p :=
  (thomPairTransferLinearEquiv hι m).trans <|
    (homologyThomMapDeckEquiv hι ω hg h).trans
      (IsCoveringMap.signHomologyLinearEquiv (E := TopCat.of (VectorBundleOrientationCover F E ι))
        (B := TopCat.of B) (p := TopCat.ofHom projection) (isCoveringMap_proj hι) K
        proj_comp_deck (fun q ↦ deck_deck q) (fun b ↦ (finite_fiber hι b).to_subtype) p).symm

/-- **The twisted Thom isomorphism read on the orientation cover.** Reading a class of
`Hₚ(B; o(E) ⊗ K)` as a class of the orientation cover `B'`, the twisted Thom isomorphism sends
`x ∈ Hₚ₊ᵣ(E, E₀; K)` to the image under the Thom map of the tautologically oriented pull-back `E'`
of the transfer of `x`. -/
theorem signHomologyToCover_thomPairSingularHomologyLinearEquivTwistedHomology
    (x : (thomPair F E).singularHomology (C := ModuleCat.{w} K) (ModuleCat.of K K) m) :
    (IsCoveringMap.signHomologyToCover (E := TopCat.of (VectorBundleOrientationCover F E ι))
      (B := TopCat.of B) (p := TopCat.ofHom projection) (isCoveringMap_proj hι) K proj_comp_deck
      (fun b ↦ (finite_fiber hι b).to_subtype) p).hom
        (thomPairSingularHomologyLinearEquivTwistedHomology hι ω hg h x) =
      (homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (ModuleCat.of K K) (finrank ℝ F) p m h
        ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g)).hom
        ((thomPairTransfer E K hι m).hom x) := by
  -- Term-mode steps: the orientation local system is the sign local system of the cover only
  -- after unfolding `signLocalSystem`, so `rw` cannot work on this goal.
  have h₁ := IsCoveringMap.coe_signHomologyLinearEquiv_apply
    (E := TopCat.of (VectorBundleOrientationCover F E ι)) (B := TopCat.of B)
    (p := TopCat.ofHom projection) (isCoveringMap_proj hι) K proj_comp_deck (fun q ↦ deck_deck q)
    (fun b ↦ (finite_fiber hι b).to_subtype) p
    (thomPairSingularHomologyLinearEquivTwistedHomology hι ω hg h x)
  rw [← h₁, thomPairSingularHomologyLinearEquivTwistedHomology, LinearEquiv.trans_apply]
  exact (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ _)).trans
    ((coe_homologyThomMapDeckEquiv_apply hι ω hg h _).trans
      (congrArg _ (coe_thomPairTransferLinearEquiv_apply hι x)))

end TauCeti
