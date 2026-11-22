/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Invariants
public import TauCeti.AlgebraicTopology.Singular.Invariants
public import TauCeti.AlgebraicTopology.Singular.Transfer.Sign
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.Thom.OrientationCover

/-!
# The Thom isomorphism with coefficients in the orientation local system

Let `E → B` be a real vector bundle of rank `r`, with Thom pair `(E, E₀)`, and let `o(E)` be its
orientation local system (`TauCeti.VectorBundleOrientationCover.signLocalSystem`). For a field `K`
in which `2` is invertible, this file proves the Thom isomorphism with orientation-twisted
coefficients

`Hₚ₊ᵣ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)`

(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`), with no
orientation of `E` and over any base. Over `ZMod 2` the twist disappears and the untwisted mod `2`
Thom isomorphism holds instead (`TauCeti.existsUnique_isThomClass_of_subsingleton_units` with
`TauCeti.homologyThomIso`).

The proof passes through the orientation double cover `B'` of `E`, with its deck involution `σ`
reversing orientations, and the pull-back `E'` of `E` to `B'`, oriented by the tautological
orientation. It composes three isomorphisms.

* The relative transfer. The Thom pair `(E', E'₀)` is a double cover of `(E, E₀)`, the quotient by
  the action of `ℤˣ` whose element `-1` acts by the lift `δ` of `σ`
  (`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_lift`). With `2` invertible, the
  transfer identifies `Hₘ(E, E₀; K)` with the classes of `Hₘ(E', E'₀; K)` fixed by `δ_*`
  (`IsQuotientCoveringMap.isLimitHomologyMapConePairTransferCone`); this is
  `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivDeckInvariants`.
* The Thom isomorphism of the oriented bundle `E'` anticommutes with the involutions, so it carries
  the `δ_*`-fixed classes onto the classes of `Hₚ(B'; K)` negated by `σ_*`
  (`TauCeti.VectorBundleOrientationCover.homologyThomMapDeckEquiv`).
* With `2` invertible, the classes of `Hₚ(B'; K)` negated by `σ_*` are the homology of `B` with
  coefficients in the sign local system of `σ` (`IsCoveringMap.signHomologyLinearEquiv`), which is
  `o(E)` by definition.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivDeckInvariants`: the transfer
  `Hₘ(E, E₀; K) ≃ {x ∈ Hₘ(E', E'₀; K) | δ_* x = x}`, for a ring `K` in which `2` is invertible.
* `TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`: the twisted
  Thom isomorphism `Hₚ₊ᵣ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)` for a field `K` in which `2` is invertible.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover and twisted
  coefficients).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.G (the transfer,
  Proposition 3G.1) and Section 3.H (local coefficients and the orientation double cover).
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

variable {K : Type w} [CommRing K] [Invertible (2 : K)]

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
`thomPairSingularHomologyEquivDeckInvariants F E ι hι K m x` is the relative transfer of `x` to
`Hₘ(E', p⁻¹ E₀; K)`, the leg of the transfer cone
(`IsQuotientCoveringMap.pairTransferCone`), carried to `Hₘ(E', E'₀; K)` by the isomorphism of
pairs `preimageThomPairIso`. -/
theorem coe_thomPairSingularHomologyEquivDeckInvariants_apply {m : ℕ}
    (x : ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K)) :
    (thomPairSingularHomologyEquivDeckInvariants F E ι hι K m x :
        ((thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E))
          |>.singularHomology (ModuleCat.of K K) m : ModuleCat.{w} K)) =
      (TopPair.singularHomologyMap (preimageThomPairIso F E ι).hom (ModuleCat.of K K) m).hom
        ((((HomologicalComplex.homologyFunctor _ _ m).mapCone
          ((isQuotientCoveringMap_liftHom F E hι).pairTransferCone (zeroSectionCompl F E)
            (ModuleCat.of K K))).π.app (SingleObj.star ℤˣ)).hom x) :=
  (rfl)

end CommRing

section Field

variable {K : Type w} [Field K] [Invertible (2 : K)] (ω : Orientation ℝ F ι)
  {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
    (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)} (hg : Submodule.span K {g} = ⊤)
  {p m : ℕ} (h : finrank ℝ F + p = m)

/-- **The Thom isomorphism with coefficients in the orientation local system.** Let `E → B` be a
real vector bundle of rank `r`, `o(E)` its orientation local system, and `K` a field in which `2`
is invertible. Then `Hₘ(E, E₀; K) ≃ Hₚ(B; o(E) ⊗ K)` for `m = r + p`, with no orientation of `E`
and over any base.

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
(`thomPairSingularHomologyEquivDeckInvariants`). -/
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
        (thomPairSingularHomologyEquivDeckInvariants F E ι hι K m x) :=
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
      (coe_homologyThomMapDeckEquiv_apply hι ω hg h _))

end Field

end TauCeti.VectorBundleOrientationCover
