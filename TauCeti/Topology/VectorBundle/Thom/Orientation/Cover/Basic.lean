/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Orientation.Proper
public import TauCeti.Topology.VectorBundle.Orientation.Tautological
public import TauCeti.Topology.VectorBundle.Thom.Homology
public import TauCeti.Topology.VectorBundle.Thom.RankZero

/-!
# The Thom class of the tautological orientation and the deck involution

Let `E → B` be a real vector bundle, `B'` its orientation double cover with deck involution `τ`
(`TauCeti.VectorBundleOrientationCover.deck`), and `E'` the pull-back of `E` to `B'`. The bundle
`E'` carries the tautological orientation, which orients the fibre over `(b, o)` by `o`
(`TauCeti.VectorBundleOrientationCover.tautologicalOrientation`), so it has a Thom class `u` with
coefficients in any commutative ring (`TauCeti.VectorBundleOrientation.thomClassOfModel`).

The deck involution lifts to the Thom pair `(E', E'₀)`: over a point `(b, o)` it is the identity of
the fibre `E_b`, viewed as the fibre over `(b, -o)`
(`TauCeti.VectorBundleOrientationCover.deckThomPairMap`). It covers `τ`, is an involution, and
reverses the tautological orientation, so it pulls `u` back to `-u`
(`TauCeti.VectorBundleOrientationCover.singularCohomologyMap_deckThomPairMap_thomClassOfModel`).
By naturality of the Thom maps, the homology Thom map `x ↦ π_*(x ⌢ u)` therefore carries the action
of the lifted involution on `Hₘ(E', E'₀)` to minus the action of `τ` on `Hₚ(B')`, and the Thom map
`a ↦ π^*a ⌣ u` carries the action of `τ` to minus that of the lifted involution.

With coefficients in a commutative ring `K`, the homology Thom map
of `E'` is bijective, so it restricts to an isomorphism from the classes of `Hₘ(E', E'₀; K)` fixed
by the lifted involution onto the classes of `Hₚ(B'; K)` negated by `τ`
(`TauCeti.VectorBundleOrientationCover.homologyThomMapDeckEquiv`). When `2` is invertible in `K`,
the fixed classes upstairs are the relative homology of `(E, E₀)` and the negated classes of `B'`
are the homology of `B` twisted by the orientation local system of `E`. Through these two
identifications, proved in `TauCeti.Topology.VectorBundle.Thom.TwistedHomology`, this isomorphism
becomes the Thom isomorphism `Hₚ₊ᵣ(E, E₀; K) ≅ Hₚ(B; o(E) ⊗ K)` with orientation-twisted
coefficients (`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyEquivTwistedHomology`).

## Main definitions and results

* `TauCeti.VectorBundleOrientationCover.deckThomPairMap`: the lift of the deck involution to the
  Thom pair of the pull-back bundle, with `deckThomPairMap_fst_comp_thomPairProj` and its pointwise
  form `deckThomPairMap_fst_proj` (it covers the deck involution), `lift_deckThomPairMap_fst` (it
  fixes the underlying vectors of `E`) and
  `deckThomPairMap_comp_deckThomPairMap` (it is an involution).
* `TauCeti.VectorBundleOrientationCover.coverThomPairMap`: the map of Thom pairs from the pull-back
  bundle to `E`, with `deckThomPairMap_comp_coverThomPairMap` (the lifted deck involution covers
  the identity of the Thom pair of `E`) and `coverThomPairMap_eq_pullbackThomPairMap` (it is
  `TauCeti.pullbackThomPairMap`).
* `TauCeti.VectorBundleOrientationCover.neg_one_smul_eq_deckThomPairMap_fst`: `-1 ∈ ℤˣ` acts on the
  Thom pair of the pull-back bundle by the lifted deck involution, and
  `isQuotientCoveringMap_coverThomPairMap_fst`, `isQuotientCoveringMap_coverThomPairMap_snd`:
  `coverThomPairMap` is the quotient covering map of this action on both spaces.
* `TauCeti.VectorBundleOrientationCover.singularCohomologyMap_deckThomPairMap_thomClassOfModel`:
  it negates the Thom class of the tautological orientation.
* `TauCeti.VectorBundleOrientationCover.singularHomologyMap_deckThomPairMap_comp_homologyThomMap`
  and `TauCeti.VectorBundleOrientationCover.thomMap_singularCohomologyMap_deck`: the Thom maps
  anticommute with the deck involutions.
* `TauCeti.VectorBundleOrientationCover.homologyThomMapDeckEquiv`: the restriction of the homology
  Thom map to deck-invariant classes, an isomorphism onto the deck-anti-invariant classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover and twisted
  coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients) and Section 4.D (the Thom
  isomorphism).
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Module

universe w

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type}

/-- The deck involution, written out on the points of the cover so that its base point is
definitionally that of its argument; this is what lets the identity of the fibres lift it to the
pull-back bundle. -/
private def deckMap : C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι) :=
  ⟨fun q ↦ ⟨q.proj, -q.orientation⟩, by
    simpa only [← deck_apply] using (deck (F := F) (E := E) (ι := ι)).continuous⟩

private theorem deckMap_eq :
    (deckMap : C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)) =
      (deck (F := F) (E := E) (ι := ι) :
        C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)) :=
  ContinuousMap.ext fun q ↦ (deck_apply q).symm

/-- Over a point `q` of the cover, the lift of the deck involution is the identity of the fibre
`E q.proj`, which is also the fibre of the pull-back over `deckMap q`. -/
private def deckFiberEquiv (q : VectorBundleOrientationCover F E ι) :
    ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q ≃L[ℝ]
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) (deckMap q) :=
  ContinuousLinearEquiv.refl ℝ (E q.proj)

variable (F E ι) in
private theorem continuous_totalSpaceMk_deckMap :
    Continuous fun v : TotalSpace F
        ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) ↦
      TotalSpace.mk' F (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (deckMap v.proj) (deckFiberEquiv v.proj v.snd) := by
  refine (inducing_pullbackTotalSpaceEmbedding F E _).continuous_iff.2 ?_
  -- Read in `B' × TotalSpace F E`, the map is `v ↦ (deckMap v.proj, Pullback.lift v)`, since
  -- `deckFiberEquiv` is the identity and `deckMap` keeps the base point, by definition.
  exact ((deckMap.continuous.comp (Pullback.continuous_proj F E _)).prodMk
    (Pullback.continuous_lift F E _))

variable (F E ι) in
/-- The deck involution of the orientation cover, lifted to the Thom pair of the pull-back of `E`
to the cover: over each point of the cover it is the identity of the fibre of `E`. -/
def deckThomPairMap :
    thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) ⟶
      thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) :=
  thomPairMapOfFiberwise (φ := deckFiberEquiv) (continuous_totalSpaceMk_deckMap F E ι)

variable (F E ι) in
/-- The lift of the deck involution covers the deck involution. -/
theorem deckThomPairMap_fst_comp_thomPairProj :
    TopPair.Hom.fst (deckThomPairMap F E ι) ≫
        thomPairProj F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) =
      thomPairProj F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) ≫
        TopCat.ofHom (deck (F := F) (E := E) (ι := ι) :
          C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)) := by
  rw [← deckMap_eq]
  exact thomPairMapOfFiberwise_fst_comp_thomPairProj (φ := deckFiberEquiv)
    (continuous_totalSpaceMk_deckMap F E ι)

-- Not a simp lemma: simplifying the coercion of the bundled projection changes the implicit
-- pull-back bundle in the left-hand side, so it is not in simp normal form.
/-- The lift of the deck involution does not move the underlying vector of `E`: its composite with
the map of the pull-back bundle to `E` is that map. -/
theorem lift_deckThomPairMap_fst
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    Pullback.lift (projection : C(VectorBundleOrientationCover F E ι, B))
        (TopPair.Hom.fst (deckThomPairMap F E ι) v) =
      Pullback.lift (projection : C(VectorBundleOrientationCover F E ι, B)) v := by
  rw [deckThomPairMap, thomPairMapOfFiberwise_fst_apply]
  -- Both are `⟨v.proj.proj, v.2⟩`: `deckMap` keeps the base point and `deckFiberEquiv` is the
  -- identity, by definition.
  rfl

-- Not a simp lemma, for the same reason as `lift_deckThomPairMap_fst`.
/-- The lift of the deck involution carries a vector over a point `q` of the cover to a vector
over `deck q`. -/
theorem deckThomPairMap_fst_proj
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    (TopPair.Hom.fst (deckThomPairMap F E ι) v).proj = deck v.proj := by
  rw [deckThomPairMap, thomPairMapOfFiberwise_fst_apply, deck_apply]
  rfl

/-- The lifted deck involution sends a vector `v` over `p` to the same vector of `E_{π p}`, now
over the point `⟨π p, -p.orientation⟩`, which is `deck p` (`deck_apply`). -/
-- Not `@[simp]`: simp rewrites the coercion of the continuous map on the left-hand side, so the
-- statement is not in simp normal form.
theorem deckThomPairMap_fst_apply
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    TopPair.Hom.fst (deckThomPairMap F E ι) v =
      TotalSpace.mk' F (⟨v.proj.proj, -v.proj.orientation⟩ : VectorBundleOrientationCover F E ι)
        v.snd := by
  rw [deckThomPairMap, thomPairMapOfFiberwise_fst_apply]
  rfl

variable (F E ι) in
/-- The lift of the deck involution is an involution. -/
@[reassoc (attr := simp)]
theorem deckThomPairMap_comp_deckThomPairMap :
    deckThomPairMap F E ι ≫ deckThomPairMap F E ι = 𝟙 _ := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun ⟨q, x⟩ ↦ ?_)
  have hq : deckMap (deckMap q) = q :=
    (congrArg (fun φ ↦ φ (φ q)) deckMap_eq).trans (deck_deck q)
  -- The first components of a composite and of the identity of pairs evaluate as composites and
  -- identities of continuous maps only after unfolding the comma-category structure.
  change TopPair.Hom.fst (deckThomPairMap F E ι) (TopPair.Hom.fst (deckThomPairMap F E ι) ⟨q, x⟩) =
    ⟨q, x⟩
  rw [deckThomPairMap, thomPairMapOfFiberwise_fst_apply, thomPairMapOfFiberwise_fst_apply]
  exact TotalSpace.ext hq HEq.rfl

variable (F E ι) in
/-- The map `(E', E'₀) ⟶ (E, E₀)` from the Thom pair of the pull-back `E'` of `E` to its
orientation cover. It is `TauCeti.pullbackThomPairMap`, with the zero of the fibres of `E'` read
through their module structure, as in the lift of the deck involution `deckThomPairMap`, so that
the two maps compose. -/
def coverThomPairMap :
    thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) ⟶ thomPair F E :=
  pullbackThomPairMap F E _

-- Not a simp lemma, for the same reason as `lift_deckThomPairMap_fst`: simp rewrites the type of
-- the coerced continuous map on the left-hand side, so it is not in simp normal form.
/-- The map of Thom pairs of the orientation cover sends a vector of `E'` to the same vector of
`E`. -/
theorem coverThomPairMap_fst_apply
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    TopPair.Hom.fst (coverThomPairMap F E ι) v = Pullback.lift _ v :=
  pullbackThomPairMap_fst_apply F E _ v

variable (F E ι) in
/-- The map of Thom pairs of the orientation cover is `TauCeti.pullbackThomPairMap`, whose Thom pair
reads the zeros of the fibres of the pull-back through `TauCeti.pullbackFiberZero` instead. -/
theorem coverThomPairMap_eq_pullbackThomPairMap :
    coverThomPairMap F E ι = pullbackThomPairMap F E projection :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
    (coverThomPairMap_fst_apply v).trans (pullbackThomPairMap_fst_apply F E _ v).symm)

/-- A vector `v` of `E'` lies over the point `v.proj` of the orientation cover, which lies over the
image of `v` in the base. -/
theorem proj_proj_eq_proj_coverThomPairMap_fst
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    v.proj.proj = (TopPair.Hom.fst (coverThomPairMap F E ι) v).proj :=
  (congrArg TotalSpace.proj (coverThomPairMap_fst_apply v)).symm

/-- The lift of the deck involution does not move the underlying vector of `E`. -/
theorem coverThomPairMap_fst_deckThomPairMap_fst
    (v : TotalSpace F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :
    TopPair.Hom.fst (coverThomPairMap F E ι) (TopPair.Hom.fst (deckThomPairMap F E ι) v) =
      TopPair.Hom.fst (coverThomPairMap F E ι) v :=
  (coverThomPairMap_fst_apply _).trans
    ((lift_deckThomPairMap_fst v).trans (coverThomPairMap_fst_apply v).symm)

variable (F E ι) in
/-- **The lift of the deck involution covers the identity of `(E, E₀)`**. -/
@[reassoc (attr := simp)]
theorem deckThomPairMap_comp_coverThomPairMap :
    deckThomPairMap F E ι ≫ coverThomPairMap F E ι = coverThomPairMap F E ι :=
  TopPair.hom_ext_of_fst _ (TopCat.ext coverThomPairMap_fst_deckThomPairMap_fst)

/-- On the fibre pair over a point of the cover, the lift of the deck involution is the inclusion
of the same fibre pair over the image point. -/
private theorem fiberThomPairMap_comp_deckThomPairMap (q : VectorBundleOrientationCover F E ι) :
    fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) q ≫
        deckThomPairMap F E ι =
      fiberThomPairMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (deckMap q) := by
  refine (fiberThomPairMap_comp_thomPairMapOfFiberwise (φ := deckFiberEquiv)
    (continuous_totalSpaceMk_deckMap F E ι) q).trans ?_
  -- The fibrewise map is the identity of `E q.proj`, whose pair isomorphism is the identity; the
  -- fibres of the pull-back at `q` and at `deckMap q` agree only after unfolding `deckMap`.
  exact (congrArg (fun φ ↦ φ.hom ≫ _) (ContinuousLinearEquiv.complZeroPairIso_refl
    (R := ℝ) (E := E q.proj))).trans (Category.id_comp _)

variable [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)
  {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K} [Module.Projective K R']

/-- **The deck involution reverses the tautological Thom class.** On the pull-back of `E` to its
orientation double cover, the lift of the deck involution pulls the Thom class of the tautological
orientation, normalized by an orientation `ω` of the model fibre and a class `g`, back to its
negative: over each point it is the identity of the fibre, while the tautological orientation of
the image point is the opposite one. -/
theorem singularCohomologyMap_deckThomPairMap_thomClassOfModel (ω : Orientation ℝ F ι)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F)) :
    TopPair.singularCohomologyMap (deckThomPairMap F E ι) (finrank ℝ F)
        ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g) =
      -(tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g := by
  refine neg_eq_iff_eq_neg.1 (VectorBundleOrientation.eq_thomClassOfModel_of_forall_exists _ hι ω g
    fun q ↦ ?_)
  let e := (trivializationAt F E q.proj).pullback
    (projection : C(VectorBundleOrientationCover F E ι, B))
  have hq : q ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q.proj
  -- The image `deckMap q` lies over the same point of `B`, so in the same base set.
  have hq' : deckMap q ∈ e.baseSet := hq
  obtain ⟨g', hg', hrestr⟩ :=
    VectorBundleOrientation.exists_singularCohomologyMap_fiberThomPairMap_thomClassOfModel
      tautologicalOrientation hι ω g e hq'
  refine ⟨e, inferInstance, hq, -g', ?_, ?_⟩
  · have hread : e.mapOrientation ι hq' (tautologicalOrientation (deckMap q)) =
        -e.mapOrientation ι hq (tautologicalOrientation q) := by
      rw [tautologicalOrientation_apply, tautologicalOrientation_apply]
      -- `erw` identifies the inherited module instances on the pullback fibre type synonym.
      erw [Trivialization.mapOrientation_pullback, Trivialization.mapOrientation_pullback]
      -- `deckMap q` lies over `q.proj` and records `-q.orientation`, by definition of `deckMap`.
      exact Trivialization.mapOrientation_neg _ _ q.orientation
    rw [hread] at hg'
    rcases hg' with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact Or.inr ⟨neg_eq_iff_eq_neg (G := Orientation ℝ F ι) |>.1 h, rfl⟩
    · exact Or.inl ⟨neg_inj (G := Orientation ℝ F ι) |>.1 h, neg_neg g⟩
  · rw [map_neg, map_neg, ← TopPair.singularCohomologyMap_comp_apply,
      fiberThomPairMap_comp_deckThomPairMap, neg_inj]
    -- The pulled-back trivialization `e` reads the fibres at `deckMap q` and at `q` by the same
    -- linear map, that of `E` at `q.proj`, by definition of the pull-back of a trivialization.
    exact hrestr

section ThomMap

variable {K : Type w} [CommRing K] (ω : Orientation ℝ F ι)
  (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
    (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))

/-- **The homology Thom map anticommutes with the deck involutions.** For the Thom class `u` of the
tautological orientation of the pull-back of `E` to its orientation cover, the homology Thom map
`x ↦ π_*(x ⌢ u)` carries the action of the lifted deck involution on `Hₘ(E', E'₀; A)` to minus the
action of the deck involution on `Hₚ(B'; A)`. -/
theorem singularHomologyMap_deckThomPairMap_comp_homologyThomMap (A : ModuleCat.{w} K) {p m : ℕ}
    (h : finrank ℝ F + p = m) :
    TopPair.singularHomologyMap (deckThomPairMap F E ι) A m ≫
        homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) A
          (finrank ℝ F) p m h
          ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g) =
      -(homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) A
          (finrank ℝ F) p m h
          ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
          (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) :
            C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)))) := by
  rw [← homologyThomMap_naturality F _ _ _ (deckThomPairMap_fst_comp_thomPairProj F E ι),
    singularCohomologyMap_deckThomPairMap_thomClassOfModel, map_neg, Preadditive.neg_comp]

/-- **The Thom map anticommutes with the deck involutions.** For the Thom class `u` of the
tautological orientation of the pull-back of `E` to its orientation cover, the Thom map
`a ↦ π^*a ⌣ u` carries the action of the deck involution on `Hᵖ(B'; M)` to minus the action of the
lifted deck involution on `Hᵐ(E', E'₀; M)`. -/
theorem thomMap_singularCohomologyMap_deck {M : ModuleCat.{w} K} {p m : ℕ}
    (h : p + finrank ℝ F = m)
    (a : (TopCat.of (VectorBundleOrientationCover F E ι)).singularCohomology
      (ModuleCat.of K K) K M p) :
    thomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) M (finrank ℝ F) p m h
        ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g)
        (TopCat.singularCohomologyMap
          (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) :
            C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι))) p a) =
      -TopPair.singularCohomologyMap (deckThomPairMap F E ι) m
        (thomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) M (finrank ℝ F)
          p m h ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g)
          a) := by
  rw [← thomMap_naturality F _ _ _ (deckThomPairMap_fst_comp_thomPairProj F E ι),
    singularCohomologyMap_deckThomPairMap_thomClassOfModel, map_neg, LinearMap.neg_apply, neg_neg]

end ThomMap

section CommRing

variable {K : Type w} [CommRing K] (ω : Orientation ℝ F ι)
  {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
    (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)} (hg : Submodule.span K {g} = ⊤)
  {p m : ℕ} (h : finrank ℝ F + p = m)

include hg in
/-- The homology Thom map of the tautological Thom class over the orientation cover is
bijective. -/
private theorem bijective_homologyThomMap_tautological :
    Function.Bijective (homologyThomMap F
      ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) (ModuleCat.of K K)
      (finrank ℝ F) p m h
      ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g)).hom :=
  bijective_homologyThomMap p m h
    ((tautologicalOrientation (F := F) (E := E) (ι := ι)).isThomClass_thomClassOfModel hι ω hg)

include hg in
/-- **The Thom isomorphism on the orientation cover, restricted to deck invariants.** Let `E → B`
be a real vector bundle, and `u` the Thom class, with coefficients in a commutative ring `K`, of the
tautological orientation of the pull-back `E'` of `E` to its orientation cover `B'`. The homology
Thom map `x ↦ π_*(x ⌢ u)` restricts to an isomorphism from the classes of `Hₘ(E', E'₀; K)` fixed
by the lifted deck involution onto the classes of `Hₚ(B'; K)`, `m = rank + p`, that the deck
involution negates. -/
def homologyThomMapDeckEquiv :
    LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom -
        LinearMap.id) ≃ₗ[K]
      LinearMap.ker ((((singularHomologyFunctor (ModuleCat.{w} K) p).obj
          (ModuleCat.of K K)).map
        (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) :
          C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)))).hom +
        LinearMap.id) := by
  let Φ := LinearEquiv.ofBijective _
    (bijective_homologyThomMap_tautological (F := F) (E := E) (ι := ι) hι ω hg h)
  refine Φ.ofSubmodules _ _ ?_
  -- `Φ ∘ S = -(T ∘ Φ)` for the deck actions `S` upstairs and `T` downstairs, so `Φ` carries the
  -- fixed points of `S` onto the classes negated by `T`.
  have hrel (x) : Φ ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom
      x) = -(((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) :
          C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι)))).hom (Φ x) :=
    congr($(singularHomologyMap_deckThomPairMap_comp_homologyThomMap hι ω g
      (ModuleCat.of K K) h).hom x)
  ext w
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← neg_eq_iff_add_eq_zero, ← hrel, hx]
  · intro hw
    obtain ⟨x, rfl⟩ := Φ.surjective w
    exact ⟨x, Φ.injective ((hrel x).trans (neg_eq_iff_add_eq_zero.2 hw)), rfl⟩

include hg in
-- Not a simp lemma: simplifying the coercion of the bundled projection changes the implicit
-- pull-back bundle in the left-hand side, so it is not in simp normal form.
/-- The isomorphism `homologyThomMapDeckEquiv` is the homology Thom map. -/
theorem coe_homologyThomMapDeckEquiv_apply
    (x : LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι)
      (ModuleCat.of K K) m).hom - LinearMap.id)) :
    ↑(homologyThomMapDeckEquiv hι ω hg h x) =
      (homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (ModuleCat.of K K) (finrank ℝ F) p m h
        ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g)).hom ↑x :=
  (rfl)

end CommRing

section UnitsAction

/-! ### The action of `ℤˣ` on the Thom pair of the pull-back -/

/-- The action `thomPairFstMulAction` of `ℤˣ` on the total space of the Thom pair of the pull-back
of `E` to the orientation cover. -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction

/-- The action `thomPairSndMulAction` of `ℤˣ` on the nonzero vectors of the Thom pair of the
pull-back of `E` to the orientation cover. -/
local instance : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd :=
  thomPairSndMulAction

/-- The action of `ℤˣ` on the total space of the Thom pair of the pull-back is continuous
(`continuousConstSMul_thomPairFst`). -/
local instance : ContinuousConstSMul ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  continuousConstSMul_thomPairFst

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The unit `-1` acts on the total space of the Thom pair of the pull-back of `E` to the
orientation cover by the lifted deck involution `deckThomPairMap`. -/
theorem neg_one_smul_eq_deckThomPairMap_fst
    (v : (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst) :
    (-1 : ℤˣ) • v = TopPair.Hom.fst (deckThomPairMap F E ι) v := by
  refine Eq.trans ?_ (deckThomPairMap_fst_apply v).symm
  exact TotalSpace.ext ((proj_smul_totalSpace (-1) v).trans
    ((neg_one_smul_eq_deck v.proj).trans (deck_apply v.proj))) HEq.rfl

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- The action of `-1` on the total space of the Thom pair of the pull-back of `E` to the
orientation cover, as a morphism of topological spaces, is the lifted deck involution. -/
theorem ofHom_neg_one_smul_eq_deckThomPairMap_fst :
    TopCat.ofHom ⟨((-1 : ℤˣ) • · :
        (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst →
          (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst),
        continuous_const_smul _⟩ =
      TopPair.Hom.fst (deckThomPairMap F E ι) :=
  TopCat.ext neg_one_smul_eq_deckThomPairMap_fst

include hι

variable (F E ι) in
/-- The map of total spaces of `(E', E'₀) ⟶ (E, E₀)` is the quotient covering map of the action
`thomPairFstMulAction` of `ℤˣ`: `isQuotientCoveringMap_pullbackThomPairMap_fst`, restated for
`coverThomPairMap`, whose Thom pair reads the zeros of the fibres through their module
structure. -/
theorem isQuotientCoveringMap_coverThomPairMap_fst :
    IsQuotientCoveringMap (TopPair.Hom.fst (coverThomPairMap F E ι)) ℤˣ := by
  rw [coverThomPairMap_eq_pullbackThomPairMap]
  exact isQuotientCoveringMap_pullbackThomPairMap_fst hι

variable (F E ι) in
/-- The map of nonzero vectors of `(E', E'₀) ⟶ (E, E₀)` is the quotient covering map of the action
`thomPairSndMulAction` of `ℤˣ`: `isQuotientCoveringMap_pullbackThomPairMap_snd`, restated for
`coverThomPairMap`. -/
theorem isQuotientCoveringMap_coverThomPairMap_snd :
    IsQuotientCoveringMap (TopPair.Hom.snd (coverThomPairMap F E ι)) ℤˣ := by
  rw [coverThomPairMap_eq_pullbackThomPairMap]
  exact isQuotientCoveringMap_pullbackThomPairMap_snd hι

end UnitsAction

end TauCeti.VectorBundleOrientationCover
