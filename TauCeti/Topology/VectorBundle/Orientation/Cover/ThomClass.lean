/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Proper
public import TauCeti.Topology.VectorBundle.Orientation.Tautological
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Bijective
public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Thom.Homology
public import TauCeti.Topology.VectorBundle.Thom.RankZero

/-!
# The Thom class of a bundle pulled back to its orientation cover

Let `E → B` be a real vector bundle of rank `r`, let `B' → B` be its orientation double cover
(`TauCeti.VectorBundleOrientationCover`), whose points are the pairs of a point `b` of `B` and an
orientation of `E_b`, and let `σ` be its deck involution, reversing the orientation
(`TauCeti.VectorBundleOrientationCover.deck`). The pull-back `E'` of `E` to `B'` is oriented by the
tautological orientation, which is the orientation recorded at each point of `B'`
(`TauCeti.VectorBundleOrientationCover.tautologicalOrientation`). Its fibre over `p` is
`E_{π p}`, which is also its fibre over `σ p`, so `σ` lifts to a map `δ` of Thom pairs
`(E', E'₀) ⟶ (E', E'₀)` covering `σ` and acting as the identity of `E_{π p}` on each fibre
(`TauCeti.VectorBundleOrientationCover.deckThomPairMap`). Since `σ` reverses the tautological
orientation, `δ` pulls the Thom class `U` of the tautological orientation, normalized by any class
`g ∈ Hʳ(F, F ∖ {0})` (`TauCeti.VectorBundleOrientation.thomClassOfModel`), back to `-U`
(`TauCeti.VectorBundleOrientationCover.singularCohomologyMap_deckThomPairMap_thomClassOfModel`).
So the homology Thom map `Φ(x) = π_*(x ⌢ U)` (`TauCeti.homologyThomMap`) anticommutes with the
two involutions, `Φ ∘ δ_* = -σ_* ∘ Φ`
(`TauCeti.VectorBundleOrientationCover.singularHomologyMap_deckThomPairMap_comp_homologyThomMap`).

Over a compact base, in rank other than one and with coefficients in a field `K`, `Φ` is bijective
when `g` generates `Hʳ(F, F ∖ {0}; K)`, by the Thom isomorphism. It therefore carries the classes
of `Hₚ₊ᵣ(E', E'₀; K)` fixed by `δ_*` isomorphically onto the classes of `Hₚ(B'; K)` negated by `σ_*`
(`TauCeti.VectorBundleOrientationCover.map_ker_singularHomologyMap_deckThomPairMap_sub_one` and
`TauCeti.VectorBundleOrientationCover.deckHomologyThomEquiv`). This is the part of the Thom
isomorphism of a bundle that need not be orientable, with coefficients twisted by its orientation
system, `Hₚ₊ᵣ(E, E₀; K) ≅ Hₚ(B; o(E) ⊗ K)` when `2 ≠ 0` in `K`, that takes place on the orientation
cover. The transfer of the double cover identifies the `δ_*`-invariant classes with
`Hₚ₊ᵣ(E, E₀; K)` and the `σ_*`-anti-invariant classes with `Hₚ(B; o(E) ⊗ K)`; neither
identification is proved in this file. In rank one the homology Thom map is not known here to be
bijective, so the statements over a field exclude it.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.deckThomPairMap`: the lift `δ` of the deck involution to
  the Thom pair of the pulled-back bundle.
* `TauCeti.VectorBundleOrientationCover.deckHomologyThomEquiv`: the Thom isomorphism from the
  `δ_*`-invariant classes of `Hₚ₊ᵣ(E', E'₀; K)` to the `σ_*`-anti-invariant classes of `Hₚ(B'; K)`.

## Main results

* `TauCeti.VectorBundleOrientationCover.singularCohomologyMap_deckThomPairMap_thomClassOfModel`:
  `δ^* U = -U`.
* `TauCeti.VectorBundleOrientationCover.singularHomologyMap_deckThomPairMap_comp_homologyThomMap`:
  `Φ ∘ δ_* = -σ_* ∘ Φ`.
* `TauCeti.VectorBundleOrientationCover.map_ker_singularHomologyMap_deckThomPairMap_sub_one`:
  over a field, `Φ` carries the `δ_*`-invariant classes onto the `σ_*`-anti-invariant classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (orientations and the orientation double cover) and §10 (the Thom class of
  an oriented bundle and the Thom isomorphism).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (the orientation
  double cover and homology with local coefficients) and Section 4.D (the Thom isomorphism).
-/

public section

noncomputable section

open Bundle CategoryTheory Module AlgebraicTopology

universe w

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type}

/-- The deck involution, with values the explicit points `⟨p.proj, -p.orientation⟩`, so that
the fibre of the pulled-back bundle at `deck p` is definitionally that at `p`. -/
private def deckMap : C(VectorBundleOrientationCover F E ι, VectorBundleOrientationCover F E ι) :=
  ⟨fun p ↦ ⟨p.proj, -p.orientation⟩, deck.continuous.congr deck_apply⟩

private theorem deckMap_eq : (deckMap : C(VectorBundleOrientationCover F E ι, _)) =
    (deck (F := F) (E := E) (ι := ι) : C(_, _)) :=
  ContinuousMap.ext fun p ↦ (deck_apply p).symm

/-- The fibres of the pulled-back bundle at `p` and at `deckMap p` are both `E p.proj`. -/
private abbrev deckFiberEquiv (p : VectorBundleOrientationCover F E ι) :
    ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) p ≃L[ℝ]
      ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) (deckMap p) :=
  ContinuousLinearEquiv.refl ℝ (E p.proj)

/-- The identity of `E p.proj`, from the fibre at `p` to the fibre at `deckMap p`, carries the
tautological orientation at `p` to the opposite of the one at `deckMap p`. -/
private theorem map_deckFiberEquiv_tautologicalOrientation
    (p : VectorBundleOrientationCover F E ι) :
    Orientation.map ι (deckFiberEquiv p).toLinearEquiv (tautologicalOrientation p) =
      -tautologicalOrientation (deckMap p) := by
  -- Both fibres of the pulled-back bundle are `E p.proj` only after unfolding the pull-back, and
  -- `deckMap p` has orientation `-p.orientation` by definition, so restate the goal in `E p.proj`.
  change Orientation.map ι (LinearEquiv.refl ℝ (E p.proj)) (tautologicalOrientation p) =
    -tautologicalOrientation (deckMap p)
  rw [Orientation.map_refl, tautologicalOrientation_apply, tautologicalOrientation_apply]
  exact (neg_neg (G := Orientation ℝ (E p.proj) ι) _).symm

private theorem continuous_deckMap_totalSpace :
    Continuous fun v : TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) ↦
      TotalSpace.mk' F (deckMap v.proj) (deckFiberEquiv v.proj v.2) := by
  refine (inducing_pullbackTotalSpaceEmbedding F E _).continuous_iff.2 ?_
  exact (deckMap.continuous.comp (Pullback.continuous_proj F E _)).prodMk
    (Pullback.continuous_lift F E _)

/-- The deck involution of the orientation cover lifted to the Thom pair of the pulled-back
bundle. -/
def deckThomPairMap :
    thomPair F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) ⟶
      thomPair F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) :=
  thomPairMapOfFiberwise continuous_deckMap_totalSpace

/-- The lifted deck involution covers the deck involution of the orientation cover. -/
theorem deckThomPairMap_fst_comp_thomPairProj :
    TopPair.Hom.fst (deckThomPairMap (F := F) (E := E) (ι := ι)) ≫
        thomPairProj F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) =
      thomPairProj F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) ≫
        TopCat.ofHom (deck (F := F) (E := E) (ι := ι) : C(_, _)) := by
  rw [← deckMap_eq]
  exact thomPairMapOfFiberwise_fst_comp_thomPairProj _

/-- The lifted deck involution sends a vector `v` over `p` to the same vector of `E_{π p}`, now
over the point `⟨π p, -p.orientation⟩`, which is `deck p` (`deck_apply`). -/
-- Not `@[simp]`: simp rewrites the coercion of the continuous map on the left-hand side, so the
-- statement is not in simp normal form.
theorem deckThomPairMap_fst_apply
    (v : TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)) :
    TopPair.Hom.fst (deckThomPairMap (F := F) (E := E) (ι := ι)) v =
      TotalSpace.mk' F (⟨v.proj.proj, -v.proj.orientation⟩ : VectorBundleOrientationCover F E ι)
        v.2 :=
  thomPairMapOfFiberwise_fst_apply continuous_deckMap_totalSpace v

/-- The lifted deck involution is an involution. -/
@[simp]
theorem deckThomPairMap_comp_self :
    deckThomPairMap (F := F) (E := E) (ι := ι) ≫ deckThomPairMap = 𝟙 _ := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun
    (v : TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)) ↦ ?_)
  -- The carrier of the Thom pair is the total space only up to unfolding, so first state the goal
  -- on the total space.
  change TopPair.Hom.fst (deckThomPairMap (F := F) (E := E) (ι := ι))
    (TopPair.Hom.fst deckThomPairMap v) = v
  simp only [deckThomPairMap_fst_apply]
  exact congrArg (fun o : Orientation ℝ (E v.proj.proj) ι ↦
    (TotalSpace.mk' F ⟨v.proj.proj, o⟩ v.2 :
      TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)))
    (neg_neg (G := Orientation ℝ (E v.proj.proj) ι) _)

variable [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι)

section Cohomology

variable {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K} [Module.Projective K R']
  (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
    (finrank ℝ F))

open VectorBundleOrientation in
/-- **The deck involution reverses the Thom class of the tautological orientation**: the lift `δ`
of the deck involution to the Thom pair of the pulled-back bundle pulls the class
`thomClassOfModel hι ω g` of the tautological orientation back to its negative. -/
theorem singularCohomologyMap_deckThomPairMap_thomClassOfModel :
    TopPair.singularCohomologyMap deckThomPairMap _
        ((tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g) =
      -(tautologicalOrientation (F := F) (E := E) (ι := ι)).thomClassOfModel hι ω g := by
  refine singularCohomologyMap_thomPairMapOfFiberwise_thomClassOfModel_of_map_eq_neg
    hι _ _ ω g continuous_deckMap_totalSpace map_deckFiberEquiv_tautologicalOrientation

end Cohomology

section Homology

variable {K : Type w} [CommRing K]
  {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology (ModuleCat.of K K) K
    (ModuleCat.of K K) (finrank ℝ F)}

/-- **The homology Thom map of the tautological orientation anticommutes with the deck
involution**: `Φ(δ_* x) = -deck_*(Φ x)` for the Thom map `Φ` of the Thom class of the tautological
orientation and the lift `δ` of the deck involution to the Thom pair. -/
theorem singularHomologyMap_deckThomPairMap_comp_homologyThomMap (A : ModuleCat.{w} K)
    {p m : ℕ} (h : finrank ℝ F + p = m) :
    TopPair.singularHomologyMap deckThomPairMap A m ≫
        homologyThomMap F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) A _ p m h
          (tautologicalOrientation.thomClassOfModel hι ω g) =
      -(homologyThomMap F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) A _ p m h
          (tautologicalOrientation.thomClassOfModel hι ω g) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
          (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) : C(_, _)))) := by
  rw [← homologyThomMap_naturality F _ _ _ deckThomPairMap_fst_comp_thomPairProj,
    singularCohomologyMap_deckThomPairMap_thomClassOfModel, map_neg, Preadditive.neg_comp]

end Homology

section Field

variable {K : Type w} [Field K]
  {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology (ModuleCat.of K K) K
    (ModuleCat.of K K) (finrank ℝ F)}

/-- Over a compact base, in rank other than one, the homology Thom map of the tautological
orientation is bijective with coefficients in a field. -/
private theorem bijective_homologyThomMap_tautologicalOrientation [CompactSpace B]
    (hF : finrank ℝ F ≠ 1) (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective
      (homologyThomMap F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)
        (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom := by
  have hU := (tautologicalOrientation (F := F) (E := E) (ι := ι)).isThomClass_thomClassOfModel hι ω
    hg
  rcases Nat.lt_or_ge (finrank ℝ F) 2 with hlt | hle
  · exact hU.bijective_homologyThomMap_of_finrank_eq_zero (by omega) h
  · have := compactSpace (E := E) hι
    exact hU.bijective_homologyThomMap hle h

/-- **The Thom isomorphism carries deck-invariant classes to deck-anti-invariant classes.** Over a
compact base, in rank other than one and with coefficients in a field `K`, the homology Thom map of
the tautological orientation carries the classes of `Hₘ(E', E'₀; K)` fixed by the lifted deck
involution `δ` onto the classes of `Hₚ(B'; K)` negated by the deck involution, `m = r + p`. -/
theorem map_ker_singularHomologyMap_deckThomPairMap_sub_one [CompactSpace B]
    (hF : finrank ℝ F ≠ 1) (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : finrank ℝ F + p = m) :
    (LinearMap.ker ((TopPair.singularHomologyMap deckThomPairMap (ModuleCat.of K K) m).hom -
        1)).map
      (homologyThomMap F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)
        (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom =
    LinearMap.ker ((((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) : C(VectorBundleOrientationCover F E ι,
          VectorBundleOrientationCover F E ι)))).hom + 1) := by
  set T := (homologyThomMap F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)
    (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom
  have hc (x) : T ((TopPair.singularHomologyMap deckThomPairMap (ModuleCat.of K K) m).hom x) =
      -(((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) : C(VectorBundleOrientationCover F E ι,
          VectorBundleOrientationCover F E ι)))).hom (T x) :=
    congr($(singularHomologyMap_deckThomPairMap_comp_homologyThomMap hι ω
      (ModuleCat.of K K) (g := g) h).hom x)
  have hT := bijective_homologyThomMap_tautologicalOrientation (E := E) hι ω hF hg h
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
    one_apply_eq_self, sub_eq_zero, add_eq_zero_iff_eq_neg]
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact neg_eq_iff_eq_neg.1 ((hx ▸ hc x).symm)
  · obtain ⟨x, rfl⟩ := hT.2 y
    exact ⟨x, hT.1 ((hc x).trans (neg_eq_iff_eq_neg.2 hy)), rfl⟩

/-- **The Thom isomorphism from deck-invariant to deck-anti-invariant classes.** Over a compact
base, in rank other than one and with coefficients in a field `K`, the homology Thom map of the
tautological orientation restricts to a linear isomorphism from the classes of `Hₘ(E', E'₀; K)`
fixed by the lifted deck involution onto the classes of `Hₚ(B'; K)` negated by the deck
involution, `m = r + p`. -/
def deckHomologyThomEquiv [CompactSpace B] (hF : finrank ℝ F ≠ 1)
    (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : finrank ℝ F + p = m) :
    LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap (F := F) (E := E) (ι := ι))
      (ModuleCat.of K K) m).hom - 1) ≃ₗ[K]
      LinearMap.ker ((((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) : C(VectorBundleOrientationCover F E ι,
          VectorBundleOrientationCover F E ι)))).hom + 1) :=
  (LinearEquiv.ofBijective
    (homologyThomMap F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)
      (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom
    (bijective_homologyThomMap_tautologicalOrientation (E := E) hι ω hF hg h)).ofSubmodules _ _
    (map_ker_singularHomologyMap_deckThomPairMap_sub_one hι ω hF hg h)

/-- The isomorphism `deckHomologyThomEquiv` is the homology Thom map of the tautological
orientation. -/
-- Not `@[simp]`: simp rewrites the coercion of `deck` to a continuous map inside the type of the
-- left-hand side, so the statement is not in simp normal form.
theorem coe_deckHomologyThomEquiv_apply [CompactSpace B] (hF : finrank ℝ F ≠ 1)
    (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : finrank ℝ F + p = m)
    (x : LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap (F := F) (E := E) (ι := ι))
      (ModuleCat.of K K) m).hom - 1)) :
    (deckHomologyThomEquiv hι ω hF hg h x : ((singularHomologyFunctor (ModuleCat.{w} K) p).obj
        (ModuleCat.of K K)).obj (TopCat.of (VectorBundleOrientationCover F E ι))) =
      (homologyThomMap F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)
        (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom ↑x :=
  (rfl)

end Field

end TauCeti.VectorBundleOrientationCover
