/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The cup product with a relative class after pulling back

Let `P = (X, A)` be a topological pair, `g : X ⟶ Z` a map and `u ∈ Hⁿ(X, A; K)` a relative class
with coefficients in a commutative ring `K`. This file defines the map

`Hᵖ(Z; M) ⟶ Hᵐ(X, A; M)`,  `a ↦ g^*a ⌣ u`,  `p + n = m`,

(`TopPair.pullbackCup`), the pull-back along `g` followed by the cup product of absolute and
relative cohomology (`TopPair.singularCup`), for any `K`-module of coefficients `M`, and proves that
it is natural in maps of pairs (`TopPair.pullbackCup_naturality`). It sends the unit `1 ∈ H⁰(Z; K)`
to `u` (`TopPair.pullbackCup_one`), and its bijectivity is invariant under isomorphisms
(`TopPair.bijective_pullbackCup_iff_of_isIso`). For the Thom pair `(E, E₀)` of a vector bundle and
its projection, it is the Thom map `TauCeti.thomMap`, which the Thom isomorphism asserts to be
bijective when `u` is a Thom class.

For a map `π : X ⟶ Y`, a subset `Z ⊆ X` and a subset `S ⊆ Y`, restricting `u ∈ Hⁿ(X, Z)` to the pair
`(π⁻¹ S, π⁻¹ S ∩ Z)` and `π` to `π⁻¹ S ⟶ S` gives the map over `S` (`TopCat.pullbackCupRestrict`).
It is natural in `S` (`TopCat.pullbackCupRestrict_naturality`), and over the whole base it is
bijective exactly when `a ↦ π^*a ⌣ u` is (`TopCat.bijective_pullbackCupRestrict_univ_iff`).
For a vector bundle and `Z` its nonzero vectors, this pair is the Thom pair `(E|_S, E₀|_S)` of the
restriction of the bundle to `S`.

## Main definitions and results

* `TopPair.pullbackCup`: the map `a ↦ g^*a ⌣ u`, bilinear in `u` and `a`.
* `TopPair.pullbackCup_naturality`: its naturality in maps of pairs.
* `TopPair.pullbackCup_one`: `1 ↦ u`.
* `TopPair.bijective_pullbackCup_iff_of_isIso`: invariance of bijectivity under isomorphisms.
* `TopCat.pullbackCupRestrict`: the map over a subset of the base.
* `TopCat.pullbackCupRestrict_naturality`: its naturality in the subset.
* `TopCat.bijective_pullbackCupRestrict_univ_iff`: over the whole base it is `a ↦ π^*a ⌣ u`.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe w

namespace TopPair

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- For a pair `P = (X, A)`, a map `g : X ⟶ Z` and a class `u ∈ Hⁿ(X, A; K)`, the map
`Hᵖ(Z; M) ⟶ Hᵐ(X, A; M)`, `a ↦ g^*a ⌣ u`, `p + n = m`, as a `K`-bilinear map of `u` and `a`. The
chain coefficients are `K`, and the pairing of values is the right unitor `M ⊗ K ≅ M`. -/
def pullbackCup (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) (n p m : ℕ) (h : p + n = m) :
    P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      Z.singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        P.singularCohomology (ModuleCat.of K K) K M m :=
  (P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h ∘ₗ
    (TopCat.singularCohomologyMap g p).hom).flip

variable {M}

/-- The map `a ↦ g^*a ⌣ u` is the cup product of the pull-back of `a` with `u`. -/
theorem pullbackCup_apply (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) {n p m : ℕ}
    (h : p + n = m) (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Z.singularCohomology (ModuleCat.of K K) K M p) :
    P.pullbackCup M g n p m h u a =
      P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap g p a) u :=
  (rfl)

/-- **Naturality of `a ↦ g^*a ⌣ u`.** For a map of pairs `φ : P ⟶ P'` and maps `g : P.fst ⟶ Z`,
`g' : P'.fst ⟶ Z'` and `f : Z ⟶ Z'` with `φ ≫ g' = g ≫ f` on the ambient spaces,
`g^*(f^*a) ⌣ φ^*u = φ^*(g'^*a ⌣ u)`. -/
theorem pullbackCup_naturality {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    (g : P.fst ⟶ Z) (g' : P'.fst ⟶ Z') (f : Z ⟶ Z') (hg : Hom.fst φ ≫ g' = g ≫ f) {n p m : ℕ}
    (h : p + n = m) (u : P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Z'.singularCohomology (ModuleCat.of K K) K M p) :
    P.pullbackCup M g n p m h (TopPair.singularCohomologyMap φ n u)
        (TopCat.singularCohomologyMap f p a) =
      TopPair.singularCohomologyMap φ m (P'.pullbackCup M g' n p m h u a) := by
  rw [pullbackCup_apply, pullbackCup_apply, ← TopPair.singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, ← hg,
    TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
  -- The two sides agree up to how the module morphisms are coerced to functions.
  rfl

/-- **`a ↦ g^*a ⌣ u` sends `1` to `u`**: the image of the class of the constant `0`-cocycle with
value `1 ∈ K` is `u`. -/
@[simp]
theorem pullbackCup_one (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) {n : ℕ}
    (h : 0 + n = n) (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.pullbackCup (ModuleCat.of K K) g n 0 n h u
        ((Z.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ 0
          (Z.constSingularCocycle K (𝟙 (ModuleCat.of K K)))) = u := by
  rw [pullbackCup_apply]
  refine (congrArg (fun x ↦ P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
    (ρ_ (ModuleCat.of K K)).hom 0 n n h x u)
    (TopCat.singularCohomologyMap_homologyπ_constSingularCocycle g K
      (𝟙 (ModuleCat.of K K)))).trans ?_
  exact P.singularCup_constSingularCocycle_left K (η := 𝟙 _) (by monoidal) (by monoidal) h u

/-- Bijectivity of `a ↦ g^*a ⌣ u` is invariant under isomorphisms `φ : P ⟶ P'` of pairs and
`f : Z ⟶ Z'` of targets with `φ ≫ g' = g ≫ f` on the ambient spaces. -/
theorem bijective_pullbackCup_iff_of_isIso {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    {g : P.fst ⟶ Z} {g' : P'.fst ⟶ Z'} (f : Z ⟶ Z') [IsIso φ] [IsIso f]
    (hg : Hom.fst φ ≫ g' = g ≫ f) {n p m : ℕ} (h : p + n = m)
    (u : P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (P.pullbackCup M g n p m h (TopPair.singularCohomologyMap φ n u)) ↔
      Function.Bijective (P'.pullbackCup M g' n p m h u) := by
  have hf : Function.Bijective (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := M) f p) :=
    ((TauCeti.singularCohomologyFunctor _ K _ p).mapIso (asIso f).op).toLinearEquiv.bijective
  have hφ : Function.Bijective (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := M) φ m) :=
    ((TopPair.singularCohomologyFunctor _ K _ m).mapIso (asIso φ).op).toLinearEquiv.bijective
  have hc : ⇑(P.pullbackCup M g n p m h (TopPair.singularCohomologyMap φ n u)) ∘
      TopCat.singularCohomologyMap f p =
        TopPair.singularCohomologyMap φ m ∘ P'.pullbackCup M g' n p m h u :=
    funext fun a ↦ pullbackCup_naturality φ g g' f hg h u a
  constructor
  · intro h'
    have := h'.comp hf
    rw [hc] at this
    exact (Function.Bijective.of_comp_iff' hφ _).1 this
  · intro h'
    have := hφ.comp h'
    rw [← hc] at this
    exact (Function.Bijective.of_comp_iff _ hf).1 this

end TopPair

namespace TopCat

variable {K : Type w} [CommRing K] {X Y : TopCat.{w}} (π : X ⟶ Y) (Z : Set X)
  (M : ModuleCat.{w} K)

/-- The map `a ↦ π^*a ⌣ u` over a subset `S` of the base: the map `TopPair.pullbackCup` of the
restriction of `u ∈ Hⁿ(X, Z)` to the pair `(π⁻¹ S, π⁻¹ S ∩ Z)` and of the restriction
`π⁻¹ S ⟶ S` of `π`, from `Hᵖ(S; M)` to `Hᵐ(π⁻¹ S, π⁻¹ S ∩ Z; M)`. -/
def pullbackCupRestrict (S : Set Y) (n p m : ℕ) (h : p + n = m) :
    (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (of S).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).singularCohomology
          (ModuleCat.of K K) K M m :=
  (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).pullbackCup M
      (ofHom (π.hom.restrictPreimage S)) n p m h ∘ₗ
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n).hom

/-- The map over `S` is `TopPair.pullbackCup` composed with the restriction to the pair over `S`. -/
theorem pullbackCupRestrict_def (S : Set Y) (n p m : ℕ) (h : p + n = m) :
    pullbackCupRestrict π Z M S n p m h =
      (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).pullbackCup M
          (ofHom (π.hom.restrictPreimage S)) n p m h ∘ₗ
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n).hom :=
  (rfl)

/-- The map over `S` of `u` is `TopPair.pullbackCup` of the restriction of `u` to the pair over
`S`. -/
theorem pullbackCupRestrict_apply (S : Set Y) {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    pullbackCupRestrict π Z M S n p m h u =
      (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).pullbackCup M
        (ofHom (π.hom.restrictPreimage S)) n p m h
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n u) :=
  (rfl)

/-- **Naturality of the map over a subset of the base in the subset.** For `S ⊆ T`, the map over
`S` of `u` at the restriction of `a ∈ Hᵖ(T; M)` to `S` is the restriction to the pair over `S` of
the map over `T` of `u` at `a`. -/
theorem pullbackCupRestrict_naturality {S T : Set Y} (hST : S ⊆ T) {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (of T).singularCohomology (ModuleCat.of K K) K M p) :
    pullbackCupRestrict π Z M S n p m h u
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion hST)) p a) =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap
        (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S) Set.inter_subset_left
        (ContinuousMap.inclusion (Set.preimage_mono hST)) fun _ hx ↦ ⟨hST hx.1, hx.2⟩) m
        (pullbackCupRestrict π Z M T n p m h u a) := by
  have hg : TopPair.Hom.fst (TopPair.ofInclusionMap
      (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S) Set.inter_subset_left
      (ContinuousMap.inclusion (Set.preimage_mono hST)) fun _ hx ↦ ⟨hST hx.1, hx.2⟩) ≫
        ofHom (π.hom.restrictPreimage T) =
      ofHom (π.hom.restrictPreimage S) ≫ ofHom (ContinuousMap.inclusion hST) :=
    TopCat.ext fun x ↦ Subtype.ext (congrArg (fun y : ↥(π ⁻¹' T) ↦ π y.1)
      (TopPair.ofInclusionMap_fst_apply _ _ x))
  rw [pullbackCupRestrict_apply, pullbackCupRestrict_apply,
    ← ofInclusionMap_inclusion_comp_restrictPreimagePairMap π Z hST,
    TopPair.singularCohomologyMap_comp_apply, TopPair.pullbackCup_naturality _ _ _ _ hg]

/-- Over the whole base, the map over `S` of `u` is bijective exactly when `a ↦ π^*a ⌣ u` is. -/
theorem bijective_pullbackCupRestrict_univ_iff {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (pullbackCupRestrict π Z M Set.univ n p m h u) ↔
      Function.Bijective ((TopPair.ofSubset Z).pullbackCup M π n p m h u) := by
  have := isIso_restrictPreimagePairMap π Z (S := Set.univ) fun _ ↦ Set.mem_univ _
  rw [pullbackCupRestrict_apply]
  exact TopPair.bijective_pullbackCup_iff_of_isIso (restrictPreimagePairMap π Z Set.univ)
    (isoOfHomeo (Homeomorph.Set.univ Y)).hom
    (TopCat.ext fun x ↦ congrArg π (restrictPreimagePairMap_fst_apply π Z Set.univ x)) h u

end TopCat
