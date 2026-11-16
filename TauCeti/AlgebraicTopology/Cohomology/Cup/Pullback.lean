/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Point

/-!
# The cup product with a relative class after pulling back

Let `P = (X, A)` be a topological pair, `g : X ⟶ Z` a map and `u ∈ Hⁿ(X, A; K)` a relative class
with coefficients in a commutative ring `K`. This file defines the map

`Hᵖ(Z; M) ⟶ Hᵐ(X, A; M)`,  `a ↦ g^*a ⌣ u`,  `p + n = m`,

(`TopPair.pullbackCup`), the pull-back along `g` followed by the cup product of absolute and
relative cohomology (`TopPair.singularCup`), for any `K`-module of coefficients `M`, and proves that
it is natural in maps of pairs (`TopPair.pullbackCup_naturality`). It sends the unit `1 ∈ H⁰(Z; K)`
to `u` (`TopPair.pullbackCup_one`), is bijective when `Z` is empty
(`TopPair.bijective_pullbackCup_of_isEmpty`), and its bijectivity is invariant under isomorphisms
(`TopPair.bijective_pullbackCup_iff_of_isIso`). Combined with graded commutativity and compatibility
of the connecting morphism with cup products, `δ (σ ⌣ (P.map ≫ g)^* c)` equals `(-1)^(p (q + 1))`
times `pullbackCup` of `δ σ` at `c`
(`TopPair.singularCohomologyδ_singularCup_eq_zsmul_pullbackCup`). For the Thom pair `(E, E₀)` of a
vector bundle and its projection, `pullbackCup` is the Thom map `TauCeti.thomMap`, which the Thom
isomorphism asserts to be bijective when `u` is a Thom class.

For a map `π : X ⟶ Y`, a subset `Z ⊆ X` and a subset `S ⊆ Y`, restricting `u ∈ Hⁿ(X, Z)` to the pair
`(π⁻¹ S, π⁻¹ S ∩ Z)` and `π` to `π⁻¹ S ⟶ S` gives the map over `S` (`TopCat.pullbackCupRestrict`).
It is natural in `S` (`TopCat.pullbackCupRestrict_naturality`), compatible with restriction from the
ambient base `Y` (`TopCat.pullbackCupRestrict_singularCohomologyMap_subtypeVal`), bijective over `∅`
(`TopCat.bijective_pullbackCupRestrict_empty`), and over the whole base it is
bijective exactly when `a ↦ π^*a ⌣ u` is (`TopCat.bijective_pullbackCupRestrict_univ_iff`).
For a vector bundle and `Z` its nonzero vectors, this pair is the Thom pair `(E|_S, E₀|_S)` of the
restriction of the bundle to `S`.

## Main definitions and results

* `TopPair.pullbackCup`: the map `a ↦ g^*a ⌣ u`, bilinear in `u` and `a`.
* `TopPair.pullbackCup_naturality`: its naturality in maps of pairs.
* `TopPair.pullbackCup_one`: `1 ↦ u`.
* `TopPair.bijective_pullbackCup_iff_of_isIso`, `TopPair.bijective_pullbackCup_of_isEmpty`:
  invariance of bijectivity under isomorphisms and bijectivity over an empty target.
* `TopPair.singularCohomologyδ_singularCup_eq_zsmul_pullbackCup`: `δ (σ ⌣ (P.map ≫ g)^* c) =
  (-1)^(p (q + 1)) • ((g^* c) ⌣ δ σ)`.
* `TopCat.pullbackCupRestrict`: the map over a subset of the base.
* `TopCat.pullbackCupRestrict_naturality`,
  `TopCat.pullbackCupRestrict_singularCohomologyMap_subtypeVal`: naturality in the subset and
  compatibility with restriction from `Y`.
* `TopCat.bijective_pullbackCupRestrict_univ_iff`, `TopCat.bijective_pullbackCupRestrict_empty`:
  bijectivity over `Set.univ` and `∅`.
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

/-- **The connecting morphism on `σ ⌣ (P.map ≫ g)^* c`.** For a pair `P`, a map `g : P.fst ⟶ Z`,
and `σ ∈ H^q(P.snd; K)`, the connecting morphism takes `σ ⌣ (P.map ≫ g)^* c` to `(-1)^(p (q + 1))`
times `P.pullbackCup` of `δ σ` at `c`. -/
theorem singularCohomologyδ_singularCup_eq_zsmul_pullbackCup (M : ModuleCat.{w} K)
    (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) {q q' p n m : ℕ}
    (h : p + q = n) (hq : q + 1 = q') (hm : n + 1 = m) (h' : p + q' = m)
    (σ : P.snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q)
    (c : Z.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p) :
    P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m hm
        (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p n (by omega) σ
          (TopCat.singularCohomologyMap (P.map ≫ g) p c)) =
      ((-1 : ℤ) ^ (p * q')) • P.pullbackCup M g q' p m h'
        (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q q' hq σ) c := by
  subst hq
  have hu : (λ_ (𝟙_ (ModuleCat.{w} K))).inv ≫
      (β_ (𝟙_ (ModuleCat.{w} K)) (𝟙_ (ModuleCat.{w} K))).hom =
      (λ_ (𝟙_ (ModuleCat.{w} K))).inv := by
    rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal]
  have hμ : (β_ M (𝟙_ (ModuleCat.{w} K))).hom ≫ (λ_ M).hom = (ρ_ M).hom := by
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
    P.snd.singularCup_gradedComm K hu hμ h, map_zsmul,
    P.singularCohomologyδ_singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom h rfl hm h',
    smul_smul, TopPair.pullbackCup_apply]
  have hexp : (-1 : ℤ) ^ (p * q) * (-1 : ℤ) ^ p = (-1 : ℤ) ^ (p * (q + 1)) := by
    rw [mul_add, mul_one, pow_add]
  rw [hexp]

/-- When the target `Z` is empty, `a ↦ g^*a ⌣ u` is bijective in every degree because both domain
and codomain vanish. -/
theorem bijective_pullbackCup_of_isEmpty (P : TopPair.{w}) (M : ModuleCat.{w} K) {Z : TopCat.{w}}
    [IsEmpty Z] (g : P.fst ⟶ Z) {n p m : ℕ} (h : p + n = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (P.pullbackCup M g n p m h u) := by
  have : IsEmpty P.fst := ⟨fun x ↦ isEmptyElim (g x)⟩
  have : IsEmpty P.snd := ⟨fun x ↦ isEmptyElim (g (P.map x))⟩
  have : Subsingleton (Z.singularCohomology (ModuleCat.of K K) K M p) :=
    ModuleCat.subsingleton_of_isZero
      (TauCeti.isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M Z p)
  have : Subsingleton (P.singularCohomology (ModuleCat.of K K) K M m) :=
    ModuleCat.subsingleton_of_isZero
      ((TauCeti.isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M P.fst m).of_iso
        (asIso (P.singularCohomologyπ (ModuleCat.of K K) K M m)))
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

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

/-- **Compatibility of `pullbackCupRestrict` with `pullbackCup` under restriction from `Y` to `S`**:
evaluating the map over `S` at the restriction of `a ∈ Hᵖ(Y; M)` agrees with restricting `π^*a ⌣ u`
to `(π⁻¹ S, π⁻¹ S ∩ Z)`. -/
theorem pullbackCupRestrict_singularCohomologyMap_subtypeVal (S : Set Y) {n p m : ℕ}
    (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Y.singularCohomology (ModuleCat.of K K) K M p) :
    pullbackCupRestrict π Z M S n p m h u
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal S)) p a) =
      TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) m
        ((TopPair.ofSubset Z).pullbackCup M π n p m h u a) := by
  have hg : TopPair.Hom.fst (restrictPreimagePairMap π Z S) ≫ π =
      ofHom (π.hom.restrictPreimage S) ≫ ofHom (ContinuousMap.subtypeVal S) :=
    TopCat.ext fun v ↦ congrArg π (restrictPreimagePairMap_fst_apply π Z S v)
  rw [pullbackCupRestrict_apply]
  exact TopPair.pullbackCup_naturality (restrictPreimagePairMap π Z S)
    (ofHom (π.hom.restrictPreimage S)) π (ofHom (ContinuousMap.subtypeVal S)) hg h u a

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

/-- Over the empty subset `∅ ⊆ Y`, the map over `S` of `u` is bijective in every degree because both
domain and codomain vanish. -/
theorem bijective_pullbackCupRestrict_empty {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (pullbackCupRestrict π Z M ∅ n p m h u) := by
  have : IsEmpty (of ↥(∅ : Set Y)) := inferInstanceAs (IsEmpty ↥(∅ : Set Y))
  rw [pullbackCupRestrict_apply]
  exact TopPair.bijective_pullbackCup_of_isEmpty _ M _ h _

end TopCat
