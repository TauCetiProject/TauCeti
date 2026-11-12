/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import TauCeti.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Thom
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair

/-!
# The Mayer–Vietoris gluing step for the Thom map

Let `π : X ⟶ Y` be a map to a base, `Z ⊆ X` and `u ∈ Hⁿ(X, Z; K)` a relative class with
coefficients in a commutative ring `K`. For a subset `S ⊆ Y` of the base, the Thom map over `S`
(`TopCat.thomMapRestrict`, defined in `TauCeti.AlgebraicTopology.Cohomology.Cup.Thom`) is the map
`Hᵖ(S; M) ⟶ Hᵖ⁺ⁿ(π⁻¹ S, π⁻¹ S ∩ Z; M)`, `a ↦ π^*a ⌣ u|`. For a vector bundle and `Z` its nonzero
vectors, the pair `(π⁻¹ S, π⁻¹ S ∩ Z)` is the Thom pair `(E|_S, E₀|_S)` of the restriction of the
bundle to `S`.

The main result is the **Mayer–Vietoris gluing step** (`TopCat.bijective_thomMapRestrict_union`):
for open sets `U` and `V` of the base, if the Thom maps over `U`, `V` and `U ∩ V` are bijective in
degrees `p ≤ N`, and `Hⁿ⁻¹(π⁻¹(U ∩ V), π⁻¹(U ∩ V) ∩ Z; M)` vanishes, then the Thom map over
`U ∪ V` is bijective in degrees `p ≤ N`. This is the inductive step of the proof of the Thom
isomorphism by induction over finite unions of trivializing open sets (Milnor–Stasheff, proof of
Theorem 10.4; Hatcher, proof of Theorem 4D.10), where the vanishing below the rank is known.

The proof is the five lemma between the Mayer–Vietoris sequence of the cover `{U, V}` of the base
and the Mayer–Vietoris sequence of the pairs over `U` and over `V`
(`TopCat.singularCohomologyPairMayerVietoris_exact₁` and its companions). The Thom maps commute with
the restrictions by naturality, and with the connecting morphisms because
`δ (π^*a ⌣ u|) = δ (π^*a) ⌣ u = π^*(δ a) ⌣ u`, by
`TopCat.singularCohomologyPairMayerVietorisδ_singularCup` and the naturality of the absolute
connecting morphism. In degree `0` the Thom map hits no class in degree `n - 1`, which is why the
vanishing hypothesis appears. The step is first proved when `U ∪ V = Y`
(`TopCat.bijective_thomMap_of_union_eq_univ`), and the general case follows by restricting `π` over
`U ∪ V`.

## Main results

* `TopCat.bijective_thomMap_of_union_eq_univ`: the gluing step for an open cover of the base by two
  sets.
* `TopCat.bijective_thomMapRestrict_union`: the gluing step over the union of two open sets.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D, proof of Theorem 4D.10, and Section 3.1 (the Mayer–Vietoris sequences in cohomology).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w

namespace TopCat

variable {K : Type w} [CommRing K] {X Y : TopCat.{w}} (π : X ⟶ Y) (Z : Set X)

/-! ### The gluing step for an open cover of the base -/

section Gluing

variable {U V : Set Y}

/-- The inclusion of the union pair of the Mayer–Vietoris sequence of the pairs over `U` and `V`
into `(X, Z)`. -/
private def unionPairMap (U V : Set Y) :
    TopPair.ofInclusion (Set.union_subset_union
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)) ⟶ TopPair.ofSubset Z :=
  TopPair.ofHom (ofHom (ContinuousMap.subtypeVal _))
    (ofHom ⟨fun x ↦ ⟨x.1, x.2.elim (·.2) (·.2)⟩, by fun_prop⟩) (by ext; rfl)

@[simp]
private theorem unionPairMap_fst_apply (x : ↥(π ⁻¹' U ∪ π ⁻¹' V)) :
    TopPair.Hom.fst (unionPairMap π Z U V) x = x.1 :=
  (rfl)

private theorem isIso_unionPairMap (hUV : U ∪ V = Set.univ) : IsIso (unionPairMap π Z U V) := by
  have h : π ⁻¹' U ∪ π ⁻¹' V = Set.univ := by rw [← Set.preimage_union, hUV, Set.preimage_univ]
  have : IsIso (TopPair.Hom.fst (unionPairMap π Z U V)) := by
    have he : TopPair.Hom.fst (unionPairMap π Z U V) = (isoOfHomeo (X := of ↥(π ⁻¹' U ∪ π ⁻¹' V))
        (Y := X) ((Homeomorph.setCongr h).trans (Homeomorph.Set.univ X))).hom :=
      TopCat.ext fun _ ↦ rfl
    rw [he]
    exact Iso.isIso_hom _
  refine TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun z ↦ ?_
  have hz : π z.1 ∈ U ∪ V := hUV ▸ Set.mem_univ _
  exact ⟨⟨z.1, hz.elim (fun h ↦ Or.inl ⟨h, z.2⟩) fun h ↦ Or.inr ⟨h, z.2⟩⟩, rfl⟩

/-- The intersection pair of the Mayer–Vietoris sequence of the pairs over `U` and `V` is the pair
over `U ∩ V`. -/
private def interPairIso (U V : Set Y) :
    TopPair.ofInclusion (Set.inter_subset_inter
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)) ≅
      TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' (U ∩ V) ∩ Z ⊆ π ⁻¹' (U ∩ V)) where
  hom := TopPair.ofHom (ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (ofHom (ContinuousMap.inclusion fun _ h ↦ ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩)) (by ext; rfl)
  inv := TopPair.ofHom (ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (ofHom (ContinuousMap.inclusion fun _ h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2, h.2⟩)) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

variable (M : ModuleCat.{w} K) (U V)

/-- The Thom map on the union pair of the Mayer–Vietoris sequence of the pairs over `U` and `V`. -/
private abbrev thomMapUnion (n p m : ℕ) (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :=
  (TopPair.ofInclusion (Set.union_subset_union
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))).thomMap M
    (ofHom (ContinuousMap.subtypeVal _) ≫ π) n p m h
    (TopPair.singularCohomologyMap (unionPairMap π Z U V) n u)

/-- The Thom map on the intersection pair of the Mayer–Vietoris sequence of the pairs over `U` and
`V`. -/
private abbrev thomMapInter (n p m : ℕ) (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :=
  (TopPair.ofInclusion (Set.inter_subset_inter
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))).thomMap M
    (ofHom ⟨((Set.mapsTo_preimage π U).inter_inter (Set.mapsTo_preimage π V)).restrict,
      π.hom.continuous.restrict _⟩) n p m h
    (TopPair.singularCohomologyMap (interToUnionMap
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)) n
      (TopPair.singularCohomologyMap (unionPairMap π Z U V) n u))

variable {U V}

/-- Restricted to the pair over a subset `S` of `U ∪ V`, the Thom map on the union pair is the Thom
map over `S`. -/
private theorem thomMapUnion_restrict {S : Set Y} (hS : π ⁻¹' S ⊆ π ⁻¹' U ∪ π ⁻¹' V)
    (hSZ : π ⁻¹' S ∩ Z ⊆ π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z) {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Y.singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap
        (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)
        (Set.union_subset_union (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))
        (ContinuousMap.inclusion hS) fun _ hx ↦ hSZ hx) m
        (thomMapUnion π Z U V M n p m h u a) =
      thomMapRestrict π Z M S n p m h u
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal S)) p a) := by
  have hφ : (TopPair.ofInclusionMap
        (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)
        (Set.union_subset_union (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))
        (ContinuousMap.inclusion hS) fun _ hx ↦ hSZ hx) ≫
      unionPairMap π Z U V = restrictPreimagePairMap π Z S :=
    TopPair.hom_ext_of_fst _ (by
      simp only [TopPair.Hom.fst_comp, TopPair.ofInclusionMap_fst,
        restrictPreimagePairMap_fst]
      exact TopCat.ext fun _ ↦ rfl)
  have hφπ : TopPair.Hom.fst (TopPair.ofInclusionMap
        (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)
        (Set.union_subset_union (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))
        (ContinuousMap.inclusion hS) fun _ hx ↦ hSZ hx) ≫ ofHom (ContinuousMap.subtypeVal _) ≫ π =
      ofHom (π.hom.restrictPreimage S) ≫ ofHom (ContinuousMap.subtypeVal S) := by
    rw [TopPair.ofInclusionMap_fst]
    exact TopCat.ext fun _ ↦ rfl
  rw [thomMapRestrict_apply, ← hφ, TopPair.singularCohomologyMap_comp_apply,
    TopPair.thomMap_naturality _ _ hφπ]

/-- Restricted from the pair over a subset `S` containing `U ∩ V` to the intersection pair, the
Thom map over `S` is the Thom map on the intersection pair. -/
private theorem thomMapRestrict_restrict_inter {S : Set Y} (hS : U ∩ V ⊆ S)
    (hSZ : (π ⁻¹' U ∩ Z) ∩ (π ⁻¹' V ∩ Z) ⊆ π ⁻¹' S ∩ Z) {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (of S).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap
        (Set.inter_subset_inter (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))
        (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)
        (ContinuousMap.inclusion (fun _ hx ↦ hS hx : π ⁻¹' U ∩ π ⁻¹' V ⊆ π ⁻¹' S))
        fun _ hx ↦ hSZ hx) m (thomMapRestrict π Z M S n p m h u a) =
      thomMapInter π Z U V M n p m h u
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion hS)) p a) := by
  have hφ : (TopPair.ofInclusionMap
        (Set.inter_subset_inter (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))
        (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)
        (ContinuousMap.inclusion (fun _ hx ↦ hS hx : π ⁻¹' U ∩ π ⁻¹' V ⊆ π ⁻¹' S))
        fun _ hx ↦ hSZ hx) ≫ restrictPreimagePairMap π Z S =
      interToUnionMap (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
        (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) ≫ unionPairMap π Z U V :=
    TopPair.hom_ext_of_fst _ (by
      simp only [TopPair.Hom.fst_comp, TopPair.ofInclusionMap_fst,
        restrictPreimagePairMap_fst]
      exact TopCat.ext fun _ ↦ rfl)
  have hφπ : TopPair.Hom.fst (TopPair.ofInclusionMap
        (Set.inter_subset_inter (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))
        (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)
        (ContinuousMap.inclusion (fun _ hx ↦ hS hx : π ⁻¹' U ∩ π ⁻¹' V ⊆ π ⁻¹' S))
        fun _ hx ↦ hSZ hx) ≫ ofHom (π.hom.restrictPreimage S) =
      ofHom ⟨((Set.mapsTo_preimage π U).inter_inter (Set.mapsTo_preimage π V)).restrict,
        π.hom.continuous.restrict _⟩ ≫ ofHom (ContinuousMap.inclusion hS) := by
    rw [TopPair.ofInclusionMap_fst]
    exact TopCat.ext fun _ ↦ rfl
  rw [thomMapRestrict_apply, ← TopPair.thomMap_naturality _ _ hφπ,
    ← TopPair.singularCohomologyMap_comp_apply, hφ, TopPair.singularCohomologyMap_comp_apply]

variable {M} in
/-- The Thom map on the intersection pair is the Thom map over `U ∩ V`, read through the
identification of the intersection pair with the pair over `U ∩ V`. -/
private theorem bijective_thomMapInter_iff {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapInter π Z U V M n p m h u) ↔
      Function.Bijective (thomMapRestrict π Z M (U ∩ V) n p m h u) := by
  have hu : TopPair.singularCohomologyMap (interToUnionMap
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)) n
      (TopPair.singularCohomologyMap (unionPairMap π Z U V) n u) =
      TopPair.singularCohomologyMap (interPairIso π Z U V).hom n
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z (U ∩ V)) n u) := by
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply]
    exact congrArg (fun f ↦ TopPair.singularCohomologyMap f n u)
      (TopPair.hom_ext_of_fst _ (by
        simp only [TopPair.Hom.fst_comp, TopPair.ofInclusionMap_fst,
        restrictPreimagePairMap_fst]
        exact TopCat.ext fun _ ↦ rfl))
  rw [thomMapInter, hu, LinearMap.ext (thomMapRestrict_apply π Z (U ∩ V) h u)]
  exact TopPair.bijective_thomMap_iff_of_isIso (π := ofHom (π.hom.restrictPreimage (U ∩ V)))
    (π' := ofHom ⟨((Set.mapsTo_preimage π U).inter_inter (Set.mapsTo_preimage π V)).restrict,
      π.hom.continuous.restrict _⟩) (interPairIso π Z U V).hom (𝟙 (of ↥(U ∩ V)))
    (TopCat.ext fun _ ↦ rfl) h
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z (U ∩ V)) n u)

variable {M} in
/-- The cohomology of the intersection pair is that of the pair over `U ∩ V`. -/
private theorem isZero_singularCohomology_interPair_iff (j : ℕ) :
    IsZero ((TopPair.ofInclusion (Set.inter_subset_inter
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))).singularCohomology
        (ModuleCat.of K K) K M j) ↔
      IsZero ((TopPair.ofInclusion (Set.inter_subset_left :
        π ⁻¹' (U ∩ V) ∩ Z ⊆ π ⁻¹' (U ∩ V))).singularCohomology (ModuleCat.of K K) K M j) :=
  Iso.isZero_iff ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K M j).mapIso
    (interPairIso π Z U V).op).symm

section Steps

variable (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
  (hA : IsOpen ((↑) ⁻¹' (π ⁻¹' U ∩ Z) : Set ↥(π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z)))
  (hB : IsOpen ((↑) ⁻¹' (π ⁻¹' V ∩ Z) : Set ↥(π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z)))

include hUV in
private theorem preimage_union_preimage_eq_univ : π ⁻¹' U ∪ π ⁻¹' V = Set.univ := by
  rw [← Set.preimage_union, hUV, Set.preimage_univ]

/-- The Thom maps commute with the Mayer–Vietoris connecting morphisms:
`δ (π^*a ⌣ u|) = δ (π^*a) ⌣ u = π^*(δ a) ⌣ u`. -/
private theorem pairMayerVietorisδ_thomMapInter {n l m' m : ℕ} (h : l + n = m') (hm : m' + 1 = m)
    (h' : l + 1 + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M l) :
    singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
        (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
        (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)
        ((hU.preimage π.hom.continuous).preimage continuous_subtype_val)
        ((hV.preimage π.hom.continuous).preimage continuous_subtype_val) hA hB m' m hm
        (thomMapInter π Z U V M n l m' h u a) =
      thomMapUnion π Z U V M n (l + 1) m h' u
        (singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV l (l + 1) rfl a) := by
  have hδ := ConcreteCategory.congr_hom (singularCohomologyMayerVietorisδ_naturality
    (ModuleCat.of K K) K M (hU.preimage π.hom.continuous) (hV.preimage π.hom.continuous)
    (preimage_union_preimage_eq_univ π hUV) hU hV hUV π (Set.mapsTo_preimage π U)
    (Set.mapsTo_preimage π V) l (l + 1)) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hδ
  -- The Thom map on the intersection pair is the cup product of `π^*a` with the restriction of
  -- `u`, so the cup-product form of the connecting morphism applies.
  have key := singularCohomologyPairMayerVietorisδ_singularCup (R := ModuleCat.of K K)
    (S := ModuleCat.of K K) (T := ModuleCat.of K K) K (hU.preimage π.hom.continuous)
    (hV.preimage π.hom.continuous) (preimage_union_preimage_eq_univ π hUV)
    (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
    (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) hA hB (λ_ (𝟙_ (ModuleCat.{w} K))).inv
    (ρ_ M).hom h rfl hm h' (TopCat.singularCohomologyMap (ofHom
      ⟨((Set.mapsTo_preimage π U).inter_inter (Set.mapsTo_preimage π V)).restrict,
        π.hom.continuous.restrict _⟩) l a)
    (TopPair.singularCohomologyMap (unionPairMap π Z U V) n u)
  refine (congrArg _ (TopPair.thomMap_apply _ _ h _ a)).trans (key.trans ?_)
  rw [← hδ, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp]
  exact (TopPair.thomMap_apply _ _ h' _ _).symm

variable {M} in
/-- The Thom maps commute with the second maps of the Mayer–Vietoris sequences, the differences of
the restrictions to `U ∩ V`. -/
private theorem fromBiprod_comp_thomMapInter {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M U V p ≫
        ConcreteCategory.ofHom (C := ModuleCat K) (thomMapInter π Z U V M n p m h u) =
      biprod.map (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M U n p m h u))
          (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M V n p m h u)) ≫
        singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
          (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) m := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [inl_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inl_map_assoc,
      inl_singularCohomologyPairMayerVietorisFromBiprod]
    ext a : 2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ConcreteCategory.hom_ofHom]
    exact (thomMapRestrict_restrict_inter π Z M Set.inter_subset_left
      Set.inter_subset_left h u a).symm
  · rw [inr_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inr_map_assoc,
      inr_singularCohomologyPairMayerVietorisFromBiprod, Preadditive.neg_comp,
      Preadditive.comp_neg]
    congr 1
    ext a : 2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ConcreteCategory.hom_ofHom]
    exact (thomMapRestrict_restrict_inter π Z M Set.inter_subset_right
      Set.inter_subset_right h u a).symm

variable {M} in
/-- The Thom maps commute with the first maps of the Mayer–Vietoris sequences, the restrictions to
`U` and to `V`. -/
private theorem toBiprod_comp_biprodMap {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M U V p ≫
        biprod.map (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M U n p m h u))
          (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M V n p m h u)) =
      ConcreteCategory.ofHom (C := ModuleCat K) (thomMapUnion π Z U V M n p m h u) ≫
        singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
          (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) m := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.map_fst, singularCohomologyMayerVietorisToBiprod_fst_assoc,
      Category.assoc, singularCohomologyPairMayerVietorisToBiprod_fst]
    ext a : 2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ConcreteCategory.hom_ofHom]
    exact (thomMapUnion_restrict π Z M (fun _ hx ↦ Or.inl hx)
      (fun _ hx ↦ Or.inl hx) h u a).symm
  · rw [Category.assoc, biprod.map_snd, singularCohomologyMayerVietorisToBiprod_snd_assoc,
      Category.assoc, singularCohomologyPairMayerVietorisToBiprod_snd]
    ext a : 2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ConcreteCategory.hom_ofHom]
    exact (thomMapUnion_restrict π Z M (fun _ hx ↦ Or.inr hx)
      (fun _ hx ↦ Or.inr hx) h u a).symm

include hU hV hUV hA hB in
/-- The gluing step in a positive degree `l + 1`, by the five lemma. -/
private theorem bijective_thomMapUnion_succ {n l m : ℕ} (h : l + 1 + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hU₁ : Function.Surjective (thomMapRestrict π Z M U n l (l + n) rfl u))
    (hV₁ : Function.Surjective (thomMapRestrict π Z M V n l (l + n) rfl u))
    (hUV₁ : Function.Bijective (thomMapInter π Z U V M n l (l + n) rfl u))
    (hU₂ : Function.Bijective (thomMapRestrict π Z M U n (l + 1) m h u))
    (hV₂ : Function.Bijective (thomMapRestrict π Z M V n (l + 1) m h u))
    (hUV₂ : Function.Injective (thomMapInter π Z U V M n (l + 1) m h u)) :
    Function.Bijective (thomMapUnion π Z U V M n (l + 1) m h u) := by
  have hU' := (hU.preimage π.hom.continuous).preimage
    (continuous_subtype_val (p := (· ∈ π ⁻¹' U ∪ π ⁻¹' V)))
  have hV' := (hV.preimage π.hom.continuous).preimage
    (continuous_subtype_val (p := (· ∈ π ⁻¹' U ∪ π ⁻¹' V)))
  have hm : l + n + 1 = m := by omega
  have : Epi (ConcreteCategory.ofHom (C := ModuleCat K)
      (thomMapRestrict π Z M U n l (l + n) rfl u)) :=
    (ModuleCat.epi_iff_surjective _).2 hU₁
  have : Epi (ConcreteCategory.ofHom (C := ModuleCat K)
      (thomMapRestrict π Z M V n l (l + n) rfl u)) :=
    (ModuleCat.epi_iff_surjective _).2 hV₁
  -- The top row is the Mayer–Vietoris sequence of the cover `{U, V}` of `Y` from degree `l` to
  -- degree `l + 1`, the bottom row that of the pairs over `U` and `V` from degree `l + n` to `m`,
  -- and the vertical maps are the Thom maps.
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M U V l).hom
    (singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV l (l + 1)).hom
    (singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M U V (l + 1)).hom
    (singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M U V (l + 1)).hom
    (singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) (l + n)).hom
    (singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) hU' hV' hA hB (l + n) m hm).hom
    (singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) m).hom
    (singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) m).hom
    (biprod.map
      (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M U n l (l + n) rfl u))
      (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M V n l (l + n) rfl u))).hom
    (thomMapInter π Z U V M n l (l + n) rfl u) (thomMapUnion π Z U V M n (l + 1) m h u)
    (biprod.map
      (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M U n (l + 1) m h u))
      (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M V n (l + 1) m h u))).hom
    (thomMapInter π Z U V M n (l + 1) m h u)
    (congrArg ModuleCat.Hom.hom (fromBiprod_comp_thomMapInter π Z rfl u)).symm
    (LinearMap.ext fun a ↦ pairMayerVietorisδ_thomMapInter π Z M hU hV hUV hA hB rfl hm h u a)
    (congrArg ModuleCat.Hom.hom (toBiprod_comp_biprodMap π Z h u)).symm
    (congrArg ModuleCat.Hom.hom (fromBiprod_comp_thomMapInter π Z h u)).symm
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₃ _ K M hU hV hUV l (l + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₁ _ K M hU hV hUV l (l + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₂ _ K M hU hV hUV (l + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyPairMayerVietoris_exact₃ _ K M _ _ hU' hV' hA hB (l + n) m hm))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyPairMayerVietoris_exact₁ _ K M _ _ hU' hV' hA hB (l + n) m hm))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyPairMayerVietoris_exact₂ _ K M _ _ hU' hV' hA hB m))
    ((ModuleCat.epi_iff_surjective _).1 inferInstance) hUV₁
    (ModuleCat.bijective_biprod_map hU₂ hV₂) hUV₂

include hU hV hUV hA hB in
/-- The gluing step in degree `0`, by a four lemma: it needs the vanishing of the cohomology of the
intersection pair in degree `n - 1`, just below the image of the Thom map. -/
private theorem bijective_thomMapUnion_zero {n m : ℕ} (h : 0 + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hU₀ : Function.Bijective (thomMapRestrict π Z M U n 0 m h u))
    (hV₀ : Function.Bijective (thomMapRestrict π Z M V n 0 m h u))
    (hUV₀ : Function.Injective (thomMapInter π Z U V M n 0 m h u))
    (hvan : ∀ j, j + 1 = n → IsZero ((TopPair.ofInclusion (Set.inter_subset_inter
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V))).singularCohomology
        (ModuleCat.of K K) K M j)) :
    Function.Bijective (thomMapUnion π Z U V M n 0 m h u) := by
  have hU' := (hU.preimage π.hom.continuous).preimage
    (continuous_subtype_val (p := (· ∈ π ⁻¹' U ∪ π ⁻¹' V)))
  have hV' := (hV.preimage π.hom.continuous).preimage
    (continuous_subtype_val (p := (· ∈ π ⁻¹' U ∪ π ⁻¹' V)))
  -- The first map of the Mayer–Vietoris sequence of the pairs is injective in degree `n`.
  have hg₀ : Function.Injective (singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K
      M (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) m).hom := by
    obtain _ | j := n
    · obtain rfl : m = 0 := by omega
      exact (ModuleCat.mono_iff_injective _).1
        (mono_singularCohomologyPairMayerVietorisToBiprod_zero (ModuleCat.of K K) K M
          (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) hU' hV' hA hB)
    · have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₁ (ModuleCat.of K K) K M
          (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
          (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) hU' hV' hA hB j m (by omega))
      have := ModuleCat.isZero_iff_subsingleton.1 (hvan j rfl)
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      obtain ⟨y, rfl⟩ := (hex x).1 hx
      rw [Subsingleton.elim y 0, map_zero]
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M U V 0).hom
    (singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M U V 0).hom
    (singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) m).hom
    (singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) m).hom
    (thomMapUnion π Z U V M n 0 m h u)
    (biprod.map (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M U n 0 m h u))
      (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapRestrict π Z M V n 0 m h u))).hom
    (thomMapInter π Z U V M n 0 m h u)
    (congrArg ModuleCat.Hom.hom (toBiprod_comp_biprodMap π Z h u)).symm
    (congrArg ModuleCat.Hom.hom (fromBiprod_comp_thomMapInter π Z h u)).symm
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₂ _ K M hU hV hUV 0))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyPairMayerVietoris_exact₂ _ K M _ _ hU' hV' hA hB m))
    (ModuleCat.bijective_biprod_map hU₀ hV₀) hUV₀
    ((ModuleCat.mono_iff_injective _).1 (mono_singularCohomologyMayerVietorisToBiprod_zero _ K M
      hU hV hUV)) hg₀

end Steps

/-- Over an open set `S` of the base, the points of `Z` lying over `S` are open among the points of
`Z` lying over `U` or `V`. -/
private theorem isOpen_preimage_inter {S : Set Y} (hS : IsOpen S) :
    IsOpen ((↑) ⁻¹' (π ⁻¹' S ∩ Z) : Set ↥(π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z)) := by
  convert (hS.preimage π.hom.continuous).preimage
    (continuous_subtype_val (p := (· ∈ π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z))) using 1
  ext ⟨x, hx⟩
  exact and_iff_left (hx.elim (·.2) (·.2))

/-- **The Mayer–Vietoris gluing step for the Thom map, for an open cover of the base.** Let
`π : X ⟶ Y` be a map, `Z ⊆ X`, `u ∈ Hⁿ(X, Z; K)`, and let `U` and `V` be open sets covering `Y`.
Suppose that the Thom maps of `u` over `U`, `V` and `U ∩ V` (`TopCat.thomMapRestrict`) are
bijective in degrees `p ≤ N`, and that `Hⁿ⁻¹(π⁻¹(U ∩ V), π⁻¹(U ∩ V) ∩ Z; M)` vanishes. Then the
Thom map `Hᵖ(Y; M) ⟶ Hᵖ⁺ⁿ(X, Z; M)`, `a ↦ π^*a ⌣ u`, is bijective in degrees `p ≤ N`. -/
theorem bijective_thomMap_of_union_eq_univ (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) {n : ℕ}
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (N : ℕ) (hU' : ∀ p ≤ N, Function.Bijective (thomMapRestrict π Z M U n p (p + n) rfl u))
    (hV' : ∀ p ≤ N, Function.Bijective (thomMapRestrict π Z M V n p (p + n) rfl u))
    (hUV' : ∀ p ≤ N, Function.Bijective (thomMapRestrict π Z M (U ∩ V) n p (p + n) rfl u))
    (hUV₀ : ∀ j, j + 1 = n → IsZero ((TopPair.ofInclusion (Set.inter_subset_left :
      π ⁻¹' (U ∩ V) ∩ Z ⊆ π ⁻¹' (U ∩ V))).singularCohomology (ModuleCat.of K K) K M j)) :
    ∀ p ≤ N, Function.Bijective ((TopPair.ofSubset Z).thomMap M π n p (p + n) rfl u) := by
  have hA := isOpen_preimage_inter π Z (U := U) (V := V) hU
  have hB := isOpen_preimage_inter π Z (U := U) (V := V) hV
  have hUV₁ (p : ℕ) (hp : p ≤ N) : Function.Bijective (thomMapInter π Z U V M n p (p + n) rfl u) :=
    (bijective_thomMapInter_iff π Z rfl u).2 (hUV' p hp)
  have := isIso_unionPairMap π Z hUV
  intro p hp
  refine (TopPair.bijective_thomMap_iff_of_isIso (unionPairMap π Z U V) (𝟙 Y)
    (π' := ofHom (ContinuousMap.subtypeVal _) ≫ π) (TopCat.ext fun _ ↦ rfl) rfl u).1 ?_
  obtain _ | l := p
  · exact bijective_thomMapUnion_zero π Z M hU hV hUV hA hB rfl u (hU' 0 hp) (hV' 0 hp)
      (hUV₁ 0 hp).1 fun j hj ↦ (isZero_singularCohomology_interPair_iff π Z j).2 (hUV₀ j hj)
  · exact bijective_thomMapUnion_succ π Z M hU hV hUV hA hB (by omega) u (hU' l (by omega)).2
      (hV' l (by omega)).2 (hUV₁ l (by omega)) (hU' _ hp) (hV' _ hp) (hUV₁ _ hp).1

end Gluing

/-! ### The gluing step over a union -/

section Union

variable {W S : Set Y}

/-- For `S ⊆ W`, restricting `(X, Z)` first over `W` and then over the preimage of `S` in `W` is
restricting it over `S`. -/
private def restrictRestrictIso (hSW : S ⊆ W) :
    TopPair.ofInclusion (Set.inter_subset_left :
      ofHom (π.hom.restrictPreimage W) ⁻¹' ((↑) ⁻¹' S) ∩ ((↑) ⁻¹' (π ⁻¹' W ∩ Z)) ⊆
        ofHom (π.hom.restrictPreimage W) ⁻¹' ((↑) ⁻¹' S)) ≅
      TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S) where
  hom := TopPair.ofHom (ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩)
    (ofHom ⟨fun x ↦ ⟨x.1.1, x.2.1, x.2.2.2⟩, by fun_prop⟩) (by ext; rfl)
  inv := TopPair.ofHom (ofHom ⟨fun x ↦ ⟨⟨x.1, hSW x.2⟩, x.2⟩, by fun_prop⟩)
    (ofHom ⟨fun x ↦ ⟨⟨x.1, hSW x.2.1⟩, x.2.1, hSW x.2.1, x.2.2⟩, by fun_prop⟩) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

variable (W) in
/-- The restriction of `u` to the pair over `W`, as a class of the pair formed by `π⁻¹ W` and its
points lying in `Z`. -/
private abbrev restrictClass {n : ℕ}
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    (TopPair.ofSubset (X := of ↥(π ⁻¹' W)) ((↑) ⁻¹' (π ⁻¹' W ∩ Z))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) n :=
  TopPair.singularCohomologyMap (TopPair.ofSubsetPreimageValIso
      (Set.inter_subset_left : π ⁻¹' W ∩ Z ⊆ π ⁻¹' W)).hom n
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z W) n u)

variable (M : ModuleCat.{w} K)

/-- For `S ⊆ W`, the Thom map over `S` agrees with the Thom map over the preimage of `S` in `W` of
the restriction of `π` over `W`, up to homeomorphisms; so the two are bijective together. -/
private theorem bijective_thomMapRestrict_restrict_iff (hSW : S ⊆ W) {n p m : ℕ}
    (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapRestrict (ofHom (π.hom.restrictPreimage W))
      ((↑) ⁻¹' (π ⁻¹' W ∩ Z)) M ((↑) ⁻¹' S) n p m h (restrictClass π Z W u)) ↔
      Function.Bijective (thomMapRestrict π Z M S n p m h u) := by
  have hu : TopPair.singularCohomologyMap (restrictPreimagePairMap
      (ofHom (π.hom.restrictPreimage W)) ((↑) ⁻¹' (π ⁻¹' W ∩ Z)) ((↑) ⁻¹' S)) n
      (restrictClass π Z W u) =
      TopPair.singularCohomologyMap (restrictRestrictIso π Z hSW).hom n
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n u) := by
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      ← TopPair.singularCohomologyMap_comp_apply]
    exact congrArg (fun f ↦ TopPair.singularCohomologyMap f n u)
      (TopPair.hom_ext_of_fst _ (by
        simp only [TopPair.Hom.fst_comp, TopPair.ofSubsetPreimageValIso_hom_fst,
          restrictPreimagePairMap_fst]
        exact TopCat.ext fun _ ↦ rfl))
  rw [show thomMapRestrict (ofHom (π.hom.restrictPreimage W)) ((↑) ⁻¹' (π ⁻¹' W ∩ Z)) M
      ((↑) ⁻¹' S) n p m h (restrictClass π Z W u) = _ from
      LinearMap.ext (thomMapRestrict_apply _ _ _ h _),
    LinearMap.ext (thomMapRestrict_apply π Z S h u), hu]
  have hS : S ⊆ Set.range ((↑) : W → Y) := by rwa [Subtype.range_coe]
  let g := isoOfHomeo (X := of ↥((↑) ⁻¹' S : Set ↥W)) (Y := of ↥S)
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hS)
  have hg : TopPair.Hom.fst (restrictRestrictIso π Z hSW).hom ≫ ofHom (π.hom.restrictPreimage S) =
      ofHom ((ofHom (π.hom.restrictPreimage W)).hom.restrictPreimage ((↑) ⁻¹' S)) ≫ g.hom :=
    TopCat.ext fun _ ↦ Subtype.ext rfl
  exact TopPair.bijective_thomMap_iff_of_isIso (restrictRestrictIso π Z hSW).hom g.hom hg h _

/-- **The Mayer–Vietoris gluing step for the Thom map.** Let `π : X ⟶ Y` be a map, `Z ⊆ X`,
`u ∈ Hⁿ(X, Z; K)`, and let `U` and `V` be open sets of `Y`. Suppose that the Thom maps of `u` over
`U`, `V` and `U ∩ V` (`TopCat.thomMapRestrict`) are bijective in degrees `p ≤ N`, and that
`Hⁿ⁻¹(π⁻¹(U ∩ V), π⁻¹(U ∩ V) ∩ Z; M)` vanishes. Then the Thom map of `u` over `U ∪ V` is
bijective in degrees `p ≤ N`. -/
theorem bijective_thomMapRestrict_union {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (N : ℕ) (hU' : ∀ p ≤ N, Function.Bijective (thomMapRestrict π Z M U n p (p + n) rfl u))
    (hV' : ∀ p ≤ N, Function.Bijective (thomMapRestrict π Z M V n p (p + n) rfl u))
    (hUV' : ∀ p ≤ N, Function.Bijective (thomMapRestrict π Z M (U ∩ V) n p (p + n) rfl u))
    (hUV₀ : ∀ j, j + 1 = n → IsZero ((TopPair.ofInclusion (Set.inter_subset_left :
      π ⁻¹' (U ∩ V) ∩ Z ⊆ π ⁻¹' (U ∩ V))).singularCohomology (ModuleCat.of K K) K M j)) :
    ∀ p ≤ N, Function.Bijective (thomMapRestrict π Z M (U ∪ V) n p (p + n) rfl u) := by
  have hUVW : U ∩ V ⊆ U ∪ V := Set.inter_subset_left.trans Set.subset_union_left
  -- The cover case, for the restriction of `π` over `U ∪ V` and the cover of `U ∪ V` by the
  -- preimages of `U` and `V`, whose hypotheses are those over `U`, `V` and `U ∩ V`.
  have key := bijective_thomMap_of_union_eq_univ (X := of ↥(π ⁻¹' (U ∪ V)))
    (ofHom (π.hom.restrictPreimage (U ∪ V))) ((↑) ⁻¹' (π ⁻¹' (U ∪ V) ∩ Z)) M
    (U := ((↑) : ↥(U ∪ V) → Y) ⁻¹' U) (V := ((↑) : ↥(U ∪ V) → Y) ⁻¹' V)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (Set.eq_univ_of_forall fun x ↦ x.2) (n := n)
  replace key := key (restrictClass π Z (U ∪ V) u) N
    (fun p hp ↦ (bijective_thomMapRestrict_restrict_iff π Z M Set.subset_union_left rfl u).2
      (hU' p hp))
    (fun p hp ↦ (bijective_thomMapRestrict_restrict_iff π Z M Set.subset_union_right rfl u).2
      (hV' p hp))
    (fun p hp ↦ (bijective_thomMapRestrict_restrict_iff π Z M hUVW rfl u).2 (hUV' p hp))
    fun j hj ↦ by
      have := (hUV₀ j hj).of_iso ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K M
        j).mapIso (restrictRestrictIso π Z hUVW).op).symm
      rwa [Set.preimage_inter (s := U) (t := V)] at this
  intro p hp
  have e : thomMapRestrict π Z M (U ∪ V) n p (p + n) rfl u =
      (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' (U ∪ V) ∩ Z ⊆ π ⁻¹' (U ∪ V))).thomMap M
        (ofHom (π.hom.restrictPreimage (U ∪ V))) n p (p + n) rfl
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z (U ∪ V)) n u) :=
    LinearMap.ext fun a ↦ thomMapRestrict_apply π Z (U ∪ V) rfl u a
  rw [e]
  refine (TopPair.bijective_thomMap_iff_of_isIso (TopPair.ofSubsetPreimageValIso
    (Set.inter_subset_left : π ⁻¹' (U ∪ V) ∩ Z ⊆ π ⁻¹' (U ∪ V))).hom (𝟙 _)
    (π' := ofHom (π.hom.restrictPreimage (U ∪ V)))
    (by rw [TopPair.ofSubsetPreimageValIso_hom_fst]; exact TopCat.ext fun _ ↦ rfl) rfl
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z (U ∪ V)) n u)).1 ?_
  exact key p hp

end Union

end TopCat
