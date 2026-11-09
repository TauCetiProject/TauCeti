/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The Thom map and the Mayer–Vietoris sequence

Let `E → B` be a vector bundle with Thom pair `(E, E₀)` and let `u ∈ Hⁿ(E, E₀; K)`. For a subset
`W` of the base, the **Thom map over `W`** of a class `u_W ∈ Hⁿ(E|_W, E₀|_W; K)` is

`Φ_{u_W} : Hᵖ(W; M) ⟶ Hᵖ⁺ⁿ(E|_W, E₀|_W; M)`,  `a ↦ π_W^*a ⌣ u_W`

(`TauCeti.thomMapOver`), where `π_W : E|_W ⟶ W` is the restricted projection
(`TauCeti.thomPairOverProj`). It is natural in restrictions to smaller subsets
(`TauCeti.singularCohomologyMap_thomPairOverMap_thomMapOver`), and the Thom map `TauCeti.thomMap` of
`u` restricts over `W` to the Thom map of the restriction of `u`
(`TauCeti.singularCohomologyMap_thomPairOverMap_thomMap`).

The main result is the **Mayer–Vietoris step of the Thom isomorphism**
(`TauCeti.thomMap_bijective_of_union_eq_univ`). Let `U` and `V` be open sets covering the base. If
the Thom maps of the restrictions of `u` over `U`, `V` and `U ∩ V` are bijective in every degree,
and `Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V}; M)` vanishes, then the Thom map of `u` is bijective in every
degree. This is the gluing step in the proof of the Thom isomorphism by induction over trivializing
open sets (Milnor and Stasheff, proof of Theorem 10.4; Hatcher, proof of Theorem 4D.10). For a real
vector bundle of rank `n`, the vanishing hypothesis holds when `U ∩ V` is a finite union of
trivializing open sets (`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`).

The Thom maps form a map from the Mayer–Vietoris sequence of the cover `{U, V}` of the base
(`TopCat.singularCohomologyMayerVietorisδ`) to the Mayer–Vietoris sequence of the Thom pairs over
`U` and over `V` (`TopCat.singularCohomologyPairMayerVietorisδ`). The squares through restrictions
commute by naturality of the cup product. The square through the connecting morphisms commutes
because the connecting morphism of the pairs carries `a ⌣ u|` to `δ a ⌣ u`
(`TopCat.singularCohomologyPairMayerVietorisδ_singularCup`), and the connecting morphism of the
cover of the total space by the preimages of `U` and `V` is compatible with the projection
(`TopCat.singularCohomologyMayerVietorisδ_naturality`). The five lemma
(`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`) concludes.

## Main definitions and results

* `TauCeti.thomPairOverProj`: the projection `E|_W ⟶ W`.
* `TauCeti.thomMapOver`: the Thom map `a ↦ π_W^*a ⌣ u_W` over a subset `W` of the base.
* `TauCeti.singularCohomologyMap_thomPairOverMap_thomMapOver`,
  `TauCeti.singularCohomologyMap_thomPairOverMap_thomMap`: naturality in restrictions.
* `TauCeti.thomMap_bijective_of_union_eq_univ`: the Mayer–Vietoris step of the Thom isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Set

universe w

namespace TauCeti

section Over

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- The projection `E|_W ⟶ W` of the restriction of a fibre bundle to a subset `W` of its base, as a
morphism of topological spaces out of the ambient space of the Thom pair over `W`. -/
def thomPairOverProj (W : Set B) : (thomPairOver F E W).fst ⟶ TopCat.of W :=
  TopCat.ofHom ⟨fun v ↦ ⟨v.1.proj, v.2⟩,
    ((FiberBundle.continuous_proj F E).comp continuous_subtype_val).subtype_mk _⟩

@[simp]
theorem thomPairOverProj_apply (W : Set B) (v : π F E ⁻¹' W) :
    thomPairOverProj F E W v = ⟨v.1.proj, v.2⟩ :=
  (rfl)

/-- **The Thom map over a subset `W` of the base**: `a ↦ π_W^*a ⌣ u` for a relative class
`u ∈ Hⁿ(E|_W, E₀|_W; K)`, from `Hᵖ(W; M)` to `Hᵐ(E|_W, E₀|_W; M)`, `p + n = m`, as a `K`-bilinear
map of `u` and `a`. As for `TauCeti.thomMap`, the chain coefficients are `K` and the pairing of
values is the right unitor `M ⊗ K ≅ M`. -/
def thomMapOver (W : Set B) (n p m : ℕ) (h : p + n = m) :
    (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  ((thomPairOver F E W).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h ∘ₗ
    (TopCat.singularCohomologyMap (thomPairOverProj F E W) p).hom).flip

variable {M}

/-- The Thom map over `W` is the cup product of the pull-back to `E|_W` with `u`. -/
theorem thomMapOver_apply (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p) :
    thomMapOver F E M W n p m h u a =
      (thomPairOver F E W).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (thomPairOverProj F E W) p a) u :=
  (rfl)

/-- Pulling back the cup product of a pulled-back absolute class with a relative class along a map
of pairs: if `j : P ⟶ Q` covers `π' : P.fst ⟶ Z` through `π_Q : Q.fst ⟶ Z`, then
`j^*(π_Q^*a ⌣ b) = π'^*a ⌣ j^*b`. -/
private theorem singularCohomologyMap_singularCup_singularCohomologyMap {P Q : TopPair.{w}}
    (j : P ⟶ Q) {Z : TopCat.{w}} (πQ : Q.fst ⟶ Z) (π' : P.fst ⟶ Z)
    (hj : TopPair.Hom.fst j ≫ πQ = π') {n p m : ℕ} (h : p + n = m)
    (b : Q.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Z.singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap j m
        (Q.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
          (TopCat.singularCohomologyMap πQ p a) b) =
      P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap π' p a) (TopPair.singularCohomologyMap j n b) := by
  rw [← TopPair.singularCup_naturality, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, hj]

/-! The maps of pairs below are inclusions of subspaces of the total space, whose definitions are
not exposed; the compatibilities between them are checked pointwise through their evaluation lemmas.
`erw` is needed because, after `ConcreteCategory.hom_ext`, points are typed in the carrier of the
`TopCat` object rather than in the subtype the evaluation lemmas are stated for. -/

private theorem fst_thomPairOverMap_comp_thomPairOverProj {W W' : Set B} (hW : W ⊆ W') :
    TopPair.Hom.fst (thomPairOverMap F E hW) ≫ thomPairOverProj F E W' =
      thomPairOverProj F E W ≫ TopCat.ofHom (ContinuousMap.inclusion hW) :=
  ConcreteCategory.hom_ext _ _ fun x ↦ by
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, thomPairOverMap_fst_apply]
    rfl

private theorem fst_thomPairOverMap_comp_thomPairProj (W : Set B) :
    TopPair.Hom.fst (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) ≫
        thomPairProj F E =
      thomPairOverProj F E W ≫ TopCat.ofHom (ContinuousMap.subtypeVal W) :=
  ConcreteCategory.hom_ext _ _ fun x ↦ by
    simp only [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      thomPairOverMap_fst_apply, thomPairOverUnivIso_hom_fst_apply, thomPairProj_apply]
    rfl

/-- **Naturality of the Thom map over a subset in restrictions**: for `W ⊆ W'`, restricting
`Φ_u(a)` from `W'` to `W` gives the Thom map over `W` of the restrictions of `u` and `a`. -/
theorem singularCohomologyMap_thomPairOverMap_thomMapOver {W W' : Set B} (hW : W ⊆ W')
    {n p m : ℕ} (h : p + n = m)
    (u : (thomPairOver F E W').singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of W').singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (thomPairOverMap F E hW) m (thomMapOver F E M W' n p m h u a) =
      thomMapOver F E M W n p m h (TopPair.singularCohomologyMap (thomPairOverMap F E hW) n u)
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.inclusion hW)) p a) := by
  rw [thomMapOver_apply, thomMapOver_apply, singularCohomologyMap_singularCup_singularCohomologyMap
    _ _ _ (fst_thomPairOverMap_comp_thomPairOverProj F E hW), TopCat.singularCohomologyMap_comp]
  rfl

/-- **The Thom map restricted to a subset of the base**: restricting `Φ_u(a)` from `B` to `W` gives
the Thom map over `W` of the restrictions of `u` and `a`. -/
theorem singularCohomologyMap_thomPairOverMap_thomMap (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (thomPairOverMap F E (subset_univ W) ≫
        (thomPairOverUnivIso F E).hom) m (thomMap F E M n p m h u a) =
      thomMapOver F E M W n p m h (TopPair.singularCohomologyMap (thomPairOverMap F E
          (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) n u)
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W)) p a) := by
  rw [thomMap_apply, thomMapOver_apply, singularCohomologyMap_singularCup_singularCohomologyMap
    _ _ _ (fst_thomPairOverMap_comp_thomPairProj F E W), TopCat.singularCohomologyMap_comp]
  rfl

end Over

section MayerVietoris

/-! ### The Mayer–Vietoris step

Throughout, `U` and `V` are open sets of the base with `U ∪ V = B`. The Mayer–Vietoris sequence of
the Thom pairs over `U` and over `V` is stated for the pairs `(E|_U ∩ E|_V, E₀|_U ∩ E₀|_V)` and
`(E|_U ∪ E|_V, E₀|_U ∪ E₀|_V)`; the first is the Thom pair over `U ∩ V`
(`TauCeti.thomPairOverInterIso`), and the second maps isomorphically onto the Thom pair
`(E, E₀)`. -/

variable {B : Type w} [TopologicalSpace B] {F : Type*} [TopologicalSpace F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] {M : ModuleCat.{w} K} {U V : Set B}

variable (F E) in
/-- The projection of the total space maps the preimage of `W` into `W`. -/
private theorem mapsTo_thomPairProj (W : Set B) : MapsTo (thomPairProj F E) (π F E ⁻¹' W) W :=
  fun x hx ↦ (congrArg (· ∈ W) (thomPairProj_apply F E x)).mpr hx

variable (F E U V) in
/-- The intersection pair of the Mayer–Vietoris sequence of the Thom pairs over `U` and `V`. -/
private abbrev interPair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
    (inter_subset_inter (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))

variable (F E U V) in
/-- The union pair of the Mayer–Vietoris sequence of the Thom pairs over `U` and `V`. -/
private abbrev unionPair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
    (union_subset_union (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))

variable (F E) in
/-- The restriction from the Thom pair `(E, E₀)` to the Thom pair over `W`. -/
private abbrev thomPairRestrict (W : Set B) : thomPairOver F E W ⟶ thomPair F E :=
  thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom

variable (F E U V) in
/-- The inclusion of the union pair into the Thom pair `(E, E₀)`. -/
private abbrev unionToThomPair : unionPair F E U V ⟶ thomPair F E :=
  (thomPairOverUnionIso F E U V).hom ≫ thomPairRestrict F E (U ∪ V)

variable (F E U V) in
/-- The inclusion of the intersection pair into the Thom pair `(E, E₀)`. -/
private abbrev interToThomPair : interPair F E U V ⟶ thomPair F E :=
  TopCat.interToUnionMap (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) ≫
    unionToThomPair F E U V

variable (F E U V) in
/-- The projection `E|_U ∩ E|_V ⟶ U ∩ V`, the restriction of the projection of the total space. -/
private abbrev interProj : TopCat.of ↥(π F E ⁻¹' U ∩ π F E ⁻¹' V) ⟶ TopCat.of ↥(U ∩ V) :=
  TopCat.ofHom ⟨((mapsTo_thomPairProj F E U).inter_inter (mapsTo_thomPairProj F E V)).restrict,
    (thomPairProj F E).hom.continuous.restrict _⟩

omit [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
private theorem isIso_unionToThomPair (hUV : U ∪ V = univ) :
    IsIso (unionToThomPair F E U V) := by
  have : IsIso (thomPairOverMap F E (subset_univ (U ∪ V))) :=
    ⟨thomPairOverMap F E hUV.ge, by simp, by simp⟩
  infer_instance

/-! #### Compatibilities of the maps of pairs -/

private theorem fst_thomPairOverInterIso_inv_comp_thomPairOverProj :
    TopPair.Hom.fst (thomPairOverInterIso F E U V).inv ≫ thomPairOverProj F E (U ∩ V) =
      interProj F E U V :=
  ConcreteCategory.hom_ext _ _ fun x ↦ by
    erw [ConcreteCategory.comp_apply, thomPairOverInterIso_inv_fst_apply]
    exact Subtype.ext (thomPairProj_apply F E x.1).symm

private theorem fst_unionToThomPair_comp_thomPairProj :
    TopPair.Hom.fst (unionToThomPair F E U V) ≫ thomPairProj F E =
      TopCat.ofHom (ContinuousMap.subtypeVal _) ≫ thomPairProj F E :=
  ConcreteCategory.hom_ext _ _ fun x ↦ by
    simp only [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, thomPairOverUnionIso_hom_fst_apply, thomPairOverMap_fst_apply,
      thomPairOverUnivIso_hom_fst_apply]
    rfl

omit [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
private theorem thomPairOverInterIso_inv_comp_thomPairRestrict :
    (thomPairOverInterIso F E U V).inv ≫ thomPairRestrict F E (U ∩ V) =
      interToThomPair F E U V :=
  TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun x ↦ by
    simp only [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      thomPairOverInterIso_inv_fst_apply, thomPairOverMap_fst_apply,
      thomPairOverUnivIso_hom_fst_apply, TopPair.ofInclusionMap_fst_apply,
      thomPairOverUnionIso_hom_fst_apply, thomPairOverMap_fst_apply,
      thomPairOverUnivIso_hom_fst_apply]
    rfl)

private theorem fst_ofInclusionMap_comp_thomPairOverProj {W : Set B} (hW : U ∩ V ⊆ W)
    (hW' : π F E ⁻¹' U ∩ π F E ⁻¹' V ⊆ π F E ⁻¹' W)
    (hs : ∀ x : ↥(π F E ⁻¹' U ∩ π F E ⁻¹' V),
      (x : TotalSpace F E) ∈ π F E ⁻¹' U ∩ zeroSectionCompl F E ∩
        (π F E ⁻¹' V ∩ zeroSectionCompl F E) →
      (ContinuousMap.inclusion hW' x : TotalSpace F E) ∈ π F E ⁻¹' W ∩ zeroSectionCompl F E) :
    TopPair.Hom.fst (TopPair.ofInclusionMap (inter_subset_inter
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))
        (inter_subset_left :
        π F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W) (ContinuousMap.inclusion hW') hs) ≫
        thomPairOverProj F E W =
      interProj F E U V ≫ TopCat.ofHom (ContinuousMap.inclusion hW) :=
  ConcreteCategory.hom_ext _ _ fun x ↦ by
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofInclusionMap_fst_apply]
    exact Subtype.ext (thomPairProj_apply F E x.1).symm

omit [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
private theorem ofInclusionMap_comp_thomPairRestrict {W : Set B}
    (hW' : π F E ⁻¹' U ∩ π F E ⁻¹' V ⊆ π F E ⁻¹' W)
    (hs : ∀ x : ↥(π F E ⁻¹' U ∩ π F E ⁻¹' V),
      (x : TotalSpace F E) ∈ π F E ⁻¹' U ∩ zeroSectionCompl F E ∩
        (π F E ⁻¹' V ∩ zeroSectionCompl F E) →
      (ContinuousMap.inclusion hW' x : TotalSpace F E) ∈ π F E ⁻¹' W ∩ zeroSectionCompl F E) :
    TopPair.ofInclusionMap (inter_subset_inter
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))
        (inter_subset_left :
        π F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W) (ContinuousMap.inclusion hW') hs ≫
        thomPairRestrict F E W =
      interToThomPair F E U V :=
  TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun x ↦ by
    simp only [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      TopPair.ofInclusionMap_fst_apply, thomPairOverMap_fst_apply,
      thomPairOverUnivIso_hom_fst_apply, TopPair.ofInclusionMap_fst_apply,
      thomPairOverUnionIso_hom_fst_apply, thomPairOverMap_fst_apply,
      thomPairOverUnivIso_hom_fst_apply]
    rfl)

omit [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
private theorem ofInclusionMap_comp_unionToThomPair {W : Set B}
    (hW' : π F E ⁻¹' W ⊆ π F E ⁻¹' U ∪ π F E ⁻¹' V)
    (hs : ∀ x : ↥(π F E ⁻¹' W), (x : TotalSpace F E) ∈ π F E ⁻¹' W ∩ zeroSectionCompl F E →
      (ContinuousMap.inclusion hW' x : TotalSpace F E) ∈
        π F E ⁻¹' U ∩ zeroSectionCompl F E ∪ π F E ⁻¹' V ∩ zeroSectionCompl F E) :
    TopPair.ofInclusionMap (inter_subset_left :
        π F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W) (union_subset_union
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))
        (ContinuousMap.inclusion hW') hs ≫
        unionToThomPair F E U V =
      thomPairRestrict F E W :=
  TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun x ↦ by
    simp only [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, TopPair.ofInclusionMap_fst_apply,
      thomPairOverUnionIso_hom_fst_apply, thomPairOverMap_fst_apply,
      thomPairOverUnivIso_hom_fst_apply, thomPairOverMap_fst_apply,
      thomPairOverUnivIso_hom_fst_apply]
    rfl)

/-! #### The Thom maps on the pairs of the Mayer–Vietoris sequence -/

/-- The Thom map over `U ∩ V`, read on the intersection pair of the Mayer–Vietoris sequence, is the
cup product with the restriction of `u` to that pair. -/
private theorem singularCohomologyMap_thomPairOverInterIso_inv_thomMapOver {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m
        (thomMapOver F E M (U ∩ V) n p m h
          (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u) a) =
      (interPair F E U V).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (interProj F E U V) p a)
        (TopPair.singularCohomologyMap (interToThomPair F E U V) n u) := by
  rw [thomMapOver_apply, singularCohomologyMap_singularCup_singularCohomologyMap _ _ _
    fst_thomPairOverInterIso_inv_comp_thomPairOverProj, ← TopPair.singularCohomologyMap_comp_apply,
    thomPairOverInterIso_inv_comp_thomPairRestrict]
  rfl

/-- Restricting the Thom map over a member `W` of the cover to the intersection pair gives the cup
product with the restriction of `u`, of the restriction of `a` to `U ∩ V`. -/
private theorem singularCohomologyMap_ofInclusionMap_thomMapOver {W : Set B} (hW : U ∩ V ⊆ W)
    (hW' : π F E ⁻¹' U ∩ π F E ⁻¹' V ⊆ π F E ⁻¹' W)
    (hs : ∀ x : ↥(π F E ⁻¹' U ∩ π F E ⁻¹' V),
      (x : TotalSpace F E) ∈ π F E ⁻¹' U ∩ zeroSectionCompl F E ∩
        (π F E ⁻¹' V ∩ zeroSectionCompl F E) →
      (ContinuousMap.inclusion hW' x : TotalSpace F E) ∈ π F E ⁻¹' W ∩ zeroSectionCompl F E)
    {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap (inter_subset_inter
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))
        (inter_subset_left :
        π F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W) (ContinuousMap.inclusion hW') hs) m
        (thomMapOver F E M W n p m h
          (TopPair.singularCohomologyMap (thomPairRestrict F E W) n u) a) =
      TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m
        (thomMapOver F E M (U ∩ V) n p m h
          (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u)
          (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.inclusion hW)) p a)) := by
  rw [singularCohomologyMap_thomPairOverInterIso_inv_thomMapOver, thomMapOver_apply,
    singularCohomologyMap_singularCup_singularCohomologyMap _ _ _
      (fst_ofInclusionMap_comp_thomPairOverProj hW hW' hs),
    ← TopPair.singularCohomologyMap_comp_apply, ofInclusionMap_comp_thomPairRestrict]
  exact congrArg (fun z ↦ (interPair F E U V).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
    (ρ_ M).hom p n m h z (TopPair.singularCohomologyMap (interToThomPair F E U V) n u))
    (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp (interProj F E U V)
      (TopCat.ofHom (ContinuousMap.inclusion hW)) p) a)

/-- Restricting the Thom map of `u`, read on the union pair, to the Thom pair over a member `W` of
the cover gives the Thom map over `W`. -/
private theorem singularCohomologyMap_ofInclusionMap_thomMap {W : Set B}
    (hW' : π F E ⁻¹' W ⊆ π F E ⁻¹' U ∪ π F E ⁻¹' V)
    (hs : ∀ x : ↥(π F E ⁻¹' W), (x : TotalSpace F E) ∈ π F E ⁻¹' W ∩ zeroSectionCompl F E →
      (ContinuousMap.inclusion hW' x : TotalSpace F E) ∈
        π F E ⁻¹' U ∩ zeroSectionCompl F E ∪ π F E ⁻¹' V ∩ zeroSectionCompl F E)
    {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap (inter_subset_left :
        π F E ⁻¹' W ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' W) (union_subset_union
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))
        (ContinuousMap.inclusion hW') hs) m
        (TopPair.singularCohomologyMap (unionToThomPair F E U V) m (thomMap F E M n p m h u a)) =
      thomMapOver F E M W n p m h (TopPair.singularCohomologyMap (thomPairRestrict F E W) n u)
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W)) p a) := by
  rw [← TopPair.singularCohomologyMap_comp_apply, ofInclusionMap_comp_unionToThomPair]
  exact singularCohomologyMap_thomPairOverMap_thomMap F E W h u a

/-- **The connecting morphisms commute with the Thom maps**: the connecting morphism of the
Mayer–Vietoris sequence of the Thom pairs over `U` and `V` carries the Thom map of `a` over
`U ∩ V` to the Thom map of the connecting morphism of `a` in the Mayer–Vietoris sequence of the
base. -/
private theorem singularCohomologyPairMayerVietorisδ_thomMapOver (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M p) :
    TopCat.singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
        (X := TopCat.of (TotalSpace F E))
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
        (isOpen_thomPairOver_mayerVietoris hU hV).1
        (isOpen_thomPairOver_mayerVietoris hU hV).2.1
        (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
        (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 m (m + 1) rfl
        (TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m
          (thomMapOver F E M (U ∩ V) n p m h
            (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u) a)) =
      TopPair.singularCohomologyMap (unionToThomPair F E U V) (m + 1)
        (thomMap F E M n (p + 1) (m + 1) (by omega) u
          (TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M
            (X := TopCat.of B) hU hV hUV p (p + 1) rfl a)) := by
  have hU' : IsOpen (π F E ⁻¹' U) := hU.preimage (FiberBundle.continuous_proj F E)
  have hV' : IsOpen (π F E ⁻¹' V) := hV.preimage (FiberBundle.continuous_proj F E)
  have hUV' : π F E ⁻¹' U ∪ π F E ⁻¹' V = univ := by rw [← preimage_union, hUV, preimage_univ]
  rw [singularCohomologyMap_thomPairOverInterIso_inv_thomMapOver,
    TopPair.singularCohomologyMap_comp_apply (TopCat.interToUnionMap _ _)
      (unionToThomPair F E U V)]
  -- The connecting morphism of the pairs carries `a ⌣ u|` to `δ a ⌣ u`, where `δ a` is taken in
  -- the Mayer–Vietoris sequence of the cover of the total space by the preimages of `U` and `V`.
  refine (TopCat.singularCohomologyPairMayerVietorisδ_singularCup K hU' hV' hUV'
    (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
    (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
    (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
    (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 _ _ h rfl rfl (by omega) _ _).trans ?_
  -- That connecting morphism is the pull-back of the one of the base along the projection.
  have hδ := ConcreteCategory.congr_hom (TopCat.singularCohomologyMayerVietorisδ_naturality
    (ModuleCat.of K K) K M hU' hV' hUV' hU hV hUV (thomPairProj F E) (mapsTo_thomPairProj F E U)
    (mapsTo_thomPairProj F E V) p (p + 1) rfl) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hδ
  rw [thomMap_apply, singularCohomologyMap_singularCup_singularCohomologyMap _ _ _
    fst_unionToThomPair_comp_thomPairProj]
  exact congrArg (fun z ↦ (unionPair F E U V).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
    (ρ_ M).hom (p + 1) n (m + 1) (by omega) z
    (TopPair.singularCohomologyMap (unionToThomPair F E U V) n u))
    ((congrArg (fun z ↦ TopCat.singularCohomologyMap
      (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' U ∪ π F E ⁻¹' V))) (p + 1) z)
        hδ.symm).trans
    (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp _ _ (p + 1)) _).symm)

/-! #### The ladder of Mayer–Vietoris sequences -/

variable (F E M) in
/-- The Thom map over `W` of the restriction of `u`, as a morphism of modules. -/
private abbrev thomMapOverHom (W : Set B) {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p ⟶
      (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  ModuleCat.ofHom (thomMapOver F E M W n p m h
    (TopPair.singularCohomologyMap (thomPairRestrict F E W) n u))

/-- The square through the second maps of the Mayer–Vietoris sequences commutes. -/
private theorem singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    TopCat.singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
        U V p ≫ thomMapOverHom F E M (U ∩ V) u p m h ≫
          TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m =
      biprod.map (thomMapOverHom F E M U u p m h) (thomMapOverHom F E M V u p m h) ≫
        TopCat.singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) m := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [TopCat.inl_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inl_map_assoc,
      TopCat.inl_singularCohomologyPairMayerVietorisFromBiprod]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (singularCohomologyMap_ofInclusionMap_thomMapOver inter_subset_left
      (inter_subset_left : π F E ⁻¹' U ∩ π F E ⁻¹' V ⊆ π F E ⁻¹' U)
      (fun _ hx ↦ hx.1) h u a).symm
  · rw [TopCat.inr_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inr_map_assoc,
      TopCat.inr_singularCohomologyPairMayerVietorisFromBiprod, Preadditive.neg_comp,
      Preadditive.comp_neg, neg_inj]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (singularCohomologyMap_ofInclusionMap_thomMapOver inter_subset_right
      (inter_subset_right : π F E ⁻¹' U ∩ π F E ⁻¹' V ⊆ π F E ⁻¹' V)
      (fun _ hx ↦ hx.2) h u a).symm

/-- The square through the first maps of the Mayer–Vietoris sequences commutes. -/
private theorem singularCohomologyMayerVietorisToBiprod_comp_biprod_map {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    TopCat.singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
        U V p ≫ biprod.map (thomMapOverHom F E M U u p m h) (thomMapOverHom F E M V u p m h) =
      (ModuleCat.ofHom (thomMap F E M n p m h u) ≫
        TopPair.singularCohomologyMap (unionToThomPair F E U V) m) ≫
        TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) m := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, biprod.map_fst,
      TopCat.singularCohomologyMayerVietorisToBiprod_fst_assoc,
      TopCat.singularCohomologyPairMayerVietorisToBiprod_fst]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (singularCohomologyMap_ofInclusionMap_thomMap
      (subset_union_left : π F E ⁻¹' U ⊆ π F E ⁻¹' U ∪ π F E ⁻¹' V)
      (fun _ hx ↦ Or.inl hx) h u a).symm
  · rw [Category.assoc, Category.assoc, biprod.map_snd,
      TopCat.singularCohomologyMayerVietorisToBiprod_snd_assoc,
      TopCat.singularCohomologyPairMayerVietorisToBiprod_snd]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (singularCohomologyMap_ofInclusionMap_thomMap
      (subset_union_right : π F E ⁻¹' V ⊆ π F E ⁻¹' U ∪ π F E ⁻¹' V)
      (fun _ hx ↦ Or.inr hx) h u a).symm

/-- The square through the connecting morphisms of the Mayer–Vietoris sequences commutes. -/
private theorem singularCohomologyMayerVietorisδ_comp_thomMap (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M (X := TopCat.of B) hU hV hUV
        p (p + 1) rfl ≫ ModuleCat.ofHom (thomMap F E M n (p + 1) (m + 1) (by omega) u) ≫
          TopPair.singularCohomologyMap (unionToThomPair F E U V) (m + 1) =
      (thomMapOverHom F E M (U ∩ V) u p m h ≫
        TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m) ≫
        TopCat.singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
          (isOpen_thomPairOver_mayerVietoris hU hV).1
          (isOpen_thomPairOver_mayerVietoris hU hV).2.1
          (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
          (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 m (m + 1) rfl :=
  ModuleCat.hom_ext (LinearMap.ext fun a ↦
    (singularCohomologyPairMayerVietorisδ_thomMapOver hU hV hUV h u a).symm)

/-- The direct sum of the Thom maps over `U` and over `V` is bijective when both are. -/
private theorem bijective_biprod_map_thomMapOverHom {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    {p m : ℕ} (h : p + n = m)
    (hΦU : Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E U) n u)))
    (hΦV : Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E V) n u))) :
    Function.Bijective
      (biprod.map (thomMapOverHom F E M U u p m h) (thomMapOverHom F E M V u p m h)) := by
  have := (ConcreteCategory.isIso_iff_bijective (thomMapOverHom F E M U u p m h)).2 hΦU
  have := (ConcreteCategory.isIso_iff_bijective (thomMapOverHom F E M V u p m h)).2 hΦV
  exact ConcreteCategory.bijective_of_isIso
    (biprod.mapIso (asIso (thomMapOverHom F E M U u p m h))
      (asIso (thomMapOverHom F E M V u p m h))).hom

/-- The Thom map over `U ∩ V`, read on the intersection pair, is bijective when the Thom map over
`U ∩ V` is. -/
private theorem bijective_thomMapOverHom_comp {W : Set B} {P : TopPair.{w}}
    (e : P ≅ thomPairOver F E W) {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    {p m : ℕ} (h : p + n = m)
    (hΦ : Function.Bijective (thomMapOver F E M W n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E W) n u))) :
    Function.Bijective
      (thomMapOverHom F E M W u p m h ≫ TopPair.singularCohomologyMap e.hom m) := by
  have := (ConcreteCategory.isIso_iff_bijective (thomMapOverHom F E M W u p m h)).2 hΦ
  exact ConcreteCategory.bijective_of_isIso _

/-- The five lemma for a ladder of exact sequences of modules, with exactness stated for short
complexes. -/
private theorem bijective_of_exact_of_comm {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : ModuleCat.{w} K}
    {f₁ : M₁ ⟶ M₂} {f₂ : M₂ ⟶ M₃} {f₃ : M₃ ⟶ M₄} {f₄ : M₄ ⟶ M₅}
    {g₁ : N₁ ⟶ N₂} {g₂ : N₂ ⟶ N₃} {g₃ : N₃ ⟶ N₄} {g₄ : N₄ ⟶ N₅}
    {i₁ : M₁ ⟶ N₁} {i₂ : M₂ ⟶ N₂} {i₃ : M₃ ⟶ N₃} {i₄ : M₄ ⟶ N₄} {i₅ : M₅ ⟶ N₅}
    {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0} {w₃ : f₃ ≫ f₄ = 0}
    {v₁ : g₁ ≫ g₂ = 0} {v₂ : g₂ ≫ g₃ = 0} {v₃ : g₃ ≫ g₄ = 0}
    (hf₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (hf₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (hf₃ : (ShortComplex.mk f₃ f₄ w₃).Exact) (hg₁ : (ShortComplex.mk g₁ g₂ v₁).Exact)
    (hg₂ : (ShortComplex.mk g₂ g₃ v₂).Exact) (hg₃ : (ShortComplex.mk g₃ g₄ v₃).Exact)
    (sq₁ : f₁ ≫ i₂ = i₁ ≫ g₁) (sq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) (sq₃ : f₃ ≫ i₄ = i₃ ≫ g₃)
    (sq₄ : f₄ ≫ i₅ = i₄ ≫ g₄) (hi₁ : Function.Surjective i₁) (hi₂ : Function.Bijective i₂)
    (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) : Function.Bijective i₃ :=
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective f₁.hom f₂.hom f₃.hom
    f₄.hom g₁.hom g₂.hom g₃.hom g₄.hom i₁.hom i₂.hom i₃.hom i₄.hom i₅.hom
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₁])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₂])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₃])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₄])
    (LinearMap.exact_iff.2 hf₁.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hf₂.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hf₃.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₁.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₂.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₃.moduleCat_range_eq_ker.symm) hi₁ hi₂ hi₄ hi₅

/-- The four lemma for a ladder of exact sequences of modules starting with a monomorphism in the
lower row, with exactness stated for short complexes. -/
private theorem surjective_of_exact_of_comm {M₂ M₃ M₄ N₂ N₃ N₄ : ModuleCat.{w} K}
    {f₂ : M₂ ⟶ M₃} {f₃ : M₃ ⟶ M₄} {g₂ : N₂ ⟶ N₃} {g₃ : N₃ ⟶ N₄}
    {i₂ : M₂ ⟶ N₂} {i₃ : M₃ ⟶ N₃} {i₄ : M₄ ⟶ N₄} {w₂ : f₂ ≫ f₃ = 0} {v₂ : g₂ ≫ g₃ = 0}
    (hf₂ : (ShortComplex.mk f₂ f₃ w₂).Exact) (hg₂ : (ShortComplex.mk g₂ g₃ v₂).Exact) [Mono g₂]
    (sq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) (sq₃ : f₃ ≫ i₄ = i₃ ≫ g₃) (hi₃ : Function.Surjective i₃)
    (hi₄ : Function.Injective i₄) : Function.Surjective i₂ :=
  LinearMap.surjective_of_surjective_of_surjective_of_injective (0 : PUnit.{w + 1} →ₗ[K] M₂)
    f₂.hom f₃.hom (0 : PUnit.{w + 1} →ₗ[K] N₂) g₂.hom g₃.hom 0 i₂.hom i₃.hom i₄.hom
    (LinearMap.ext fun _ ↦ by simp)
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₂])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₃])
    (LinearMap.exact_iff.2 hf₂.moduleCat_range_eq_ker.symm)
    ((LinearMap.exact_zero_iff_injective _ _).2 ((ModuleCat.mono_iff_injective _).1 inferInstance))
    (LinearMap.exact_iff.2 hg₂.moduleCat_range_eq_ker.symm) (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩)
    hi₃ hi₄

/-- The degree-`0` case of the Mayer–Vietoris step, read on the union pair: the Thom map is
injective since the first map of the Mayer–Vietoris sequence of the base is, and surjective by the
four lemma, since `Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V})` vanishes. -/
private theorem bijective_thomMap_comp_zero (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E U) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E V) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u)))
    (hUVn : ∀ k, k + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).singularCohomology (ModuleCat.of K K) K M k))
    (h : 0 + n = n) :
    Function.Bijective (ModuleCat.ofHom (thomMap F E M n 0 n h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) n) := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  have sq₃ := singularCohomologyMayerVietorisToBiprod_comp_biprod_map (M := M) (U := U) (V := V)
    u 0 n h
  have sq₄ := singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom (M := M) (U := U)
    (V := V) u 0 n h
  have hbi := bijective_biprod_map_thomMapOverHom u h (hΦU 0 n h) (hΦV 0 n h)
  have : Mono (TopCat.singularCohomologyPairMayerVietorisToBiprod
      (ModuleCat.of K K) K M (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n) := by
    rcases n with _ | k
    · exact TopCat.mono_singularCohomologyPairMayerVietorisToBiprod_zero _ _ _ _ _ hA hB hC hD
    · refine (TopCat.singularCohomologyPairMayerVietoris_exact₁ _ _ _ _ _ hA hB hC hD k
        (k + 1) rfl).mono_g (IsZero.eq_of_src ?_ _ _)
      exact (hUVn k rfl).of_iso
        (asIso (TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).hom k))
  refine ⟨fun x y hxy ↦ ?_, surjective_of_exact_of_comm
    (TopCat.singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV 0)
    (TopCat.singularCohomologyPairMayerVietoris_exact₂ _ _ _ _ _ hA hB hC hD n) sq₃ sq₄ hbi.2
    (bijective_thomMapOverHom_comp (thomPairOverInterIso F E U V).symm u h (hΦUV 0 n h)).1⟩
  -- The composite with the first map of the Mayer–Vietoris sequence of the pairs is a
  -- monomorphism, since the square through the first maps commutes.
  have := (ConcreteCategory.isIso_iff_bijective _).2 hbi
  have := TopCat.mono_singularCohomologyMayerVietorisToBiprod_zero (ModuleCat.of K K) K M
    (X := TopCat.of B) hU hV hUV
  have : Mono ((ModuleCat.ofHom (thomMap F E M n 0 n h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) n) ≫
        TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n) := by
    rw [← sq₃]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).1 (mono_of_mono _
    (TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n)) hxy

/-- The positive-degree case of the Mayer–Vietoris step, read on the union pair: the five lemma
applied to the ladder of Mayer–Vietoris sequences. -/
private theorem bijective_thomMap_comp_succ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E U) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E V) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u)))
    (q : ℕ) (h : q + 1 + n = q + n + 1) :
    Function.Bijective (ModuleCat.ofHom (thomMap F E M n (q + 1) (q + n + 1) h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) (q + n + 1)) := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  exact bijective_of_exact_of_comm
    (TopCat.singularCohomologyMayerVietoris_exact₃ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV q (q + 1) rfl)
    (TopCat.singularCohomologyMayerVietoris_exact₁ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV q (q + 1) rfl)
    (TopCat.singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV (q + 1))
    (TopCat.singularCohomologyPairMayerVietoris_exact₃ _ _ _ _ _ hA hB hC hD (q + n)
      (q + n + 1) rfl)
    (TopCat.singularCohomologyPairMayerVietoris_exact₁ _ _ _ _ _ hA hB hC hD (q + n)
      (q + n + 1) rfl)
    (TopCat.singularCohomologyPairMayerVietoris_exact₂ _ _ _ _ _ hA hB hC hD (q + n + 1))
    (singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom u q (q + n) rfl)
    (singularCohomologyMayerVietorisδ_comp_thomMap hU hV hUV u q (q + n) rfl)
    (singularCohomologyMayerVietorisToBiprod_comp_biprod_map u (q + 1) (q + n + 1) h)
    (singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom u (q + 1) (q + n + 1) h)
    (bijective_biprod_map_thomMapOverHom u rfl (hΦU q (q + n) rfl) (hΦV q (q + n) rfl)).2
    (bijective_thomMapOverHom_comp (thomPairOverInterIso F E U V).symm u rfl (hΦUV q (q + n) rfl))
    (bijective_biprod_map_thomMapOverHom u h (hΦU (q + 1) (q + n + 1) h)
      (hΦV (q + 1) (q + n + 1) h))
    (bijective_thomMapOverHom_comp (thomPairOverInterIso F E U V).symm u h
      (hΦUV (q + 1) (q + n + 1) h)).1

/-- **The Mayer–Vietoris step of the Thom isomorphism.** Let `U` and `V` be open sets covering the
base of a fibre bundle `E → B` and let `u ∈ Hⁿ(E, E₀; K)`. If the Thom maps of the restrictions of
`u` over `U`, `V` and `U ∩ V` are bijective in every degree, and
`Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V}; M)` vanishes, then the Thom map `a ↦ π^*a ⌣ u` of `u` is bijective
in every degree. -/
theorem thomMap_bijective_of_union_eq_univ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairOverMap F E (subset_univ U) ≫
        (thomPairOverUnivIso F E).hom) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairOverMap F E (subset_univ V) ≫
        (thomPairOverUnivIso F E).hom) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap (thomPairOverMap F E (subset_univ (U ∩ V)) ≫
        (thomPairOverUnivIso F E).hom) n u)))
    (hUVn : ∀ k, k + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).singularCohomology (ModuleCat.of K K) K M k))
    (p m : ℕ) (h : p + n = m) :
    Function.Bijective (thomMap F E M n p m h u) := by
  have := isIso_unionToThomPair (F := F) (E := E) hUV
  -- It suffices to show that the Thom map followed by the isomorphism onto the cohomology of the
  -- union pair of the Mayer–Vietoris sequence is bijective.
  suffices hI : Function.Bijective (ModuleCat.ofHom (thomMap F E M n p m h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) m) by
    have := (ConcreteCategory.isIso_iff_bijective _).2 hI
    have := IsIso.of_isIso_comp_right (ModuleCat.ofHom (thomMap F E M n p m h u))
      (TopPair.singularCohomologyMap (unionToThomPair F E U V) m)
    exact ConcreteCategory.bijective_of_isIso (ModuleCat.ofHom (thomMap F E M n p m h u))
  rcases p with _ | q
  · obtain rfl : m = n := by omega
    exact bijective_thomMap_comp_zero hU hV hUV u hΦU hΦV hΦUV hUVn h
  · obtain rfl : m = q + n + 1 := by omega
    exact bijective_thomMap_comp_succ hU hV hUV u hΦU hΦV hΦUV q h

end MayerVietoris

end TauCeti
