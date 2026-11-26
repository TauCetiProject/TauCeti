/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
import TauCeti.AlgebraicTopology.Cohomology.Collar
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.Geometry.Manifold.Boundary.Collar.Retraction

/-!
# Lefschetz duality

Let `X` be a compact Hausdorff space and `ι : M → X` an open embedding of an oriented `n`-manifold
`M` without boundary, whose complement `∂X = X ∖ ι(M)` is the image of a collared map
`f : N → X` (`TauCeti.IsCollared`), as for a compact topological manifold with boundary or with
corners and its interior. Let `L` be an abelian group. Capping with the fundamental class
`[X, ∂X] ∈ Hₙ(X, ∂X; ℤ)` relative to the boundary
(`TauCeti.HomologicalOrientation.fundamentalClassRel`) is a map

`Hᵖ(X, ∂X; L) ⟶ H_q(X; L)`, `α ↦ [X, ∂X] ⌢ α`, `p + q = n`

(`TauCeti.HomologicalOrientation.capFundamentalClassRel`), and **Lefschetz duality** asserts that it
is bijective (`TauCeti.HomologicalOrientation.bijective_capFundamentalClassRel`). For `∂X = ∅` this
is Poincaré duality for the closed manifold `X`.

The proof is Hatcher's, through Poincaré duality for the interior. For `0 < t`, let
`Cₜ = c(N × [0, t))` be the collar of depth less than `t` and `Kₜ = X ∖ Cₜ`, a compact subset of
`ι(M)`. Then:

* restriction `Hᵖ(X, X ∖ Kₜ) = Hᵖ(X, Cₜ) ⟶ Hᵖ(X, ∂X)` is an isomorphism, since the collar deforms
  `Cₜ` onto `∂X` relative to `∂X`
  (`TauCeti.IsCollar.isIso_singularCohomologyMap_ofSubsetMap_collarPart`);
* excision identifies `Hᵖ(X, X ∖ Kₜ)` with `Hᵖ(M, M ∖ ι⁻¹(Kₜ))`, and these groups compute the
  cohomology with compact supports of `M`: every compact subset of `M` misses some collar
  (`TauCeti.IsCollar.exists_disjoint_collarPart`), and restriction between two of them is an
  isomorphism, since both are isomorphic to `Hᵖ(X, ∂X)`;
* `[X, ∂X]` restricts to the fundamental class of `M` along `ι⁻¹(Kₜ)`, so by naturality of the
  cap product, capping with `[X, ∂X]` is the duality map of `M` followed by the map induced by `ι`;
* the duality map of `M` is bijective (`TauCeti.HomologicalOrientation.bijective_dualityMap`), and
  `ι` is a homotopy equivalence, since the collar pushes `X` off its boundary
  (`TauCeti.IsCollar.homotopyEquivOfRangeEq`).

## Main definitions

* `TauCeti.HomologicalOrientation.capFundamentalClassRel`: capping with the fundamental class
  relative to the boundary, `Hᵖ(X, ∂X; L) ⟶ H_q(X; L)`.

## Main results

* `TauCeti.HomologicalOrientation.capFundamentalClassRel_restrict`: for compact `K ⊆ M`, on
  classes restricted from `Hᵖ(X, X ∖ ι(K))`, capping with `[X, ∂X]` is capping with the
  fundamental class of `M` along `K` after excision, followed by the map induced by `ι`.
* `TauCeti.HomologicalOrientation.bijective_capFundamentalClassRel`: **Lefschetz duality**, and
  `TauCeti.HomologicalOrientation.isIso_capFundamentalClassRel` as an isomorphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.43 and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module TopologicalSpace Topology Set

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {ι : M → X}
  {f : N → X} [TopologicalSpace M] [T2Space X] [CompactSpace X] [T2Space M] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f) (L : ModuleCat.{0} ℤ)

/-- **Capping with the fundamental class relative to the boundary**: the map
`Hᵖ(X, ∂X; L) ⟶ H_q(X; L)`, `α ↦ [X, ∂X] ⌢ α`, for `p + q = n`, where the boundary
`∂X = X ∖ ι(M)` is the complement of the interior. -/
def capFundamentalClassRel (p q : ℕ) (h : p + q = n) :
    (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj
        (TopCat.of X) :=
  (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCapWith L
    (o.fundamentalClassRel hn hι hιf hf) p q h

/-- Capping with the relative fundamental class evaluates the relative cap product at
`[X, ∂X]`. -/
lemma capFundamentalClassRel_apply (p q : ℕ) (h : p + q = n)
    (α : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.capFundamentalClassRel hn hι hιf hf L p q h α =
      ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h α).hom (o.fundamentalClassRel hn hι hιf hf) :=
  TopPair.singularCapWith_apply _ L _ p q h α

/-- **Capping with `[X, ∂X]` through the interior.** For compact `K ⊆ M`, on a class restricted
from `Hᵖ(X, X ∖ ι(K))`, capping with the relative fundamental class is capping the excised class in
`Hᵖ(M, M ∖ K)` with the fundamental class of `M` along `K`, followed by the map induced by `ι`. -/
theorem capFundamentalClassRel_restrict (K : Compacts (TopCat.of M)) (p q : ℕ) (h : p + q = n)
    (β : (TopPair.ofSubset ((K.map (TopCat.ofHom ⟨ι, hι.continuous⟩)
      (TopCat.ofHom ⟨ι, hι.continuous⟩).hom.continuous : Set (TopCat.of X)))ᶜ).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.capFundamentalClassRel hn hι hιf hf L p q h (TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (TopCat.mapsTo_id_compl
          (S := (K.map (TopCat.ofHom ⟨ι, hι.continuous⟩)
            (TopCat.ofHom ⟨ι, hι.continuous⟩).hom.continuous : Set (TopCat.of X)))
          (image_subset_range ι K))) p β) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopCat.ofHom ⟨ι, hι.continuous⟩)
        (o.capFundamentalClassOn hn L K.isCompact p q h
          (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (TopCat.ofHom ⟨ι, hι.continuous⟩)
            (TopCat.mapsTo_compl_compacts_map hι.injective K)) p β)) := by
  -- Naturality of the cap product along the identity of `X`, from `(X, ∂X)` to `(X, X ∖ ι(K))`.
  have h₁ := ConcreteCategory.congr_hom (TopPair.singularCap_naturality
    (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (TopCat.mapsTo_id_compl (image_subset_range ι K))) ℤ
    (ρ_ _).inv (ρ_ L).hom p q n h β) (o.fundamentalClassRel hn hι hιf hf)
  -- Naturality of the cap product along `ι`, from `(M, M ∖ K)` to `(X, X ∖ ι(K))`.
  have h₂ := ConcreteCategory.congr_hom (TopPair.singularCap_naturality
    (TopPair.ofSubsetMap (TopCat.ofHom ⟨ι, hι.continuous⟩)
      (TopCat.mapsTo_compl_compacts_map hι.injective K)) ℤ (ρ_ _).inv (ρ_ L).hom p q n h β)
    (o.fundamentalClassOn hn K.isCompact)
  -- The relative fundamental class restricts to the image of the fundamental class along `K`.
  have hμ := o.localHomologyRestriction_fundamentalClassRel_image hn hι hιf hf K.isCompact
  rw [localHomologyRestriction_def, localHomologyMap_def] at hμ
  have hfst : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (TopPair.Hom.fst (TopPair.ofSubsetMap (𝟙 (TopCat.of X))
        (TopCat.mapsTo_id_compl (image_subset_range ι K)))) = 𝟙 _ := by
    rw [TopPair.ofSubsetMap_fst]
    exact CategoryTheory.Functor.map_id _ _
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfst] at h₁
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst] at h₂
  rw [capFundamentalClassRel_apply, capFundamentalClassOn_apply]
  -- The source and target of the identity from `hfst` agree only after unfolding
  -- `TopPair.ofSubset`, so `ConcreteCategory.id_apply` applies by `exact` but not by `rw`.
  exact (ConcreteCategory.id_apply _).symm.trans (h₁.trans ((congrArg _ hμ).trans h₂.symm))

/-! ### Proof of Lefschetz duality -/

section Proof

variable {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c)

/-- The interior `ι : M → X` as a morphism of spaces. -/
private abbrev interiorHom (hι : IsOpenEmbedding ι) : TopCat.of M ⟶ TopCat.of X :=
  TopCat.ofHom ⟨ι, hι.continuous⟩

/-- The points of the interior outside the collar of depth less than `s`, a compact set. -/
private def interiorCompl {s : ℝ} (hs : 0 < s) : Compacts (TopCat.of M) :=
  ⟨ι ⁻¹' (collarPart c s)ᶜ, hc.isCompact_preimage_compl_collarPart hι.isInducing hιf hs⟩

/-- Its image in `X`, the complement of the collar of depth less than `s`. -/
private abbrev collarCompl {s : ℝ} (hs : 0 < s) : Compacts (TopCat.of X) :=
  (interiorCompl hι hιf hc hs).map (interiorHom hι) (interiorHom hι).hom.continuous

omit [T2Space X] [T2Space M] in
private lemma compl_collarCompl {s : ℝ} (hs : 0 < s) :
    ((collarCompl hι hιf hc hs : Set (TopCat.of X)))ᶜ = collarPart c s := by
  rw [Compacts.coe_map, compl_eq_comm]
  exact (image_preimage_eq_of_subset (hc.compl_collarPart_subset_range hιf hs)).symm

omit [T2Space X] [T2Space M] in
private lemma compl_range_subset_compl_collarCompl {s : ℝ} (hs : 0 < s) :
    MapsTo (𝟙 (TopCat.of X)) ((range ι)ᶜ : Set (TopCat.of X))
      (collarCompl hι hιf hc hs : Set (TopCat.of X))ᶜ :=
  TopCat.mapsTo_id_compl (image_subset_range ι _)

omit [T2Space X] [T2Space M] in
/-- Restriction `Hᵖ(X, Cₛ) ⟶ Hᵖ(X, ∂X)` is an isomorphism. -/
private lemma isIso_restrict {s : ℝ} (hs : 0 < s) (p : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (compl_range_subset_compl_collarCompl hι hιf hc hs))
      p) :=
  hc.isIso_singularCohomologyMap_ofSubsetMap_collarPart _ (by rw [hιf, compl_compl]) hs
    (compl_collarCompl hι hιf hc hs) _ ℤ L p

omit [T2Space M] in
/-- Excision `Hᵖ(X, Cₛ) ⟶ Hᵖ(M, M ∖ ι⁻¹(Kₛ))` is an isomorphism. -/
private lemma isIso_excision {s : ℝ} (hs : 0 < s) (p : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (TopPair.ofSubsetMap (interiorHom hι)
        (TopCat.mapsTo_compl_compacts_map hι.injective (interiorCompl hι hιf hc hs))) p) :=
  TopCat.isIso_singularCohomologyMap_ofSubsetMap_compl_compacts_map hι _ p

omit [T2Space M] in
/-- For `0 < s` and `0 < t` with `ι⁻¹(Kₜ) ⊆ ι⁻¹(Kₛ)`, restriction
`Hᵖ(M, M ∖ ι⁻¹(Kₜ)) ⟶ Hᵖ(M, M ∖ ι⁻¹(Kₛ))` is an isomorphism: in `X`, both groups are isomorphic to
`Hᵖ(X, ∂X)`. -/
private lemma isIso_restrict_interiorCompl {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (p : ℕ)
    (hle : interiorCompl hι hιf hc ht ≤ interiorCompl hι hιf hc hs) :
    IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (TopCat.mapsTo_id_compl_compacts hle)) p) := by
  have hX : MapsTo (𝟙 (TopCat.of X)) (collarCompl hι hιf hc hs : Set (TopCat.of X))ᶜ
      (collarCompl hι hιf hc ht : Set (TopCat.of X))ᶜ :=
    TopCat.mapsTo_id_compl (image_mono hle)
  -- In `X`, the restriction from `Kₜ` to `Kₛ` is an isomorphism, since both restrictions to `∂X`
  -- are.
  have := isIso_restrict hι hιf L hc hs p
  have := isIso_restrict hι hιf L hc ht p
  have hrX : TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
        (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) hX) p ≫
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (compl_range_subset_compl_collarCompl hι hιf hc hs))
        p =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (compl_range_subset_compl_collarCompl hι hιf hc ht))
        p := by
    rw [← TopPair.singularCohomologyMap_comp]
    congr 1
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (Category.id_comp _)
  have := IsIso.of_isIso_fac_right hrX
  -- Excision carries it to the restriction in `M`.
  have := isIso_excision hι hιf L hc hs p
  have := isIso_excision hι hιf L hc ht p
  have hsq : TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
        (TopPair.ofSubsetMap (interiorHom hι)
          (TopCat.mapsTo_compl_compacts_map hι.injective (interiorCompl hι hιf hc ht))) p ≫
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (TopCat.mapsTo_id_compl_compacts hle)) p =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) hX) p ≫
        TopPair.singularCohomologyMap (TopPair.ofSubsetMap (interiorHom hι)
          (TopCat.mapsTo_compl_compacts_map hι.injective (interiorCompl hι hιf hc hs))) p := by
    rw [← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp]
    congr 1
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact IsIso.of_isIso_fac_left hsq

variable [CompactSpace N]

omit [T2Space M] in
/-- Restriction `Hᵖ(M, M ∖ ι⁻¹(Kₜ)) ⟶ Hᵖ_c(M)` is an isomorphism, for `0 < t`. -/
private lemma isIso_compactSupportCohomologyι_interiorCompl {t : ℝ} (ht : 0 < t) (p : ℕ) :
    IsIso (TopCat.compactSupportCohomologyι (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      p (interiorCompl hι hιf hc ht)) := by
  refine TopCat.isIso_compactSupportCohomologyι_of_forall_exists fun K ↦ ?_
  -- The image of `K` misses some collar, of depth `s ≤ t`.
  obtain ⟨s, hs, hK⟩ := hc.exists_disjoint_collarPart (K.isCompact.image hι.continuous)
    (by rw [← subset_compl_iff_disjoint_right, ← hιf]; exact image_subset_range ι K)
  have hs' : 0 < min s t := lt_min hs ht
  have hle : interiorCompl hι hιf hc ht ≤ interiorCompl hι hιf hc hs' :=
    fun x hx hx' ↦ hx (collarPart_mono (min_le_right s t) hx')
  refine ⟨interiorCompl hι hιf hc hs', hle, fun x hx hx' ↦ ?_,
    isIso_restrict_interiorCompl hι hιf L hc hs' ht p hle⟩
  exact disjoint_left.1 hK (mem_image_of_mem ι hx) (collarPart_mono (min_le_left s t) hx')

/-- Capping with the fundamental class of `M` along `ι⁻¹(Kₜ)` is bijective, for `0 < t`. -/
private lemma bijective_capFundamentalClassOn_interiorCompl {t : ℝ} (ht : 0 < t) (p q : ℕ)
    (h : p + q = n) :
    Function.Bijective
      (o.capFundamentalClassOn hn L (interiorCompl hι hιf hc ht).isCompact p q h) := by
  have := isIso_compactSupportCohomologyι_interiorCompl hι hιf L hc ht p
  convert (o.bijective_dualityMap hn L p q h).comp (ConcreteCategory.bijective_of_isIso
    (TopCat.compactSupportCohomologyι p (interiorCompl hι hιf hc ht))) using 1
  funext α
  rw [Function.comp_apply, ← ConcreteCategory.comp_apply, compactSupportCohomologyι_dualityMap]

omit [CompactSpace X] [T2Space M] in
include hιf hc in
/-- The map `H_q(M; L) ⟶ H_q(X; L)` induced by the interior is bijective. -/
private lemma bijective_singularHomologyMap_interiorHom (q : ℕ) :
    Function.Bijective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (interiorHom hι)) := by
  have : TopCat.ofHom (hc.homotopyEquivOfRangeEq hι.isEmbedding hιf).toFun = interiorHom hι :=
    TopCat.hom_ext (ContinuousMap.ext fun x ↦
      congrFun (hc.coe_homotopyEquivOfRangeEq hι.isEmbedding hιf) x)
  rw [← this, ← ContinuousMap.HomotopyEquiv.singularHomologyIso_hom]
  exact ConcreteCategory.bijective_of_isIso _

end Proof

/-- **Lefschetz duality.** Let `X` be a compact Hausdorff space and `ι : M → X` an open embedding
of an oriented `n`-manifold without boundary whose complement `∂X = X ∖ ι(M)` is collared, such as
a compact oriented topological manifold with boundary or with corners and its interior. Then
capping with the fundamental class relative to the boundary, `α ↦ [X, ∂X] ⌢ α`, is a bijection
`Hᵖ(X, ∂X; L) → H_q(X; L)` for `p + q = n`. -/
theorem bijective_capFundamentalClassRel (p q : ℕ) (h : p + q = n) :
    Function.Bijective (o.capFundamentalClassRel hn hι hιf hf L p q h) := by
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  have : CompactSpace N := IsClosedEmbedding.compactSpace ⟨hc.isEmbedding, by
    rw [← compl_compl (range f), ← hιf]
    exact hι.isOpen_range.isClosed_compl⟩
  have ht : (0 : ℝ) < 1 / 2 := by norm_num
  have := isIso_restrict hι hιf L hc ht p
  have := isIso_excision hι hιf L hc ht p
  -- Precomposed with the isomorphism `Hᵖ(X, C₁/₂) ≅ Hᵖ(X, ∂X)`, capping with `[X, ∂X]` is excision,
  -- duality on the interior and the map induced by the interior, all bijective.
  rw [← Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso
    (TopPair.singularCohomologyMap
      (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (compl_range_subset_compl_collarCompl hι hιf hc ht))
      p))]
  convert (bijective_singularHomologyMap_interiorHom hι hιf L hc q).comp
    ((o.bijective_capFundamentalClassOn_interiorCompl hn hι hιf L hc ht p q h).comp
      (ConcreteCategory.bijective_of_isIso (TopPair.singularCohomologyMap
        (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L) (TopPair.ofSubsetMap (interiorHom hι)
          (TopCat.mapsTo_compl_compacts_map hι.injective (interiorCompl hι hιf hc ht))) p))) using 1
  funext β
  exact o.capFundamentalClassRel_restrict hn hι hιf hf L (interiorCompl hι hιf hc ht) p q h β

/-- **Lefschetz duality**, as an isomorphism `Hᵖ(X, ∂X; L) ≅ H_q(X; L)`. -/
theorem isIso_capFundamentalClassRel (p q : ℕ) (h : p + q = n) :
    IsIso (o.capFundamentalClassRel hn hι hιf hf L p q h) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (o.bijective_capFundamentalClassRel hn hι hιf hf L p q h)

end HomologicalOrientation

end TauCeti
