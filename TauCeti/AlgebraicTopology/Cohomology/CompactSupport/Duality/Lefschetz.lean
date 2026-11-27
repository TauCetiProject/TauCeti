/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.AbsoluteRelative
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
import TauCeti.Algebra.Ring.Parity
import TauCeti.AlgebraicTopology.Cohomology.Collar
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.LocalHomology.BoundaryFundamentalClass
import TauCeti.CategoryTheory.Linear.Int
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

Capping absolute cohomology with `[X, ∂X]`, with values in relative homology
(`TopPair.absoluteSingularCap`), is a map

`Hᵖ(X; L) ⟶ H_q(X, ∂X; L)`, `α ↦ [X, ∂X] ⌢ α`, `p + q = n`

(`TauCeti.HomologicalOrientation.absoluteCapFundamentalClassRel`), and it is also bijective when the
boundary is a manifold of dimension `n - 1`, that is, when `N` is
(`TauCeti.HomologicalOrientation.bijective_absoluteCapFundamentalClassRel`). The proof is Hatcher's
five-lemma argument. Capping with `[X, ∂X]` maps the long exact cohomology sequence of `(X, ∂X)`
to its long exact homology sequence, up to the sign `(-1)ᵖ` at the connecting morphisms
(`TopPair.singularCap_singularCohomologyδ`, `TopPair.absoluteSingularCap_singularCohomologyπ`,
`TopPair.absoluteSingularCap_comp_singularHomologyδ`). On `Hᵖ(X, ∂X)` this is the duality above,
and on the cohomology of `∂X` it is capping with `∂[X, ∂X]`, a fundamental class of the closed
manifold `∂X`
(`TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`), which
is Poincaré duality of `∂X` (`TauCeti.IsFundamentalClass.bijective_singularCapAddHom`). At the
ends of the sequences, the homology and the cohomology of `∂X` vanish above its dimension
(`TauCeti.isZero_singularHomology_of_lt`, `TopCat.isZero_singularCohomology_of_finrank_lt`).
Without a manifold structure on the boundary there is no duality on `∂X` for this argument to use.

## Main definitions

* `TauCeti.HomologicalOrientation.capFundamentalClassRel`: capping with the fundamental class
  relative to the boundary, `Hᵖ(X, ∂X; L) ⟶ H_q(X; L)`.
* `TauCeti.HomologicalOrientation.absoluteCapFundamentalClassRel`: capping absolute cohomology with
  the fundamental class relative to the boundary, `Hᵖ(X; L) ⟶ H_q(X, ∂X; L)`.

## Main results

* `TauCeti.HomologicalOrientation.capFundamentalClassRel_restrict`: for compact `K ⊆ M`, on
  classes restricted from `Hᵖ(X, X ∖ ι(K))`, capping with `[X, ∂X]` is capping with the
  fundamental class of `M` along `K` after excision, followed by the map induced by `ι`.
* `TauCeti.HomologicalOrientation.bijective_capFundamentalClassRel`: **Lefschetz duality**, and
  `TauCeti.HomologicalOrientation.isIso_capFundamentalClassRel` as an isomorphism.
* `TauCeti.HomologicalOrientation.bijective_absoluteCapFundamentalClassRel`: **Lefschetz duality
  from absolute cohomology**, and
  `TauCeti.HomologicalOrientation.isIso_absoluteCapFundamentalClassRel` as an isomorphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.43 and its proof, for both forms.
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

/-! ### Lefschetz duality from absolute cohomology to relative homology -/

/-- **Capping absolute cohomology with the fundamental class relative to the boundary**: the map
`Hᵖ(X; L) ⟶ H_q(X, ∂X; L)`, `α ↦ [X, ∂X] ⌢ α`, for `p + q = n`, where the boundary
`∂X = X ∖ ι(M)` is the complement of the interior. -/
def absoluteCapFundamentalClassRel (p q : ℕ) (h : p + q = n) :
    (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p ⟶
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology L q :=
  -- As for `TopPair.singularCapWith`, the `ℤ`-linear map is built from the additive one.
  let g := (LinearMap.applyₗ (R := ℤ) (o.fundamentalClassRel hn hι hιf hf)).toAddMonoidHom.comp <|
    ModuleCat.homAddEquiv.toAddMonoidHom.comp
      ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).absoluteSingularCap
        (C := ModuleCat.{0} ℤ) ℤ (ρ_ _).inv (ρ_ L).hom p q n h).toAddMonoidHom
  ModuleCat.ofHom { g with map_smul' := map_intCast_smul g ℤ ℤ }

/-- Capping absolute cohomology with the relative fundamental class evaluates the cap product of
absolute cohomology with relative homology at `[X, ∂X]`. -/
lemma absoluteCapFundamentalClassRel_apply (p q : ℕ) (h : p + q = n)
    (α : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h α =
      ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).absoluteSingularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h α).hom (o.fundamentalClassRel hn hι hιf hf) :=
  (rfl)

section AbsoluteProof

/-! The boundary `∂X` is assumed here to be a manifold of dimension `n - 1`, charted on `E'`; it is
compact, as a closed subset of `X`. -/

omit [T2Space X] [T2Space M] in
include hι in
/-- The boundary `∂X = X ∖ ι(M)` is compact, as a closed subset of the compact space `X`. -/
private lemma compactSpace_boundary : CompactSpace ((range ι)ᶜ : Set X) :=
  isCompact_iff_compactSpace.1 hι.isOpen_range.isClosed_compl.isCompact

/-- Two equal signs `(-1)ᵖ` acting on an abelian group cancel. -/
private lemma neg_one_pow_zsmul_neg_one_pow_zsmul {G : Type*} [AddCommGroup G] (p : ℕ) (a : G) :
    (-1 : ℤ) ^ p • (-1 : ℤ) ^ p • a = a := by
  rw [smul_smul, neg_one_pow_mul_neg_one_pow, one_zsmul]

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [ChartedSpace E' ((range ι)ᶜ : Set X)]

omit [FiniteDimensional ℝ E'] [ChartedSpace E' ((range ι)ᶜ : Set X)] in
/-- The boundary `∂[X, ∂X] ∈ Hₙ₋₁(∂X; ℤ)` of the relative fundamental class, a fundamental class of
the boundary. It is typed as a class of the singular homology of the space `∂X`, rather than of
the subspace of the pair, so that `TopCat.singularCapAddHom_apply` rewrites the cap products with
it. -/
private abbrev boundaryClass (hE' : finrank ℝ E' + 1 = n) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (finrank ℝ E')).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of ((range ι)ᶜ : Set X)) :=
  (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
    (ModuleCat.of ℤ (ULift.{0} ℤ)) n (finrank ℝ E') hE' (o.fundamentalClassRel hn hι hιf hf)

/-- Poincaré duality on the boundary, for its fundamental class `∂[X, ∂X]`. -/
private lemma bijective_singularCapAddHom_boundary (hE' : finrank ℝ E' + 1 = n) (p' q' : ℕ)
    (h' : p' + q' = finrank ℝ E') :
    Function.Bijective ((TopCat.of ((range ι)ᶜ : Set X)).singularCapAddHom ℤ (ρ_ _).inv (ρ_ L).hom
      h' (o.boundaryClass hn hι hιf hf hE')) := by
  have := compactSpace_boundary hι
  subst hE'
  exact (o.isFundamentalClass_singularHomologyδ_fundamentalClassRel hn hι hιf hf)
    |>.bijective_singularCapAddHom rfl L p' q' h'

omit [FiniteDimensional ℝ E'] [ChartedSpace E' ((range ι)ᶜ : Set X)] in
/-- **The square at the connecting morphisms.** Capping with `[X, ∂X]` and taking the boundary is,
up to the sign `(-1)ᵖ`, restricting to `∂X` and capping with `∂[X, ∂X]`. -/
private lemma singularHomologyδ_absoluteCapFundamentalClassRel (hE' : finrank ℝ E' + 1 = n)
    (p q q' : ℕ) (h : p + q = n) (hq : q' + 1 = q)
    (x : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ L q q' hq
        (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h x) =
      ((-1 : ℤ) ^ p) • ((TopCat.of ((range ι)ᶜ : Set X)).singularCap ℤ (ρ_ _).inv (ρ_ L).hom p q'
        (finrank ℝ E') (by omega) (TopCat.singularCohomologyMap
          (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).map p x)).hom
        (o.boundaryClass hn hι hιf hf hE') := by
  subst hq hE'
  exact ConcreteCategory.congr_hom ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X)))
    |>.absoluteSingularCap_comp_singularHomologyδ ℤ (ρ_ _).inv (ρ_ L).hom p q' _ (q' + 1) _
      (by omega) h x) (o.fundamentalClassRel hn hι hιf hf)

/-- **Injectivity at the subspace.** A class of `Hᵖ(X)` whose cap product with `[X, ∂X]` vanishes
restricts to zero on `∂X`. -/
private lemma singularCohomologyMap_eq_zero (hE' : finrank ℝ E' + 1 = n) (p q : ℕ) (h : p + q = n)
    (x : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p)
    (hx : o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h x = 0) :
    TopCat.singularCohomologyMap (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).map p x =
      0 := by
  rcases q with _ | q'
  · -- `Hⁿ(∂X) = 0` above the dimension of the boundary.
    have := compactSpace_boundary hι
    -- The vanishing theorem is stated for the `ℤ`-linear structure of a category of modules, the
    -- cohomology here for that of a preadditive category; they agree by uniqueness.
    have hz : IsZero ((TopCat.of ((range ι)ᶜ : Set X)).singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) := by
      convert TopCat.isZero_singularCohomology_of_finrank_lt (ModuleCat.of ℤ (ULift.{0} ℤ)) L
        (M := ((range ι)ᶜ : Set X)) (E := E') (m := p) (by omega)
      exact Subsingleton.elim _ _
    exact (ModuleCat.subsingleton_of_isZero hz).elim _ _
  · have h₀ := o.singularHomologyδ_absoluteCapFundamentalClassRel hn hι hιf hf L hE' p (q' + 1) q'
      h rfl x
    rw [hx, map_zero] at h₀
    refine (injective_iff_map_eq_zero _).1
      (o.bijective_singularCapAddHom_boundary hn hι hιf hf L hE' p q' (by omega)).1 _ ?_
    refine (TopCat.singularCapAddHom_apply _ _ _ _ _ _ _).trans ?_
    -- Cancel the sign `(-1)ᵖ`.
    exact (neg_one_pow_zsmul_neg_one_pow_zsmul p _).symm.trans
      ((congrArg _ h₀.symm).trans (zsmul_zero _))

/-- **Injectivity at the pair.** A relative class of `Hᵖ(X, ∂X)` whose dual in `H_q(X)` comes from
`∂X` maps to zero in `Hᵖ(X)`. -/
private lemma singularCohomologyπ_eq_zero (hE' : finrank ℝ E' + 1 = n) (p q : ℕ) (h : p + q = n)
    (y : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p)
    (z : ((TopCat.toSSet.obj (TopCat.of ((range ι)ᶜ : Set X))).homology L q : ModuleCat.{0} ℤ))
    (hz : SSet.homologyMap (TopCat.toSSet.map
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).map) L q z =
        o.capFundamentalClassRel hn hι hιf hf L p q h y) :
    (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomologyπ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p y = 0 := by
  subst hE'
  rcases p with _ | p'
  · -- `Hₙ(∂X) = 0` above the dimension of the boundary, so `y = 0`.
    have hz₀ : z = 0 := (ModuleCat.subsingleton_of_isZero (isZero_singularHomology_of_lt L
      (M := ((range ι)ᶜ : Set X)) (E := E') rfl (k := q) (by omega))).elim _ _
    have hy : y = 0 := (o.bijective_capFundamentalClassRel hn hι hιf hf L 0 q h).1 <|
      hz.symm.trans <| by
        rw [hz₀]
        exact (map_zero _).trans (map_zero _).symm
    rw [hy, map_zero]
  · -- `z` is dual to a class `w` of `∂X`, and `y = δw`, which vanishes on `X`.
    obtain ⟨w, rfl⟩ := (o.bijective_singularCapAddHom_boundary hn hι hιf hf L rfl p' q
      (by omega)).2 z
    rw [TopCat.singularCapAddHom_apply] at hz
    have hy : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p' (p' + 1) rfl w = y :=
      (o.bijective_capFundamentalClassRel hn hι hιf hf L (p' + 1) q h).1 <|
        (o.capFundamentalClassRel_apply hn hι hιf hf L (p' + 1) q h _).trans <|
          (ConcreteCategory.congr_hom ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X)))
            |>.singularCap_singularCohomologyδ ℤ (ρ_ _).inv (ρ_ L).hom p' q _ (by omega) w)
              (o.fundamentalClassRel hn hι hιf hf)).trans hz
    rw [← hy]
    exact ConcreteCategory.congr_hom ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X)))
      |>.singularCohomologyδ_comp_singularCohomologyπ _ ℤ L p' (p' + 1) rfl) w

/-- **Surjectivity up to the pair.** Every class `c` of `H_q(X, ∂X)` is the dual of a class of
`Hᵖ(X)` up to the image of a class of `H_q(X)`. -/
private lemma exists_sub_mem_range (hE' : finrank ℝ E' + 1 = n) (p q : ℕ) (h : p + q = n)
    (c : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology
      (C := ModuleCat.{0} ℤ) L q) :
    ∃ x : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p,
      c - o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h x ∈ Set.range
        ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyπ
          (C := ModuleCat.{0} ℤ) L q) := by
  rcases q with _ | q'
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance c
  subst hE'
  let P := TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))
  -- `(-1)ᵖ ∂c` is dual to a class `w` of `∂X`.
  obtain ⟨w, hw⟩ := (o.bijective_singularCapAddHom_boundary hn hι hιf hf L rfl p q'
    (by omega)).2 (((-1 : ℤ) ^ p) • P.singularHomologyδ L (q' + 1) q' rfl c)
  rw [TopCat.singularCapAddHom_apply] at hw
  -- `δw` is dual to `(-1)ᵖ i_*∂c = 0`, so it vanishes and `w` is restricted from `X`.
  have hδw : P.singularCohomologyδ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p (p + 1) rfl w = 0 := by
    refine (o.bijective_capFundamentalClassRel hn hι hιf hf L (p + 1) q' (by omega)).1 <|
      (o.capFundamentalClassRel_apply hn hι hιf hf L (p + 1) q' (by omega) _).trans <|
        (ConcreteCategory.congr_hom (P.singularCap_singularCohomologyδ ℤ (ρ_ _).inv (ρ_ L).hom p q'
          _ (by omega) w) (o.fundamentalClassRel hn hι hιf hf)).trans ?_
    have hi : SSet.homologyMap (TopCat.toSSet.map P.map) L q'
        (P.singularHomologyδ L (q' + 1) q' rfl c) = 0 :=
      (ConcreteCategory.comp_apply _ _ c).symm.trans
        (by simpa using ConcreteCategory.congr_hom (P.singularHomologyδ_comp L (q' + 1) q' rfl) c)
    refine (ConcreteCategory.comp_apply _ _ _).trans <| (ConcreteCategory.comp_apply _ _ _).trans <|
      (congrArg (SSet.homologyMap (TopCat.toSSet.map P.map) L q').hom hw).trans ?_
    refine (map_zsmul (SSet.homologyMap (TopCat.toSSet.map P.map) L q').hom _ _).trans ?_
    rw [hi, zsmul_zero]
    exact (map_zero _).symm
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (P.singularCohomology_exact_subspace (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p (p + 1) rfl) w hδw
  refine ⟨x, (ShortComplex.moduleCat_exact_iff _).1
    (P.singularHomology_exact_relative L (q' + 1) q' rfl) _ ?_⟩
  dsimp only
  rw [map_sub, o.singularHomologyδ_absoluteCapFundamentalClassRel hn hι hιf hf L rfl p (q' + 1) q'
    h rfl x, hx, hw]
  exact sub_eq_zero.2 (neg_one_pow_zsmul_neg_one_pow_zsmul p _).symm

/-- Lefschetz duality from absolute cohomology, for a boundary carrying a manifold structure. -/
private lemma bijective_absoluteCapFundamentalClassRel_aux (hE' : finrank ℝ E' + 1 = n)
    (p q : ℕ) (h : p + q = n) :
    Function.Bijective (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h) := by
  let P := TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))
  -- The square at the maps `j^* : Hᵖ(X, ∂X) ⟶ Hᵖ(X)` and `j_* : H_q(X) ⟶ H_q(X, ∂X)`.
  have hj (y : P.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
      o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h
          (P.singularCohomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p y) =
        P.singularHomologyπ L q (o.capFundamentalClassRel hn hι hιf hf L p q h y) :=
    (o.absoluteCapFundamentalClassRel_apply hn hι hιf hf L p q h _).trans <|
      (ConcreteCategory.congr_hom (P.absoluteSingularCap_singularCohomologyπ ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h y) (o.fundamentalClassRel hn hι hιf hf)).trans <|
          (ConcreteCategory.comp_apply _ _ _).trans
            (congrArg _ (o.capFundamentalClassRel_apply hn hι hιf hf L p q h y).symm)
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun c ↦ ?_⟩
  · -- `x` restricts to zero on `∂X`, so it is `j^* y` for a relative class `y`, whose dual comes
    -- from `∂X`; so `x = 0`.
    obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_space _ ℤ L p) x
      (o.singularCohomologyMap_eq_zero hn hι hιf hf L hE' p q h x hx)
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (P.singularHomology_exact_space L q)
      (o.capFundamentalClassRel hn hι hιf hf L p q h y) ((hj y).symm.trans hx)
    exact o.singularCohomologyπ_eq_zero hn hι hιf hf L hE' p q h y z hz
  · -- Up to the dual of a class of `X`, `c` is `j_*` of a dual of a relative class.
    obtain ⟨x, b, hb⟩ := o.exists_sub_mem_range hn hι hιf hf L hE' p q h c
    obtain ⟨y, rfl⟩ := (o.bijective_capFundamentalClassRel hn hι hιf hf L p q h).2 b
    let x' : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p :=
      P.singularCohomologyπ _ ℤ L p y
    refine ⟨x + x', ?_⟩
    rw [map_add, hj, hb, add_sub_cancel]

end AbsoluteProof

/-- **Lefschetz duality from absolute cohomology.** Let `X` be a compact Hausdorff space and
`ι : M → X` an open embedding of an oriented `n`-manifold without boundary whose complement
`∂X = X ∖ ι(M)` is the image of a collared map from a manifold `N` of dimension `n - 1`, such as a
compact oriented topological manifold with boundary and its interior. Then capping with the
fundamental class relative to the boundary, `α ↦ [X, ∂X] ⌢ α`, is a bijection
`Hᵖ(X; L) → H_q(X, ∂X; L)` for `p + q = n`. -/
theorem bijective_absoluteCapFundamentalClassRel {E' : Type} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' N] (hE' : finrank ℝ E' + 1 = n)
    (p q : ℕ) (h : p + q = n) :
    Function.Bijective (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h) := by
  -- The collar identifies `N` with the boundary, which therefore is a manifold.
  have hrange : range f = (range ι)ᶜ := by rw [hιf, compl_compl]
  let _ : ChartedSpace E' ((range ι)ᶜ : Set X) :=
    (hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)).chartedSpace
  exact o.bijective_absoluteCapFundamentalClassRel_aux hn hι hιf hf L hE' p q h

/-- **Lefschetz duality from absolute cohomology**, as an isomorphism
`Hᵖ(X; L) ≅ H_q(X, ∂X; L)`. -/
theorem isIso_absoluteCapFundamentalClassRel {E' : Type} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' N] (hE' : finrank ℝ E' + 1 = n)
    (p q : ℕ) (h : p + q = n) :
    IsIso (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (o.bijective_absoluteCapFundamentalClassRel hn hι hιf hf L hE' p q h)

end HomologicalOrientation

end TauCeti
