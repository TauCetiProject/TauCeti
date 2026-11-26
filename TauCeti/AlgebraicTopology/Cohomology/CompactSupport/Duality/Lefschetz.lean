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
import TauCeti.AlgebraicTopology.Cohomology.Collar
import TauCeti.AlgebraicTopology.Cohomology.Manifold
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

The companion isomorphism caps absolute cohomology with `[X, ∂X]`:

`Hᵖ(X; L) ⟶ H_q(X, ∂X; L)`, `α ↦ [X, ∂X] ⌢ α`, `p + q = n`

(`TauCeti.HomologicalOrientation.absoluteCapFundamentalClassRel`), and it is bijective as soon as
the boundary is itself a manifold, that is `N` is charted on a real normed space of dimension
`n - 1` (`TauCeti.HomologicalOrientation.bijective_absoluteCapFundamentalClassRel`). The proof is
Hatcher's five-lemma argument. The connecting morphism sends `[X, ∂X]` to a fundamental class
`[∂X]` of the boundary
(`TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`), so
capping with `[∂X]` is Poincaré duality of the closed manifold `∂X`
(`TauCeti.IsFundamentalClass.bijective_singularCapAddHom`). Capping with `[X, ∂X]` and with
`[∂X]` maps the long exact cohomology sequence of `(X, ∂X)` to its long exact homology sequence,
up to sign:

```
Hᵖ⁻¹(∂X) ⟶ Hᵖ(X, ∂X) ⟶ Hᵖ(X) ⟶ Hᵖ(∂X) ⟶ Hᵖ⁺¹(X, ∂X)
    ↓            ↓          ↓         ↓            ↓
 H_q(∂X)  ⟶   H_q(X)  ⟶ H_q(X, ∂X) ⟶ H_{q-1}(∂X) ⟶ H_{q-1}(X)
```

(`TopPair.singularCap_singularCohomologyδ`, `TopPair.absoluteSingularCap_singularCohomologyπ` and
`TopPair.absoluteSingularCap_comp_singularHomologyδ`). The other four vertical maps are
bijective, by Lefschetz duality and by Poincaré duality of `∂X`; at the ends of the sequences
`Hₙ(∂X)` and `Hⁿ(∂X)` vanish, above the dimension of `∂X`.

## Main definitions

* `TauCeti.HomologicalOrientation.capFundamentalClassRel`: capping with the fundamental class
  relative to the boundary, `Hᵖ(X, ∂X; L) ⟶ H_q(X; L)`.
* `TauCeti.HomologicalOrientation.absoluteCapFundamentalClassRel`: capping absolute cohomology
  with the fundamental class relative to the boundary, `Hᵖ(X; L) ⟶ H_q(X, ∂X; L)`.

## Main results

* `TauCeti.HomologicalOrientation.capFundamentalClassRel_restrict`: for compact `K ⊆ M`, on
  classes restricted from `Hᵖ(X, X ∖ ι(K))`, capping with `[X, ∂X]` is capping with the
  fundamental class of `M` along `K` after excision, followed by the map induced by `ι`.
* `TauCeti.HomologicalOrientation.bijective_capFundamentalClassRel`: **Lefschetz duality**, and
  `TauCeti.HomologicalOrientation.isIso_capFundamentalClassRel` as an isomorphism.
* `TauCeti.HomologicalOrientation.bijective_absoluteCapFundamentalClassRel`: **Lefschetz duality
  for absolute cohomology**, when the boundary is a manifold, and
  `TauCeti.HomologicalOrientation.isIso_absoluteCapFundamentalClassRel` as an isomorphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.43 and its proof (the five-lemma argument for the absolute form).
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

/-! ### Lefschetz duality for absolute cohomology -/

/-- **Capping absolute cohomology with the fundamental class relative to the boundary**: the map
`Hᵖ(X; L) ⟶ H_q(X, ∂X; L)`, `α ↦ [X, ∂X] ⌢ α`, for `p + q = n`, where the boundary
`∂X = X ∖ ι(M)` is the complement of the interior. -/
def absoluteCapFundamentalClassRel (p q : ℕ) (h : p + q = n) :
    (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).fst.singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p ⟶
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology L q :=
  (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).absoluteSingularCapWith L
    (o.fundamentalClassRel hn hι hιf hf) p q h

/-- Capping absolute cohomology with the relative fundamental class evaluates the cap product of
absolute cohomology with relative homology at `[X, ∂X]`. -/
lemma absoluteCapFundamentalClassRel_apply (p q : ℕ) (h : p + q = n)
    (α : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).fst.singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h α =
      ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).absoluteSingularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h α).hom (o.fundamentalClassRel hn hι hιf hf) :=
  TopPair.absoluteSingularCapWith_apply _ L _ p q h α

section Absolute

/-! The two duality maps of `X`, and capping with the boundary `[∂X] = ∂[X, ∂X]` of the relative
fundamental class on `∂X`, form a ladder between the long exact sequence of the pair `(X, ∂X)` in
cohomology and in homology, commuting up to sign (Hatcher, proof of Theorem 3.43). -/

/-- The square of the connecting morphisms: `[X, ∂X] ⌢ δβ = i_*([∂X] ⌢ β)` for `β ∈ Hᵖ(∂X)`. -/
private lemma capFundamentalClassRel_singularCohomologyδ {m : ℕ} (hm : m + 1 = n) (p q : ℕ)
    (h : p + q = m)
    (β : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.capFundamentalClassRel hn hι hιf hf L (p + 1) q (by omega)
        ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomologyδ _ ℤ L p (p + 1) rfl
          β) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).map
        (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCap ℤ (ρ_ _).inv
          (ρ_ L).hom p q m h β).hom
          ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm
            (o.fundamentalClassRel hn hι hιf hf))) := by
  subst hm
  rw [capFundamentalClassRel_apply]
  exact ConcreteCategory.congr_hom (TopPair.singularCap_singularCohomologyδ _ ℤ (ρ_ _).inv
    (ρ_ L).hom p q m h β) (o.fundamentalClassRel hn hι hιf hf)

/-- The square of the restriction to `∂X` and the connecting morphism:
`∂([X, ∂X] ⌢ α) = (-1)ᵖ [∂X] ⌢ α|_{∂X}` for `α ∈ Hᵖ(X)`. -/
private lemma singularHomologyδ_absoluteCapFundamentalClassRel {m : ℕ} (hm : m + 1 = n)
    (p q : ℕ) (h : p + (q + 1) = n) (h' : p + q = m)
    (α : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).fst.singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ L (q + 1) q rfl
        (o.absoluteCapFundamentalClassRel hn hι hιf hf L p (q + 1) h α) =
      ((-1 : ℤ) ^ p) •
        (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCap ℤ (ρ_ _).inv
          (ρ_ L).hom p q m h' (TopCat.singularCohomologyMap
            (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).map p α)).hom
          ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm
            (o.fundamentalClassRel hn hι hιf hf))) := by
  rw [absoluteCapFundamentalClassRel_apply, ← ConcreteCategory.comp_apply,
    TopPair.absoluteSingularCap_comp_singularHomologyδ _ ℤ (ρ_ _).inv (ρ_ L).hom p q m (q + 1) n
      h' h α rfl hm]
  rfl

/-- The square of the maps from relative to absolute cohomology and from absolute to relative
homology: `[X, ∂X] ⌢ j^*β = j_*([X, ∂X] ⌢ β)` for `β ∈ Hᵖ(X, ∂X)`. -/
private lemma absoluteCapFundamentalClassRel_singularCohomologyπ (p q : ℕ) (h : p + q = n)
    (β : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h
        ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomologyπ _ ℤ L p β) =
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyπ L q
        (o.capFundamentalClassRel hn hι hιf hf L p q h β) := by
  rw [absoluteCapFundamentalClassRel_apply, capFundamentalClassRel_apply,
    TopPair.absoluteSingularCap_singularCohomologyπ]
  rfl

/-- Injectivity in the duality ladder: if capping with `[∂X]` is bijective in every degree and
`Hₙ(∂X; L)` and `Hⁿ(∂X; L)` vanish, then capping with `[X, ∂X]` is injective on `Hᵖ(X; L)`. -/
private lemma injective_absoluteCapFundamentalClassRel_of_bijective {m : ℕ} (hm : m + 1 = n)
    (hPD : ∀ p q (h : p + q = m), Function.Bijective fun β ↦
      (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q m h β).hom
          ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm (o.fundamentalClassRel hn hι hιf hf))))
    (hH : Subsingleton (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      L).obj (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd))
    (hC : Subsingleton ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L n))
    (p q : ℕ) (h : p + q = n) :
    Function.Injective (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h) := by
  refine (injective_iff_map_eq_zero
    (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h).hom).2 fun α hα ↦ ?_
  -- The restriction of `α` to `∂X` vanishes, since capping it with `[∂X]` is `±∂([X, ∂X] ⌢ α)`.
  have hres : TopCat.singularCohomologyMap
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).map p α = 0 := by
    rcases q with _ | q
    · obtain rfl : p = n := by omega
      exact Subsingleton.elim _ _
    · have hδ := o.singularHomologyδ_absoluteCapFundamentalClassRel hn hι hιf hf L hm p q h
        (by omega) α
      rw [hα, map_zero] at hδ
      refine (hPD p q (by omega)).1 ?_
      simp only [map_zero, ModuleCat.hom_zero]
      rcases neg_one_pow_eq_or ℤ p with hp | hp
      · rw [hp, one_smul] at hδ
        exact hδ.symm
      · rw [hp, neg_one_zsmul] at hδ
        exact neg_eq_zero.1 hδ.symm
  obtain ⟨β, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomology_exact_space _ ℤ L p)
    α hres
  rw [o.absoluteCapFundamentalClassRel_singularCohomologyπ] at hα
  -- So `[X, ∂X] ⌢ β` comes from `H_q(∂X)`, which is capping with `[∂X]` followed by the inclusion.
  obtain ⟨γ, hγ⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology_exact_space L q) _ hα
  rcases p with _ | p
  · obtain rfl : q = n := by omega
    have hβ : β = 0 := (o.bijective_capFundamentalClassRel hn hι hιf hf L 0 q h).1 <| by
      rw [map_zero, ← hγ, @Subsingleton.elim _ hH γ 0]
      exact map_zero _
    rw [hβ, map_zero]
  · obtain ⟨ζ, rfl⟩ := (hPD p q (by omega)).2 γ
    have hβ := (o.bijective_capFundamentalClassRel hn hι hιf hf L (p + 1) q h).1
      ((o.capFundamentalClassRel_singularCohomologyδ hn hι hιf hf L hm p q (by omega) ζ).trans
        hγ).symm
    rw [hβ, TopPair.singularCohomologyδ_comp_singularCohomologyπ_apply _
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p (p + 1) rfl]

/-- In the duality ladder, if capping with `[∂X]` is bijective in every degree, then every
`∂y ∈ H_q(∂X)` with `y ∈ H_{q+1}(X, ∂X)` is the boundary of some `[X, ∂X] ⌢ α`: write
`∂y = [∂X] ⌢ ζ`; then `[X, ∂X] ⌢ δζ = i_*∂y = 0`, so `δζ = 0` and `ζ` is the restriction of some
`α₀ ∈ Hᵖ(X)`, and `α = ±α₀` for the sign `(-1)ᵖ`. -/
private lemma exists_singularHomologyδ_absoluteCapFundamentalClassRel_eq {m : ℕ}
    (hm : m + 1 = n)
    (hPD : ∀ p q (h : p + q = m), Function.Bijective fun β ↦
      (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q m h β).hom
          ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm (o.fundamentalClassRel hn hι hιf hf))))
    (p q : ℕ) (h : p + (q + 1) = n)
    (y : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology
      (C := ModuleCat.{0} ℤ) L (q + 1)) :
    ∃ α : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).fst.singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p,
      (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ L (q + 1) q rfl
        (o.absoluteCapFundamentalClassRel hn hι hιf hf L p (q + 1) h α) =
          (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ L (q + 1) q rfl
            y := by
  obtain ⟨ζ, hζ⟩ := (hPD p q (by omega)).2
    ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ L (q + 1) q rfl y)
  dsimp only at hζ
  have hδζ : (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomologyδ _ ℤ L p
      (p + 1) rfl ζ = 0 := by
    refine (o.bijective_capFundamentalClassRel hn hι hιf hf L (p + 1) q (by omega)).1 ?_
    rw [o.capFundamentalClassRel_singularCohomologyδ hn hι hιf hf L hm p q (by omega) ζ, hζ,
      map_zero]
    exact ConcreteCategory.congr_hom
      ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ_comp L (q + 1) q rfl) y
  obtain ⟨α₀, hα₀⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomology_exact_subspace _ ℤ L p
      (p + 1) rfl) ζ hδζ
  dsimp only at hα₀
  have hcap := o.singularHomologyδ_absoluteCapFundamentalClassRel hn hι hιf hf L hm p q h
    (by omega)
  rcases neg_one_pow_eq_or ℤ p with hp | hp
  · refine ⟨α₀, ?_⟩
    rw [hcap, hp, one_smul, hα₀]
    exact hζ
  · refine ⟨-α₀, ?_⟩
    rw [hcap, hp, neg_one_zsmul, map_neg, hα₀, map_neg]
    -- Capping with the negated morphism negates the class.
    exact (neg_neg _).trans hζ

/-- Surjectivity in the duality ladder: if capping with `[∂X]` is bijective in every degree, then
capping with `[X, ∂X]` is surjective onto `H_q(X, ∂X; L)`. -/
private lemma surjective_absoluteCapFundamentalClassRel_of_bijective {m : ℕ} (hm : m + 1 = n)
    (hPD : ∀ p q (h : p + q = m), Function.Bijective fun β ↦
      (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q m h β).hom
          ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm (o.fundamentalClassRel hn hι hιf hf))))
    (p q : ℕ) (h : p + q = n) :
    Function.Surjective (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h) := by
  intro y
  rcases q with _ | q
  · -- In degree `0` every relative class comes from `H₀(X)`, which is the image of `Hᵖ(X, ∂X)`.
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 (inferInstance : Epi
      ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyπ L 0)) y
    obtain ⟨β, rfl⟩ := (o.bijective_capFundamentalClassRel hn hι hιf hf L p 0 h).2 x
    exact ⟨_, o.absoluteCapFundamentalClassRel_singularCohomologyπ hn hι hιf hf L p 0 h β⟩
  -- Otherwise `y - [X, ∂X] ⌢ α₁` has no boundary for some `α₁`, so it comes from `H_q(X)`, hence
  -- from `Hᵖ(X, ∂X)`.
  obtain ⟨α₁, hα₁⟩ :=
    o.exists_singularHomologyδ_absoluteCapFundamentalClassRel_eq hn hι hιf hf L hm hPD p q h y
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomology_exact_relative L (q + 1) q
      rfl) (y - o.absoluteCapFundamentalClassRel hn hι hιf hf L p (q + 1) h α₁)
    (by rw [map_sub, hα₁, sub_self])
  obtain ⟨β, rfl⟩ := (o.bijective_capFundamentalClassRel hn hι hιf hf L p (q + 1) h).2 x
  refine ⟨α₁ + (TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularCohomologyπ _ ℤ L p β,
    ?_⟩
  dsimp only at hx
  rw [map_add, o.absoluteCapFundamentalClassRel_singularCohomologyπ, hx, add_sub_cancel]

end Absolute

/-- **Lefschetz duality for absolute cohomology.** Let `X` be a compact Hausdorff space and
`ι : M → X` an open embedding of an oriented `n`-manifold without boundary whose complement
`∂X = X ∖ ι(M)` is collared, the image of a collared map `f : N → X`, such as a compact oriented
topological manifold with boundary and its interior. Suppose that `N` is a manifold, charted on a
real normed space of dimension `n - 1`. Then capping with the fundamental class relative to the
boundary, `α ↦ [X, ∂X] ⌢ α`, is a bijection `Hᵖ(X; L) → H_q(X, ∂X; L)` for `p + q = n`. -/
theorem bijective_absoluteCapFundamentalClassRel {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N] (hF : finrank ℝ F + 1 = n)
    (p q : ℕ) (h : p + q = n) :
    Function.Bijective (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h) := by
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  -- The boundary `∂X = f(N)` is a compact manifold modelled on `F`.
  have hfA : range f = (range ι)ᶜ := by rw [hιf, compl_compl]
  let : ChartedSpace F ↥((range ι)ᶜ : Set X) :=
    (hc.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hfA)).chartedSpace
  have : CompactSpace ↥((range ι)ᶜ : Set X) :=
    isCompact_iff_compactSpace.1 hι.isOpen_range.isClosed_compl.isCompact
  obtain rfl := hF
  -- `[∂X] = ∂[X, ∂X]` is a fundamental class of the boundary, so capping with it is Poincaré
  -- duality of `∂X`.
  have hPD := IsFundamentalClass.bijective_singularCapAddHom (M := ↥((range ι)ᶜ : Set X)) rfl L
    (o.isFundamentalClass_singularHomologyδ_fundamentalClassRel hn hι hιf hf)
  have hPD' : ∀ p q (h : p + q = finrank ℝ F), Function.Bijective fun β ↦
      (((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).snd.singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q _ h β).hom
          ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) _ _ rfl (o.fundamentalClassRel hn hι hιf hf))) :=
    fun p q h ↦ (congrArg Function.Bijective (funext fun β ↦ TopCat.singularCapAddHom_apply ℤ
      (ρ_ _).inv (ρ_ L).hom _ h _ β)).mp (hPD p q h)
  refine ⟨o.injective_absoluteCapFundamentalClassRel_of_bijective hn hι hιf hf L rfl hPD' ?_ ?_
    p q h, o.surjective_absoluteCapFundamentalClassRel_of_bijective hn hι hιf hf L rfl hPD' p q h⟩
  · have := isZero_singularHomology_of_compactSpace (M := ↥((range ι)ᶜ : Set X)) (E := F)
      (n := finrank ℝ F) (k := finrank ℝ F + 1) L rfl (lt_add_one _)
    exact ModuleCat.subsingleton_of_isZero this
  · -- The vanishing above the dimension is stated for the `ℤ`-linear structure of a category of
    -- modules, the duality maps for that of a preadditive category; they agree by uniqueness.
    have hZ (_ : Linear ℤ (ModuleCat.{0} ℤ)) :
        IsZero ((TopCat.of ↥((range ι)ᶜ : Set X)).singularCohomology
          (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L (finrank ℝ F + 1)) := by
      obtain rfl := Subsingleton.elim ‹Linear ℤ (ModuleCat.{0} ℤ)› ModuleCat.instLinear
      exact isZero_singularCohomology_of_compactSpace (E := F) (ModuleCat.of ℤ (ULift.{0} ℤ)) L
        rfl (lt_add_one _)
    exact ModuleCat.subsingleton_of_isZero (hZ Linear.preadditiveIntLinear)

/-- **Lefschetz duality for absolute cohomology**, as an isomorphism
`Hᵖ(X; L) ≅ H_q(X, ∂X; L)`. -/
theorem isIso_absoluteCapFundamentalClassRel {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N] (hF : finrank ℝ F + 1 = n)
    (p q : ℕ) (h : p + q = n) :
    IsIso (o.absoluteCapFundamentalClassRel hn hι hιf hf L p q h) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (o.bijective_absoluteCapFundamentalClassRel hn hι hιf hf L hF p q h)

end HomologicalOrientation

end TauCeti
