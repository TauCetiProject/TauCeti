/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup
public import TauCeti.Topology.VectorBundle.Thom.Class
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The Thom isomorphism over trivializing sets

Let `E → B` be a real vector bundle with fibre `F` of rank `r ≥ 2`, and `u ∈ Hʳ(E, E₀; K)` a Thom
class (`TauCeti.IsThomClass`) with coefficients in a commutative ring `K`. For a subset `W` of the
base, the Thom map of the restriction of `E` to `W` is the map

`Hᵖ(W; M) ⟶ Hᵖ⁺ʳ(E|_W, E₀|_W; M)`,  `a ↦ π^*a ⌣ u|_W`,

`TopCat.pullbackCupRestrict` of the projection `π : E → B` over `W`. This file proves that it is
bijective in every degree and for every `K`-module `M` when `W` lies in the base set of a linear
trivialization `e` (`Bundle.Trivialization.bijective_pullbackCupRestrict_thomPairProj`). Over such
a `W` the trivialization identifies `(E|_W, E₀|_W)` with the Thom pair of the product bundle
`W × F` (`Bundle.Trivialization.thomPairOverIso`), carrying the restriction of `u` to a class which
restricts to a generator on every fibre, because `u` does; the Thom isomorphism for product bundles
(`TauCeti.bijective_pullbackCup_prodThomPair`) applies.

These are the maps that the Mayer–Vietoris step `TopCat.bijective_pullbackCupRestrict_union`
glues along unions of open sets; open subsets of a trivializing set and their intersections are
again trivializing sets. In particular the Thom map `TauCeti.thomMap` of a Thom class of a bundle
with a trivialization over the whole base is bijective
(`Bundle.Trivialization.bijective_thomMap`).

## Main results

* `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPairProj`: the Thom isomorphism over a
  subset of the base set of a linear trivialization.
* `Bundle.Trivialization.bijective_thomMap`: the Thom isomorphism for a bundle with a global
  trivialization.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Module TauCeti

universe w

namespace Bundle.Trivialization

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- Over a subset `W` of the base set of a linear trivialization, the restriction of a Thom class,
transported to the Thom pair of the product bundle `W × F` along the trivialization, restricts to a
generator on the fibre pair over every point of `W`. -/
private theorem span_singularCohomologyMap_prodThomPairFiberMap {W : Set B} (hW : W ⊆ e.baseSet)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (b : W) :
    Submodule.span K {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F)
      (TopPair.singularCohomologyMap (e.thomPairOverIso ℝ hW).inv _
        (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) _ u)))} = ⊤ := by
  -- On the fibre over `b`, the transported class is the image of the restriction of `u` to the
  -- fibre pair `(E_b, E_b ∖ {0})` under the isomorphism `ψ` of fibre pairs given by `e` at `b`.
  let ψ := (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso
  have hφ : prodThomPairFiberMap F b ≫ (e.thomPairOverIso ℝ hW).inv =
      ψ.inv ≫ fiberThomPairOverMap F E b.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2]
  simp only [← TopPair.singularCohomologyMap_comp_apply, reassoc_of% hφ,
    fiberThomPairOverMap_comp_restrictPreimagePairMap]
  have hsurj : Function.Surjective (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := ModuleCat.of K K) ψ.inv (finrank ℝ F)) := fun y ↦
    ⟨TopPair.singularCohomologyMap ψ.hom _ y, by
      rw [← TopPair.singularCohomologyMap_comp_apply, Iso.inv_hom_id,
        TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]⟩
  have hL := congrArg (Submodule.map (TopPair.singularCohomologyMap ψ.inv (finrank ℝ F)).hom)
    ((isThomClass_iff.1 hu).2 b)
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    LinearMap.range_eq_top.2 hsurj] at hL
  rw [TopPair.singularCohomologyMap_comp_apply]
  exact hL

/-- **The Thom isomorphism over a trivializing set.** Let `u` be a Thom class of a real vector
bundle `E` of rank `r ≥ 2`, with coefficients in `K`, and let `W` lie in the base set of a linear
trivialization of `E`. Then for every `K`-module `M` and every degree `p`, the Thom map over `W`,
`a ↦ π^*a ⌣ u|_W`, `Hᵖ(W; M) ⟶ Hᵖ⁺ʳ(E|_W, E₀|_W; M)`, is bijective. -/
theorem bijective_pullbackCupRestrict_thomPairProj {W : Set B} (hW : W ⊆ e.baseSet)
    (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E) (zeroSectionCompl F E) M W
      (finrank ℝ F) p m h u) := by
  have := (isThomClass_iff.1 hu).1
  -- Transport the restriction of `u` to the product bundle `W × F` along the trivialization.
  let φ := e.thomPairOverIso ℝ hW
  let r := TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
    (zeroSectionCompl F E) W
  have hfib := e.span_singularCohomologyMap_prodThomPairFiberMap hW hu
  -- The Thom isomorphism for the product bundle, with `F` identified with `ℝʳ`.
  have hprod : Function.Bijective ((prodThomPair W F).pullbackCup M (prodThomPairProj W F)
      (finrank ℝ F) p m h (TopPair.singularCohomologyMap φ.inv _
        (TopPair.singularCohomologyMap r _ u))) := by
    obtain ⟨d, hd⟩ : ∃ d, finrank ℝ F = d + 2 := ⟨finrank ℝ F - 2, by omega⟩
    let eF : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
      ContinuousLinearEquiv.ofFinrankEq (by rw [hd, finrank_euclideanSpace_fin])
    -- The product theorem is stated in degree `d + 2`: generalize the class, so that its degree
    -- `finrank ℝ F` can be rewritten.
    generalize TopPair.singularCohomologyMap φ.inv _ (TopPair.singularCohomologyMap r _ u) = u'
      at hfib ⊢
    revert u' h
    rw [hd]
    intro h u' hfib
    exact bijective_pullbackCup_prodThomPair M eF u' hfib h
  have hg : TopPair.Hom.fst φ.hom ≫ prodThomPairProj W F =
      TopCat.ofHom ((ContinuousMap.mk (π F E) (FiberBundle.continuous_proj F E)).restrictPreimage
        W) ≫ 𝟙 _ :=
    TopCat.ext fun v ↦ (prodThomPairProj_apply F _).trans
      (congrArg Prod.fst (e.thomPairOverIso_hom_fst_apply ℝ hW v))
  have key := (TopPair.bijective_pullbackCup_iff_of_isIso φ.hom (𝟙 (TopCat.of W)) hg h _).2 hprod
  have hφ : TopPair.singularCohomologyMap φ.hom _ (TopPair.singularCohomologyMap φ.inv _
      (TopPair.singularCohomologyMap r _ u)) = TopPair.singularCohomologyMap r _ u := by
    simp [← TopPair.singularCohomologyMap_comp_apply]
  rw [hφ] at key
  -- `TopCat.pullbackCupRestrict` over `W` is `TopPair.pullbackCup` of this restriction.
  refine (congrArg (fun f : _ →ₗ[K] _ ↦ Function.Bijective f)
    (TopCat.pullbackCupRestrict_apply (thomPairProj F E) (zeroSectionCompl F E) M W h u)).mpr ?_
  rw [thomPairProj_def]
  exact key

/-- **The Thom isomorphism for a trivializable bundle.** If a real vector bundle `E` of rank
`r ≥ 2` has a linear trivialization over the whole base, then for every Thom class `u` of `E` with
coefficients in `K`, every `K`-module `M` and every degree `p`, the Thom map
`a ↦ π^*a ⌣ u`, `Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, is bijective. -/
theorem bijective_thomMap (he : e.baseSet = Set.univ) (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  rw [thomMap_def]
  exact (TopCat.bijective_pullbackCupRestrict_univ_iff (thomPairProj F E) (zeroSectionCompl F E) M
    h u).1 (e.bijective_pullbackCupRestrict_thomPairProj M he.symm.subset hF hu h)

end Bundle.Trivialization
