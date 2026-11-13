/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Euclidean
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality
public import TauCeti.Analysis.Convex.Topology

/-!
# Poincaré duality for a vector space and its star-convex open subsets

Let `F` be a finite-dimensional real normed space of dimension `d` with a homological orientation
`o`, and let `L` be an abelian group. For an open embedding `j : U → F` whose image is star-convex,
the duality map `D_U : Hᵖ_c(U; L) ⟶ H_q(U; L)`, `p + q = d`
(`TauCeti.HomologicalOrientation.dualityMap`), of the pulled-back orientation is bijective
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_starConvex`). In particular the
duality map of `F` itself is bijective (`TauCeti.HomologicalOrientation.bijective_dualityMap_self`),
and so is the duality map of every convex open subset of `F`
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_convex`). These are the case
`M = ℝⁿ` of Hatcher's proof of Poincaré duality for noncompact manifolds (Theorem 3.35) and the
convex step of its induction (Lemma 3.36).

For empty `U` both groups vanish. Otherwise the image of `j` is star-convex about one of its
points `y`, so `U` and `F` are contractible and `j_* : H_q(U; L) ⟶ H_q(F; L)` is bijective
(`TauCeti.isIso_singularHomologyFunctor_map_of_contractibleSpace`). The star hulls about `y` of
the images of compact subsets of `U` stay in the image of `j`, so their preimages are cofinal among
the compact subsets of `U`. Along such a preimage `K`, capping with the fundamental class of the
pulled-back orientation is bijective exactly when capping along `j(K)` is
(`TauCeti.HomologicalOrientation.bijective_capFundamentalClassOn_comap_iff`), and `j(K)` is a
nonempty compact set star-convex about `y`, along which capping is bijective
(`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClassOn_of_starConvex`). The
cofinality criterion `TauCeti.HomologicalOrientation.bijective_dualityMap_of_cofinal` concludes.

## Main results

* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_starConvex`: Poincaré duality for
  an open subset of a finite-dimensional real normed space, embedded with star-convex image.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_self`: Poincaré duality for a
  finite-dimensional real normed space.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_convex`: Poincaré duality for a
  convex open subset.

## Implementation notes

The coefficient conventions are those of `TauCeti.HomologicalOrientation.dualityMap`. The local
instance `CategoryTheory.MonoidalPreadditive.monoidalLinearInt` makes the `ℤ`-linear structure of
`ModuleCat ℤ` as a preadditive category monoidal linear, as there.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the proof of Theorem 3.35: the case `M = ℝⁿ` and the convex open sets of
  Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Module TopologicalSpace Topology Set

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {d : ℕ}
  (o : HomologicalOrientation F F d) (hd : finrank ℝ F = d) (L : ModuleCat.{0} ℤ)
  {p q : ℕ} (h : p + q = d)

/-- **Poincaré duality for a star-convex open subset**: for an open embedding `j : U → F` whose
image is star-convex, the duality map `Hᵖ_c(U; L) ⟶ H_q(U; L)` of the pulled-back orientation is
bijective. -/
theorem bijective_dualityMap_comap_of_starConvex {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace F U] {j : U → F} (hj : IsOpenEmbedding j) {y : F}
    (hU : StarConvex ℝ y (range j)) :
    Function.Bijective ((o.comap hj).dualityMap hd L p q h) := by
  rcases isEmpty_or_nonempty U with hU₀ | ⟨⟨u₀⟩⟩
  · exact (o.comap hj).bijective_dualityMap_of_isEmpty hd L h
  have hy : y ∈ range j := hU.mem ⟨j u₀, u₀, rfl⟩
  have : ContractibleSpace (range j) := hU.contractibleSpace ⟨y, hy⟩
  have : ContractibleSpace U := hj.isEmbedding.toHomeomorph.contractibleSpace
  let j' : C(U, F) := ⟨j, hj.continuous⟩
  refine (o.comap hj).bijective_dualityMap_of_cofinal hd L h fun K₀ ↦ ?_
  -- The star hull about `y` of the image of `K₀` lies in the image of `j`, so its preimage is a
  -- compact subset of `U` containing `K₀`, with star-convex image.
  let S := Compacts.starHull (E := F) ℝ y (K₀.map (TopCat.ofHom j') j'.continuous)
  have hS : (S : Set F) ⊆ range j := Compacts.starHull_subset hU hy (by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩)
  let K : Compacts (TopCat.of U) := ⟨j ⁻¹' S, hj.isInducing.isCompact_preimage' S.isCompact hS⟩
  have hKS : ((K.map (TopCat.ofHom j') j'.continuous : Compacts F) : Set F) = S :=
    image_preimage_eq_of_subset hS
  refine ⟨K, fun u hu ↦ Compacts.le_starHull (E := F) ℝ y _ ⟨u, hu, rfl⟩, ?_⟩
  rw [o.bijective_capFundamentalClassOn_comap_iff hd L (j := j') hj h
    (ConcreteCategory.bijective_of_isIso _) K]
  refine (congrArg Function.Bijective (funext (o.capFundamentalClassOn_apply hd L _ p q h))).mpr ?_
  exact o.bijective_singularCap_fundamentalClassOn_of_starConvex hd L _ (y := y)
    (hKS ▸ Compacts.starConvex_starHull (E := F) ℝ y _)
    (hKS ▸ Compacts.mem_starHull_self (E := F) ℝ y _) p q h

/-- **Poincaré duality for a finite-dimensional real normed space**: the duality map
`Hᵖ_c(F; L) ⟶ H_q(F; L)`, `p + q = d`, of a homological orientation of `F` is bijective. -/
theorem bijective_dualityMap_self : Function.Bijective (o.dualityMap hd L p q h) := by
  simpa only [comap_id] using o.bijective_dualityMap_comap_of_starConvex hd L h
    IsOpenEmbedding.id (y := 0) (range_id ▸ starConvex_univ 0)

/-- **Poincaré duality for a finite-dimensional real normed space**, as an isomorphism. -/
instance isIso_dualityMap_self : IsIso (o.dualityMap hd L p q h) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (o.bijective_dualityMap_self hd L h)

/-- **Poincaré duality for a convex open subset**: for a convex open subset `V` of `F`, the
duality map `Hᵖ_c(V; L) ⟶ H_q(V; L)` of the restricted orientation is bijective. -/
theorem bijective_dualityMap_comap_of_convex (V : Opens F) (hV : Convex ℝ (V : Set F)) :
    Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hd L p q h) := by
  have hr : range (Subtype.val : V → F) = V := Subtype.range_coe
  rcases (V : Set F).eq_empty_or_nonempty with hV₀ | ⟨y, hy⟩
  · exact o.bijective_dualityMap_comap_of_starConvex hd L h V.isOpenEmbedding' (y := 0)
      (hr ▸ hV₀ ▸ starConvex_empty 0)
  · exact o.bijective_dualityMap_comap_of_starConvex hd L h V.isOpenEmbedding'
      (hr ▸ hV.starConvex hy)

end HomologicalOrientation

end TauCeti
