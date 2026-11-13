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
`o`, and let `L` be an abelian group. The duality map `D_F : Hᵖ_c(F; L) ⟶ H_q(F; L)`, `p + q = d`
(`TauCeti.HomologicalOrientation.dualityMap`), is bijective
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_finiteDimensional`). More generally, for an
open embedding `j : U → F` whose image is star-convex, the duality map of `U` with the pulled-back
orientation is bijective
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_starConvex`); in particular this
holds for every nonempty convex open subset of `F`
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_convex`). These are the case
`M = ℝⁿ` of Hatcher's proof of Poincaré duality for noncompact manifolds (Theorem 3.35) and the
convex step of its induction (Lemma 3.36).

Both proofs go through a criterion for an arbitrary oriented manifold `M`
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_cofinal`): if every compact set lies in
a compact `K` for which capping with the fundamental class `μ_K` is bijective
`Hᵖ(M, M ∖ K; L) ⟶ H_q(M; L)`, then the duality map is bijective. Indeed every class with
compact support comes from some `Hᵖ(M, M ∖ K; L)`, on which the duality map is capping with
`μ_K`. In `F` the compact star-convex sets, such as the star hull of a compact set about a point,
are cofinal, and for them capping with `μ_K` is bijective
(`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClassOn_of_starConvex`).

For `j : U → F`, the star hulls about a point of the image of compact subsets of `U` stay in the
image, so their preimages are cofinal among the compact subsets of `U`. By naturality of the
duality map along `j`, capping with the fundamental class of the pulled-back orientation along a
compact `K ⊆ U`, followed by `j_* : H_q(U; L) ⟶ H_q(F; L)`, is the excision isomorphism
`Hᵖ(U, U ∖ K; L) ≅ Hᵖ(F, F ∖ j(K); L)` followed by capping with `μ_{j(K)}`
(`TauCeti.HomologicalOrientation.capFundamentalClassOn_comap_comp_singularHomologyMap`). Since `U`
and `F` are contractible, `j_*` is bijective, so capping along `K` is bijective exactly when
capping along `j(K)` is
(`TauCeti.HomologicalOrientation.bijective_capFundamentalClassOn_comap_iff`).

## Main results

* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_cofinal`: the duality map of an oriented
  manifold is bijective if capping is bijective along cofinally many compact sets.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_finiteDimensional`: Poincaré duality for
  a finite-dimensional real normed space.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_starConvex`: Poincaré duality for
  an open subset of such a space, embedded with star-convex image.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_of_convex`: Poincaré duality for a
  nonempty convex open subset.

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

section Manifold

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)
  {p q : ℕ} (h : p + q = n)

/-- The duality map is surjective if capping with the fundamental class along some compact set is
surjective. -/
theorem surjective_dualityMap_of_surjective_capFundamentalClassOn {K : Compacts (TopCat.of M)}
    (hK : Function.Surjective (o.capFundamentalClassOn hn L K.isCompact p q h)) :
    Function.Surjective (o.dualityMap hn L p q h) := fun z ↦ by
  obtain ⟨α, rfl⟩ := hK z
  refine ⟨TopCat.compactSupportCohomologyι p K α, ?_⟩
  rw [← ConcreteCategory.comp_apply, compactSupportCohomologyι_dualityMap]

/-- The duality map is injective if every compact set lies in a compact set `K` along which
capping with the fundamental class is injective. -/
theorem injective_dualityMap_of_cofinal
    (H : ∀ K₀ : Compacts (TopCat.of M), ∃ K, K₀ ≤ K ∧
      Function.Injective (o.capFundamentalClassOn hn L K.isCompact p q h)) :
    Function.Injective (o.dualityMap hn L p q h) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨K₀, -, α, rfl⟩ := TopCat.exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨K, hK₀K, hK⟩ := H K₀
  rw [← TopCat.singularCohomologyMap_comp_compactSupportCohomologyι_apply p hK₀K] at hx ⊢
  rw [← ConcreteCategory.comp_apply, compactSupportCohomologyι_dualityMap] at hx
  rw [(injective_iff_map_eq_zero _).1 hK _ hx, map_zero]

/-- **Criterion for Poincaré duality**: the duality map of an oriented manifold is bijective if
every compact set lies in a compact set `K` along which capping with the fundamental class,
`Hᵖ(M, M ∖ K; L) ⟶ H_q(M; L)`, is bijective. -/
theorem bijective_dualityMap_of_cofinal
    (H : ∀ K₀ : Compacts (TopCat.of M), ∃ K, K₀ ≤ K ∧
      Function.Bijective (o.capFundamentalClassOn hn L K.isCompact p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) :=
  ⟨o.injective_dualityMap_of_cofinal hn L h fun K₀ ↦ (H K₀).imp fun _ hK ↦ ⟨hK.1, hK.2.1⟩,
    o.surjective_dualityMap_of_surjective_capFundamentalClassOn hn L h (H ⊥).choose_spec.2.2⟩

section OpenEmbedding

variable {U : Type} [TopologicalSpace U] [T2Space U] [ChartedSpace E U] {j : C(U, M)}
  (hj : IsOpenEmbedding j)

/-- **Capping along a compact subset of an open subset**: for an open embedding `j : U → M` and a
compact `K ⊆ U`, capping with the fundamental class of the pulled-back orientation along `K`,
followed by `j_* : H_q(U; L) ⟶ H_q(M; L)`, is the inverse of the excision isomorphism
`Hᵖ(M, M ∖ j(K); L) ≅ Hᵖ(U, U ∖ K; L)` followed by capping with the fundamental class along
`j(K)`. -/
@[reassoc]
lemma capFundamentalClassOn_comap_comp_singularHomologyMap (K : Compacts (TopCat.of U)) :
    (o.comap hj).capFundamentalClassOn hn L K.isCompact p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (TopCat.ofHom j) =
      (TopCat.singularCohomologyComplCompactsMapIso (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L
          (f := TopCat.ofHom j) hj K p).inv ≫
        o.capFundamentalClassOn hn L
          (K.map (TopCat.ofHom j) (TopCat.ofHom j).hom.continuous).isCompact p q h := by
  have := TopCat.compactSupportCohomologyι p K ≫=
    o.compactSupportCohomologyExtend_dualityMap hn L hj p q h
  rw [TopCat.compactSupportCohomologyι_comp_extend_assoc, compactSupportCohomologyι_dualityMap,
    compactSupportCohomologyι_dualityMap_assoc] at this
  exact this.symm

/-- For an open embedding `j : U → M` inducing a bijection `j_*` on `H_q`, capping with the
fundamental class of the pulled-back orientation along a compact `K ⊆ U` is bijective exactly
when capping with the fundamental class along `j(K)` is. -/
theorem bijective_capFundamentalClassOn_comap_iff
    (hjq : Function.Bijective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopCat.ofHom j)))
    (K : Compacts (TopCat.of U)) :
    Function.Bijective ((o.comap hj).capFundamentalClassOn hn L K.isCompact p q h) ↔
      Function.Bijective (o.capFundamentalClassOn hn L
        (K.map (TopCat.ofHom j) (TopCat.ofHom j).hom.continuous).isCompact p q h) := by
  rw [← Function.Bijective.of_comp_iff' hjq, ← Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (TopCat.singularCohomologyComplCompactsMapIso
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L (f := TopCat.ofHom j) hj K p).inv)]
  refine iff_of_eq (congrArg _ (funext fun α ↦ ?_))
  simpa only [ConcreteCategory.comp_apply, Function.comp_apply] using ConcreteCategory.congr_hom
    (o.capFundamentalClassOn_comap_comp_singularHomologyMap hn L h hj K) α

end OpenEmbedding

end Manifold

section Euclidean

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {d : ℕ}
  (o : HomologicalOrientation F F d) (hd : finrank ℝ F = d) (L : ModuleCat.{0} ℤ)
  {p q : ℕ} (h : p + q = d)

/-- **Poincaré duality for a finite-dimensional real normed space**: the duality map
`Hᵖ_c(F; L) ⟶ H_q(F; L)`, `p + q = d`, of a homological orientation of `F` is bijective. -/
theorem bijective_dualityMap_of_finiteDimensional :
    Function.Bijective (o.dualityMap hd L p q h) :=
  o.bijective_dualityMap_of_cofinal hd L h fun K₀ ↦
    ⟨Compacts.starHull (E := F) ℝ 0 K₀, Compacts.le_starHull (E := F) ℝ 0 K₀,
      (congrArg Function.Bijective (funext (o.capFundamentalClassOn_apply hd L _ p q h))).mpr <|
        o.bijective_singularCap_fundamentalClassOn_of_starConvex hd L _
          (Compacts.starConvex_starHull (E := F) ℝ 0 K₀)
          (Compacts.mem_starHull_self (E := F) ℝ 0 K₀) p q h⟩

/-- **Poincaré duality for a finite-dimensional real normed space**, as an isomorphism. -/
instance isIso_dualityMap_of_finiteDimensional : IsIso (o.dualityMap hd L p q h) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (o.bijective_dualityMap_of_finiteDimensional hd L h)

variable {U : Type} [TopologicalSpace U] [T2Space U] [ChartedSpace F U] {j : C(U, F)}

omit [FiniteDimensional ℝ F] [T2Space U] [ChartedSpace F U] in
/-- For an open embedding `j : U → F` with nonempty star-convex image, `j_*` is bijective on
singular homology: both spaces are contractible. -/
lemma bijective_singularHomologyMap_of_starConvex (hj : IsOpenEmbedding j) {y : F}
    (hy : y ∈ range j) (hU : StarConvex ℝ y (range j)) (q : ℕ) :
    Function.Bijective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopCat.ofHom j)) := by
  have : ContractibleSpace (range j) := hU.contractibleSpace ⟨y, hy⟩
  have : ContractibleSpace U := hj.isEmbedding.toHomeomorph.contractibleSpace
  rcases q with _ | q
  · -- In degree zero, `j_*` intertwines the augmentations, which are isomorphisms.
    have hε : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj L).map
        (TopCat.ofHom j) = (TopCat.of U).singularHomology₀ε L ≫
          inv ((TopCat.of F).singularHomology₀ε L) := by
      rw [← singularHomologyMap_singularHomology₀ε L (TopCat.ofHom j), Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    rw [hε]
    exact ConcreteCategory.bijective_of_isIso _
  · exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **Poincaré duality for a star-convex open subset**: for an open embedding `j : U → F` whose
image is star-convex about one of its points, the duality map `Hᵖ_c(U; L) ⟶ H_q(U; L)` of the
pulled-back orientation is bijective. -/
theorem bijective_dualityMap_comap_of_starConvex (hj : IsOpenEmbedding j) {y : F}
    (hy : y ∈ range j) (hU : StarConvex ℝ y (range j)) :
    Function.Bijective ((o.comap hj).dualityMap hd L p q h) := by
  refine (o.comap hj).bijective_dualityMap_of_cofinal hd L h fun K₀ ↦ ?_
  -- The star hull about `y` of the image of `K₀` lies in the image of `j`, so its preimage is a
  -- compact subset of `U` containing `K₀`, with star-convex image.
  let S := Compacts.starHull (E := F) ℝ y (K₀.map (TopCat.ofHom j) (TopCat.ofHom j).hom.continuous)
  have hS : (S : Set F) ⊆ range j := Compacts.starHull_subset hU hy (by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩)
  let K : Compacts (TopCat.of U) := ⟨j ⁻¹' S, hj.isInducing.isCompact_preimage' S.isCompact hS⟩
  have hKS : ((K.map (TopCat.ofHom j) (TopCat.ofHom j).hom.continuous : Compacts F) : Set F) =
      S :=
    image_preimage_eq_of_subset hS
  refine ⟨K, fun u hu ↦ Compacts.le_starHull (E := F) ℝ y _ ⟨u, hu, rfl⟩, ?_⟩
  rw [o.bijective_capFundamentalClassOn_comap_iff hd L h hj
    (bijective_singularHomologyMap_of_starConvex L hj hy hU q) K]
  refine (congrArg Function.Bijective (funext (o.capFundamentalClassOn_apply hd L _ p q h))).mpr ?_
  exact o.bijective_singularCap_fundamentalClassOn_of_starConvex hd L _ (y := y)
    (hKS ▸ Compacts.starConvex_starHull (E := F) ℝ y _)
    (hKS ▸ Compacts.mem_starHull_self (E := F) ℝ y _) p q h

/-- **Poincaré duality for a convex open subset**: for a nonempty convex open subset `V` of `F`,
the duality map `Hᵖ_c(V; L) ⟶ H_q(V; L)` of the restricted orientation is bijective. -/
theorem bijective_dualityMap_comap_of_convex (V : Opens F) (hV : Convex ℝ (V : Set F))
    (hne : (V : Set F).Nonempty) :
    Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hd L p q h) := by
  obtain ⟨y, hy⟩ := hne
  have hr : range (⟨Subtype.val, continuous_subtype_val⟩ : C(V, F)) = V := Subtype.range_coe
  exact o.bijective_dualityMap_comap_of_starConvex hd L h
    (j := ⟨Subtype.val, continuous_subtype_val⟩) V.isOpenEmbedding' (hr ▸ hy)
    (hr ▸ hV.starConvex hy)

end Euclidean

end HomologicalOrientation

end TauCeti
