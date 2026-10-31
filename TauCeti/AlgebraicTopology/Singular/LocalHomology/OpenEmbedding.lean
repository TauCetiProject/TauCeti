/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System

/-!
# Local homology along open embeddings

A continuous map `j : M → N` with `j ⁻¹' T ⊆ S` induces a map
`Hₖ(M, M ∖ S) ⟶ Hₖ(N, N ∖ T)` of local homology groups (`TauCeti.localHomologyMap`). When `j` is
an open embedding, `T` is closed and contained in the image of `j`, and `S = j ⁻¹' T`, this map is
an isomorphism (`TauCeti.isIso_localHomologyMap`): by excision, local
homology along `T` may be computed in the open neighbourhood `j(M)` of `T`, which `j` identifies
with `M`. In particular an open embedding into a `T₁` space identifies the local homology of `M`
at `x` with that of `N` at `j x` (`TauCeti.localHomologyIsoOfIsOpenEmbedding`).

For Hausdorff spaces `M` and `N` modelled on the same finite-dimensional real normed space,
these isomorphisms intertwine the transport of local homology along paths
(`TauCeti.localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom`): the local
homology system of `M` is the pullback along `j` of the local homology system of `N`. This holds
because a chart of `M`, read on the open subset `j(M)` of `N`, is a chart of `N`, and transport is
determined by its behaviour along paths inside compact convex sets of charts
(`TauCeti.eq_localHomologyTransport`). In top degree with integral coefficients it is the
naturality of the orientation local system under open embeddings, through which orientations
restrict to open subsets and are compared along homeomorphisms.

## Main definitions

* `TauCeti.localHomologyIsoOfIsOpenEmbedding`: for an open embedding `j`, the isomorphism
  `Hₖ(M, M ∖ {x}) ≅ Hₖ(N, N ∖ {j x})`.

## Main results

* `TauCeti.isIso_localHomologyMap`: excision along an open embedding.
* `TauCeti.localHomologyIsoOfIsOpenEmbedding_id`,
  `TauCeti.localHomologyIsoOfIsOpenEmbedding_trans`: these isomorphisms are functorial.
* `TauCeti.localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom`: open embeddings
  intertwine the transport of local homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3: local homology, computed by excision in a neighbourhood, and its transport along
  paths through balls in charts.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section OpenEmbedding

variable {M N P : Type w} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  (j : C(M, N))

/-- **Excision along an open embedding.** If `j` is an open embedding, `T` is closed and lies in
the image of `j`, and `S = j ⁻¹' T`, then `j` induces an isomorphism
`Hₖ(M, M ∖ S) ≅ Hₖ(N, N ∖ T)`. -/
theorem isIso_localHomologyMap (hj : IsOpenEmbedding j) {S : Set M} {T : Set N}
    (h : j ⁻¹' T = S) (hT : IsClosed T) (hTj : T ⊆ range j) (k : ℕ) :
    IsIso (localHomologyMap R j h.subset k) := by
  rw [localHomologyMap_def]
  -- The open sets `j(M)` and `N ∖ T` cover `N`; the first lies in the image of `j`, the second in
  -- the subspace `N ∖ T` of the pair.
  refine TopPair.isIso_singularHomologyMap_of_open_cover R _
    (by rw [TopPair.ofSubsetMap_fst]; exact hj.isEmbedding) ?_
    (fun b : Bool ↦ bif b then range j else Tᶜ)
    (fun b ↦ by cases b; exacts [hT.isOpen_compl, hj.isOpen_range]) ?_ ?_ k
  · intro x hx
    rw [TopPair.range_ofSubset_map, TopPair.ofSubsetMap_fst] at hx
    rw [TopPair.range_ofSubset_map]
    exact fun hxS ↦ hx (h.symm.subset hxS)
  · rw [← union_eq_iUnion]
    exact eq_univ_of_forall fun y ↦ (em (y ∈ T)).imp (fun hy ↦ hTj hy) id
  · rintro (_ | _)
    · exact Or.inl TopPair.range_ofSubset_map.symm.subset
    · refine Or.inr ?_
      rw [TopPair.ofSubsetMap_fst]
      exact subset_rfl

/-- An open embedding `j : M → N` into a `T₁` space identifies the local homology of `M` at `x`
with the local homology of `N` at `j x`. -/
def localHomologyIsoOfIsOpenEmbedding [T1Space N] {j : M → N} (hj : IsOpenEmbedding j) (x : M)
    (k : ℕ) : localHomology R {x} k ≅ localHomology R {j x} k :=
  have h : j ⁻¹' {j x} = {x} := by rw [← image_singleton, hj.injective.preimage_image]
  have := isIso_localHomologyMap R ⟨j, hj.continuous⟩ hj h isClosed_singleton
    (singleton_subset_iff.2 (mem_range_self x)) k
  asIso (localHomologyMap R ⟨j, hj.continuous⟩ h.subset k)

@[simp]
lemma localHomologyIsoOfIsOpenEmbedding_hom [T1Space N] {j : M → N} (hj : IsOpenEmbedding j)
    (x : M) (k : ℕ) :
    (localHomologyIsoOfIsOpenEmbedding R hj x k).hom =
      localHomologyMap R ⟨j, hj.continuous⟩
        (by rw [ContinuousMap.coe_mk, ← image_singleton, hj.injective.preimage_image]) k :=
  (rfl)

/-- The isomorphism of local homology induced by the identity is the identity. -/
@[simp]
lemma localHomologyIsoOfIsOpenEmbedding_id [T1Space M] (x : M) (k : ℕ) :
    localHomologyIsoOfIsOpenEmbedding R IsOpenEmbedding.id x k = Iso.refl _ := by
  ext : 1
  rw [localHomologyIsoOfIsOpenEmbedding_hom, Iso.refl_hom]
  exact (localHomologyMap_id R (S := {x}) (T := {x}) subset_rfl k).trans
    (localHomologyRestriction_refl R {x} k)

/-- The isomorphisms of local homology induced by open embeddings are functorial. -/
@[simp]
lemma localHomologyIsoOfIsOpenEmbedding_trans [T1Space N] [T1Space P] {j : M → N} {j' : N → P}
    (hj : IsOpenEmbedding j) (hj' : IsOpenEmbedding j') (x : M) (k : ℕ) :
    localHomologyIsoOfIsOpenEmbedding R hj x k ≪≫ localHomologyIsoOfIsOpenEmbedding R hj' (j x) k =
      localHomologyIsoOfIsOpenEmbedding R (hj'.comp hj) x k := by
  ext : 1
  simp only [Iso.trans_hom, localHomologyIsoOfIsOpenEmbedding_hom, localHomologyMap_comp]
  rfl

end OpenEmbedding

section Transport

variable {M N : Type w} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E N] {j : M → N}

/-- Along a path in a compact convex set of a chart of `M`, the transport of local homology of `N`
along the image path, read through the isomorphisms induced by `j`, is the comparison through
that set. This is the defining property of the transport of `M`. -/
private lemma localHomologyRestriction_comp_conj (hj : IsOpenEmbedding j) (k : ℕ)
    (φ : OpenPartialHomeomorph M E) {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K)
    (hKφ : K ⊆ φ.target) {x y : M} (γ : Path x y) (hγ : ∀ s, γ s ∈ φ.symm '' K) :
    localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
        (localHomologyIsoOfIsOpenEmbedding R hj x k).hom ≫
          localHomologyTransport R N E k (Path.Homotopic.Quotient.mk (γ.map hj.continuous) :
            FundamentalGroupoid.mk (j x) ⟶ FundamentalGroupoid.mk (j y)) ≫
            (localHomologyIsoOfIsOpenEmbedding R hj y k).inv =
      localHomologyRestriction R (singleton_subset_iff.2 (γ.target ▸ hγ 1)) k := by
  have : Nonempty M := ⟨x⟩
  -- The chart `φ`, read on the open subset `j(M)` of `N`.
  let ψ : OpenPartialHomeomorph N E := (hj.toOpenPartialHomeomorph j).symm.trans φ
  have hψ (z : E) : ψ.symm z = j (φ.symm z) := (rfl)
  have hKψ : K ⊆ ψ.target := fun z hz ↦ ⟨hKφ hz, mem_univ _⟩
  -- `j` carries the compact set `φ.symm '' K` onto `ψ.symm '' K`.
  have hpre : j ⁻¹' (ψ.symm '' K) ⊆ φ.symm '' K := by
    rintro w ⟨z, hz, hzw⟩
    exact ⟨z, hz, hj.injective ((hψ z).symm.trans hzw)⟩
  have hγ' (s : unitInterval) : γ.map hj.continuous s ∈ ψ.symm '' K := by
    obtain ⟨z, hz, hzs⟩ := hγ s
    exact ⟨z, hz, by rw [hψ, hzs, Path.map_coe, Function.comp_apply]⟩
  have hjx : j x ∈ ψ.symm '' K := (γ.map hj.continuous).source ▸ hγ' 0
  have hjy : j y ∈ ψ.symm '' K := (γ.map hj.continuous).target ▸ hγ' 1
  have hN := localHomologyRestriction_comp_localHomologyTransport R ψ hK hKc hKψ
    (γ.map hj.continuous) hγ' k
  -- Restricting to an endpoint commutes with the maps induced by `j`.
  have hx : localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
      (localHomologyIsoOfIsOpenEmbedding R hj x k).hom =
        localHomologyMap R ⟨j, hj.continuous⟩ hpre k ≫
          localHomologyRestriction R (singleton_subset_iff.2 hjx) k := by
    rw [localHomologyIsoOfIsOpenEmbedding_hom, localHomologyRestriction_comp_localHomologyMap,
      localHomologyMap_comp_localHomologyRestriction]
  have hy : localHomologyRestriction R (singleton_subset_iff.2 (γ.target ▸ hγ 1)) k ≫
      (localHomologyIsoOfIsOpenEmbedding R hj y k).hom =
        localHomologyMap R ⟨j, hj.continuous⟩ hpre k ≫
          localHomologyRestriction R (singleton_subset_iff.2 hjy) k := by
    rw [localHomologyIsoOfIsOpenEmbedding_hom, localHomologyRestriction_comp_localHomologyMap,
      localHomologyMap_comp_localHomologyRestriction]
  rw [← Iso.eq_comp_inv] at hy
  rw [hy, reassoc_of% hx, reassoc_of% hN, Category.assoc]

/-- **Open embeddings intertwine the transport of local homology.** For an open embedding
`j : M → N` of Hausdorff spaces modelled on the same finite-dimensional real normed space, the
isomorphisms `Hₖ(M, M ∖ {x}) ≅ Hₖ(N, N ∖ {j x})` induced by `j` carry the transport of local
homology of `M` along a path class to the transport of local homology of `N` along its image. -/
@[reassoc]
theorem localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom [T2Space M]
    [ChartedSpace E M] (hj : IsOpenEmbedding j) (k : ℕ) {x y : FundamentalGroupoid M}
    (f : x ⟶ y) :
    localHomologyTransport R M E k f ≫ (localHomologyIsoOfIsOpenEmbedding R hj y.as k).hom =
      (localHomologyIsoOfIsOpenEmbedding R hj x.as k).hom ≫
        localHomologyTransport R N E k (x := (FundamentalGroupoid.map ⟨j, hj.continuous⟩).obj x)
          (y := (FundamentalGroupoid.map ⟨j, hj.continuous⟩).obj y)
          ((FundamentalGroupoid.map ⟨j, hj.continuous⟩).map f) := by
  set F := FundamentalGroupoid.map ⟨j, hj.continuous⟩
  -- The isomorphisms induced by `j`, with targets indexed by the image objects of the
  -- fundamental groupoid, so that composites with the transport of `N` typecheck syntactically.
  let I (z : FundamentalGroupoid M) : localHomology R {z.as} k ≅
      localHomology R {(F.obj z).as} k :=
    localHomologyIsoOfIsOpenEmbedding R hj z.as k
  have key := eq_localHomologyTransport R k
    (fun {x y} f ↦ (I x).hom ≫ localHomologyTransport R N E k (F.map f) ≫ (I y).inv)
    (fun f g ↦ by
      rw [Functor.map_comp, localHomologyTransport_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc])
    (@fun φ _ hK hKc hKφ _ _ γ hγ ↦ localHomologyRestriction_comp_conj R hj k φ hK hKc hKφ γ hγ) f
  have h : localHomologyTransport R M E k f ≫ (I y).hom =
      (I x).hom ≫ localHomologyTransport R N E k (F.map f) := by
    rw [← key]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h

end Transport

end TauCeti
