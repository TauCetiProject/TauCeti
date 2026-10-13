/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.Order.Filter.Basic

/-!
# Local homology of a set as a colimit over its neighbourhoods

For a subset `S` of a space `M`, the relative singular homology `Hₖ(M, M ∖ S)`
(`TauCeti.localHomology`) is approximated by the groups `Hₖ(M, M ∖ K)` of larger sets `K ⊇ S`,
through the restriction maps `Hₖ(M, M ∖ K) ⟶ Hₖ(M, M ∖ S)`.  A singular simplex of `M ∖ S` has
compact image.  So when every compact set disjoint from `S` misses some member of a downward
directed family of sets `K ⊇ S`, the subspaces `M ∖ K` exhaust `M ∖ S` in the sense of compact
supports, and relative homology of the pair `(M, M ∖ S)` is the colimit of the relative homology
of the pairs `(M, M ∖ K)` (`TopPair.isColimitMapCoconeSingularHomology`).  With coefficients in a
module this says two things:

* every class of `Hₖ(M, M ∖ S)` is the restriction of a class of some `Hₖ(M, M ∖ K)`
  (`TauCeti.exists_localHomologyRestriction_eq`);
* a class of `Hₖ(M, M ∖ K)` whose restriction to `S` vanishes already restricts to zero on some
  smaller member of the family (`TauCeti.exists_localHomologyRestriction_eq_zero`).

In a Hausdorff space compact sets are closed, so the neighbourhoods of any set `A` form such a
family (`TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq` and
`TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq_zero`).  For a compact subset `A` of a
manifold this is the compactness step in the computation of `Hₖ(M, M ∖ A)`: it reduces statements
about `A` to statements about neighbourhoods of `A` that are finite unions of compact convex sets
in charts, the input to the fundamental class.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the proof of Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology

universe w

namespace TauCeti

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) (k : ℕ) {M : Type w} [TopologicalSpace M]

section Family

variable {S : Set M} {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {K : ι → Set M} (hK : Antitone K) (hSK : ∀ i, S ⊆ K i)

/-- The pairs `(M, M ∖ K i)`, with the maps induced by the identity of `M`. -/
private def complPairDiagram : ι ⥤ TopPair.{w} where
  obj i := TopPair.ofSubset ((K i)ᶜ : Set (TopCat.of M))
  map h := TopPair.ofSubsetMap (𝟙 _) (compl_subset_compl.2 (hK h.le))
  map_id _ := TopPair.ofSubsetMap_id _
  map_comp _ _ := TopPair.ofSubsetMap_comp (𝟙 _) (𝟙 _) _ _ _

/-- The cocone of the pairs `(M, M ∖ K i)` over the pair `(M, M ∖ S)`. -/
private def complPairCocone : Cocone (complPairDiagram hK) where
  pt := TopPair.ofSubset (Sᶜ : Set (TopCat.of M))
  ι := { app i := TopPair.ofSubsetMap (𝟙 _) (compl_subset_compl.2 (hSK i))
         naturality _ _ _ :=
           (TopPair.ofSubsetMap_comp (𝟙 _) (𝟙 _) _ _ _).symm.trans (Category.comp_id _).symm }

variable (hcpt : ∀ T : Set M, IsCompact T → Disjoint T S → ∃ i, Disjoint T (K i))
include hK hcpt

/-- Relative homology of `(M, M ∖ S)` is the colimit of relative homology of the pairs
`(M, M ∖ K i)`: on the ambient spaces the legs are identities, and a compact subset of `M ∖ S`
misses some `K i`. -/
private def isColimitComplPairCocone :
    IsColimit ((TopPair.singularHomologyFunctor N k).mapCocone (complPairCocone hK hSK)) := by
  have hfst (i : ι) : TopPair.Hom.fst ((complPairCocone hK hSK).ι.app i) = 𝟙 (TopCat.of M) :=
    TopPair.ofSubsetMap_fst _ _
  refine TopPair.isColimitMapCoconeSingularHomology N k _ (fun i ↦ ?_) (fun T _ ↦ ?_)
    fun T hT ↦ ?_
  · rw [hfst]
    exact IsEmbedding.id
  · refine ⟨Classical.arbitrary ι, fun x _ ↦ ⟨x, ?_⟩⟩
    rw [hfst]
    rfl
  · obtain ⟨i, hi⟩ := hcpt _ (hT.image continuous_subtype_val)
      (disjoint_left.2 fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.2)
    exact ⟨i, fun x hx ↦ ⟨⟨x.1, disjoint_left.1 hi ⟨x, hx, rfl⟩⟩,
      Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)⟩⟩

/-- The colimit of `isColimitComplPairCocone`, with its components written as local homology
groups and restriction maps. -/
private def isColimitLocalHomology :
    IsColimit ((TopPair.toSSetPair ⋙ SSetPair.homologyFunctor N k).mapCocone
      (complPairCocone hK hSK)) := by
  have h := isColimitComplPairCocone N k hK hSK hcpt
  rwa [TopPair.singularHomologyFunctor_eq_toSSetPair_comp] at h

/-- **Local homology classes come from larger sets.**  If every compact set disjoint from `S`
misses some member of a downward directed family of sets `K i ⊇ S`, then every class of
`Hₖ(M, M ∖ S)` is the restriction of a class of some `Hₖ(M, M ∖ K i)`. -/
theorem exists_localHomologyRestriction_eq (x : (localHomology N S k : ModuleCat.{w} Λ)) :
    ∃ i, ∃ y : (localHomology N (K i) k : ModuleCat.{w} Λ),
      localHomologyRestriction N (hSK i) k y = x := by
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep _ (isColimitLocalHomology N k hK hSK hcpt) x
  exact ⟨i, y, by rw [localHomologyRestriction_def]; exact hy⟩

/-- **Vanishing of local homology classes is detected on a smaller set.**  If every compact set
disjoint from `S` misses some member of a downward directed family of sets `K i ⊇ S`, then a class
of `Hₖ(M, M ∖ K i)` whose restriction to `S` vanishes already restricts to zero on some
`K j ⊆ K i`. -/
theorem exists_localHomologyRestriction_eq_zero {i : ι}
    (y : (localHomology N (K i) k : ModuleCat.{w} Λ))
    (hy : localHomologyRestriction N (hSK i) k y = 0) :
    ∃ j, ∃ hij : i ≤ j, localHomologyRestriction N (hK hij) k y = 0 := by
  obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq (j := i) _
    (isColimitLocalHomology N k hK hSK hcpt) y 0
    (by rw [map_zero]; rw [localHomologyRestriction_def] at hy; exact hy)
  rw [map_zero] at hfg
  exact ⟨j, f.le, by rw [localHomologyRestriction_def]; exact hfg⟩

end Family

section Nhds

variable [T2Space M] {A : Set M}

/-- **Local homology classes come from a neighbourhood.**  In a Hausdorff space, every class of
`Hₖ(M, M ∖ A)` is the restriction of a class of `Hₖ(M, M ∖ U)` for some neighbourhood `U`
of `A`. -/
theorem exists_mem_nhdsSet_localHomologyRestriction_eq
    (x : (localHomology N A k : ModuleCat.{w} Λ)) :
    ∃ U, ∃ hU : U ∈ 𝓝ˢ A, ∃ y : (localHomology N U k : ModuleCat.{w} Λ),
      localHomologyRestriction N (subset_of_mem_nhdsSet hU) k y = x := by
  obtain ⟨U, y, hy⟩ := exists_localHomologyRestriction_eq N k
    (K := fun U : {U : Set M // U ∈ 𝓝ˢ A}ᵒᵈ ↦ (OrderDual.ofDual U).1) (fun _ _ h ↦ h)
    (fun U ↦ subset_of_mem_nhdsSet (OrderDual.ofDual U).2)
    (fun T hT hTA ↦ ⟨OrderDual.toDual ⟨Tᶜ,
      hT.isClosed.isOpen_compl.mem_nhdsSet.2 hTA.subset_compl_left⟩, disjoint_compl_right⟩) x
  exact ⟨_, (OrderDual.ofDual U).2, y, hy⟩

/-- **Vanishing of local homology classes is detected on a neighbourhood.**  In a Hausdorff
space, a class of `Hₖ(M, M ∖ U)` for a neighbourhood `U` of `A` whose restriction to `A` vanishes
already restricts to zero on some neighbourhood `V ⊆ U` of `A`. -/
theorem exists_mem_nhdsSet_localHomologyRestriction_eq_zero {U : Set M} (hU : U ∈ 𝓝ˢ A)
    (y : (localHomology N U k : ModuleCat.{w} Λ))
    (hy : localHomologyRestriction N (subset_of_mem_nhdsSet hU) k y = 0) :
    ∃ V, ∃ _ : V ∈ 𝓝ˢ A, ∃ hVU : V ⊆ U, localHomologyRestriction N hVU k y = 0 := by
  obtain ⟨V, hUV, hV⟩ := exists_localHomologyRestriction_eq_zero N k
    (K := fun U : {U : Set M // U ∈ 𝓝ˢ A}ᵒᵈ ↦ (OrderDual.ofDual U).1) (fun _ _ h ↦ h)
    (fun U ↦ subset_of_mem_nhdsSet (OrderDual.ofDual U).2)
    (fun T hT hTA ↦ ⟨OrderDual.toDual ⟨Tᶜ,
      hT.isClosed.isOpen_compl.mem_nhdsSet.2 hTA.subset_compl_left⟩, disjoint_compl_right⟩)
    (i := OrderDual.toDual ⟨U, hU⟩) y hy
  exact ⟨_, (OrderDual.ofDual V).2, hUV, hV⟩

end Nhds

end TauCeti
