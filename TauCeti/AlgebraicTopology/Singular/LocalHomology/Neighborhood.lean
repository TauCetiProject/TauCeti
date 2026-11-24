/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Chains
public import TauCeti.Order.Filter.Basic

/-!
# Local homology of a set as a colimit over its neighbourhoods

For a subset `S` of a space `M`, the relative singular homology `Hₖ(M, M ∖ S)`
(`TauCeti.localHomology`) is approximated by the groups `Hₖ(M, M ∖ K)` of larger sets `K ⊇ S`,
through the restriction maps `Hₖ(M, M ∖ K) ⟶ Hₖ(M, M ∖ S)`.  A singular simplex of `M ∖ S` has
compact image.  So when every compact set disjoint from `S` misses some member of a downward
directed family of sets `K ⊇ S`, the subspaces `M ∖ K` exhaust `M ∖ S` in the sense of compact
supports, and relative homology of the pair `(M, M ∖ S)` is the colimit of the relative homology
of the pairs `(M, M ∖ K)`, as already the relative singular chains are
(`TauCeti.isColimitMapCoconeSingularChainComplexComplPairCocone`).  This holds for sets `K`
indexed by any filtered category, with coefficients whose filtered colimits are exact
(`TauCeti.isColimitComplPairCocone`, for the diagram `TauCeti.complPairDiagram` of the pairs
`(M, M ∖ K)` and its cocone `TauCeti.complPairCocone`).  With coefficients in a module this says
two things:

* every class of `Hₖ(M, M ∖ S)` is the restriction of a class of some `Hₖ(M, M ∖ K)`
  (`TauCeti.exists_localHomologyRestriction_eq`);
* a class of `Hₖ(M, M ∖ K)` whose restriction to `S` vanishes already restricts to zero on some
  smaller member of the family (`TauCeti.exists_localHomologyRestriction_eq_zero`).

In a Hausdorff space compact sets are closed, so the neighbourhoods of any set `A` form such a
family (`TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq` and
`TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq_zero`), and local homology along `A`
vanishes once it vanishes along sets between `A` and any of its neighbourhoods
(`TauCeti.isZero_localHomology_of_forall_mem_nhdsSet`).  For a compact subset `A` of a
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

universe w v u

namespace TauCeti

variable {M : Type w} [TopologicalSpace M]

section Diagram

variable {J : Type*} [Category J] {S : Set M} {K : J → Set M} (hK : ∀ ⦃i j⦄, (i ⟶ j) → K j ⊆ K i)
  (hSK : ∀ j, S ⊆ K j)

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) (k : ℕ)
  [IsFiltered J] [HasColimitsOfShape J (Type w)] [HasColimitsOfShape J A]
  [HasExactColimitsOfShape J A]
  (hcpt : ∀ T : Set M, IsCompact T → Disjoint T S → ∃ j, Disjoint T (K j))
include hcpt

/-- **Local homology is a colimit over larger sets.** Let `K j ⊇ S` be sets over a filtered
category `J`, getting smaller along its morphisms, such that every compact set disjoint from `S`
misses some `K j`. For coefficients whose filtered colimits are exact, relative homology of
`(M, M ∖ S)` is the colimit of relative homology of the pairs `(M, M ∖ K j)`: on the ambient spaces
the legs are identities, and a compact subset of `M ∖ S` misses some `K j`. -/
def isColimitComplPairCocone :
    IsColimit ((TopPair.singularHomologyFunctor R k).mapCocone (complPairCocone hK hSK)) := by
  rw [TopPair.singularHomologyFunctor_eq_chainComplexFunctor]
  exact isColimitOfPreserves (HomologicalComplex.homologyFunctor _ _ k)
    (isColimitMapCoconeSingularChainComplexComplPairCocone R hK hSK hcpt)

end Diagram

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) (k : ℕ)

section Family

variable {S : Set M} {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {K : ι → Set M} (hK : Antitone K) (hSK : ∀ i, S ⊆ K i)

variable (hcpt : ∀ T : Set M, IsCompact T → Disjoint T S → ∃ i, Disjoint T (K i))
include hK hcpt

/-- The colimit of `isColimitComplPairCocone`, with its components written as local homology
groups and restriction maps. -/
private def isColimitLocalHomology :
    IsColimit ((TopPair.toSSetPair ⋙ SSetPair.homologyFunctor N k).mapCocone
      (complPairCocone (fun _ _ f ↦ hK f.le) hSK)) := by
  have h := isColimitComplPairCocone (fun _ _ f ↦ hK f.le) hSK N k hcpt
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
    (K := fun U : {U : Set M // U ∈ 𝓝ˢ A}ᵒᵈ ↦ (OrderDual.ofDual U).val) (fun _ _ h ↦ h)
    (fun U ↦ subset_of_mem_nhdsSet (OrderDual.ofDual U).property)
    (fun T hT hTA ↦ ⟨OrderDual.toDual ⟨Tᶜ,
      hT.isClosed.isOpen_compl.mem_nhdsSet.2 hTA.subset_compl_left⟩, disjoint_compl_right⟩) x
  exact ⟨_, (OrderDual.ofDual U).property, y, hy⟩

variable {k} in
/-- **Vanishing of local homology from larger sets.**  In a Hausdorff space, local homology
along `A` vanishes in degree `k` if every neighbourhood of `A` contains a set `K ⊇ A` along which
it vanishes in degree `k`: every class along `A` is restricted from a class along a neighbourhood
of `A` (`TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq`), hence from a class along such
a `K`. -/
theorem isZero_localHomology_of_forall_mem_nhdsSet
    (h : ∀ U ∈ 𝓝ˢ A, ∃ K, A ⊆ K ∧ K ⊆ U ∧ IsZero (localHomology N K k)) :
    IsZero (localHomology N A k) := by
  have h0 (α : (localHomology N A k : ModuleCat.{w} Λ)) : α = 0 := by
    obtain ⟨U, hU, β, rfl⟩ := exists_mem_nhdsSet_localHomologyRestriction_eq N k α
    obtain ⟨K, hAK, hKU, hK⟩ := h U hU
    rw [← localHomologyRestriction_comp_apply N hAK hKU,
      (ModuleCat.subsingleton_of_isZero hK).elim (localHomologyRestriction N hKU k β) 0, map_zero]
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun α β ↦ (h0 α).trans (h0 β).symm⟩

/-- **Vanishing of local homology classes is detected on a neighbourhood.**  In a Hausdorff
space, a class of `Hₖ(M, M ∖ U)` for a neighbourhood `U` of `A` whose restriction to `A` vanishes
already restricts to zero on some neighbourhood `V ⊆ U` of `A`. -/
theorem exists_mem_nhdsSet_localHomologyRestriction_eq_zero {U : Set M} (hU : U ∈ 𝓝ˢ A)
    (y : (localHomology N U k : ModuleCat.{w} Λ))
    (hy : localHomologyRestriction N (subset_of_mem_nhdsSet hU) k y = 0) :
    ∃ V, ∃ _ : V ∈ 𝓝ˢ A, ∃ hVU : V ⊆ U, localHomologyRestriction N hVU k y = 0 := by
  obtain ⟨V, hUV, hV⟩ := exists_localHomologyRestriction_eq_zero N k
    (K := fun U : {U : Set M // U ∈ 𝓝ˢ A}ᵒᵈ ↦ (OrderDual.ofDual U).val) (fun _ _ h ↦ h)
    (fun U ↦ subset_of_mem_nhdsSet (OrderDual.ofDual U).property)
    (fun T hT hTA ↦ ⟨OrderDual.toDual ⟨Tᶜ,
      hT.isClosed.isOpen_compl.mem_nhdsSet.2 hTA.subset_compl_left⟩, disjoint_compl_right⟩)
    (i := OrderDual.toDual ⟨U, hU⟩) y hy
  exact ⟨_, (OrderDual.ofDual V).property, hUV, hV⟩

end Nhds

end TauCeti
