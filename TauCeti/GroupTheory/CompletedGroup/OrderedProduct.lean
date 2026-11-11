/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.CompletedGroup.Map
public import TauCeti.Data.Finset.Sort
public import Mathlib.Algebra.Group.Support

/-!
# Ordered products in completed groups

A family in a completed group has an ordered product whenever only finitely many
factors project nontrivially at each order. The order may be any linear order,
without a countability or well-ordering assumption. The smallest index is the
leftmost factor. The finite products are compatible even when their supports grow
with the cutoff.

The construction uses Mathlib's `Function.mulSupport`, `Finset.sort` and
`List.prod` on the compatible-family carrier of `CompletedGroup`. Products can be
computed using any finite set containing the support at the chosen order. This
also proves uniqueness, deletion of identity factors, order-preserving reindexing,
swapping adjacent commuting factors, and preservation by maps of reindexed towers.
The reindexing proof uses Mathlib's `Finset.map_sort`. The predicate
`HasFiniteSupport` records the support condition and is preserved by injective
reindexing and maps of reindexed towers.

Adapted from `Mei/GroupTheory/CompletedGroup/OrderedProduct.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

open CategoryTheory Opposite

universe u

namespace TauCeti.CompletedGroup

variable {F G : ℕᵒᵖ ⥤ GrpCat.{u}} {ι κ : Type*}

/-- A family has finite support at each order if only finitely many factors have
nonidentity projection to any fixed tower group. -/
abbrev HasFiniteSupport (x : ι → completedGroup F) : Prop :=
  ∀ k, (Function.mulSupport fun i => projection k (x i)).Finite

namespace HasFiniteSupport

/-- A subfamily indexed by an injection still has finite support at each order. -/
theorem comp {x : ι → completedGroup F} (hx : HasFiniteSupport x)
    {e : κ → ι} (he : Function.Injective e) : HasFiniteSupport (x ∘ e) :=
  fun k => (hx k).preimage he.injOn

/-- A map of reindexed towers preserves finite support at each order. -/
theorem map {x : ι → completedGroup F} (hx : HasFiniteSupport x)
    (ρ : ℕ →o ℕ) (f : ρ.toFunctor.op ⋙ F ⟶ G) :
    HasFiniteSupport (fun i => CompletedGroup.map ρ f (x i)) := by
  intro k
  apply (hx (ρ k)).subset
  intro i hi
  simp only [Function.mem_mulSupport, projection_map] at hi ⊢
  intro h
  exact hi (by simp [h])

end HasFiniteSupport

variable [LinearOrder ι] [LinearOrder κ]

/-- The ordered product of a family with finite support in every quotient.
The smallest index is the leftmost factor. -/
noncomputable def orderedProd (f : ι → completedGroup F)
    (hf : HasFiniteSupport f) :
    completedGroup F := by
  classical
  refine ⟨fun k => (((hf k).toFinset).sort.map fun i => projection k (f i)).prod,
    (mem_completedGroup_iff F _).mpr ?_⟩
  intro k l h
  simp only [← List.prod_hom, List.map_map, Function.comp_def, map_projection]
  apply (Finset.prod_map_sort_subset (f := fun i => projection k (f i)) ?_ ?_).symm
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hi ⊢
    intro he
    apply hi
    rw [← map_projection k l h, he, map_one]
  · intro i _ hi
    simpa only [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] using hi

/-- The projection of the ordered product is the increasing product of its
nonidentity factors at that order. -/
@[simp]
theorem projection_orderedProd (f : ι → completedGroup F)
    (hf : HasFiniteSupport f) (k : ℕ) :
    projection k (orderedProd f hf) =
      (((hf k).toFinset).sort.map fun i => projection k (f i)).prod := by
  rw [projection_apply]
  rfl

/-- Any finite set containing the nonidentity factors computes the same projection. -/
theorem projection_orderedProd_of_support (f : ι → completedGroup F)
    (hf : HasFiniteSupport f)
    (k : ℕ) (s : Finset ι)
    (hs : ∀ i, projection k (f i) ≠ 1 → i ∈ s) :
    projection k (orderedProd f hf) = (s.sort.map fun i => projection k (f i)).prod := by
  classical
  rw [projection_orderedProd]
  apply Finset.prod_map_sort_subset
  · intro i hi
    exact hs i ((hf k).mem_toFinset.mp hi)
  · intro i _ hi
    simpa only [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] using hi

/-- An element is the ordered product exactly when it has the prescribed finite products
as its projections. -/
theorem eq_orderedProd_iff (f : ι → completedGroup F)
    (hf : HasFiniteSupport f)
    (x : completedGroup F) :
    x = orderedProd f hf ↔ ∀ k, projection k x =
      (((hf k).toFinset).sort.map fun i => projection k (f i)).prod := by
  constructor
  · rintro rfl k
    exact projection_orderedProd f hf k
  · intro h
    exact ext fun k => (h k).trans (projection_orderedProd f hf k).symm

/-- A globally finite family has its usual finite increasing product. -/
theorem orderedProd_eq_list_prod (f : ι → completedGroup F)
    (hf : HasFiniteSupport f)
    (s : Finset ι) (hs : ∀ i, f i ≠ 1 → i ∈ s) :
    orderedProd f hf = (s.sort.map f).prod := by
  apply ext
  intro k
  rw [projection_orderedProd_of_support f hf k s (fun i hi => hs i (by
    intro he
    exact hi (by simp [he])))]
  simp only [← List.prod_hom, List.map_map, Function.comp_def]

/-- A family consisting entirely of identities has ordered product one. -/
@[simp]
theorem orderedProd_one
    (hf : HasFiniteSupport (fun _ : ι => (1 : completedGroup F))) :
    orderedProd (fun _ : ι => (1 : completedGroup F)) hf = 1 := by
  apply ext
  intro k
  simp

/-- The product of an empty indexed family is the identity. -/
@[simp]
theorem orderedProd_of_isEmpty [IsEmpty ι] (f : ι → completedGroup F)
    (hf : HasFiniteSupport f) :
    orderedProd f hf = 1 := by
  simpa using orderedProd_eq_list_prod f hf ∅ (fun i => isEmptyElim i)

/-- Order-preserving reindexing does not change the product if all omitted factors are one. -/
theorem orderedProd_comp (f : κ → completedGroup F)
    (hf : HasFiniteSupport f)
    (e : ι ↪o κ) (he : ∀ j, f j ≠ 1 → j ∈ Set.range e) :
    orderedProd (fun i => f (e i)) (hf.comp e.injective) = orderedProd f hf := by
  classical
  apply ext
  intro k
  have hfe : (Function.mulSupport fun i => projection k (f (e i))).Finite :=
    hf.comp e.injective k
  let s := hfe.toFinset
  rw [projection_orderedProd_of_support f hf k (s.map e.toEmbedding)]
  · rw [projection_orderedProd, ← Finset.map_sort e.toEmbedding s (· ≤ ·) (· ≤ ·)
      (by intros; exact e.le_iff_le.symm), List.map_map]
    rfl
  · intro j hj
    obtain ⟨i, rfl⟩ := he j (by intro h; exact hj (by simp [h]))
    exact Finset.mem_map.mpr
      ⟨i, hfe.mem_toFinset.mpr hj, rfl⟩

/-- Deleting any set of identity factors preserves the ordered product. -/
theorem orderedProd_subtype (f : ι → completedGroup F)
    (hf : HasFiniteSupport f)
    (s : Set ι) (hs : ∀ i, f i ≠ 1 → i ∈ s) :
    orderedProd (fun i : s => f i) (hf.comp Subtype.val_injective) = orderedProd f hf :=
  orderedProd_comp f hf (OrderEmbedding.subtype (fun i => i ∈ s))
    (fun i hi => ⟨⟨i, hs i hi⟩, rfl⟩)

/-- Two factors adjacent among the nonidentity factors may be swapped when their
projections commute at every order. Identity factors between the two indices are allowed. -/
theorem orderedProd_swap (f : ι → completedGroup F)
    (hf : HasFiniteSupport f)
    {a b : ι} (hab : a < b) (hgap : ∀ i, a < i → i < b → f i = 1)
    (hcomm : ∀ k, Commute (projection k (f a)) (projection k (f b))) :
    orderedProd (fun i => f (Equiv.swap a b i))
      (hf.comp (Equiv.swap a b).injective) = orderedProd f hf := by
  classical
  apply ext
  intro k
  let s := (hf k).toFinset ∪ {a, b}
  have hs : ∀ i, projection k (f i) ≠ 1 → i ∈ s := by
    intro i hi
    exact Finset.mem_union_left _ ((hf k).mem_toFinset.mpr hi)
  rw [projection_orderedProd_of_support f hf k s hs,
    projection_orderedProd_of_support _ _ k s]
  · apply Finset.prod_map_sort_swap s (fun i => projection k (f i)) hab
      (by simp [s]) (by simp [s]) ?_ (hcomm k)
    intro i hi ⟨hai, hib⟩
    have hia : i ≠ a := ne_of_gt hai
    have hib' : i ≠ b := ne_of_lt hib
    have hfi : projection k (f i) ≠ 1 := by
      simpa only [s, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        hia, hib', or_false, Set.Finite.mem_toFinset, Function.mem_mulSupport] using hi
    exact hfi (by simp [hgap i hai hib])
  · intro i hi
    by_cases hia : i = a
    · simp [s, hia]
    by_cases hib : i = b
    · simp [s, hib]
    apply hs i
    simpa only [Equiv.swap_apply_of_ne_of_ne hia hib] using hi

/-- Maps of reindexed towers preserve ordered products. -/
@[simp]
theorem map_orderedProd (ρ : ℕ →o ℕ) (g : ρ.toFunctor.op ⋙ F ⟶ G)
    (f : ι → completedGroup F)
    (hf : HasFiniteSupport f) :
    map ρ g (orderedProd f hf) =
      orderedProd (fun i => map ρ g (f i)) (hf.map ρ g) := by
  apply ext
  intro k
  rw [projection_map, projection_orderedProd,
    projection_orderedProd_of_support _ _ k (hf (ρ k)).toFinset]
  · simp only [← List.prod_hom, List.map_map, Function.comp_def, projection_map]
  · intro i hi
    apply (hf (ρ k)).mem_toFinset.mpr
    intro he
    exact hi (by simp [he])

end TauCeti.CompletedGroup
