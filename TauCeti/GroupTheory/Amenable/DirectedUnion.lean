/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.WeakStar
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import Mathlib.GroupTheory.Finiteness

/-!
# Directed unions of amenable subgroups

A topological group is amenable when it is exhausted, finite set by finite set, by images of
amenable topological groups. Given continuous homomorphisms `φ i : K i →ₜ* G` from amenable groups,
push a left-invariant mean `m` on `UCB (K i)` forward to the mean `f ↦ m (f ∘ φ i)` on `UCB G`;
since `(L_(φ i k) f) ∘ φ i = L_k (f ∘ φ i)`, this mean satisfies every invariance equation
`m (L_g f) = m f` with `g` in the range of `φ i`. If every finite subset of `G` lies in the range
of some `φ i`, then every finite family of invariance equations has a solution, and the
finite-intersection criterion `TauCeti.amenable_iff_forall_finset_exists`, which rests on the
weak-* compactness of the space of means, produces a left-invariant mean on `UCB G`.

Specializing to inclusions of subgroups, with their subspace topologies, gives the closure of
amenability under directed unions: if `H i` is a nonempty directed family of amenable subgroups of
`G`, then the subgroup `⨆ i, H i = ⋃ i, H i` is amenable, and `G` is amenable when this union is
all of `G`. Since every finite subset of `G` lies in a finitely generated subgroup, a topological
group whose finitely generated subgroups are all amenable is amenable.

No discreteness is needed: the subgroups carry the subspace topology, and a function in `UCB G`
restricts to a function in the `UCB` space of each of them.

## Main results

* `TauCeti.Amenable.of_forall_finset_subset_range`: a topological group is amenable if each of its
  finite subsets lies in the range of a continuous homomorphism from an amenable topological group,
  drawn from a fixed family.
* `TauCeti.amenable_iSup_of_directed`: the union of a nonempty directed family of amenable
  subgroups is an amenable subgroup.
* `TauCeti.Amenable.of_directed_of_iSup_eq_top`: a topological group which is the union of a
  nonempty directed family of amenable subgroups is amenable.
* `TauCeti.Amenable.of_forall_fg`: a topological group whose finitely generated subgroups are
  amenable is amenable.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.
* A. Garrido, *An introduction to amenable groups*, Proposition 2.2.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group `G` is amenable if, for a family of continuous homomorphisms
`φ i : K i →ₜ* G` from amenable topological groups, every finite subset of `G` lies in the range of
some `φ i`. -/
theorem Amenable.of_forall_finset_subset_range {ι : Type*} {K : ι → Type*} [∀ i, Group (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalGroup (K i)] [∀ i, Amenable (K i)]
    (φ : ∀ i, K i →ₜ* G) (h : ∀ s : Finset G, ∃ i, (s : Set G) ⊆ Set.range (φ i)) :
    Amenable G := by
  classical
  refine amenable_iff_forall_finset_exists.2 fun t => ?_
  obtain ⟨i, hi⟩ := h (t.image Prod.fst)
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := K i)
  refine ⟨m.map (φ i), fun p hp => ?_⟩
  obtain ⟨k, hk⟩ := hi (Finset.mem_coe.2 (Finset.mem_image_of_mem Prod.fst hp))
  rw [← hk]
  exact hm.map_apply_leftTranslation (φ i) k p.2

/-- The union `⨆ i, H i` of a nonempty directed family of amenable subgroups `H i` of a topological
group is an amenable subgroup. -/
theorem amenable_iSup_of_directed {ι : Type*} [Nonempty ι] {H : ι → Subgroup G}
    (hH : Directed (· ≤ ·) H) [∀ i, Amenable (H i)] : Amenable ↥(⨆ i, H i) := by
  classical
  refine .of_forall_finset_subset_range
    (fun i => ContinuousMonoidHom.subgroupInclusion (le_iSup H i)) fun s => ?_
  have hH' : Directed (· ⊆ ·) fun i => (H i : Set G) :=
    hH.mono_comp _ fun _ _ => SetLike.coe_subset_coe.2
  obtain ⟨i, hi⟩ := hH'.exists_mem_subset_of_finset_subset_biUnion (s := s.image Subtype.val) <| by
    rw [Finset.coe_image, ← Subgroup.coe_iSup_of_directed hH]
    exact Set.image_subset_iff.2 fun x _ => x.2
  exact ⟨i, fun x hx => ⟨⟨x, hi (Finset.mem_image_of_mem _ hx)⟩, rfl⟩⟩

/-- A topological group which is the union of a nonempty directed family of amenable subgroups is
amenable. -/
theorem Amenable.of_directed_of_iSup_eq_top {ι : Type*} [Nonempty ι] {H : ι → Subgroup G}
    (hH : Directed (· ≤ ·) H) (htop : ⨆ i, H i = ⊤) [∀ i, Amenable (H i)] : Amenable G :=
  have := amenable_iSup_of_directed hH
  .of_surjective (ContinuousMonoidHom.subgroupSubtype (⨆ i, H i)) fun x =>
    ⟨⟨x, htop ▸ Subgroup.mem_top x⟩, rfl⟩

/-- A topological group all of whose finitely generated subgroups are amenable is amenable. -/
theorem Amenable.of_forall_fg (h : ∀ K : Subgroup G, K.FG → Amenable K) : Amenable G := by
  have : ∀ K : {K : Subgroup G // K.FG}, Amenable K.1 := fun K => h K.1 K.2
  refine .of_forall_finset_subset_range
    (fun K : {K : Subgroup G // K.FG} => ContinuousMonoidHom.subgroupSubtype K.1) fun s => ?_
  refine ⟨⟨Subgroup.closure s, (Group.fg_iff_subgroup_fg _).1 inferInstance⟩, fun x hx => ?_⟩
  exact ⟨⟨x, Subgroup.subset_closure hx⟩, rfl⟩

end TauCeti
