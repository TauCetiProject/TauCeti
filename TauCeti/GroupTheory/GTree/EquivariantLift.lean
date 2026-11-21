/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Between
public import TauCeti.GroupTheory.GTree.Refinement

/-!
# Lifting equivariant maps along collapse maps of trees

A collapse map `p : T' → T` of `G`-trees preserves betweenness: it sends the vertices of the
geodesic between two vertices into the geodesic between their images. Let `X` be a `G`-set whose
point stabilizers are elliptic in `T'`. Every equivariant map `X → T` then lifts along `p` to an
equivariant map `X → T'`: the preimage of a vertex fixed by a point stabilizer is an invariant
subtree, in which the stabilizer, being elliptic, fixes a vertex. Applied along a sequence of
refinements `T 0 ← T 1 ← ⋯` this gives compatible equivariant maps to all the trees, the
*resolutions* of the sequence.

## Main results

* `TauCeti.GTree.IsCollapseMap.isBetween`: collapse maps preserve betweenness.
* `TauCeti.GTree.IsEllipticSubgroup.exists_fixed_mem_of_isConvex`: an elliptic subgroup fixes a
  vertex of every nonempty convex set it preserves.
* `TauCeti.GTree.exists_lift_of_isCollapseMap`: lifting an equivariant map along a collapse map.
* `TauCeti.GTree.exists_seq_lift_of_isCollapseMap`: lifting an equivariant map along a sequence of
  collapse maps.
* `TauCeti.GTree.exists_resolution_of_refines`: compatible equivariant maps to a sequence of
  refinements.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), proof of
  Proposition 2.24 (the construction of the maps `f_k`).
-/

public section

universe u v u' v' w w'

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] {T : GTree.{u, v} G} {T' : GTree.{u', v'} G}

/-- A collapse map preserves betweenness: a vertex between `a` and `b` is sent to a vertex
between the images of `a` and `b`. -/
theorem IsCollapseMap.isBetween {p : T'.V →[G] T.V} (hp : IsCollapseMap p) {a x b : T'.V}
    (h : T'.IsBetween a x b) : T.IsBetween (p a) (p x) (p b) := by
  -- The vertices between `p a` and `p b` form a convex set. Its preimage is convex and contains
  -- `a` and `b`, so it contains the reduced path from `a` to `b`, whose vertices are those
  -- between `a` and `b`.
  obtain ⟨q⟩ := h.nonempty_path
  have hq := Path.isReduced_reduce T'.toSerreGraph q
  refine (hp.isConvex_preimage (T.isAcyclic.isConvex_setOf_isBetween _ _)).convexHull_subset
    (Set.pair_subset (isBetween_left (T.nonempty_path _ _)) (isBetween_right (T.nonempty_path _ _)))
    ?_
  rw [T'.isAcyclic.convexHull_pair hq]
  exact (T'.isAcyclic.isBetween_iff_mem_vertices hq).mp h

/-- An elliptic subgroup fixes a vertex of every nonempty convex set of vertices which it
preserves: the vertex of the set nearest to a fixed vertex. -/
theorem IsEllipticSubgroup.exists_fixed_mem_of_isConvex {H : Subgroup G}
    (hH : T.IsEllipticSubgroup H) {C : Set T.V} (hC : T.IsConvex C) (hne : C.Nonempty)
    (hinv : ∀ h ∈ H, ∀ x ∈ C, h • x ∈ C) : ∃ x ∈ C, ∀ h ∈ H, h • x = x := by
  -- Let `a` be a vertex of `C` nearest to a vertex `v` fixed by `H`, and `h ∈ H`. The reduced path
  -- from `v` to `a` meets `C` only at its end, so it continues to `h • a` without backtracking;
  -- since `h • a` is as near to `v` as `a`, the continuation is trivial.
  obtain ⟨v, hv⟩ := isEllipticSubgroup_iff_forall.mp hH
  obtain ⟨a, ha, hmin⟩ := exists_forall_dist_le hne v
  refine ⟨a, ha, fun h hh => ?_⟩
  obtain ⟨q, hq, -⟩ := T.isTree.existsUnique_isReduced v a
  obtain ⟨r, hr, -⟩ := T.isTree.existsUnique_isReduced a (h • a)
  have hqr := T.isAcyclic.dist_eq_length (hC.isReduced_comp ha (hinv h hh a ha) hq
    (fun e he => T.isAcyclic.src_notMem_of_forall_dist_le hmin hq (List.mem_of_mem_getLast? he))
    hr)
  have hdist := T.dist_smul h v a
  rw [hv h hh] at hdist
  rw [Quiver.Path.length_comp, ← T.isAcyclic.dist_eq_length hq,
    ← T.isAcyclic.dist_eq_length hr] at hqr
  exact ((dist_eq_zero_iff (T.nonempty_path _ _)).mp (by lia)).symm

variable {X : Type w'} [MulAction G X]

/-- **Lifting along a collapse map.** Let `p : T' → T` be a collapse map of `G`-trees and `X` a
`G`-set all of whose point stabilizers are elliptic in `T'`. Every equivariant map from `X` to the
vertices of `T` lifts along `p` to an equivariant map to the vertices of `T'`. -/
theorem exists_lift_of_isCollapseMap {p : T'.V →[G] T.V} (hp : IsCollapseMap p) (f : X →[G] T.V)
    (hX : ∀ x : X, T'.IsEllipticSubgroup (stabilizer G x)) :
    ∃ f' : X →[G] T'.V, ∀ x : X, p (f' x) = f x := by
  -- The stabilizer of `x` preserves the fibre of `p` over `f x`, a nonempty convex set, so it
  -- fixes a vertex of it; such choices extend along the orbits.
  obtain ⟨f', hf'⟩ := (p.exists_comp_eq_iff f).mpr fun x => by
    obtain ⟨y, hy, hfix⟩ := (hX x).exists_fixed_mem_of_isConvex
      (hp.isConvex_preimage (T.isAcyclic.isConvex_singleton (f x))) (hp.surjective (f x))
      fun g hg y (hy : p y = f x) => by simpa [hy] using congrArg f (mem_stabilizer_iff.mp hg)
    exact ⟨y, fun g hg => mem_stabilizer_iff.mpr (hfix g hg), hy⟩
  exact ⟨f', DFunLike.congr_fun hf'⟩

/-- A `G`-set whose point stabilizers are elliptic in `T` has an equivariant map to the vertices
of `T`. -/
theorem nonempty_mulActionHom_of_isEllipticSubgroup_stabilizer
    (hX : ∀ x : X, T.IsEllipticSubgroup (stabilizer G x)) : Nonempty (X →[G] T.V) :=
  MulAction.nonempty_mulActionHom_iff.mpr fun x => isEllipticSubgroup_iff.mp (hX x)

/-- **Lifting along a sequence of collapse maps.** Let `p k : T (k + 1) → T k` be collapse maps
of `G`-trees and `X` a `G`-set whose point stabilizers are elliptic in every `T (k + 1)`. Every
equivariant map `f₀ : X → T 0` is the first term of a sequence of equivariant maps `f k : X → T k`
with `p k ∘ f (k + 1) = f k` for every `k`. -/
theorem exists_seq_lift_of_isCollapseMap (T : ℕ → GTree.{u, v} G)
    (p : ∀ k, (T (k + 1)).V →[G] (T k).V) (hp : ∀ k, IsCollapseMap (p k)) (f₀ : X →[G] (T 0).V)
    (hX : ∀ k, ∀ x : X, (T (k + 1)).IsEllipticSubgroup (stabilizer G x)) :
    ∃ f : ∀ k, X →[G] (T k).V, f 0 = f₀ ∧ ∀ k x, p k (f (k + 1) x) = f k x := by
  -- Lift the maps one after the other; by definition `f (k + 1)` is the lift of `f k`.
  choose lift hlift using fun k (φ : X →[G] (T k).V) =>
    exists_lift_of_isCollapseMap (hp k) φ (hX k)
  exact ⟨fun k => Nat.rec (motive := fun k => X →[G] (T k).V) f₀ lift k, rfl,
    fun k => hlift k _⟩

/-- **Resolutions of a sequence of refinements.** Let `T 0 ← T 1 ← ⋯` be `G`-trees, each a
refinement of the previous one, and `X` a `G`-set whose point stabilizers are elliptic in every
`T k`. There are equivariant maps `f k : X → T k` and collapse maps `p k l : T l → T k` for
`k ≤ l` with `p k l ∘ f l = f k`. -/
theorem exists_resolution_of_refines (T : ℕ → GTree.{u, v} G)
    (href : ∀ k, (T (k + 1)).Refines (T k))
    (hX : ∀ k, ∀ x : X, (T k).IsEllipticSubgroup (stabilizer G x)) :
    ∃ (f : ∀ k, X →[G] (T k).V) (p : ∀ k l, k ≤ l → ((T l).V →[G] (T k).V)),
      (∀ k l (h : k ≤ l), IsCollapseMap (p k l h)) ∧
        ∀ k l (h : k ≤ l) (x : X), p k l h (f l x) = f k x := by
  choose q hq using fun k => refines_iff.mp (href k)
  obtain ⟨f, -, hf⟩ := exists_seq_lift_of_isCollapseMap T q hq
    (nonempty_mulActionHom_of_isEllipticSubgroup_stabilizer (hX 0)).some fun k => hX (k + 1)
  -- The composites of the collapse maps `q` are collapse maps compatible with the maps `f`.
  have hp (k l : ℕ) (hkl : k ≤ l) :
      ∃ P : (T l).V →[G] (T k).V, IsCollapseMap P ∧ ∀ x, P (f l x) = f k x := by
    induction l, hkl using Nat.le_induction with
    | base => exact ⟨MulActionHom.id G, isCollapseMap_id _, fun _ => rfl⟩
    | succ l _ ih =>
      obtain ⟨P, hP, hPf⟩ := ih
      exact ⟨P.comp (q l), hP.comp (hq l), fun x => by rw [MulActionHom.comp_apply, hf, hPf]⟩
  choose p hp hpf using hp
  exact ⟨f, p, hp, hpf⟩

end GTree

end TauCeti
