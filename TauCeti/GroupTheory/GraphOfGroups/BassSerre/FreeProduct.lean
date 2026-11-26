/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import Mathlib.GroupTheory.CoprodI
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Tree
import TauCeti.GroupTheory.GraphOfGroups.FreeProduct.Basic
import TauCeti.GroupTheory.GraphOfGroups.SpanningTree
import TauCeti.GroupTheory.GTree.Restrict

/-!
# The Bass–Serre tree of a free product

The free product `∗ᵢ Mᵢ` of a family of groups is the fundamental group of the graph of groups
`GraphOfGroups.freeProduct M PEmpty` over the star with one spoke for each `i`: the group `Mᵢ`
sits at the tip of the spoke `i`, and the center and the edges carry the trivial group. Through
this identification `∗ᵢ Mᵢ` acts without inversions on the Bass–Serre tree of that graph of
groups, and the action has the following properties.

* Every dart has trivial stabilizer, since the edge groups are trivial.
* There is a vertex `t i` for each `i` whose stabilizer is the factor `Mᵢ`, that is the range of
  `Monoid.CoprodI.of`.
* Every vertex either has trivial stabilizer (the translates of the center) or is a translate
  `g • t i`, whose stabilizer is the conjugate `g Mᵢ g⁻¹`.
* No translate of `t i` is `t i'` for `i ≠ i'`: the vertices `t i` lie over different vertices of
  the star.

This is the tree from which Kurosh's subgroup theorem is read off, by restricting the action to a
subgroup.

## Main results

* `TauCeti.GraphOfGroups.exists_gTree_coprodI`: the free product `∗ᵢ Mᵢ` acts on a tree with the
  properties above.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.5, Theorem 14.
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §3.2.
-/

public section

open Monoid _root_.MulAction

universe u w

namespace TauCeti.GraphOfGroups

open SerreGraph

variable {ι : Type u} (M : ι → Type w) [∀ i, Group (M i)]

/-- **The tree of a free product.** The free product `∗ᵢ Mᵢ` acts without inversions on a tree
with trivial dart stabilizers, with a vertex `t i` for each `i` whose stabilizer is the factor
`Mᵢ`, such that every vertex with nontrivial stabilizer is a translate of some `t i`, and no
translate of `t i` is `t i'` for `i ≠ i'`. The tree is the Bass–Serre tree of the free product
as a graph of groups over a star. -/
theorem exists_gTree_coprodI :
    ∃ (T : GTree.{max u w, max u w} (CoprodI M)) (t : ι → T.V),
      (∀ e : T.E, stabilizer (CoprodI M) e = ⊥) ∧
      (∀ i, stabilizer (CoprodI M) (t i) = (CoprodI.of (M := M) (i := i)).range) ∧
      (∀ y : T.V, stabilizer (CoprodI M) y = ⊥ ∨ ∃ i, ∃ g : CoprodI M, g • t i = y) ∧
      (∀ i i' (g : CoprodI M), g • t i = t i' → i = i') := by
  let 𝔸 := freeProduct M PEmpty.{1}
  -- The path from the center to the tip `i` along the spoke.
  let s (i : ι) := (dartPrefunctor 𝔸).mapPath
    ((starRoseTree ι PEmpty).path (starRose.center ι PEmpty) (starRose.tip _ i))
  let e := coprodIEquivπ₁ M
  have he (i : ι) (m : M i) : e (CoprodI.of m) = π₁.vertexHom (s i) m := coprodIEquivπ₁_of M m
  have hbot (K : Subgroup (π₁ 𝔸 (starRose.center ι PEmpty))) (hK : K = ⊥) :
      K.comap e.toMonoidHom = ⊥ := by
    rw [hK, MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).2 e.injective
  let X := bassSerreTree 𝔸 (starRose.center ι PEmpty)
  refine ⟨X.comap e.toMonoidHom, fun i => bassSerreVertex (s i), fun d => ?_, fun i => ?_,
    fun y => ?_, fun i i' g h => ?_⟩
  · exact (GTree.stabilizer_comap_dart X e.toMonoidHom d).trans
      (hbot _ (stabilizer_bassSerreTree_dart_eq_bot _))
  · refine (GTree.stabilizer_comap_vertex X e.toMonoidHom _).trans ?_
    ext g
    rw [stabilizer_bassSerreVertex, Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.mem_range]
    exact ⟨fun ⟨m, hm⟩ => ⟨m, e.injective ((he i m).trans hm)⟩,
      fun ⟨m, hm⟩ => ⟨m, (he i m).symm.trans (congrArg e hm)⟩⟩
  · obtain ⟨b, p, hp⟩ := bassSerreVertex_surjective (y : X.V)
    rcases starRose.eq_center_or_eq_tip b with rfl | ⟨i, rfl⟩
    · -- A vertex over the center has trivial stabilizer.
      exact .inl ((GTree.stabilizer_comap_vertex X e.toMonoidHom _).trans
        (hbot _ (hp ▸ stabilizer_bassSerreVertex_eq_bot p)))
    · -- A vertex over the tip `i` is a translate of the vertex of the spoke path.
      obtain ⟨γ, hγ⟩ := exists_smul_bassSerreVertex_eq (s i) p
      refine .inr ⟨i, e.symm γ, (GTree.comap_smul_vertex X e.toMonoidHom _ _).trans ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hγ.trans hp
  · -- The vertices `t i` lie over the distinct tips of the star.
    have := congrArg (bassSerreProjection 𝔸 (starRose.center ι PEmpty)).mapV
      ((GTree.comap_smul_vertex X e.toMonoidHom g _).symm.trans h)
    rw [bassSerreProjection_mapV_smul, bassSerreProjection_mapV_bassSerreVertex,
      bassSerreProjection_mapV_bassSerreVertex] at this
    exact starRose.tip_injective this

end TauCeti.GraphOfGroups
