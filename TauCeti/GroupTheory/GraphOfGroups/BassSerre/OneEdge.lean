/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Elliptic
public import TauCeti.GroupTheory.GraphOfGroups.OneEdge

/-!
# Bass–Serre trees of one-edge splittings

An amalgamated product `A ∗_C B` and an HNN extension `G ∗_C` are the fundamental groups of the
one-edge graphs of groups `GraphOfGroups.segment` and `GraphOfGroups.loop`. Through the
isomorphisms `π₁.equivPushoutI` and `π₁.equivHNNExtension` they act on the Bass–Serre trees of
these graphs of groups. The stabilizer of the vertex `p A_b` of the Bass–Serre tree is the
conjugate `p A_b p⁻¹` of the vertex group, and each vertex group maps onto its factor, or onto the
base group, along a path from the base vertex. So in `A ∗_C B` the vertex stabilizers are the
conjugates of `A` and of `B` (`TauCeti.GraphOfGroups.exists_map_stabilizer_eq_map_conj` with
these factors as reference subgroups), and in the HNN extension they are the conjugates of the base
group `G`. Hence a subgroup is elliptic in the splitting exactly when it lies in such a conjugate.

## Main results

* `TauCeti.GraphOfGroups.exists_path_map_range_vertexHom_segment`,
  `TauCeti.GraphOfGroups.exists_path_map_range_vertexHom_loop`: each vertex group maps onto a
  factor of `A ∗_C B`, or onto the base group of the HNN extension, along a path from the base
  vertex.
* `TauCeti.GraphOfGroups.bassSerreTree_segment_isEllipticSubgroup_comap_iff`,
  `TauCeti.GraphOfGroups.bassSerreTree_loop_isEllipticSubgroup_comap_iff`: a subgroup is elliptic
  in the splitting exactly when it lies in a conjugate of a factor, or of the base group.

## References

* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5 and the paragraph after it
  (the vertex stabilizers of the Bass–Serre tree).
-/

public section

universe w x

namespace TauCeti

namespace GraphOfGroups

/-! ### Amalgamated products -/

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}
  {hf : Function.Injective f} {hg : Function.Injective g}

/-- From either vertex `a` of the segment, each vertex group `A_b` maps onto its factor of
`A ∗_C B` along some path: the empty path if `b = a`, the dart from `a` to `b` otherwise. With the
factors as reference subgroups, `exists_map_stabilizer_eq_map_conj` shows that each vertex
stabilizer of the Bass–Serre tree is a conjugate of a factor. -/
theorem exists_path_map_range_vertexHom_segment (a b : SerreGraph.segment.V) :
    ∃ q : (segment f g hf hg).Path ⟨a⟩ ⟨b⟩,
      (π₁.vertexHom q).range.map (π₁.equivPushoutI f g hf hg a).toMonoidHom =
        (Monoid.PushoutI.of b).range := by
  obtain rfl | rfl := Bool.eq_or_eq_not b a
  · exact ⟨.nil, (MonoidHom.map_range _ _).trans
      (congrArg _ (π₁.equivPushoutI_comp_vertexHom_nil _))⟩
  · exact ⟨Path.ofDart (SerreGraph.segment.dart a), (MonoidHom.map_range _ _).trans
      (congrArg _ (π₁.equivPushoutI_comp_vertexHom_ofDart _))⟩

/-- A subgroup `H` of `A ∗_C B` is elliptic in the Bass–Serre tree of the segment exactly when it
lies in a conjugate of one of the two factors. -/
theorem bassSerreTree_segment_isEllipticSubgroup_comap_iff {a : SerreGraph.segment.V}
    {H : Subgroup (Monoid.PushoutI (segmentMaps f g hf hg))} :
    (bassSerreTree (segment f g hf hg) a).IsEllipticSubgroup
        (H.comap (π₁.equivPushoutI f g hf hg a).toMonoidHom) ↔
      ∃ (b : SerreGraph.segment.V) (w : Monoid.PushoutI (segmentMaps f g hf hg)),
        H ≤ (Monoid.PushoutI.of b).range.map (MulAut.conj w).toMonoidHom :=
  -- The segment is connected, so every vertex is joined to `a`, and `π₁.equivPushoutI` is
  -- surjective, so every subgroup and every conjugator lies in its range.
  (bassSerreTree_isEllipticSubgroup_comap_iff _ (π₁.equivPushoutI f g hf hg a).injective
    (fun b _ ↦ exists_path_map_range_vertexHom_segment a b)
    fun x _ ↦ (π₁.equivPushoutI f g hf hg a).surjective x).trans
    ⟨fun ⟨b, _, w, _, h⟩ ↦ ⟨b, w, h⟩, fun ⟨b, w, h⟩ ↦
      ⟨b, (exists_path_map_range_vertexHom_segment a b).nonempty, w,
        (π₁.equivPushoutI f g hf hg a).surjective w, h⟩⟩

end segment

/-! ### HNN extensions -/

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] {f g : C →* G}
  {hf : Function.Injective f} {hg : Function.Injective g}

open MonoidHom (ker_eq_ker_of_injective)

/-- The vertex group of the loop maps onto the base group of the HNN extension along the empty
path: the rose has a single vertex. With the base group as reference subgroup,
`exists_map_stabilizer_eq_map_conj` shows that each vertex stabilizer of the Bass–Serre tree is a
conjugate of the base group. -/
theorem exists_path_map_range_vertexHom_loop (v b : (SerreGraph.rose Unit).V) :
    ∃ q : (loop f g hf hg).Path ⟨v⟩ ⟨b⟩,
      (π₁.vertexHom q).range.map (π₁.equivHNNExtension f g hf hg v).toMonoidHom =
        (HNNExtension.of : G →* _).range := by
  obtain rfl : v = b := Subsingleton.elim _ _
  exact ⟨.nil, (MonoidHom.map_range _ _).trans
    (congrArg _ (π₁.equivHNNExtension_comp_vertexHom_nil v))⟩

/-- A subgroup `H` of the HNN extension is elliptic in the Bass–Serre tree of the loop exactly when
it lies in a conjugate of the base group. -/
theorem bassSerreTree_loop_isEllipticSubgroup_comap_iff {v : (SerreGraph.rose Unit).V}
    {H : Subgroup
      (HNNExtension G f.range g.range (f.rangeEquivRange g (ker_eq_ker_of_injective hf hg)))} :
    (bassSerreTree (loop f g hf hg) v).IsEllipticSubgroup
        (H.comap (π₁.equivHNNExtension f g hf hg v).toMonoidHom) ↔
      ∃ w : HNNExtension G f.range g.range (f.rangeEquivRange g (ker_eq_ker_of_injective hf hg)),
        H ≤ (HNNExtension.of : G →* _).range.map (MulAut.conj w).toMonoidHom := by
  have key := bassSerreTree_isEllipticSubgroup_comap_iff (H := H) _
    (π₁.equivHNNExtension f g hf hg v).injective
    (fun b _ ↦ exists_path_map_range_vertexHom_loop v b)
    fun x _ ↦ (π₁.equivHNNExtension f g hf hg v).surjective x
  -- The rose has a single vertex, so the vertex in the criterion carries no information, and
  -- `π₁.equivHNNExtension` is surjective, so every conjugator lies in its range.
  exact key.trans ⟨fun ⟨_, _, w, _, h⟩ => ⟨w, h⟩, fun ⟨w, h⟩ =>
    ⟨v, ⟨.nil⟩, w, (π₁.equivHNNExtension f g hf hg v).surjective w, h⟩⟩

end loop

end GraphOfGroups

end TauCeti
