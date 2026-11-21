/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree
public import TauCeti.GroupTheory.GraphOfGroups.OneEdge

/-!
# Bass–Serre trees of one-edge splittings

An amalgamated product `A ∗_C B` and an HNN extension `G ∗_C` are the fundamental groups of the
one-edge graphs of groups `GraphOfGroups.segment` and `GraphOfGroups.loop`. Through the
isomorphisms `π₁.equivPushoutI` and `π₁.equivHNNExtension` they act on the Bass–Serre trees of
these graphs of groups. The stabilizer of the vertex `p A_b` of the Bass–Serre tree is the
conjugate `p A_b p⁻¹` of the vertex group. So in `A ∗_C B` each vertex stabilizer is a conjugate
of `A` or of `B`, and in the HNN extension it is a conjugate of the base group `G`.

## Main results

* `TauCeti.GraphOfGroups.exists_map_stabilizer_eq_segment`,
  `TauCeti.GraphOfGroups.exists_map_stabilizer_eq_loop`: each vertex stabilizer of the
  Bass–Serre tree is a conjugate of a factor of `A ∗_C B`, or of the base group of the HNN
  extension.

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

/-- Each vertex stabilizer of the Bass–Serre tree of the segment is, in `A ∗_C B`, a conjugate of
one of the two factors. -/
theorem exists_map_stabilizer_eq_segment {a : SerreGraph.segment.V}
    (y : (bassSerreTree (segment f g hf hg) a).V) :
    ∃ (b : SerreGraph.segment.V) (w : Monoid.PushoutI (segmentMaps f g hf hg)),
      (MulAction.stabilizer (π₁ (segment f g hf hg) a) y).map
          (π₁.equivPushoutI f g hf hg a).toMonoidHom =
        (Monoid.PushoutI.of b).range.map (MulAut.conj w).toMonoidHom := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
  -- A path `q` from `a` to `b` along which `A_b` maps identically onto its factor: the empty path
  -- if `b = a`, the dart from `a` to `b` otherwise.
  obtain ⟨q, hq⟩ : ∃ q : (segment f g hf hg).Path ⟨a⟩ ⟨b⟩, ∀ x,
      π₁.equivPushoutI f g hf hg a (π₁.vertexHom q x) = Monoid.PushoutI.of b x := by
    obtain rfl | rfl := Bool.eq_or_eq_not b a
    · exact ⟨.nil, fun x => by simp⟩
    · exact ⟨Path.ofDart (SerreGraph.segment.dart a), π₁.equivPushoutI_vertexHom_ofDart _⟩
  refine ⟨b, π₁.equivPushoutI f g hf hg a (π₁.mk (p.comp q.reverse)), ?_⟩
  rw [stabilizer_bassSerreVertex, π₁.vertexHom_eq_conj_comp q p, MonoidHom.map_range,
    MonoidHom.map_range]
  congr 1
  ext x
  simp [hq, MulAut.conj_apply]

end segment

/-! ### HNN extensions -/

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] {f g : C →* G}
  {hf : Function.Injective f} {hg : Function.Injective g}

/-- Each vertex stabilizer of the Bass–Serre tree of the loop is, in the HNN extension, a conjugate
of the base group. -/
theorem exists_map_stabilizer_eq_loop {v : (SerreGraph.rose Unit).V}
    (y : (bassSerreTree (loop f g hf hg) v).V) :
    ∃ w : HNNExtension G f.range g.range (loopEquiv f g hf hg),
      (MulAction.stabilizer (π₁ (loop f g hf hg) v) y).map
          (π₁.equivHNNExtension f g hf hg v).toMonoidHom =
        (HNNExtension.of : G →* HNNExtension G f.range g.range (loopEquiv f g hf hg)).range.map
          (MulAut.conj w).toMonoidHom := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
  -- The rose has a single vertex.
  obtain rfl : b = v := Subsingleton.elim _ _
  let P := HNNExtension G f.range g.range (loopEquiv f g hf hg)
  let e : π₁ (loop f g hf hg) b →* P := (π₁.equivHNNExtension f g hf hg b).toMonoidHom
  let m := π₁.mk (p.comp Quiver.Path.nil.reverse)
  refine ⟨e m, ?_⟩
  -- `π₁.vertexHom_eq_conj_comp` states the conjugation as a coercion to a monoid homomorphism.
  have hconj : e.comp ((MulAut.conj m : π₁ (loop f g hf hg) b →* π₁ (loop f g hf hg) b).comp
      (π₁.vertexHom .nil)) =
      (MulAut.conj (e m)).toMonoidHom.comp (e.comp (π₁.vertexHom .nil)) := by
    ext x
    simp [MulAut.conj_apply]
  have hnil : e.comp (π₁.vertexHom .nil) = (HNNExtension.of : G →* P) :=
    MonoidHom.ext fun x => (congrArg _ (π₁.vertexHom_nil_apply x)).trans
      (π₁.equivHNNExtension_mk_ofVertex (hf := hf) (hg := hg) b x)
  rw [stabilizer_bassSerreVertex, π₁.vertexHom_eq_conj_comp .nil p, MonoidHom.map_range,
    MonoidHom.map_range, hconj, hnil]
  -- The two sides differ only in the implicit domain of `comp`: `G` and the vertex group `G`.
  rfl

end loop

end GraphOfGroups

end TauCeti
