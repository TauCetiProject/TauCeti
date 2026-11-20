/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree
public import TauCeti.GroupTheory.GraphOfGroups.OneEdge
public import TauCeti.GroupTheory.PushoutI.DehnTwist
public import TauCeti.GroupTheory.HNNExtension.DehnTwist

/-!
# Dehn twists of one-edge splittings and their elliptic subgroups

An amalgamated product `A ∗_C B` and an HNN extension `G ∗_C` are the fundamental groups of the
one-edge graphs of groups `GraphOfGroups.segment` and `GraphOfGroups.loop`, and so act on the
Bass–Serre trees of these graphs of groups through the isomorphisms `π₁.equivPushoutI` and
`π₁.equivHNNExtension`. A subgroup of `A ∗_C B` or of `G ∗_C` is *elliptic in the splitting* when
it fixes a vertex of this tree.

Each vertex stabilizer of the Bass–Serre tree is a conjugate of a vertex group, so in `A ∗_C B` it
is a conjugate of `A` or of `B`, and in `G ∗_C` a conjugate of `G`. A Dehn
twist fixes `A` and conjugates `B` by its parameter `z`, or fixes `G` and multiplies the stable
letter by `z`; on each conjugate `w A w⁻¹`, `w B w⁻¹` or `w G w⁻¹` it therefore agrees with an
inner automorphism. Hence a Dehn twist agrees with an inner automorphism on every elliptic
subgroup, and in particular carries every elliptic subgroup to a conjugate of itself.

## Main results

* `TauCeti.GraphOfGroups.exists_map_stabilizer_eq_segment`,
  `TauCeti.GraphOfGroups.exists_map_stabilizer_eq_loop`: each vertex stabilizer of the
  Bass–Serre tree is a conjugate of a factor of `A ∗_C B`, or of the base group of `G ∗_C`.
* `TauCeti.GraphOfGroups.exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_segment`,
  `TauCeti.GraphOfGroups.exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_loop`: a Dehn twist
  agrees with an inner automorphism on every elliptic subgroup.
* `TauCeti.GraphOfGroups.exists_map_dehnTwist_eq_map_conj_of_isEllipticSubgroup_segment`,
  `TauCeti.GraphOfGroups.exists_map_dehnTwist_eq_map_conj_of_isEllipticSubgroup_loop`: a Dehn
  twist preserves the conjugacy class of every elliptic subgroup.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §9.5,
  p. 97 (Dehn twists of a one-edge splitting).
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5 and the paragraph after it
  (the vertex stabilizers of the Bass–Serre tree).
* Z. Sela, *Diophantine geometry over groups I: Makanin–Razborov diagrams*, Publ. Math. IHÉS 93
  (2001), §5, Definition 5.2 (Dehn twists in the modular group).
-/

public section

universe w x

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

/-! ### Amalgamated products -/

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}
  {hf : Function.Injective f} {hg : Function.Injective g}

/-- Each vertex stabilizer of the Bass–Serre tree of the segment is, in `A ∗_C B`, a conjugate of
one of the two factors. -/
theorem exists_map_stabilizer_eq_segment {a : SerreGraph.segment.V}
    (y : (bassSerreTree (segment f g hf hg) a).V) :
    ∃ (b : SerreGraph.segment.V) (w : Monoid.PushoutI (segmentMaps f g hf hg)),
      (stabilizer (π₁ (segment f g hf hg) a) y).map (π₁.equivPushoutI f g hf hg a).toMonoidHom =
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

/-- **Dehn twists act on elliptic subgroups by conjugation.** A Dehn twist of `A ∗_C B` agrees with
an inner automorphism on every subgroup that is elliptic in the Bass–Serre tree of the splitting. -/
theorem exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_segment {a : SerreGraph.segment.V}
    (z : Subgroup.centralizer (Set.range (segmentMaps f g hf hg true)))
    {H : Subgroup (Monoid.PushoutI (segmentMaps f g hf hg))}
    (hH : (bassSerreTree (segment f g hf hg) a).IsEllipticSubgroup
      (H.comap (π₁.equivPushoutI f g hf hg a).toMonoidHom)) :
    ∃ x : Monoid.PushoutI (segmentMaps f g hf hg),
      Set.EqOn (Monoid.PushoutI.dehnTwist (segmentMaps f g hf hg) z) (MulAut.conj x)
        (H : Set (Monoid.PushoutI (segmentMaps f g hf hg))) := by
  obtain ⟨y, hy⟩ := GTree.isEllipticSubgroup_iff.1 hH
  obtain ⟨b, w, hbw⟩ := exists_map_stabilizer_eq_segment y
  have hHw : H ≤ (Monoid.PushoutI.of b).range.map (MulAut.conj w).toMonoidHom := by
    rwa [← hbw, Subgroup.map_equiv_eq_comap_symm', ← Subgroup.map_le_iff_le_comap,
      ← Subgroup.comap_equiv_eq_map_symm']
  cases b
  · exact ⟨_, (Monoid.PushoutI.eqOn_dehnTwist_conj_of_false _ z w).mono hHw⟩
  · exact ⟨_, (Monoid.PushoutI.eqOn_dehnTwist_conj_of_true _ z w).mono hHw⟩

/-- **Dehn twists preserve the conjugacy classes of elliptic subgroups.** A Dehn twist of
`A ∗_C B` carries every subgroup that is elliptic in the Bass–Serre tree of the splitting to a
conjugate of itself. -/
theorem exists_map_dehnTwist_eq_map_conj_of_isEllipticSubgroup_segment {a : SerreGraph.segment.V}
    (z : Subgroup.centralizer (Set.range (segmentMaps f g hf hg true)))
    {H : Subgroup (Monoid.PushoutI (segmentMaps f g hf hg))}
    (hH : (bassSerreTree (segment f g hf hg) a).IsEllipticSubgroup
      (H.comap (π₁.equivPushoutI f g hf hg a).toMonoidHom)) :
    ∃ x : Monoid.PushoutI (segmentMaps f g hf hg),
      H.map (Monoid.PushoutI.dehnTwist (segmentMaps f g hf hg) z).toMonoidHom =
        H.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_segment z hH
  exact ⟨x, SetLike.coe_injective (by rw [Subgroup.coe_map, Subgroup.coe_map]; exact hx.image_eq)⟩

end segment

/-! ### HNN extensions -/

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] {f g : C →* G}
  {hf : Function.Injective f} {hg : Function.Injective g} {v : (SerreGraph.rose Unit).V}

/-- Each vertex stabilizer of the Bass–Serre tree of the loop is, in the HNN extension, a conjugate
of the base group. -/
theorem exists_map_stabilizer_eq_loop (y : (bassSerreTree (loop f g hf hg) v).V) :
    ∃ w : HNNExtension G f.range g.range (loopEquiv f g hf hg),
      (stabilizer (π₁ (loop f g hf hg) v) y).map (π₁.equivHNNExtension f g hf hg v).toMonoidHom =
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

/-- **Dehn twists act on elliptic subgroups by conjugation.** A Dehn twist of an HNN extension
agrees with an inner automorphism on every subgroup that is elliptic in the Bass–Serre tree of the
splitting. -/
theorem exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_loop
    (z : Subgroup.centralizer (f.range : Set G))
    {H : Subgroup (HNNExtension G f.range g.range (loopEquiv f g hf hg))}
    (hH : (bassSerreTree (loop f g hf hg) v).IsEllipticSubgroup
      (H.comap (π₁.equivHNNExtension f g hf hg v).toMonoidHom)) :
    ∃ x : HNNExtension G f.range g.range (loopEquiv f g hf hg),
      Set.EqOn (HNNExtension.dehnTwist (loopEquiv f g hf hg) z) (MulAut.conj x)
        (H : Set (HNNExtension G f.range g.range (loopEquiv f g hf hg))) := by
  obtain ⟨y, hy⟩ := GTree.isEllipticSubgroup_iff.1 hH
  obtain ⟨w, hw⟩ := exists_map_stabilizer_eq_loop y
  have hHw : H ≤ (HNNExtension.of : G →* _).range.map (MulAut.conj w).toMonoidHom := by
    rwa [← hw, Subgroup.map_equiv_eq_comap_symm', ← Subgroup.map_le_iff_le_comap,
      ← Subgroup.comap_equiv_eq_map_symm']
  exact ⟨_, (HNNExtension.eqOn_dehnTwist_conj_of _ z w).mono hHw⟩

/-- **Dehn twists preserve the conjugacy classes of elliptic subgroups.** A Dehn twist of an HNN
extension carries every subgroup that is elliptic in the Bass–Serre tree of the splitting to a
conjugate of itself. -/
theorem exists_map_dehnTwist_eq_map_conj_of_isEllipticSubgroup_loop
    (z : Subgroup.centralizer (f.range : Set G))
    {H : Subgroup (HNNExtension G f.range g.range (loopEquiv f g hf hg))}
    (hH : (bassSerreTree (loop f g hf hg) v).IsEllipticSubgroup
      (H.comap (π₁.equivHNNExtension f g hf hg v).toMonoidHom)) :
    ∃ x : HNNExtension G f.range g.range (loopEquiv f g hf hg),
      H.map (HNNExtension.dehnTwist (loopEquiv f g hf hg) z).toMonoidHom =
        H.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_loop z hH
  exact ⟨x, SetLike.coe_injective (by rw [Subgroup.coe_map, Subgroup.coe_map]; exact hx.image_eq)⟩

end loop

end GraphOfGroups

end TauCeti
