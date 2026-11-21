/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.OneEdge
public import TauCeti.GroupTheory.PushoutI.DehnTwist
public import TauCeti.GroupTheory.HNNExtension.DehnTwist
import TauCeti.Algebra.Group.Subgroup.EqOn

/-!
# Dehn twists of one-edge splittings and their elliptic subgroups

An amalgamated product `A ∗_C B` and an HNN extension `G ∗_C` are the fundamental groups of the
one-edge graphs of groups `GraphOfGroups.segment` and `GraphOfGroups.loop`, and so act on the
Bass–Serre trees of these graphs of groups through the isomorphisms `π₁.equivPushoutI` and
`π₁.equivHNNExtension`. A subgroup of `A ∗_C B` or of `G ∗_C` is *elliptic in the splitting* when
it fixes a vertex of this tree.

Each vertex stabilizer of the Bass–Serre tree is a conjugate of a vertex group, so a subgroup of
`A ∗_C B` is elliptic exactly when it lies in a conjugate of `A` or of `B`, and a subgroup of
`G ∗_C` exactly when it lies in a conjugate of `G`
(`bassSerreTree_segment_isEllipticSubgroup_comap_iff`,
`bassSerreTree_loop_isEllipticSubgroup_comap_iff`). A Dehn twist fixes `A` and conjugates `B` by
its parameter `z`, or fixes `G` and multiplies the stable letter by `z`; on each conjugate
`w A w⁻¹`, `w B w⁻¹` or `w G w⁻¹` it therefore agrees with an inner automorphism of the whole
group, whose conjugating element depends on `w`. Hence for each elliptic subgroup `H` there is an
inner automorphism, which may depend on `H`, that agrees with the Dehn twist on `H`; in particular
the twist carries `H` to a conjugate of itself.

## Main results

* `TauCeti.GraphOfGroups.exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_segment`,
  `TauCeti.GraphOfGroups.exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_loop`: on each elliptic
  subgroup `H`, a Dehn twist agrees with an inner automorphism, which may depend on `H`.
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

/-! ### Amalgamated products -/

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}
  {hf : Function.Injective f} {hg : Function.Injective g}

/-- **Dehn twists act on elliptic subgroups by conjugation.** For each subgroup `H` of `A ∗_C B`
that is elliptic in the Bass–Serre tree of the splitting, a Dehn twist agrees on `H` with an inner
automorphism, which may depend on `H`. -/
theorem exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_segment {a : SerreGraph.segment.V}
    (z : Subgroup.centralizer (Set.range (segmentMaps f g hf hg true)))
    {H : Subgroup (Monoid.PushoutI (segmentMaps f g hf hg))}
    (hH : (bassSerreTree (segment f g hf hg) a).IsEllipticSubgroup
      (H.comap (π₁.equivPushoutI f g hf hg a).toMonoidHom)) :
    ∃ x : Monoid.PushoutI (segmentMaps f g hf hg),
      Set.EqOn (Monoid.PushoutI.dehnTwist (segmentMaps f g hf hg) z) (MulAut.conj x)
        (H : Set (Monoid.PushoutI (segmentMaps f g hf hg))) := by
  obtain ⟨b, w, hHw⟩ := bassSerreTree_segment_isEllipticSubgroup_comap_iff.1 hH
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
  -- `Monoid.PushoutI.dehnTwist` is indexed by `Bool`, only definitionally the vertex type of the
  -- segment, so instance search fails on the group read off `hx`; the group and twist are named.
  exact ⟨x, hx.subgroup_map_eq (G := Monoid.PushoutI (segmentMaps f g hf hg))
    (N := Monoid.PushoutI (segmentMaps f g hf hg))
    (f := (Monoid.PushoutI.dehnTwist (segmentMaps f g hf hg) z).toMonoidHom)⟩

end segment

/-! ### HNN extensions -/

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] {f g : C →* G}
  {hf : Function.Injective f} {hg : Function.Injective g} {v : (SerreGraph.rose Unit).V}

/-- **Dehn twists act on elliptic subgroups by conjugation.** For each subgroup `H` of an HNN
extension that is elliptic in the Bass–Serre tree of the splitting, a Dehn twist agrees on `H` with
an inner automorphism, which may depend on `H`. -/
theorem exists_eqOn_dehnTwist_conj_of_isEllipticSubgroup_loop
    (z : Subgroup.centralizer (f.range : Set G))
    {H : Subgroup (HNNExtension G f.range g.range (loopEquiv f g hf hg))}
    (hH : (bassSerreTree (loop f g hf hg) v).IsEllipticSubgroup
      (H.comap (π₁.equivHNNExtension f g hf hg v).toMonoidHom)) :
    ∃ x : HNNExtension G f.range g.range (loopEquiv f g hf hg),
      Set.EqOn (HNNExtension.dehnTwist (loopEquiv f g hf hg) z) (MulAut.conj x)
        (H : Set (HNNExtension G f.range g.range (loopEquiv f g hf hg))) := by
  obtain ⟨w, hHw⟩ := bassSerreTree_loop_isEllipticSubgroup_comap_iff.1 hH
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
  exact ⟨x, hx.subgroup_map_eq⟩

end loop

end GraphOfGroups

end TauCeti
