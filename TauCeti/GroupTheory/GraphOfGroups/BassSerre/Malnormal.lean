/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree
public import TauCeti.GroupTheory.GraphOfGroups.OneEdge
public import TauCeti.GroupTheory.TrivialIntersection
public import TauCeti.Combinatorics.Graph.Serre.GeodesicLine
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Bass–Serre trees with malnormal edge groups

Let `e : b ⟶ c` be a dart of a graph of groups `𝔸` whose edge group `α_e(A_e)` is malnormal in
the vertex group `A_b`: `α_e(A_e) ∩ g α_e(A_e) g⁻¹ = 1` for every `g ∈ A_b ∖ α_e(A_e)`. In the
Bass–Serre tree, the element `p g p⁻¹` with `g ∈ A_b` fixes the vertex `p A_b` and carries the dart
`p α_e(A_e)` leaving it to the dart `p g α_e(A_e)`; the two darts are distinct exactly when
`g ∉ α_e(A_e)`. Their stabilizers are `p α_e(A_e) p⁻¹` and `p g α_e(A_e) g⁻¹ p⁻¹`, which then
intersect trivially. Every dart over `e` leaving `p A_b` is such a translate, since `π₁(𝔸, a)`
acts transitively on the darts over `e`.

For an amalgamated product `A ∗_C B`, the segment graph of groups, every dart of the Bass–Serre
tree leaving a vertex over a vertex `b` of the segment lies over the single dart of the segment
leaving `b`. If `C` is malnormal in the factor at `b`, distinct darts of the tree with a common
source over `b` therefore have stabilizers intersecting trivially. Consecutive vertices of the
tree lie over the two different vertices of the segment, so a geodesic line passes through a
vertex over `b` along two distinct darts: only the identity fixes every vertex of a geodesic line.

## Main results

* `TauCeti.GraphOfGroups.stabilizer_bassSerreDart_inf_stabilizer_smul_eq_bot`: two distinct darts
  `p α_e(A_e)` and `p g α_e(A_e)` have stabilizers intersecting trivially when `α_e(A_e)` is
  malnormal in `A_b`.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreDart_inf_stabilizer_bassSerreDart_eq_bot`: the same
  for any two distinct darts over `e` with a common source.
* `TauCeti.GraphOfGroups.bassSerreTree_segment_stabilizer_inf_stabilizer_eq_bot`: the same for any
  two distinct darts with a common source in the Bass–Serre tree of `A ∗_C B`, over a factor in
  which `C` is malnormal.
* `TauCeti.GraphOfGroups.bassSerreTree_segment_fixingSubgroup_range_eq_bot`: if `C` is malnormal
  in one factor, only the identity of `A ∗_C B` fixes every vertex of a geodesic line of the
  Bass–Serre tree.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1 (the tree of an amalgam and its stabilizers).
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5 and the paragraph after it (vertex and
  edge stabilizers of the Bass–Serre tree).
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {a : Γ.V}

/-- Let `e : b ⟶ c` be a dart whose edge group `α_e(A_e)` is malnormal in `A_b`, and let
`g ∈ A_b ∖ α_e(A_e)`. In the Bass–Serre tree, the dart `p α_e(A_e)` and its translate
`p g α_e(A_e)` by `p g p⁻¹` have stabilizers intersecting trivially. -/
theorem stabilizer_bassSerreDart_inf_stabilizer_smul_eq_bot {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    {e : b ⟶ c} (hT : IsTISubgroup (𝔸.αArrow e).range) {g : 𝔸.vertexGroup b}
    (hg : g ∉ (𝔸.αArrow e).range) :
    stabilizer (π₁ 𝔸 a) (bassSerreDart p e) ⊓
      stabilizer (π₁ 𝔸 a) (π₁.vertexHom p g • bassSerreDart p e) = ⊥ := by
  -- The two stabilizers are the images of `α_e(A_e)` and `g α_e(A_e) g⁻¹` in `π₁(𝔸, a)` under the
  -- injective homomorphism `π₁.vertexHom p`.
  have hconj : (MulAut.conj (π₁.vertexHom p g)).toMonoidHom.comp (π₁.vertexHom p) =
      (π₁.vertexHom p).comp (MulAut.conj g).toMonoidHom := MonoidHom.ext fun _ => by simp
  rw [stabilizer_smul_eq_stabilizer_map_conj, stabilizer_bassSerreDart, Subgroup.map_map, hconj,
    ← Subgroup.map_map, ← Subgroup.map_inf _ _ _ (π₁.vertexHom_injective p)]
  -- The pointwise conjugate `MulAut.conj g • H` is by definition the image of `H` under
  -- `MulAut.conj g` (`Subgroup.pointwise_smul_def`).
  exact (congrArg _ (isTISubgroup_iff_inf_conj_smul_eq_bot.1 hT g hg)).trans (Subgroup.map_bot _)

/-- Let `e : b ⟶ c` be a dart whose edge group `α_e(A_e)` is malnormal in `A_b`. In the Bass–Serre
tree, two distinct darts `p α_e(A_e)` and `q α_e(A_e)` over `e` leaving the same vertex
`p A_b = q A_b` have stabilizers intersecting trivially. -/
theorem stabilizer_bassSerreDart_inf_stabilizer_bassSerreDart_eq_bot {b c : Γ.V}
    {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} {e : b ⟶ c} (hT : IsTISubgroup (𝔸.αArrow e).range)
    (hpq : bassSerreVertex q = bassSerreVertex p) (hne : bassSerreDart q e ≠ bassSerreDart p e) :
    stabilizer (π₁ 𝔸 a) (bassSerreDart p e) ⊓ stabilizer (π₁ 𝔸 a) (bassSerreDart q e) = ⊥ := by
  -- The dart `q α_e(A_e)` is the translate of `p α_e(A_e)` by an element fixing `p A_b`.
  obtain ⟨γ, hγ⟩ := exists_smul_bassSerreDart_eq p q e
  have hγv : γ ∈ stabilizer _ (bassSerreVertex p) := by
    simpa [hpq] using congrArg (bassSerreTree 𝔸 a).src hγ
  rw [stabilizer_bassSerreVertex] at hγv
  obtain ⟨g, rfl⟩ := hγv
  rw [← hγ] at hne ⊢
  exact stabilizer_bassSerreDart_inf_stabilizer_smul_eq_bot p hT
    fun h => hne ((vertexHom_smul_bassSerreDart_eq_self_iff p e g).2 h)

section segment

/-- A vertex `b` of the segment has a single dart leaving it, so every dart of the Bass–Serre tree
of a segment of groups leaving `p A_b` over a dart `e : b ⟶ c` lies over `segmentArrow b`. -/
private theorem bassSerreDart_eq_segmentArrow {𝔸 : GraphOfGroups.{0, 0, w, x} SerreGraph.segment}
    {a b c : SerreGraph.segment.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    bassSerreDart p e = bassSerreDart p (SerreGraph.segmentArrow b) := by
  have he : e.val = b := (SerreGraph.segment_src _).symm.trans e.property.1
  obtain rfl : c = SerreGraph.segment.tgt b := e.property.2.symm.trans (congrArg _ he)
  obtain rfl : e = SerreGraph.segmentArrow b :=
    Subtype.ext (he.trans (SerreGraph.segmentArrow_val b).symm)
  rfl

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}
  {hf : Function.Injective f} {hg : Function.Injective g} {a : SerreGraph.segment.V}

/-- In the Bass–Serre tree of `A ∗_C B`, let `d` and `d'` be distinct darts with a common source
over a vertex `b` of the segment, and suppose that `C` is malnormal in the vertex group at `b`.
Then the stabilizers of `d` and `d'` intersect trivially. -/
theorem bassSerreTree_segment_stabilizer_inf_stabilizer_eq_bot {b : SerreGraph.segment.V}
    (hT : IsTISubgroup (segmentMaps f g hf hg b).range)
    {d d' : (bassSerreTree (segment f g hf hg) a).E}
    (hb : (bassSerreProjection _ a).mapV ((bassSerreTree _ a).src d) = b)
    (hsrc : (bassSerreTree _ a).src d' = (bassSerreTree _ a).src d) (hne : d' ≠ d) :
    stabilizer (π₁ (segment f g hf hg) a) d ⊓ stabilizer (π₁ (segment f g hf hg) a) d' = ⊥ := by
  obtain ⟨b₁, c₁, p, e, rfl⟩ := bassSerreDart_surjective d
  obtain ⟨b₂, c₂, q, e', rfl⟩ := bassSerreDart_surjective d'
  rw [src_bassSerreDart, bassSerreProjection_mapV_bassSerreVertex] at hb
  subst hb
  rw [src_bassSerreDart, src_bassSerreDart] at hsrc
  obtain rfl : b₁ = b₂ := by simpa using congrArg (bassSerreProjection _ a).mapV hsrc.symm
  rw [bassSerreDart_eq_segmentArrow p, bassSerreDart_eq_segmentArrow q] at hne ⊢
  exact stabilizer_bassSerreDart_inf_stabilizer_bassSerreDart_eq_bot
    (by rwa [αArrow_segmentArrow]) hsrc hne

/-- Adjacent vertices of the Bass–Serre tree of `A ∗_C B` lie over the two different vertices of
the segment, so a geodesic line passes over every vertex of the segment. -/
private theorem exists_bassSerreProjection_mapV_eq {c : ℤ → (bassSerreTree (segment f g hf hg) a).V}
    (hc : ∀ m n, (bassSerreTree (segment f g hf hg) a).dist (c m) (c n) = (m - n).natAbs)
    (b : SerreGraph.segment.V) : ∃ n, (bassSerreProjection _ a).mapV (c n) = b := by
  obtain ⟨d, hs, ht⟩ := SerreGraph.exists_src_eq_and_tgt_eq_of_dist_eq_one (hc 0 1)
  set π := bassSerreProjection (segment f g hf hg) a
  have h₀ : SerreGraph.segment.src (π.mapE d) = π.mapV (c 0) := hs ▸ π.map_src d
  have h₁ : SerreGraph.segment.tgt (π.mapE d) = π.mapV (c 1) := ht ▸ π.map_tgt _ d
  by_cases h : π.mapV (c 0) = b
  · exact ⟨0, h⟩
  · -- The source of the dart `π d` is the vertex `π (c 0) ≠ b`, so its target is `b`.
    exact ⟨1, h₁ ▸ SerreGraph.segment_tgt_eq_of_ne (h₀.trans_ne h)⟩

/-- **Geodesic lines have trivial pointwise stabilizers** in the Bass–Serre tree of `A ∗_C B`
when `C` is malnormal in one of the factors: only the identity fixes every vertex of a geodesic
line. -/
theorem bassSerreTree_segment_fixingSubgroup_range_eq_bot {b : SerreGraph.segment.V}
    (hT : IsTISubgroup (segmentMaps f g hf hg b).range)
    {c : ℤ → (bassSerreTree (segment f g hf hg) a).V}
    (hc : ∀ m n, (bassSerreTree (segment f g hf hg) a).dist (c m) (c n) = (m - n).natAbs) :
    fixingSubgroup (π₁ (segment f g hf hg) a) (Set.range c) = ⊥ := by
  have hdart (m n : ℤ) (h : (m - n).natAbs = 1) : ∃ d : (bassSerreTree (segment f g hf hg) a).E,
      (bassSerreTree _ a).src d = c m ∧ (bassSerreTree _ a).tgt d = c n :=
    SerreGraph.exists_src_eq_and_tgt_eq_of_dist_eq_one (by rw [hc, h])
  -- The line passes through a vertex `c n` over `b`, with darts to `c (n + 1)` and `c (n - 1)`.
  obtain ⟨n, hn⟩ := exists_bassSerreProjection_mapV_eq hc b
  obtain ⟨d, hds, hdt⟩ := hdart n (n + 1) (by omega)
  obtain ⟨d', hds', hdt'⟩ := hdart n (n - 1) (by omega)
  have hne : d' ≠ d := fun h => by
    have := SerreGraph.injective_of_dist_eq_natAbs hc (hdt'.symm.trans (h ▸ hdt))
    omega
  rw [eq_bot_iff, ← bassSerreTree_segment_stabilizer_inf_stabilizer_eq_bot hT (by rwa [hds])
    (hds'.trans hds.symm) hne]
  intro k hk
  rw [mem_fixingSubgroup_iff] at hk
  -- An element fixing both endpoints of a dart of a tree fixes the dart.
  have hfix (e : (bassSerreTree (segment f g hf hg) a).E) (hs : (bassSerreTree _ a).src e = c n)
      (m : ℤ) (ht : (bassSerreTree _ a).tgt e = c m) : k • e = e :=
    (SerreGraph.IsTree.isAcyclic _ (bassSerreTree _ a).isTree).eq_of_src_eq_of_tgt_eq
      (by rw [GTree.src_smul, hs, hk _ (Set.mem_range_self n)])
      (by rw [GTree.tgt_smul, ht, hk _ (Set.mem_range_self m)])
  exact Subgroup.mem_inf.2 ⟨hfix d hds _ hdt, hfix d' hds' _ hdt'⟩

end segment

end GraphOfGroups

end TauCeti
