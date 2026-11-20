/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.NormalForm
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic

/-!
# Britton's lemma for graphs of groups

Let `𝔸` be a graph of groups over a connected Serre graph `Γ` with a spanning tree `T`. The
normal form theorem for `𝔸`-paths says that a reduced alternating path of positive length is not
homotopic to a shorter path. Read in the presented group `π₁(𝔸, T)`, this is Britton's lemma for
graphs of groups: the element spelled by a reduced closed alternating path at a vertex `a` lies in
the image of the vertex group `A_a` exactly when the path has length zero.

For the two graphs of groups with one geometric edge this recovers the classical normal forms.

* For the segment `A ← C → B`, whose fundamental group is the amalgamated product `A ∗_C B`
  (Mathlib's `Monoid.PushoutI`), a word in the letters of `A` and `B` spells a closed
  alternating path, `segmentPath`. The path is reduced when the letters alternate between the two
  factors and its interior letters avoid `C`, and it spells the product of the word. Together
  with Britton's lemma this gives Mathlib's normal form theorem for amalgams,
  `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`, for the segment.
* For the loop with monomorphisms `f g : C →* G`, whose fundamental group is the HNN extension
  `HNNExtension G (range f) (range g) φ`, a word `h t^{u₁} g₁ ⋯ t^{u_k} g_k` spells the
  alternating path `h, t^{u₁}, g₁, …` of the loop, `loopPath`. A pinch `t g t⁻¹`, `g ∈ range f`,
  or `t⁻¹ g t`, `g ∈ range g`, is exactly a backtracking of the path, so the reduced words of
  Mathlib's `HNNExtension.NormalWord.ReducedWord` are the reduced paths. Together with the
  graph-of-groups form of Britton's lemma for the loop this gives Britton's lemma for HNN
  extensions, `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`.

Both recovered statements are checked as examples, together with the examples: in the
Baumslag–Solitar group `⟨a, t ∣ t a² t⁻¹ = a⟩` the path `t a t⁻¹` is reduced, so `t a t⁻¹ ∉ ⟨a⟩`,
while `t a² t⁻¹` is not reduced and equals `a`; for a segment whose edge maps are isomorphisms
there is no reduced closed path of positive length and the fundamental group is the vertex
group; and crossing the edge of a segment once is a reduced path of length one.

## Main definitions

* `TauCeti.GraphOfGroups.segmentPath`: the closed alternating path of the segment spelled by a
  word in the letters of the two vertex groups.
* `TauCeti.GraphOfGroups.loopPath`: the closed alternating path of the loop spelled by a word
  `h t^{u₁} g₁ ⋯ t^{u_k} g_k`.

## Main results

* `TauCeti.GraphOfGroups.AlternatingPath.IsReduced.toπ₁Tree_toPath_mem_range_iff`: Britton's lemma
  for graphs of groups, in `π₁(𝔸, S)` for every set `S` of darts of a spanning tree.
* `TauCeti.GraphOfGroups.AlternatingPath.IsReduced.equivPushoutI_toπ₁Tree_toPath_mem_range_iff`:
  the normal form theorem for the amalgamated product of the segment.
* `TauCeti.GraphOfGroups.AlternatingPath.IsReduced.equivHNNExtension_toπ₁Tree_toPath_mem_range_iff`:
  Britton's lemma for the HNN extension of the loop.
* `TauCeti.GraphOfGroups.isReduced_segmentPath`, `TauCeti.GraphOfGroups.isReduced_loopPath_iff`:
  reduced words spell reduced paths.
* `TauCeti.GraphOfGroups.AlternatingPath.IsReduced.length_eq_zero_of_surjective_segmentMaps`,
  `TauCeti.GraphOfGroups.π₁.vertexHom_bijective_segment`: when the edge group of a segment maps
  onto the vertex group at the other end, every reduced closed path has length zero, and the
  vertex group is the fundamental group.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.4.
* J.-P. Serre, *Trees*, Chapter I, §1 and §5.2, Theorem 11.
* J. L. Britton, *The word problem*, Ann. of Math. 77 (1963).
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

/-! ### Britton's lemma in `π₁(𝔸, T)` -/

section britton

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ}

/- Killing the darts of `S' ⊇ S` maps the element of `π₁(𝔸, S)` read off a path to the element
of `π₁(𝔸, S')` read off the same path. -/
private theorem lift_toπ₁Tree_of_subset {S S' : Set Γ.E} (hS : S ⊆ S') {x y : 𝔸.LetterVertex}
    (q : 𝔸.Path x y) :
    π₁Tree.lift (π₁Tree.of S') (π₁Tree.edge S') (fun _ he => π₁Tree.edge_eq_one (hS he))
      π₁Tree.edge_rev π₁Tree.edge_mul_of_ω_mul_edge_inv (q.toπ₁Tree S) = q.toπ₁Tree S' := by
  induction q with
  | nil => simp
  | cons q l ih => cases l <;> simp [ih]

/-- **Britton's lemma for graphs of groups.** Let `T` be a spanning tree of `Γ` (so `Γ` is
connected) and `S` a set of darts of `T`. A reduced closed alternating path at `a` spells an
element of `π₁(𝔸, S)` in the image of the vertex group `A_a` exactly when it has length zero; in
particular a reduced closed path of positive length spells a nontrivial element. -/
theorem AlternatingPath.IsReduced.toπ₁Tree_toPath_mem_range_iff {a : Γ.V}
    {p : 𝔸.AlternatingPath a a} (hp : p.IsReduced) (T : Γ.SpanningTree) {S : Set Γ.E}
    (hS : S ⊆ T.darts) : p.toPath.toπ₁Tree S ∈ (π₁Tree.of S a).range ↔ p.length = 0 := by
  refine ⟨fun ⟨g, hg⟩ => ?_, fun h => ?_⟩
  · -- Through `π₁(𝔸, a) ≃* π₁(𝔸, T)`, the path is homotopic to the length-zero path `g`.
    have hmk : π₁.mk p.toPath = π₁.mk (Path.ofVertex g) := by
      apply (π₁Equiv 𝔸 a T).injective
      rw [π₁Equiv_mk, ← lift_toπ₁Tree_of_subset hS p.toPath, ← hg, π₁Tree.lift_of,
        ← π₁.vertexHom_nil_apply]
      simp
    rw [hp.toPath_homotopic_ofVertex_iff.1 (π₁.mk_eq_mk_iff.1 hmk), AlternatingPath.length_single]
  · rw [AlternatingPath.length_eq_zero_iff.1 h]
    exact ⟨p.last, by simp⟩

end britton

/-! ### The segment: amalgamated products -/

/- Every set of darts of the segment lies in each of its spanning trees: the tree path between
the two vertices crosses the edge. -/
private theorem subset_darts_segment (T : SerreGraph.segment.SpanningTree)
    (S : Set SerreGraph.segment.E) : S ⊆ T.darts := by
  obtain ⟨e, he⟩ : ∃ e, e ∈ SerreGraph.Path.darts _ (T.path false true) := by
    generalize T.path false true = q
    cases q with
    | cons q e => exact ⟨e.1, (SerreGraph.Path.darts_cons _ q e).symm ▸
        List.mem_append_right _ (List.mem_singleton_self _)⟩
  intro b _
  rcases Bool.eq_or_eq_not b e with rfl | rfl
  · exact T.mem_of_mem_darts_path he
  · exact T.rev_mem _ (T.mem_of_mem_darts_path he)

/-- The dart of the segment leaving the vertex `b`: the dart with the same Boolean label. -/
private def segmentDart (b : SerreGraph.segment.V) : SerreGraph.segment.E := b

/-- The dart leaving `b`, as an arrow from `b` to the other vertex. Its source is `b` itself, not
`SerreGraph.segment.src (segmentDart b)` as for `SerreGraph.dart`, so that it extends alternating
paths ending at `b` without a cast. -/
private def segmentArrow (b : SerreGraph.segment.V) : b ⟶ SerreGraph.segment.tgt (segmentDart b) :=
  ⟨segmentDart b, rfl, rfl⟩

/- A vertex of the segment other than `b` is the target of the dart leaving `b`. -/
private theorem segment_tgt_eq_of_ne {b v : SerreGraph.segment.V} (h : b ≠ v) :
    SerreGraph.segment.tgt (segmentDart b) = v := by
  cases b <;> cases v <;> first | rfl | exact absurd rfl h

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}
  {hf : Function.Injective f} {hg : Function.Injective g}

/-- **The normal form theorem for amalgamated products.** A reduced closed alternating path at a
vertex `v` of the segment, that is a word `a₀ b₁ a₁ ⋯ b_k a_k` alternating between the vertex
group `A_v` and the other vertex group whose interior letters avoid the edge group, spells an
element of `A ∗_C B` in `A_v` exactly when it has length zero. -/
theorem AlternatingPath.IsReduced.equivPushoutI_toπ₁Tree_toPath_mem_range_iff
    {v : SerreGraph.segment.V} {p : (segment f g hf hg).AlternatingPath v v} (hp : p.IsReduced)
    {T : Set SerreGraph.segment.E} (hT : T.Nonempty) :
    π₁Tree.equivPushoutI f g hf hg hT (p.toPath.toπ₁Tree T) ∈
      (Monoid.PushoutI.of (φ := segmentMaps f g hf hg) v).range ↔ p.length = 0 := by
  obtain ⟨T'⟩ := SerreGraph.segment.exists_spanningTree SerreGraph.segment_isTree.connected
  rw [← hp.toπ₁Tree_toPath_mem_range_iff T' (subset_darts_segment T' T)]
  have : Monoid.PushoutI.of (φ := segmentMaps f g hf hg) v =
      (π₁Tree.equivPushoutI f g hf hg hT).toMonoidHom.comp (π₁Tree.of T v) :=
    MonoidHom.ext fun a => (π₁Tree.equivPushoutI_of hT v a).symm
  rw [this, MonoidHom.range_comp]
  exact Subgroup.mem_map_iff_mem (π₁Tree.equivPushoutI f g hf hg hT).injective

open scoped Classical in
/-- Reading a list of letters of the vertex groups along an alternating path `p` of the segment
from `v` to `b`: a letter of the vertex group at the current end is multiplied onto the last
element, a letter of the other vertex group is appended after crossing the edge, and at the end
the path crosses back to `v` with the element `1` if it ended at the other vertex. -/
private noncomputable def segmentPathAux {v : SerreGraph.segment.V} :
    ∀ {b : SerreGraph.segment.V}, (segment f g hf hg).AlternatingPath v b →
      List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i) →
      (segment f g hf hg).AlternatingPath v v
  | b, p, [] =>
    if h : b = v then h ▸ p else segment_tgt_eq_of_ne h ▸ p.cons (segmentArrow b) 1
  | b, p, ⟨i, x⟩ :: l =>
    if h : i = b then segmentPathAux (p.setLast (p.last * h ▸ x)) l
    else segmentPathAux (p.cons (segmentArrow b) ((segment_tgt_eq_of_ne (Ne.symm h)).symm ▸ x)) l

variable (f g hf hg) in
/-- The closed alternating path of the segment at the vertex `v` spelled by a word in the letters
of the two vertex groups, as in Mathlib's `Monoid.CoprodI.Word`: starting from `1`, a letter of
the vertex group at the current vertex is multiplied onto the last element, a letter of the other
vertex group is appended after crossing the edge, and the path crosses back to `v` with `1` at
the end if needed. Its element of `A ∗_C B` is the product of the word
(`equivPushoutI_toπ₁Tree_toPath_segmentPath`). -/
noncomputable def segmentPath (v : SerreGraph.segment.V)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    (segment f g hf hg).AlternatingPath v v :=
  segmentPathAux (.single 1) l

private theorem toπ₁Tree_toPath_segmentPathAux {T : Set SerreGraph.segment.E} (hT : T.Nonempty)
    {v : SerreGraph.segment.V} : ∀ {b : SerreGraph.segment.V}
      (p : (segment f g hf hg).AlternatingPath v b)
      (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)),
      (segmentPathAux p l).toPath.toπ₁Tree T =
        p.toPath.toπ₁Tree T * (l.map fun x => π₁Tree.of T x.1 x.2).prod
  | b, p, [] => by
    rw [segmentPathAux]
    split_ifs with h
    · subst h
      simp
    · obtain rfl := segment_tgt_eq_of_ne h
      simp [hT]
  | b, p, ⟨i, x⟩ :: l => by
    rw [segmentPathAux]
    split_ifs with h
    · subst h
      rw [toπ₁Tree_toPath_segmentPathAux hT,
        Path.Homotopic.toπ₁Tree_eq T (p.toPath_setLast_mul_homotopic x)]
      simp [mul_assoc]
    · obtain rfl := segment_tgt_eq_of_ne (Ne.symm h)
      rw [toπ₁Tree_toPath_segmentPathAux hT]
      simp [hT, mul_assoc]

/-- A word spells the element of `A ∗_C B` given by its product. -/
@[simp] theorem equivPushoutI_toπ₁Tree_toPath_segmentPath {T : Set SerreGraph.segment.E}
    (hT : T.Nonempty) (v : SerreGraph.segment.V)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    π₁Tree.equivPushoutI f g hf hg hT ((segmentPath f g hf hg v l).toPath.toπ₁Tree T) =
      (l.map fun x => Monoid.PushoutI.of (φ := segmentMaps f g hf hg) x.1 x.2).prod := by
  simp [segmentPath, toπ₁Tree_toPath_segmentPathAux hT, map_list_prod, Function.comp_def]

/- The boundary map `α_e` of the dart `e` of the segment is the edge map into the vertex group at
the source of `e`. -/
private theorem α_segment_apply (e : SerreGraph.segment.E) (c : C) :
    (segment f g hf hg).α e c = segmentMaps f g hf hg (SerreGraph.segment.src e) c := by
  cases e
  · exact (DFunLike.congr_fun (segment_α_false f g hf hg) c).trans
      (DFunLike.congr_fun (segmentMaps_false f g hf hg).symm c)
  · exact (DFunLike.congr_fun (segment_α_true f g hf hg) c).trans
      (DFunLike.congr_fun (segmentMaps_true f g hf hg).symm c)

private theorem αArrow_segmentArrow_apply (b : SerreGraph.segment.V) (c : C) :
    (segment f g hf hg).αArrow (segmentArrow b) c = segmentMaps f g hf hg b c :=
  (DFunLike.congr_fun ((segment f g hf hg).αArrow_mk (segmentDart b)) c).trans
    (α_segment_apply (segmentDart b) c)

private theorem not_cancels_segmentArrow {v b : SerreGraph.segment.V}
    {p : (segment f g hf hg).AlternatingPath v b}
    (h : p.length = 0 ∨ p.last ∉ (segmentMaps f g hf hg b).range) :
    ¬ p.Cancels (segmentArrow b) := by
  cases p with
  | single => exact AlternatingPath.not_cancels_single _ _
  | cons q e y =>
    rw [AlternatingPath.cancels_cons_iff]
    rintro ⟨-, c, hc⟩
    simp only [AlternatingPath.length_cons, Nat.add_one_ne_zero, false_or,
      AlternatingPath.last_cons] at h
    exact h ⟨c, (αArrow_segmentArrow_apply _ c).symm.trans hc⟩

/- The invariant for reading a list of letters: if the path read so far is reduced and does not
end in the edge group before a further crossing, if a letter is merged into the last element only
when the path has length zero, and if the letters alternate and avoid the edge group wherever they
are followed by a crossing, then the path read is reduced. -/
private theorem isReduced_segmentPathAux {v : SerreGraph.segment.V} :
    ∀ {b : SerreGraph.segment.V} (p : (segment f g hf hg).AlternatingPath v b)
      (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)),
      p.IsReduced → ((l ≠ [] ∨ b ≠ v) → p.length = 0 ∨ p.last ∉ (segmentMaps f g hf hg b).range) →
      (∀ x ∈ l.head?, x.1 = b → p.length = 0) → l.IsChain (fun x y => x.1 ≠ y.1) →
      (∀ x ∈ l, x.1 ≠ v ∨ x ∈ l.dropLast → x.2 ∉ (segmentMaps f g hf hg x.1).range) →
      (segmentPathAux p l).IsReduced
  | b, p, [], hp, hlast, _, _, _ => by
    rw [segmentPathAux]
    split_ifs with h
    · subst h
      exact hp
    · obtain rfl := segment_tgt_eq_of_ne h
      exact (AlternatingPath.isReduced_cons_iff _ _ _).2
        ⟨hp, not_cancels_segmentArrow (hlast (.inr h))⟩
  | b, p, ⟨i, x⟩ :: l, hp, hlast, hhead, hc, hl => by
    rw [segmentPathAux]
    rw [List.isChain_cons] at hc
    -- A letter followed by another letter of `l` is followed by one in `⟨i, x⟩ :: l` too.
    have hdrop : ∀ y ∈ l.dropLast, y ∈ (⟨i, x⟩ :: l).dropLast := fun y hy => by
      rw [List.dropLast_cons_of_ne_nil (List.ne_nil_of_mem (List.mem_of_mem_dropLast hy))]
      exact List.mem_cons_of_mem _ hy
    split_ifs with h
    · subst h
      have h0 : p.length = 0 := hhead _ rfl rfl
      exact isReduced_segmentPathAux _ l (by simpa using hp) (fun _ => .inl (by simpa using h0))
        (fun y hy hy' => absurd hy' (hc.1 y hy).symm) hc.2
        (fun y hy hy' => hl y (List.mem_cons_of_mem _ hy) (hy'.imp_right (hdrop y)))
    · obtain rfl := segment_tgt_eq_of_ne (Ne.symm h)
      refine isReduced_segmentPathAux _ l ((AlternatingPath.isReduced_cons_iff _ _ _).2
        ⟨hp, not_cancels_segmentArrow (hlast (.inl (List.cons_ne_nil _ _)))⟩)
        (fun hl' => .inr ?_) (fun y hy hy' => absurd hy' (hc.1 y hy).symm) hc.2
        (fun y hy hy' => hl y (List.mem_cons_of_mem _ hy) (hy'.imp_right (hdrop y)))
      rw [AlternatingPath.last_cons]
      exact hl _ List.mem_cons_self (hl'.symm.imp_right fun hl' => by
        obtain ⟨y, l, rfl⟩ := List.exists_cons_of_ne_nil hl'
        simp)

/-- A word whose letters alternate between the two vertex groups spells a reduced path when its
letters of the other vertex group, and its letters other than the first and the last, avoid the
image of the edge group. In particular the reduced words of Mathlib's `Monoid.PushoutI.Reduced`
spell reduced paths. -/
theorem isReduced_segmentPath {v : SerreGraph.segment.V}
    {l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)}
    (hc : l.IsChain fun x y => x.1 ≠ y.1)
    (hl : ∀ x ∈ l, x.1 ≠ v ∨ x ∈ l.tail.dropLast → x.2 ∉ (segmentMaps f g hf hg x.1).range) :
    (segmentPath f g hf hg v l).IsReduced := by
  cases l with
  | nil => simp [segmentPath, segmentPathAux]
  | cons x l =>
    rw [List.isChain_cons] at hc
    obtain ⟨i, x⟩ := x
    by_cases hi : i = v
    · subst hi
      rw [segmentPath, segmentPathAux, dite_eq_left rfl]
      exact isReduced_segmentPathAux _ l (by simp) (fun _ => .inl (by simp))
        (fun y hy hy' => absurd hy' (hc.1 y hy).symm) hc.2
        (fun y hy hy' => hl y (List.mem_cons_of_mem _ hy) hy')
    · refine isReduced_segmentPathAux _ _ (by simp) (fun _ => .inl (by simp))
        (fun _ _ _ => by simp) (List.isChain_cons.2 hc) fun y hy hy' => hl y hy ?_
      by_cases hyv : y.1 = v
      · refine .inr ?_
        replace hy' := hy'.resolve_left (not_not.2 hyv)
        cases l with
        | nil => simp at hy'
        | cons z l =>
          rw [List.dropLast_cons_cons, List.mem_cons] at hy'
          rcases hy' with rfl | hy'
          · exact absurd hyv hi
          · simpa using hy'
      · exact .inl hyv

private theorem length_segmentPathAux_eq_zero_iff {v : SerreGraph.segment.V} :
    ∀ {b : SerreGraph.segment.V} (p : (segment f g hf hg).AlternatingPath v b)
      (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)),
      (segmentPathAux p l).length = 0 ↔ p.length = 0 ∧ b = v ∧ ∀ x ∈ l, x.1 = b
  | b, p, [] => by
    rw [segmentPathAux]
    split_ifs with h
    · subst h
      simp
    · obtain rfl := segment_tgt_eq_of_ne h
      simp [h]
  | b, p, ⟨i, x⟩ :: l => by
    rw [segmentPathAux]
    split_ifs with h
    · subst h
      rw [length_segmentPathAux_eq_zero_iff]
      simp
    · obtain rfl := segment_tgt_eq_of_ne (Ne.symm h)
      rw [length_segmentPathAux_eq_zero_iff]
      simp [h]

/-- A word spells a path of length zero exactly when all its letters lie in the vertex group at
the base vertex. -/
theorem length_segmentPath_eq_zero_iff (v : SerreGraph.segment.V)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    (segmentPath f g hf hg v l).length = 0 ↔ ∀ x ∈ l, x.1 = v := by
  simp [segmentPath, length_segmentPathAux_eq_zero_iff]

/-- **Mathlib's normal form theorem for amalgams, recovered for the segment**: a reduced word of
the free product of the two vertex groups whose product lies in the image of the edge group is
empty. This is `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`, derived here from Britton's lemma
for the segment and the path spelled by the word. -/
example (w : Monoid.CoprodI.Word (segment f g hf hg).vertexGroup)
    (hw : Monoid.PushoutI.Reduced (segmentMaps f g hf hg) w)
    (h : Monoid.PushoutI.ofCoprodI w.prod ∈ (Monoid.PushoutI.base (segmentMaps f g hf hg)).range) :
    w = .empty := by
  -- Read `w` as a closed path at a vertex `v` (either vertex will do).
  suffices ∀ _ : SerreGraph.segment.V, w = .empty from this false
  intro v
  have hT : (Set.univ : Set SerreGraph.segment.E).Nonempty := ⟨v, Set.mem_univ _⟩
  obtain ⟨c, hc⟩ := h
  have hprod : π₁Tree.equivPushoutI f g hf hg hT
      ((segmentPath f g hf hg v w.toList).toPath.toπ₁Tree Set.univ) =
      Monoid.PushoutI.of v (segmentMaps f g hf hg v c) := by
    rw [equivPushoutI_toπ₁Tree_toPath_segmentPath, Monoid.PushoutI.of_apply_eq_base, hc,
      Monoid.CoprodI.Word.prod, map_list_prod, List.map_map]
    simp [Function.comp_def]
  have h0 := ((isReduced_segmentPath (v := v) w.chain_ne fun x hx _ => hw x hx)
    |>.equivPushoutI_toπ₁Tree_toPath_mem_range_iff hT).1 ⟨_, hprod.symm⟩
  rw [length_segmentPath_eq_zero_iff] at h0
  -- All letters lie in `A_v`, so the word, alternating between the factors, has at most one.
  rcases hl : w.toList with _ | ⟨⟨i, a⟩, _ | ⟨y, l⟩⟩
  · exact Monoid.CoprodI.Word.ext hl
  · obtain rfl : i = v := h0 ⟨i, a⟩ (by simp [hl])
    refine (hw ⟨i, a⟩ (by simp [hl]) ⟨c, ?_⟩).elim
    rw [equivPushoutI_toπ₁Tree_toPath_segmentPath, hl] at hprod
    exact (Monoid.PushoutI.of_injective (φ := segmentMaps f g hf hg)
      (fun b c c' h => (segment f g hf hg).α_injective (segmentDart b)
        ((α_segment_apply _ c).trans (h.trans (α_segment_apply _ c').symm))) i
      (by simpa using hprod)).symm
  · have hc := w.chain_ne
    rw [hl, List.isChain_cons_cons] at hc
    exact (hc.1 ((h0 ⟨i, a⟩ (by simp [hl])).trans (h0 y (by simp [hl])).symm)).elim

/-- If the edge group of the segment maps onto the vertex group at the vertex `!v` other than
`v`, then every reduced closed alternating path at `v` has length zero: a closed path of positive
length ends with `e', x, e` where `e` returns to `v` and `x ∈ A_{!v} = α_e(A_e)`, a backtracking.
This is the case of the segment whose edge maps are the identity maps of a common group. -/
theorem AlternatingPath.IsReduced.length_eq_zero_of_surjective_segmentMaps
    {v : SerreGraph.segment.V} {p : (segment f g hf hg).AlternatingPath v v} (hp : p.IsReduced)
    (hv : Function.Surjective (segmentMaps f g hf hg (!v))) : p.length = 0 := by
  by_contra h0
  obtain ⟨c, q, ⟨e, rfl, he⟩, x, rfl⟩ := AlternatingPath.length_ne_zero_iff_eq_cons.1 h0
  subst he
  have hq : q.length ≠ 0 := fun h => by
    have := q.eq_of_length_zero h
    cases e <;> exact Bool.noConfusion this
  obtain ⟨c', r, e', y, rfl⟩ := AlternatingPath.length_ne_zero_iff_eq_cons.1 hq
  refine ((AlternatingPath.isReduced_cons_iff _ _ _).1 hp).2
    ((AlternatingPath.cancels_cons_iff ..).2 ⟨?_, ?_⟩)
  · have h := e'.2.2
    revert h
    generalize e'.1 = d
    cases d <;> cases e <;> intro h <;> first | rfl | exact Bool.noConfusion h
  · have key : ∀ b : SerreGraph.segment.E, Function.Surjective
        (segmentMaps f g hf hg (!SerreGraph.segment.tgt b)) →
        Function.Surjective (segmentMaps f g hf hg (SerreGraph.segment.src b)) := by
      intro b
      cases b <;> exact id
    obtain ⟨c₀, hc₀⟩ := key e hv y
    exact ⟨c₀, (DFunLike.congr_fun ((segment f g hf hg).αArrow_mk e) c₀).trans
      ((α_segment_apply e c₀).trans hc₀)⟩

/-- If the edge group of the segment maps onto the vertex group at the vertex `!v` other than
`v`, then the vertex group `A_v` is the fundamental group `π₁(𝔸, v)`: for the segment of
`C → A`, `C → B` with `C → B` onto, `A ∗_C B = A`. -/
theorem π₁.vertexHom_bijective_segment {v : SerreGraph.segment.V}
    (hv : Function.Surjective (segmentMaps f g hf hg (!v))) :
    Function.Bijective
      (π₁.vertexHom (Quiver.Path.nil : (segment f g hf hg).Path ⟨v⟩ ⟨v⟩)) := by
  refine ⟨π₁.vertexHom_injective _, fun x => π₁.induction_on x fun q => ?_⟩
  -- The normal form of a closed path is reduced, hence of length zero.
  have h0 := (normalForm default q).isReduced.length_eq_zero_of_surjective_segmentMaps hv
  refine ⟨(normalForm default q).toAlternatingPath.last, ?_⟩
  rw [π₁.vertexHom_nil_apply, ← π₁.mk_toPath_normalForm default v q, NormalWord.toPath_def,
    AlternatingPath.length_eq_zero_iff.1 h0]
  simp

end segment

/-! ### The loop: HNN extensions -/

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] {f g : C →* G}
  {hf : Function.Injective f} {hg : Function.Injective g} {v : (SerreGraph.rose Unit).V}

/-- The dart of the loop read as `t ^ u` in the HNN extension of the loop, for `u = ±1`: the dart
`((), false)` is `t` and `((), true)` is `t⁻¹` (`π₁Tree.equivHNNExtension`). -/
private def loopArrow (u : ℤˣ) : v ⟶ v :=
  ⟨((), decide (u = -1)), rfl, rfl⟩

/-- The group `G` as the vertex group of the loop. -/
private def loopVertexEquiv : G ≃* (loop f g hf hg).vertexGroup v :=
  MulEquiv.refl G

variable (f g hf hg) in
/-- The closed alternating path `h, t^{u₁}, g₁, …, t^{u_k}, g_k` of the loop spelled by the word
`h t^{u₁} g₁ ⋯ t^{u_k} g_k` of the HNN extension of the loop, as in Mathlib's
`HNNExtension.NormalWord.ReducedWord` (head `h`, list `(u₁, g₁), …`): the dart `((), false)` is
`t` and `((), true)` is `t⁻¹`, as for `π₁Tree.equivHNNExtension`. -/
def loopPath (h : G) (l : List (ℤˣ × G)) : (loop f g hf hg).AlternatingPath v v :=
  l.foldl (fun p x => p.cons (loopArrow x.1) (loopVertexEquiv x.2)) (.single (loopVertexEquiv h))

private theorem length_foldl_loopArrow (p : (loop f g hf hg).AlternatingPath v v)
    (l : List (ℤˣ × G)) :
    (l.foldl (fun p x => p.cons (loopArrow x.1) (loopVertexEquiv x.2)) p).length =
      p.length + l.length := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, ih, AlternatingPath.length_cons, List.length_cons]
    omega

/-- The path spelled by a word has one dart for each letter `t^{u_i}`. -/
@[simp] theorem length_loopPath (h : G) (l : List (ℤˣ × G)) :
    (loopPath f g hf hg h l : (loop f g hf hg).AlternatingPath v v).length = l.length := by
  simp [loopPath, length_foldl_loopArrow]

private theorem equivHNNExtension_edge_loopArrow (u : ℤˣ) :
    π₁Tree.equivHNNExtension f g hf hg (π₁Tree.edge ∅ (loopArrow (v := v) u).1) =
      HNNExtension.t ^ (u : ℤ) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact (π₁Tree.equivHNNExtension_edge_false f g hf hg).trans (zpow_one _).symm
  · exact (π₁Tree.equivHNNExtension_edge_true f g hf hg).trans (zpow_neg_one _).symm

private theorem toπ₁Tree_foldl_loopArrow (p : (loop f g hf hg).AlternatingPath v v)
    (l : List (ℤˣ × G)) :
    (l.foldl (fun p x => p.cons (loopArrow x.1) (loopVertexEquiv x.2)) p).toPath.toπ₁Tree ∅ =
      p.toPath.toπ₁Tree ∅ * (l.map fun x =>
        π₁Tree.edge ∅ (loopArrow (v := v) x.1).1 * π₁Tree.of ∅ v (loopVertexEquiv x.2)).prod := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    simp [mul_assoc]

/-- A word spells the element of the HNN extension of the loop given by its product, Mathlib's
`HNNExtension.NormalWord.ReducedWord.prod`. -/
@[simp] theorem equivHNNExtension_toπ₁Tree_toPath_loopPath (h : G) (l : List (ℤˣ × G)) :
    π₁Tree.equivHNNExtension f g hf hg
        ((loopPath f g hf hg h l : (loop f g hf hg).AlternatingPath v v).toPath.toπ₁Tree ∅) =
      HNNExtension.of h *
        (l.map fun x => HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2).prod := by
  rw [loopPath, toπ₁Tree_foldl_loopArrow]
  simp only [AlternatingPath.toPath_single, Path.toπ₁Tree_ofVertex, map_mul, map_list_prod,
    List.map_map, Function.comp_def, equivHNNExtension_edge_loopArrow]
  -- `π₁Tree.equivHNNExtension_of` is stated at the vertex `()` for elements of `G`, which are `v`
  -- and the elements of the vertex group at `v` only up to unfolding: it is applied as a term.
  exact congr_arg₂ (· * ·) (π₁Tree.equivHNNExtension_of f g hf hg h) <| congrArg List.prod <|
    List.map_congr_left fun x _ => congrArg (_ * ·) (π₁Tree.equivHNNExtension_of f g hf hg x.2)

private theorem loopVertexEquiv_mem_range_αArrow_loopArrow_iff (u : ℤˣ) (y : G) :
    loopVertexEquiv y ∈ ((loop f g hf hg).αArrow (loopArrow (v := v) u)).range ↔
      y ∈ HNNExtension.toSubgroup f.range g.range (-u) := by
  -- `α` of the dart `((), false)` is `g` and of `((), true)` is `f`.
  have key : ∀ c, (loop f g hf hg).αArrow (loopArrow (v := v) u) c =
      loopVertexEquiv (if u = 1 then g c else f c) := fun c => by
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact (DFunLike.congr_fun ((loop f g hf hg).αArrow_mk ((), false)) c).trans
        (DFunLike.congr_fun (loop_α_false f g hf hg) c)
    · exact (DFunLike.congr_fun ((loop f g hf hg).αArrow_mk ((), true)) c).trans
        (DFunLike.congr_fun (loop_α_true f g hf hg) c)
  simp only [MonoidHom.mem_range, key, EmbeddingLike.apply_eq_iff_eq]
  rcases Int.units_eq_one_or u with rfl | rfl <;> exact Iff.rfl

private theorem loopArrow_val_eq_rev_iff (u u' : ℤˣ) :
    (loopArrow (v := v) u).1 = (SerreGraph.rose Unit).rev (loopArrow (v := v) u').1 ↔ u ≠ u' := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl
  · exact iff_of_false (fun h => Bool.noConfusion (congrArg Prod.snd h)) (not_not.2 rfl)
  · exact iff_of_true rfl (by decide)
  · exact iff_of_true rfl (by decide)
  · exact iff_of_false (fun h => Bool.noConfusion (congrArg Prod.snd h)) (not_not.2 rfl)

/- A letter `t^u g` followed by `t^{u'}` is a backtracking exactly when it is a pinch:
`u' = -u` and `g ∈ toSubgroup u`. -/
private theorem cancels_cons_loopArrow_iff {p : (loop f g hf hg).AlternatingPath v v} {u u' : ℤˣ}
    {y : G} : (p.cons (loopArrow u) (loopVertexEquiv y)).Cancels (loopArrow (v := v) u') ↔
      y ∈ HNNExtension.toSubgroup f.range g.range u ∧ u ≠ u' := by
  rw [AlternatingPath.cancels_cons_iff, loopVertexEquiv_mem_range_αArrow_loopArrow_iff,
    loopArrow_val_eq_rev_iff, and_comm]
  refine and_congr_left fun h => ?_
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl <;>
    simp_all

private theorem isReduced_foldl_loopArrow_iff (p : (loop f g hf hg).AlternatingPath v v)
    (l : List (ℤˣ × G)) :
    (l.foldl (fun p x => p.cons (loopArrow x.1) (loopVertexEquiv x.2)) p).IsReduced ↔
      p.IsReduced ∧ (∀ x ∈ l.head?, ¬ p.Cancels (loopArrow x.1)) ∧
        l.IsChain fun x y => x.2 ∈ HNNExtension.toSubgroup f.range g.range x.1 → x.1 = y.1 := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.isChain_cons, AlternatingPath.isReduced_cons_iff]
    simp only [cancels_cons_loopArrow_iff, not_and, not_not, Option.mem_def, List.head?_cons,
      Option.some.injEq, forall_eq']
    tauto

/-- **A word without pinches spells a reduced path.** The path spelled by `h t^{u₁} g₁ ⋯` is
reduced exactly when the word has no pinch `t g t⁻¹` with `g ∈ range f` and no pinch `t⁻¹ g t`
with `g ∈ range g`: the condition on the right is the `chain` field of Mathlib's
`HNNExtension.NormalWord.ReducedWord`. -/
theorem isReduced_loopPath_iff (h : G) (l : List (ℤˣ × G)) :
    (loopPath f g hf hg h l : (loop f g hf hg).AlternatingPath v v).IsReduced ↔
      l.IsChain fun x y => x.2 ∈ HNNExtension.toSubgroup f.range g.range x.1 → x.1 = y.1 := by
  rw [loopPath, isReduced_foldl_loopArrow_iff]
  simp

/-- **Britton's lemma for the loop.** A reduced closed alternating path of the loop spells an
element of the HNN extension `HNNExtension G (range f) (range g) φ` in `G` exactly when it has
length zero. With `isReduced_loopPath_iff` this is Britton's lemma for HNN extensions: a word
`t^{ε₁} g₁ ⋯` with a letter `t^{±1}` and no pinch does not lie in `G`, in particular is
nontrivial. -/
theorem AlternatingPath.IsReduced.equivHNNExtension_toπ₁Tree_toPath_mem_range_iff
    {p : (loop f g hf hg).AlternatingPath v v} (hp : p.IsReduced) :
    π₁Tree.equivHNNExtension f g hf hg (p.toPath.toπ₁Tree ∅) ∈
      (HNNExtension.of : G →* HNNExtension G f.range g.range (loopEquiv f g hf hg)).range ↔
      p.length = 0 := by
  rw [← hp.toπ₁Tree_toPath_mem_range_iff (SerreGraph.roseTree Unit) (Set.empty_subset _)]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨loopVertexEquiv y, (π₁Tree.equivHNNExtension f g hf hg).injective
      ((π₁Tree.equivHNNExtension_of f g hf hg y).trans hy)⟩
  · rintro ⟨y, hy⟩
    exact ⟨loopVertexEquiv.symm y,
      (π₁Tree.equivHNNExtension_of f g hf hg _).symm.trans (congrArg _ hy)⟩

/-- **Britton's lemma for HNN extensions, recovered for the loop**: a reduced word of the HNN
extension of the loop whose product lies in `G` has no letter `t^{±1}`. This is
`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`, derived here from Britton's lemma for
the loop and the path spelled by the word. -/
example (w : HNNExtension.NormalWord.ReducedWord G f.range g.range)
    (hw : w.prod (loopEquiv f g hf hg) ∈
      (HNNExtension.of : G →* HNNExtension G f.range g.range (loopEquiv f g hf hg)).range) :
    w.toList = [] := by
  -- Read `w` as a closed path at the vertex `v` of the loop.
  suffices ∀ _ : (SerreGraph.rose Unit).V, w.toList = [] from this ()
  intro v
  rw [← List.length_eq_zero_iff, ← length_loopPath (f := f) (g := g) (hf := hf) (hg := hg)
    (v := v) w.head, ← ((isReduced_loopPath_iff w.head w.toList).2
      w.chain).equivHNNExtension_toπ₁Tree_toPath_mem_range_iff,
    equivHNNExtension_toπ₁Tree_toPath_loopPath]
  exact hw

/- In the fundamental group of the loop relative to `∅`, the element `t⁻¹ y t` (with `t` the dart
`((), false)`), read off the path `1, t⁻¹, y, t, 1`, lies in the vertex group only when
`y ∈ range g`; this is the computation behind the Baumslag–Solitar example below. -/
private theorem mem_range_of_mem_range_loop {y : G}
    (h : π₁Tree.edge ∅ (loopArrow (v := v) (-1)).1 *
      π₁Tree.of (𝔸 := loop f g hf hg) ∅ v (loopVertexEquiv y) *
      π₁Tree.edge ∅ (loopArrow (v := v) 1).1 ∈ (π₁Tree.of (𝔸 := loop f g hf hg) ∅ v).range) :
    y ∈ g.range := by
  by_contra hy
  have hP : (loopPath f g hf hg 1 [(-1, y), (1, 1)] :
      (loop f g hf hg).AlternatingPath v v).IsReduced :=
    (isReduced_loopPath_iff _ _).2 (List.isChain_pair.2 fun hy' => absurd hy' (by simpa using hy))
  have := (hP.toπ₁Tree_toPath_mem_range_iff (SerreGraph.roseTree Unit) (Set.empty_subset _)).1 ?_
  · simp at this
  · rw [loopPath, toπ₁Tree_foldl_loopArrow]
    simpa [← mul_assoc] using h

end loop

/-! ### Examples -/

section Examples

open Multiplicative

/-- In the Baumslag–Solitar group `⟨a, t ∣ t a² t⁻¹ = a⟩`, the fundamental group of the loop
`baumslagSolitar 1 2` with `α = id` and `ω = (· ^ 2)` on its dart `t = ((), true)`, the path
`1, t, a, t⁻¹, 1` is reduced, because `a ∉ ω(ℤ) = ⟨a²⟩`. In the notation of `loopPath`, whose
letter `t^{-1}` is the dart `((), true)`, this path is `loopPath 1 [(-1, a), (1, 1)]`. -/
example {v : (SerreGraph.rose Unit).V} :
    (loopPath (zpowGroupHom (α := Multiplicative ℤ) 1) (zpowGroupHom 2)
      (zpow_left_injective one_ne_zero) (zpow_left_injective two_ne_zero) 1
      [(-1, ofAdd 1), (1, 1)] :
        (baumslagSolitar 1 2 one_ne_zero two_ne_zero).AlternatingPath v v).IsReduced := by
  refine (isReduced_loopPath_iff _ _).2 (List.isChain_pair.2 fun ⟨c, hc⟩ => ?_)
  have := congrArg Multiplicative.toAdd hc
  simp at this
  omega

/-- Hence `t a t⁻¹ ∉ ⟨a⟩` in `⟨a, t ∣ t a² t⁻¹ = a⟩`. -/
example : (PresentedGroup.of true * PresentedGroup.of false * (PresentedGroup.of true)⁻¹ :
      PresentedGroup {baumslagSolitarRelator 1 2}) ∉
      Subgroup.zpowers (PresentedGroup.of false) := by
  rintro ⟨k, hk⟩
  -- Read `t a t⁻¹` at the vertex `v` of the loop, through `π₁(𝔸, ∅) ≃* ⟨a, t ∣ t a² t⁻¹ = a⟩`.
  suffices ∀ _ : (SerreGraph.rose Unit).V, False from this ()
  intro v
  have hf : Function.Injective (zpowGroupHom (α := Multiplicative ℤ) 1) :=
    zpow_left_injective one_ne_zero
  have hg : Function.Injective (zpowGroupHom (α := Multiplicative ℤ) 2) :=
    zpow_left_injective two_ne_zero
  have h1 := congrArg (π₁Tree.baumslagSolitarEquiv 1 2 one_ne_zero two_ne_zero).symm hk
  simp only [map_zpow, map_mul, map_inv, π₁Tree.baumslagSolitarEquiv_symm_of_false,
    π₁Tree.baumslagSolitarEquiv_symm_of_true] at h1
  obtain ⟨c, hc⟩ := mem_range_of_mem_range_loop (hf := hf) (hg := hg) (v := v) (y := ofAdd 1)
    ⟨loopVertexEquiv (ofAdd k : Multiplicative ℤ), by
      have e2 := π₁Tree.edge_rev (𝔸 := loop _ _ hf hg) (T := ∅) (loopArrow (v := v) (-1)).1
      -- The reverse of the dart `((), true)` is `((), false)`, by definition of the rose.
      rw [show (SerreGraph.rose Unit).rev (loopArrow (v := v) (-1)).1 = (loopArrow (v := v) 1).1
        from rfl] at e2
      rw [e2, show (ofAdd k : Multiplicative ℤ) = ofAdd 1 ^ k by
        rw [← ofAdd_zsmul, smul_eq_mul, mul_one], map_zpow, map_zpow]
      exact h1⟩
  have := congrArg Multiplicative.toAdd hc
  simp at this
  omega

/-- In `⟨a, t ∣ t a² t⁻¹ = a⟩` the path `1, t, a², t⁻¹, 1` is not reduced, because
`a² ∈ ω(ℤ)`. -/
example {v : (SerreGraph.rose Unit).V} :
    ¬ (loopPath (zpowGroupHom (α := Multiplicative ℤ) 1) (zpowGroupHom 2)
      (zpow_left_injective one_ne_zero) (zpow_left_injective two_ne_zero) 1
      [(-1, ofAdd 2), (1, 1)] :
        (baumslagSolitar 1 2 one_ne_zero two_ne_zero).AlternatingPath v v).IsReduced := fun h =>
  absurd (List.isChain_pair.1 ((isReduced_loopPath_iff _ _).1 h) ⟨ofAdd 1, rfl⟩) (by decide)

/-- In `⟨a, t ∣ t a² t⁻¹ = a⟩` the element `t a² t⁻¹` equals `a`. -/
example : (PresentedGroup.of true * PresentedGroup.of false ^ 2 * (PresentedGroup.of true)⁻¹ :
    PresentedGroup {baumslagSolitarRelator 1 2}) = PresentedGroup.of false := by
  simpa using baumslagSolitarRelator_relation 1 2

/-- For the segment whose edge maps are the identity maps of a common group `A`, a reduced closed
path has length zero. -/
example {A : Type*} [Group A] {v : SerreGraph.segment.V}
    {p : (segment (MonoidHom.id A) (MonoidHom.id A) Function.injective_id
      Function.injective_id).AlternatingPath v v} (hp : p.IsReduced) : p.length = 0 := by
  refine hp.length_eq_zero_of_surjective_segmentMaps ?_
  cases v
  · exact fun a => ⟨a, DFunLike.congr_fun (segmentMaps_true (MonoidHom.id A) (MonoidHom.id A)
      Function.injective_id Function.injective_id) a⟩
  · exact fun a => ⟨a, DFunLike.congr_fun (segmentMaps_false (MonoidHom.id A) (MonoidHom.id A)
      Function.injective_id Function.injective_id) a⟩

/-- For the segment whose edge maps are the identity maps of a common group `A`, the fundamental
group is `A`. -/
example {A : Type*} [Group A] {v : SerreGraph.segment.V} :
    Function.Bijective (π₁.vertexHom (Quiver.Path.nil : (segment (MonoidHom.id A)
      (MonoidHom.id A) Function.injective_id Function.injective_id).Path ⟨v⟩ ⟨v⟩)) := by
  refine π₁.vertexHom_bijective_segment ?_
  cases v
  · exact fun a => ⟨a, DFunLike.congr_fun (segmentMaps_true (MonoidHom.id A) (MonoidHom.id A)
      Function.injective_id Function.injective_id) a⟩
  · exact fun a => ⟨a, DFunLike.congr_fun (segmentMaps_false (MonoidHom.id A) (MonoidHom.id A)
      Function.injective_id Function.injective_id) a⟩

/-- Crossing the edge of a segment once is a reduced path of length one between distinct
vertices. -/
example {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}
    {hf : Function.Injective f} {hg : Function.Injective g} {e : SerreGraph.segment.E}
    (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src e))
    (y : (segment f g hf hg).vertexGroup (SerreGraph.segment.tgt e)) :
    ((AlternatingPath.single x).cons (SerreGraph.segment.dart e) y).IsReduced ∧
      ((AlternatingPath.single x).cons (SerreGraph.segment.dart e) y).length = 1 ∧
      SerreGraph.segment.src e ≠ SerreGraph.segment.tgt e :=
  ⟨(AlternatingPath.isReduced_cons_iff _ _ _).2
    ⟨AlternatingPath.isReduced_single _, AlternatingPath.not_cancels_single _ _⟩,
    (AlternatingPath.length_cons _ _ _).trans (by rw [AlternatingPath.length_single]),
    by cases e <;> exact Bool.noConfusion⟩

end Examples

end GraphOfGroups

end TauCeti
