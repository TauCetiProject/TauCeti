/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.NormalForm
public import TauCeti.GroupTheory.GraphOfGroups.OneEdge

/-!
# Britton's lemma for one-edge graphs of groups

Britton's lemma for graphs of groups,
`TauCeti.GraphOfGroups.AlternatingPath.IsReduced.toπ₁Tree_toPath_mem_range_of_iff`, says that a
reduced closed alternating path at a vertex `a` spells an element of `π₁(𝔸, T)` in the image of
the vertex group `A_a` exactly when it has length zero. For the two graphs of groups with one
geometric edge it recovers the classical normal forms.

* For the segment `A ← C → B`, whose fundamental group is the amalgamated product `A ∗_C B`
  (Mathlib's `Monoid.PushoutI`), a word in the letters of `A` and `B` spells a closed
  alternating path at a vertex `v`, `segmentPath`, and the path spells the product of the word.
  The path is reduced when the letters alternate between the two factors, every letter of the
  vertex group at the other vertex `!v` avoids the image of `C`, including a first or a last
  letter, and every letter of `A_v` other than the first and the last avoids it too. Together
  with Britton's lemma this gives Mathlib's normal form theorem for amalgams,
  `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`, for the segment.
* For the loop with monomorphisms `f g : C →* G`, whose fundamental group is the HNN extension
  `HNNExtension G (range f) (range g) φ`, a word `h t^{u₁} g₁ ⋯ t^{u_k} g_k` spells the
  alternating path `h, t^{u₁}, g₁, …` of the loop, `loopPath`. A pinch `t g t⁻¹`, `g ∈ range f`,
  or `t⁻¹ g t`, `g ∈ range g`, is exactly a backtracking of the path, so the reduced words of
  Mathlib's `HNNExtension.NormalWord.ReducedWord` are the reduced paths. With the form of
  Britton's lemma for the loop this gives Britton's lemma for HNN extensions,
  `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`.

Both recovered statements are checked as examples, together with the examples: for a segment
whose edge maps are isomorphisms there is no reduced closed path of positive length and the
fundamental group is the vertex group; and crossing the edge of a segment once is a reduced path
of length one.

## Main definitions

* `segmentPath`: the closed alternating path of the segment spelled by a
  word in the letters of the two vertex groups.
* `loopArrow`: the dart of the loop read as `t ^ u`, `u = ±1`.
* `loopPath`: the closed alternating path of the loop spelled by a word
  `h t^{u₁} g₁ ⋯ t^{u_k} g_k`.

## Main results

* `AlternatingPath.IsReduced.equivPushoutI_toπ₁Tree_toPath_mem_range_of_iff`:
  the normal form theorem for the amalgamated product of the segment.
* `AlternatingPath.IsReduced.equivHNNExtension_toπ₁Tree_toPath_mem_range_of_iff`:
  Britton's lemma for the HNN extension of the loop.
* `isReduced_segmentPath`, `isReduced_loopPath_iff`:
  reduced words spell reduced paths.
* `AlternatingPath.IsReduced.length_eq_zero_of_surjective_segmentMaps`,
  `π₁.vertexHom_bijective_of_surjective_segmentMaps`: when the edge group of
  a segment maps onto the vertex group at the vertex `!v`, every reduced closed path based at `v`
  has length zero, and the vertex group `A_v` is the fundamental group `π₁(𝔸, v)`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.4.
* J.-P. Serre, *Trees*, Chapter I, §1 and §5.2, Theorem 11.
* J. L. Britton, *The word problem*, Ann. of Math. 77 (1963).
-/

public section

universe w x

namespace TauCeti

namespace GraphOfGroups

/-! ### The segment: amalgamated products -/

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] {f : C →* A} {g : C →* B}
  {hf : Function.Injective f} {hg : Function.Injective g}

/-- **The normal form theorem for amalgamated products.** A reduced closed alternating path at a
vertex `v` of the segment, that is a word `a₀ b₁ a₁ ⋯ b_k a_k` alternating between the vertex
group `A_v` and the other vertex group whose interior letters avoid the edge group, spells an
element of `A ∗_C B` in `A_v` exactly when it has length zero. -/
theorem AlternatingPath.IsReduced.equivPushoutI_toπ₁Tree_toPath_mem_range_of_iff
    {v : SerreGraph.segment.V} {p : (segment f g hf hg).AlternatingPath v v} (hp : p.IsReduced)
    {T : Set SerreGraph.segment.E} (hT : T.Nonempty) :
    π₁Tree.equivPushoutI f g hf hg hT (p.toPath.toπ₁Tree T) ∈
      (Monoid.PushoutI.of (φ := segmentMaps f g hf hg) v).range ↔ p.length = 0 := by
  obtain ⟨T'⟩ := SerreGraph.segment.exists_spanningTree SerreGraph.segment_isTree.connected
  rw [← hp.toπ₁Tree_toPath_mem_range_of_iff T'
    ((SerreGraph.segment_spanningTree_darts T').symm ▸ Set.subset_univ T)]
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
    if h : b = v then h ▸ p
    else SerreGraph.segment_tgt_eq_of_ne h ▸ p.cons (SerreGraph.segmentArrow b) 1
  | b, p, ⟨i, x⟩ :: l =>
    if h : i = b then segmentPathAux (p.setLast (p.last * h ▸ x)) l
    else segmentPathAux (p.cons (SerreGraph.segmentArrow b)
      ((SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)).symm ▸ x)) l

/- The four steps of `segmentPathAux`, without casts: the end of the word at the base vertex or
at the other vertex, and a letter of the vertex group at the current vertex or at the other one.
The vertex of the segment other than `b` is `segment.tgt b`. -/
private theorem segmentPathAux_nil_self {v : SerreGraph.segment.V}
    (p : (segment f g hf hg).AlternatingPath v v) : segmentPathAux p [] = p := by
  simp [segmentPathAux]

private theorem segmentPathAux_nil_tgt {b : SerreGraph.segment.V}
    (p : (segment f g hf hg).AlternatingPath (SerreGraph.segment.tgt b) b) :
    segmentPathAux p [] = p.cons (SerreGraph.segmentArrow b) 1 := by
  have hb : b ≠ SerreGraph.segment.tgt b := SerreGraph.segment_isTree.isAcyclic.src_ne_tgt b
  simp [segmentPathAux, hb]

private theorem segmentPathAux_cons_self {v b : SerreGraph.segment.V}
    (p : (segment f g hf hg).AlternatingPath v b) (x : (segment f g hf hg).vertexGroup b)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    segmentPathAux p (⟨b, x⟩ :: l) = segmentPathAux (p.setLast (p.last * x)) l := by
  simp [segmentPathAux]

private theorem segmentPathAux_cons_tgt {v b : SerreGraph.segment.V}
    (p : (segment f g hf hg).AlternatingPath v b)
    (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.tgt b))
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    segmentPathAux p (⟨SerreGraph.segment.tgt b, x⟩ :: l) =
      segmentPathAux (p.cons (SerreGraph.segmentArrow b) x) l := by
  have hb : SerreGraph.segment.tgt b ≠ b := (SerreGraph.segment_isTree.isAcyclic.src_ne_tgt b).symm
  simp [segmentPathAux, hb]

/- The end of the word at the other vertex, seen from the base vertex `v`: the path crosses back
along the reverse of the dart leaving `v`. -/
private theorem segmentPathAux_nil_reverse {v : SerreGraph.segment.V}
    (p : (segment f g hf hg).AlternatingPath v (SerreGraph.segment.tgt v)) :
    segmentPathAux p [] = p.cons (Quiver.reverse (SerreGraph.segmentArrow v)) 1 := by
  have h : (Quiver.reverse (SerreGraph.segmentArrow v)).val = SerreGraph.segment.rev v := by
    rw [SerreGraph.reverse_val, SerreGraph.segmentArrow_val]
  -- The other vertex `segment.tgt v` is `!v`, and `!!v` is `v` only once `v` is a constructor.
  cases v
  · exact (segmentPathAux_nil_tgt (b := true) p).trans
      (congrArg (p.cons · 1) (Subtype.ext ((SerreGraph.segmentArrow_val true).trans h.symm)))
  · exact (segmentPathAux_nil_tgt (b := false) p).trans
      (congrArg (p.cons · 1) (Subtype.ext ((SerreGraph.segmentArrow_val false).trans h.symm)))

variable (f g hf hg) in
/-- The closed alternating path of the segment at the vertex `v` spelled by a word in the letters
of the two vertex groups, as in Mathlib's `Monoid.CoprodI.Word`: starting from `1`, a letter of
the vertex group at the current vertex is multiplied onto the last element, a letter of the other
vertex group is appended after crossing the edge, and the path crosses back to `v` with `1` at
the end if needed. Its element of `A ∗_C B` is the product of the word
(`equivPushoutI_toπ₁Tree_toPath_segmentPath`). The equations `segmentPath_nil`,
`segmentPath_append_singleton_self`, `segmentPath_append_singleton_tgt` and
`segmentPath_append_cons_cons_self` compute it on every word. -/
noncomputable def segmentPath (v : SerreGraph.segment.V)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    (segment f g hf hg).AlternatingPath v v :=
  segmentPathAux (.single 1) l

/-- The empty word spells the path `1`. -/
@[simp] theorem segmentPath_nil (v : SerreGraph.segment.V) :
    segmentPath f g hf hg v [] = .single 1 :=
  segmentPathAux_nil_self _

/-- A word with a single letter of the vertex group at the base vertex spells that letter. -/
@[simp] theorem segmentPath_singleton (v : SerreGraph.segment.V)
    (x : (segment f g hf hg).vertexGroup v) :
    segmentPath f g hf hg v [⟨v, x⟩] = .single x := by
  simp [segmentPath, segmentPathAux_cons_self, segmentPathAux_nil_self]

private theorem segmentPathAux_append_singleton_self {v : SerreGraph.segment.V}
    (x : (segment f g hf hg).vertexGroup v) : ∀ {b : SerreGraph.segment.V}
      (p : (segment f g hf hg).AlternatingPath v b)
      (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)),
      segmentPathAux p (l ++ [⟨v, x⟩]) =
        (segmentPathAux p l).setLast ((segmentPathAux p l).last * x)
  | b, p, [] => by
    by_cases h : b = v
    · subst h
      simp [segmentPathAux_cons_self, segmentPathAux_nil_self]
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne h
      simp [segmentPathAux_cons_tgt, segmentPathAux_nil_self, segmentPathAux_nil_tgt]
  | b, p, ⟨i, y⟩ :: l => by
    by_cases h : i = b
    · subst h
      simpa [segmentPathAux_cons_self] using segmentPathAux_append_singleton_self x _ l
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)
      simpa [segmentPathAux_cons_tgt] using segmentPathAux_append_singleton_self x _ l

/-- Appending a letter of the vertex group at the base vertex multiplies it onto the last
element of the path. -/
@[simp] theorem segmentPath_append_singleton_self (v : SerreGraph.segment.V)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i))
    (x : (segment f g hf hg).vertexGroup v) :
    segmentPath f g hf hg v (l ++ [⟨v, x⟩]) =
      (segmentPath f g hf hg v l).setLast ((segmentPath f g hf hg v l).last * x) :=
  segmentPathAux_append_singleton_self x _ l

private theorem segmentPathAux_append_singleton_tgt {v : SerreGraph.segment.V}
    (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.tgt v)) :
    ∀ {b : SerreGraph.segment.V} (p : (segment f g hf hg).AlternatingPath v b)
      (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)),
      (∀ y ∈ l.getLast?, y.1 = v) → (l = [] → b = v) →
      segmentPathAux p (l ++ [⟨SerreGraph.segment.tgt v, x⟩]) =
        ((segmentPathAux p l).cons (SerreGraph.segmentArrow v) x).cons
          (Quiver.reverse (SerreGraph.segmentArrow v)) 1
  | b, p, [], _, hb => by
    obtain rfl := hb rfl
    simp [segmentPathAux_cons_tgt, segmentPathAux_nil_self, segmentPathAux_nil_reverse]
  | b, p, ⟨i, y⟩ :: l, hl, _ => by
    have hl' : ∀ z ∈ l.getLast?, z.1 = v := fun z hz => hl z (List.mem_getLast?_cons hz)
    have hi : l = [] → i = v := fun h => by
      subst h
      exact hl _ rfl
    by_cases h : i = b
    · subst h
      simpa [segmentPathAux_cons_self] using segmentPathAux_append_singleton_tgt x _ l hl' hi
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)
      simpa [segmentPathAux_cons_tgt] using segmentPathAux_append_singleton_tgt x _ l hl' hi

/-- Appending a letter of the vertex group at the other vertex `segment.tgt v` to a word that is
empty or ends with a letter of the vertex group at the base vertex `v` crosses the edge with that
letter and crosses back with `1`. -/
theorem segmentPath_append_singleton_tgt (v : SerreGraph.segment.V)
    {l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)}
    (hl : ∀ y ∈ l.getLast?, y.1 = v)
    (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.tgt v)) :
    segmentPath f g hf hg v (l ++ [⟨SerreGraph.segment.tgt v, x⟩]) =
      ((segmentPath f g hf hg v l).cons (SerreGraph.segmentArrow v) x).cons
        (Quiver.reverse (SerreGraph.segmentArrow v)) 1 :=
  segmentPathAux_append_singleton_tgt x _ l hl fun _ => rfl

/-- A word with a single letter of the vertex group at the other vertex `segment.tgt v` crosses
the edge with that letter and crosses back with `1`. -/
@[simp] theorem segmentPath_singleton_tgt (v : SerreGraph.segment.V)
    (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.tgt v)) :
    segmentPath f g hf hg v [⟨SerreGraph.segment.tgt v, x⟩] =
      ((.single 1 : (segment f g hf hg).AlternatingPath v v).cons (SerreGraph.segmentArrow v)
        x).cons (Quiver.reverse (SerreGraph.segmentArrow v)) 1 := by
  simpa using segmentPath_append_singleton_tgt (l := []) v (by simp) x

private theorem segmentPathAux_cons_cons_self {v i : SerreGraph.segment.V}
    (x y : (segment f g hf hg).vertexGroup i) {b : SerreGraph.segment.V}
    (p : (segment f g hf hg).AlternatingPath v b)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    segmentPathAux p (⟨i, x⟩ :: ⟨i, y⟩ :: l) = segmentPathAux p (⟨i, x * y⟩ :: l) := by
  by_cases h : i = b
  · subst h
    simp [segmentPathAux_cons_self, mul_assoc]
  · obtain rfl := SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)
    simp [segmentPathAux_cons_tgt, segmentPathAux_cons_self]

/-- Two consecutive letters of the same vertex group spell the same path as their product. -/
theorem segmentPath_append_cons_cons_self (v : SerreGraph.segment.V) {i : SerreGraph.segment.V}
    (l l' : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i))
    (x y : (segment f g hf hg).vertexGroup i) :
    segmentPath f g hf hg v (l ++ ⟨i, x⟩ :: ⟨i, y⟩ :: l') =
      segmentPath f g hf hg v (l ++ ⟨i, x * y⟩ :: l') := by
  suffices ∀ {b : SerreGraph.segment.V} (p : (segment f g hf hg).AlternatingPath v b),
      segmentPathAux p (l ++ ⟨i, x⟩ :: ⟨i, y⟩ :: l') =
        segmentPathAux p (l ++ ⟨i, x * y⟩ :: l') from this _
  induction l with
  | nil => exact fun p => segmentPathAux_cons_cons_self x y p l'
  | cons z l ih =>
    intro b p
    obtain ⟨j, z⟩ := z
    by_cases h : j = b
    · subst h
      simpa [segmentPathAux_cons_self] using ih _
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)
      simpa [segmentPathAux_cons_tgt] using ih _

private theorem toπ₁Tree_toPath_segmentPathAux {T : Set SerreGraph.segment.E} (hT : T.Nonempty)
    {v : SerreGraph.segment.V} : ∀ {b : SerreGraph.segment.V}
      (p : (segment f g hf hg).AlternatingPath v b)
      (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)),
      (segmentPathAux p l).toPath.toπ₁Tree T =
        p.toPath.toπ₁Tree T * (l.map fun x => π₁Tree.of T x.1 x.2).prod
  | b, p, [] => by
    by_cases h : b = v
    · subst h
      simp [segmentPathAux_nil_self]
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne h
      simp [segmentPathAux_nil_tgt, hT]
  | b, p, ⟨i, x⟩ :: l => by
    by_cases h : i = b
    · subst h
      rw [segmentPathAux_cons_self, toπ₁Tree_toPath_segmentPathAux hT,
        Path.Homotopic.toπ₁Tree_eq T (p.toPath_setLast_mul_homotopic x)]
      simp [mul_assoc]
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)
      rw [segmentPathAux_cons_tgt, toπ₁Tree_toPath_segmentPathAux hT]
      simp [hT, mul_assoc]

/-- A word spells the element of `A ∗_C B` given by its product. -/
@[simp] theorem equivPushoutI_toπ₁Tree_toPath_segmentPath {T : Set SerreGraph.segment.E}
    (hT : T.Nonempty) (v : SerreGraph.segment.V)
    (l : List (Σ i : SerreGraph.segment.V, (segment f g hf hg).vertexGroup i)) :
    π₁Tree.equivPushoutI f g hf hg hT ((segmentPath f g hf hg v l).toPath.toπ₁Tree T) =
      (l.map fun x => Monoid.PushoutI.of (φ := segmentMaps f g hf hg) x.1 x.2).prod := by
  simp [segmentPath, toπ₁Tree_toPath_segmentPathAux hT, map_list_prod, Function.comp_def]

private theorem not_cancels_segmentArrow {v b : SerreGraph.segment.V}
    {p : (segment f g hf hg).AlternatingPath v b}
    (h : p.length = 0 ∨ p.last ∉ (segmentMaps f g hf hg b).range) :
    ¬ p.Cancels (SerreGraph.segmentArrow b) := by
  cases p with
  | single => exact AlternatingPath.not_cancels_single _ _
  | cons q e y =>
    rw [AlternatingPath.cancels_cons_iff, αArrow_segmentArrow]
    simp only [AlternatingPath.length_cons, Nat.add_one_ne_zero, false_or,
      AlternatingPath.last_cons] at h
    exact fun h' => h h'.2

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
    by_cases h : b = v
    · subst h
      rwa [segmentPathAux_nil_self]
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne h
      rw [segmentPathAux_nil_tgt]
      exact (AlternatingPath.isReduced_cons_iff _ _ _).2
        ⟨hp, not_cancels_segmentArrow (hlast (.inr h))⟩
  | b, p, ⟨i, x⟩ :: l, hp, hlast, hhead, hc, hl => by
    rw [List.isChain_cons] at hc
    -- A letter followed by another letter of `l` is followed by one in `⟨i, x⟩ :: l` too.
    have hdrop : ∀ y ∈ l.dropLast, y ∈ (⟨i, x⟩ :: l).dropLast := fun y hy => by
      rw [List.dropLast_cons_of_ne_nil (List.ne_nil_of_mem (List.mem_of_mem_dropLast hy))]
      exact List.mem_cons_of_mem _ hy
    have hl' : ∀ y ∈ l, y.1 ≠ v ∨ y ∈ l.dropLast → y.2 ∉ (segmentMaps f g hf hg y.1).range :=
      fun y hy hy' => hl y (List.mem_cons_of_mem _ hy) (hy'.imp_right (hdrop y))
    by_cases h : i = b
    · subst h
      rw [segmentPathAux_cons_self]
      have h0 : p.length = 0 := hhead _ rfl rfl
      exact isReduced_segmentPathAux _ l (by simpa using hp) (fun _ => .inl (by simpa using h0))
        (fun y hy hy' => absurd hy' (hc.1 y hy).symm) hc.2 hl'
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)
      rw [segmentPathAux_cons_tgt]
      refine isReduced_segmentPathAux _ l ((AlternatingPath.isReduced_cons_iff _ _ _).2
        ⟨hp, not_cancels_segmentArrow (hlast (.inl (List.cons_ne_nil _ _)))⟩)
        (fun hl' => .inr ?_) (fun y hy hy' => absurd hy' (hc.1 y hy).symm) hc.2 hl'
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
  | nil => simp
  | cons x l =>
    rw [List.isChain_cons] at hc
    obtain ⟨i, x⟩ := x
    by_cases hi : i = v
    · subst hi
      rw [segmentPath, segmentPathAux_cons_self]
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
    by_cases h : b = v
    · subst h
      simp [segmentPathAux_nil_self]
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne h
      simp [segmentPathAux_nil_tgt, h]
  | b, p, ⟨i, x⟩ :: l => by
    by_cases h : i = b
    · subst h
      rw [segmentPathAux_cons_self, length_segmentPathAux_eq_zero_iff]
      simp
    · obtain rfl := SerreGraph.segment_tgt_eq_of_ne (Ne.symm h)
      rw [segmentPathAux_cons_tgt, length_segmentPathAux_eq_zero_iff]
      simp [h]

/-- A word spells a path of length zero exactly when all its letters lie in the vertex group at
the base vertex. -/
@[simp] theorem length_segmentPath_eq_zero_iff (v : SerreGraph.segment.V)
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
  -- The path spelled by `w` spells the product of `w`.
  have hprod : π₁Tree.equivPushoutI f g hf hg hT
      ((segmentPath f g hf hg v w.toList).toPath.toπ₁Tree Set.univ) =
      Monoid.PushoutI.ofCoprodI w.prod := by
    simp [Monoid.CoprodI.Word.prod, map_list_prod, Function.comp_def]
  obtain ⟨c, hc⟩ := h
  have h0 := ((isReduced_segmentPath (v := v) w.chain_ne fun x hx _ => hw x hx)
    |>.equivPushoutI_toπ₁Tree_toPath_mem_range_of_iff hT).1
    ⟨segmentMaps f g hf hg v c, by rw [Monoid.PushoutI.of_apply_eq_base, hc, hprod]⟩
  rw [length_segmentPath_eq_zero_iff] at h0
  -- All letters lie in `A_v`, so the word, alternating between the factors, has at most one.
  rcases hl : w.toList with _ | ⟨⟨i, a⟩, _ | ⟨y, l⟩⟩
  · exact Monoid.CoprodI.Word.ext hl
  · obtain rfl : i = v := h0 ⟨i, a⟩ (by simp [hl])
    refine (hw ⟨i, a⟩ (by simp [hl]) ⟨c, ?_⟩).elim
    refine Monoid.PushoutI.of_injective (segmentMaps_injective f g hf hg) i ?_
    rw [Monoid.PushoutI.of_apply_eq_base, hc, Monoid.CoprodI.Word.prod, hl]
    simp
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
  -- The path `q` runs from `tgt e` to `src e ≠ tgt e`, so it has positive length.
  have hq : q.length ≠ 0 := fun h =>
    SerreGraph.segment_isTree.isAcyclic.src_ne_tgt e (q.eq_of_length_zero h).symm
  obtain ⟨c', r, e', y, rfl⟩ := AlternatingPath.length_ne_zero_iff_eq_cons.1 hq
  refine ((AlternatingPath.isReduced_cons_iff _ _ _).1 hp).2
    ((AlternatingPath.cancels_cons_iff ..).2 ⟨?_, ?_⟩)
  · -- `rev e'` and `e` both leave `src e`, and a vertex of the segment has one outgoing dart.
    have h := congrArg Subtype.val (Subsingleton.elim
      (⟨SerreGraph.segment.rev e'.val, (SerreGraph.segment.src_rev _).trans e'.property.2⟩ :
        {d : SerreGraph.segment.E // SerreGraph.segment.src d = SerreGraph.segment.src e})
      ⟨e, rfl⟩)
    exact (SerreGraph.segment.rev_rev _).symm.trans (congrArg _ h)
  · -- The vertex other than `tgt e` is `src e`.
    have hsrc : (!SerreGraph.segment.tgt e) = SerreGraph.segment.src e := by cases e <;> rfl
    rw [hsrc] at hv
    obtain ⟨c₀, hc₀⟩ := hv y
    exact ⟨c₀, (DFunLike.congr_fun ((segment f g hf hg).αArrow_mk e) c₀).trans
      ((DFunLike.congr_fun (segment_α_eq_segmentMaps f g hf hg e) c₀).trans hc₀)⟩

/-- If the edge group of the segment maps onto the vertex group at the vertex `!v` other than
`v`, then the vertex group `A_v` is the fundamental group `π₁(𝔸, v)`: for the segment of
`C → A`, `C → B` with `C → B` onto, `A ∗_C B = A`. -/
theorem π₁.vertexHom_bijective_of_surjective_segmentMaps {v : SerreGraph.segment.V}
    (hv : Function.Surjective (segmentMaps f g hf hg (!v))) :
    Function.Bijective
      (π₁.vertexHom (Quiver.Path.nil : (segment f g hf hg).Path ⟨v⟩ ⟨v⟩)) :=
  π₁.vertexHom_nil_bijective_iff.2 fun _ hp => hp.length_eq_zero_of_surjective_segmentMaps hv

end segment

/-! ### The loop: HNN extensions -/

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] {f g : C →* G}
  {hf : Function.Injective f} {hg : Function.Injective g} {v : (SerreGraph.rose Unit).V}

open MonoidHom (ker_eq_ker_of_injective)

/-- The dart of the loop read as `t ^ u` in the HNN extension of the loop, for `u = ±1`: the dart
`((), false)` is `t` and `((), true)` is `t⁻¹`, as for `π₁Tree.equivHNNExtension`. The loop has a
single vertex `v`. -/
def loopArrow (u : ℤˣ) : v ⟶ v :=
  ⟨((), decide (u = -1)), rfl, rfl⟩

theorem loopArrow_val (u : ℤˣ) : (loopArrow (v := v) u).val = ((), decide (u = -1)) :=
  (rfl)

variable (f g hf hg) in
/-- The group `G` as the vertex group of the loop at its vertex `v`. -/
def loopVertexEquiv : G ≃* (loop f g hf hg).vertexGroup v :=
  MulEquiv.refl G

variable (f g hf hg) in
/-- The closed alternating path `h, t^{u₁}, g₁, …, t^{u_k}, g_k` of the loop spelled by the word
`h t^{u₁} g₁ ⋯ t^{u_k} g_k` of the HNN extension of the loop, as in Mathlib's
`HNNExtension.NormalWord.ReducedWord` (head `h`, list `(u₁, g₁), …`): the letter `t^{u_i}` is the
dart `loopArrow u_i`. Its element of the HNN extension is the product of the word
(`equivHNNExtension_toπ₁Tree_toPath_loopPath`). -/
def loopPath (h : G) (l : List (ℤˣ × G)) : (loop f g hf hg).AlternatingPath v v :=
  l.foldl (fun p x => p.cons (loopArrow x.1) (loopVertexEquiv f g hf hg x.2))
    (.single (loopVertexEquiv f g hf hg h))

/-- The word `h` without letters `t^{±1}` spells the path `h`. -/
@[simp] theorem loopPath_nil (h : G) :
    (loopPath f g hf hg h [] : (loop f g hf hg).AlternatingPath v v) =
      .single (loopVertexEquiv f g hf hg h) :=
  (rfl)

/-- Appending `t^u x` to a word appends the dart `loopArrow u` and the element `x` to its
path. -/
@[simp] theorem loopPath_append_singleton (h : G) (l : List (ℤˣ × G)) (u : ℤˣ) (x : G) :
    (loopPath f g hf hg h (l ++ [(u, x)]) : (loop f g hf hg).AlternatingPath v v) =
      (loopPath f g hf hg h l).cons (loopArrow u) (loopVertexEquiv f g hf hg x) :=
  List.foldl_append ..

/-- The path spelled by a word has one dart for each letter `t^{u_i}`. -/
@[simp] theorem length_loopPath (h : G) (l : List (ℤˣ × G)) :
    (loopPath f g hf hg h l : (loop f g hf hg).AlternatingPath v v).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    obtain ⟨u, y⟩ := x
    simp [ih]

private theorem equivHNNExtension_edge_loopArrow (u : ℤˣ) :
    π₁Tree.equivHNNExtension f g hf hg (π₁Tree.edge ∅ (loopArrow (v := v) u).val) =
      HNNExtension.t ^ (u : ℤ) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact (π₁Tree.equivHNNExtension_edge_false f g hf hg).trans (zpow_one _).symm
  · exact (π₁Tree.equivHNNExtension_edge_true f g hf hg).trans (zpow_neg_one _).symm

/-- A word spells the element of the HNN extension of the loop given by its product, Mathlib's
`HNNExtension.NormalWord.ReducedWord.prod`. -/
@[simp] theorem equivHNNExtension_toπ₁Tree_toPath_loopPath (h : G) (l : List (ℤˣ × G)) :
    π₁Tree.equivHNNExtension f g hf hg
        ((loopPath f g hf hg h l : (loop f g hf hg).AlternatingPath v v).toPath.toπ₁Tree ∅) =
      HNNExtension.of h *
        (l.map fun x => HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2).prod := by
  -- `π₁Tree.equivHNNExtension_of` is stated at the vertex `()` for elements of `G`, which are `v`
  -- and the elements `loopVertexEquiv y` of the vertex group at `v` up to unfolding `rose`, `loop`.
  have hof (y : G) : π₁Tree.equivHNNExtension f g hf hg
      (π₁Tree.of ∅ v (loopVertexEquiv f g hf hg y)) = HNNExtension.of y :=
    π₁Tree.equivHNNExtension_of f g hf hg y
  induction l using List.reverseRecOn with
  | nil => simp [hof]
  | append_singleton l x ih =>
    obtain ⟨u, y⟩ := x
    simp [ih, hof, equivHNNExtension_edge_loopArrow, mul_assoc]

private theorem loopVertexEquiv_mem_range_αArrow_loopArrow_iff (u : ℤˣ) (y : G) :
    loopVertexEquiv f g hf hg y ∈ ((loop f g hf hg).αArrow (loopArrow (v := v) u)).range ↔
      y ∈ HNNExtension.toSubgroup f.range g.range (-u) := by
  -- `α` of the dart `((), false)` is `g` and of `((), true)` is `f`.
  have key : ∀ c, (loop f g hf hg).αArrow (loopArrow (v := v) u) c =
      loopVertexEquiv f g hf hg (if u = 1 then g c else f c) := fun c => by
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact (DFunLike.congr_fun ((loop f g hf hg).αArrow_mk ((), false)) c).trans
        (DFunLike.congr_fun (loop_α_false f g hf hg) c)
    · exact (DFunLike.congr_fun ((loop f g hf hg).αArrow_mk ((), true)) c).trans
        (DFunLike.congr_fun (loop_α_true f g hf hg) c)
  simp only [MonoidHom.mem_range, key, EmbeddingLike.apply_eq_iff_eq]
  rcases Int.units_eq_one_or u with rfl | rfl <;> exact Iff.rfl

private theorem loopArrow_val_eq_rev_iff (u u' : ℤˣ) :
    (loopArrow (v := v) u).val = (SerreGraph.rose Unit).rev (loopArrow (v := v) u').val ↔
      u ≠ u' := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl
  · exact iff_of_false (fun h => Bool.noConfusion (congrArg Prod.snd h)) (not_not.2 rfl)
  · exact iff_of_true rfl (by decide)
  · exact iff_of_true rfl (by decide)
  · exact iff_of_false (fun h => Bool.noConfusion (congrArg Prod.snd h)) (not_not.2 rfl)

/- A letter `t^u g` followed by `t^{u'}` is a backtracking exactly when it is a pinch:
`u' = -u` and `g ∈ toSubgroup u`. -/
private theorem cancels_cons_loopArrow_iff {p : (loop f g hf hg).AlternatingPath v v} {u u' : ℤˣ}
    {y : G} : (p.cons (loopArrow u) (loopVertexEquiv f g hf hg y)).Cancels (loopArrow (v := v) u') ↔
      y ∈ HNNExtension.toSubgroup f.range g.range u ∧ u ≠ u' := by
  rw [AlternatingPath.cancels_cons_iff, loopVertexEquiv_mem_range_αArrow_loopArrow_iff,
    loopArrow_val_eq_rev_iff, and_comm]
  refine and_congr_left fun h => ?_
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl <;>
    simp_all

private theorem isReduced_foldl_loopArrow_iff (p : (loop f g hf hg).AlternatingPath v v)
    (l : List (ℤˣ × G)) :
    (l.foldl (fun p x => p.cons (loopArrow x.1) (loopVertexEquiv f g hf hg x.2)) p).IsReduced ↔
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
@[simp] theorem isReduced_loopPath_iff (h : G) (l : List (ℤˣ × G)) :
    (loopPath f g hf hg h l : (loop f g hf hg).AlternatingPath v v).IsReduced ↔
      l.IsChain fun x y => x.2 ∈ HNNExtension.toSubgroup f.range g.range x.1 → x.1 = y.1 := by
  rw [loopPath, isReduced_foldl_loopArrow_iff]
  simp

/-- **Britton's lemma for the loop.** A reduced closed alternating path of the loop spells an
element of the HNN extension `HNNExtension G (range f) (range g) φ` in `G` exactly when it has
length zero. With `isReduced_loopPath_iff` this is Britton's lemma for HNN extensions: a word
`t^{ε₁} g₁ ⋯` with a letter `t^{±1}` and no pinch does not lie in `G`, in particular is
nontrivial. -/
theorem AlternatingPath.IsReduced.equivHNNExtension_toπ₁Tree_toPath_mem_range_of_iff
    {p : (loop f g hf hg).AlternatingPath v v} (hp : p.IsReduced) :
    π₁Tree.equivHNNExtension f g hf hg (p.toPath.toπ₁Tree ∅) ∈
      (HNNExtension.of : G →* HNNExtension G f.range g.range
        (f.rangeEquivRange g (ker_eq_ker_of_injective hf hg))).range ↔
      p.length = 0 := by
  rw [← hp.toπ₁Tree_toPath_mem_range_of_iff (SerreGraph.roseTree Unit) (Set.empty_subset _)]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨loopVertexEquiv f g hf hg y, (π₁Tree.equivHNNExtension f g hf hg).injective
      ((π₁Tree.equivHNNExtension_of f g hf hg y).trans hy)⟩
  · rintro ⟨y, hy⟩
    exact ⟨(loopVertexEquiv f g hf hg).symm y,
      (π₁Tree.equivHNNExtension_of f g hf hg _).symm.trans (congrArg _ hy)⟩

/-- **Britton's lemma for HNN extensions, recovered for the loop**: a reduced word of the HNN
extension of the loop whose product lies in `G` has no letter `t^{±1}`. This is
`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`, derived here from Britton's lemma for
the loop and the path spelled by the word. -/
example (w : HNNExtension.NormalWord.ReducedWord G f.range g.range)
    (hw : w.prod (f.rangeEquivRange g (ker_eq_ker_of_injective hf hg)) ∈
      (HNNExtension.of : G →* HNNExtension G f.range g.range
        (f.rangeEquivRange g (ker_eq_ker_of_injective hf hg))).range) :
    w.toList = [] := by
  -- Read `w` as a closed path at the vertex `v` of the loop.
  suffices ∀ _ : (SerreGraph.rose Unit).V, w.toList = [] from this ()
  intro v
  -- The path spelled by `w` spells the product of `w`.
  have hprod : π₁Tree.equivHNNExtension f g hf hg
      ((loopPath f g hf hg w.head w.toList : (loop f g hf hg).AlternatingPath v v).toPath.toπ₁Tree
        ∅) = w.prod (f.rangeEquivRange g (ker_eq_ker_of_injective hf hg)) := by
    simp [HNNExtension.NormalWord.ReducedWord.prod]
  rw [← List.length_eq_zero_iff, ← length_loopPath (f := f) (g := g) (hf := hf) (hg := hg)
    (v := v) w.head, ← ((isReduced_loopPath_iff w.head w.toList).2
      w.chain).equivHNNExtension_toπ₁Tree_toPath_mem_range_of_iff, hprod]
  exact hw

end loop

/-! ### Examples for the segment -/

section Examples

/- The edge maps of the segment of identity maps are onto. -/
private theorem surjective_segmentMaps_id {A : Type*} [Group A] (b : SerreGraph.segment.V) :
    Function.Surjective (segmentMaps (MonoidHom.id A) (MonoidHom.id A) Function.injective_id
      Function.injective_id b) := by
  cases b
  · exact fun a => ⟨a, DFunLike.congr_fun (segmentMaps_false (MonoidHom.id A) (MonoidHom.id A)
      Function.injective_id Function.injective_id) a⟩
  · exact fun a => ⟨a, DFunLike.congr_fun (segmentMaps_true (MonoidHom.id A) (MonoidHom.id A)
      Function.injective_id Function.injective_id) a⟩

/-- For the segment whose edge maps are the identity maps of a common group `A`, a reduced closed
path has length zero. -/
example {A : Type*} [Group A] {v : SerreGraph.segment.V}
    {p : (segment (MonoidHom.id A) (MonoidHom.id A) Function.injective_id
      Function.injective_id).AlternatingPath v v} (hp : p.IsReduced) : p.length = 0 :=
  hp.length_eq_zero_of_surjective_segmentMaps (surjective_segmentMaps_id _)

/-- For the segment whose edge maps are the identity maps of a common group `A`, the fundamental
group is `A`. -/
example {A : Type*} [Group A] {v : SerreGraph.segment.V} :
    Function.Bijective (π₁.vertexHom (Quiver.Path.nil : (segment (MonoidHom.id A)
      (MonoidHom.id A) Function.injective_id Function.injective_id).Path ⟨v⟩ ⟨v⟩)) :=
  π₁.vertexHom_bijective_of_surjective_segmentMaps (surjective_segmentMaps_id _)

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
