/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.DualGraph.Basic
public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Flag
import Mathlib.Algebra.Group.Indicator
import Mathlib.Tactic.Abel

/-!
# The graph dual to the pattern of a map to a tree is a tree

Let `Γ` be a simple graph, `Δ` a tree and `f` a map from the vertices of `Γ` to the vertices of
`Δ`, and consider the graph `SerreGraph.dualGraph Γ Δ f` dual to the pattern of `f`, whose
vertices are the components of the complement of the pattern and whose darts are its tracks.

When the flag complex of `Γ` is connected and has trivial first cohomology with coefficients in
`ℤ/2`, every track separates the two-skeleton of the complex, so every edge separates the dual
graph, and Dunwoody concludes that the dual graph is a tree. Here the cochain counting the
crossings of the edges of `Γ` with a track is a cocycle, and a primitive of it colours the places
so that the colour changes across the track and nowhere else: the track separates the component
of the two-skeleton containing it. Since the tracks of a map to a tree are two-sided, the signed
count of crossings is a cocycle with coefficients in any abelian group, and trivial first
cohomology with coefficients in any nontrivial abelian group, such as `ℤ`, suffices. The argument
only uses the paths of `Δ` between the images of adjacent vertices of `Γ`: it applies when `Δ` is
acyclic and these images are joined.

## Main results

* `TauCeti.SerreGraph.isAcyclic_dualGraph`, `TauCeti.SerreGraph.isTree_dualGraph`: the dual graph
  is acyclic when `Δ` is acyclic, the images of adjacent vertices of `Γ` are joined in `Δ` and the
  flag complex of `Γ` has trivial first cohomology with coefficients in a nontrivial abelian
  group, and a tree when moreover `Γ` is connected.

## References

* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457: §2 (the cocycle of a track) and the construction of the dual tree in the proof of
  Theorem 5.1.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), proof of
  Proposition 2.24.
-/

public section

universe u v w

namespace TauCeti

namespace SerreGraph

variable {V : Type w} {Γ : SimpleGraph V} {Δ : SerreGraph.{u, v}} {f : V → Δ.V}

/-- The edge `(a, b)` of `Γ` has a crossing on the dart `s` of the dual graph whose dart of `Δ` is
crossed from `f a` to `x`, in the sense of `Δ.Crosses`. When `Δ` is acyclic and `x` lies between
`f a` and `f b`, so that the darts crossed from `f a` to `x` are those of the segment of the
geodesic from `f a` to `f b` before `x`, this says that the track of `s` meets the edge between `a`
and the region over `x`. -/
private def TrackBefore (s : (dualGraph Γ Δ f).E) (a b : V) (x : Δ.V) : Prop :=
  ∃ q : DualDart Γ Δ f, q.fst = a ∧ q.snd = b ∧ Δ.Crosses (f a) x q.dart ∧ q.toDart = s

/-- Two crossings of the same oriented edge of `Γ` on the same dart of the dual graph are equal:
they lie over the same dart of `Δ`. -/
private theorem DualDart.eq_of_fst_eq_of_snd_eq_of_toDart_eq {q q' : DualDart Γ Δ f}
    (hf : q.fst = q'.fst) (hs : q.snd = q'.snd) (h : q.toDart = q'.toDart) : q = q' :=
  DualDart.ext hf hs (by simpa using congrArg (dualGraphHom Γ Δ f).mapE h)

/-- The crossing of `(a, b)` on `s` before `x` and the crossing of `(b, a)` on `rev s` before `x`
cannot both exist: the reverse of the second would be the first, crossed after `x`. -/
private theorem not_trackBefore_and_trackBefore {s : (dualGraph Γ Δ f).E} {a b : V} {x : Δ.V} :
    ¬(TrackBefore s a b x ∧ TrackBefore ((dualGraph Γ Δ f).rev s) b a x) := by
  rintro ⟨⟨q, rfl, rfl, hq, rfl⟩, ⟨q', hb, ha, hq', hs⟩⟩
  -- The reverse of the second crossing is a crossing of `(a, b)` on `s`, hence is the first.
  have hrev : q'.reverse.toDart = q.toDart := by rw [← dualGraph_rev_toDart, hs, rev_rev]
  obtain rfl := DualDart.eq_of_fst_eq_of_snd_eq_of_toDart_eq (q'.reverse_fst.trans ha)
    (q'.reverse_snd.trans hb) hrev
  rw [DualDart.reverse_dart] at hq
  exact hq.not_crosses_right (crosses_rev.mpr hq')

/-- Splitting the edge `(a, b)` at a vertex `x` between `f a` and `f b`: its crossing on `s` lies
before `x`, or its reverse is the crossing of `(b, a)` on `rev s` before `x`. -/
private theorem trackBefore_iff (hΔ : Δ.IsAcyclic) {s : (dualGraph Γ Δ f).E} {a b : V} {x : Δ.V}
    (hx : Δ.IsBetween (f a) x (f b)) : TrackBefore s a b (f b) ↔
      TrackBefore s a b x ∨ TrackBefore ((dualGraph Γ Δ f).rev s) b a x := by
  refine ⟨fun ⟨q, ha, hb, hq, hs⟩ => ?_, ?_⟩
  · refine (hΔ.crosses_or_crosses hq hx.nonempty_path_left).imp (fun h => ⟨q, ha, hb, h, hs⟩)
      fun h => ⟨q.reverse, q.reverse_fst.trans hb, q.reverse_snd.trans ha, ?_, ?_⟩
    · rw [DualDart.reverse_dart, crosses_rev]
      exact h
    · rw [← dualGraph_rev_toDart, hs]
  · rintro (⟨q, rfl, rfl, -, rfl⟩ | ⟨q, rfl, rfl, -, hs⟩)
    · exact ⟨q, rfl, rfl, q.crosses, rfl⟩
    · refine ⟨q.reverse, q.reverse_fst, q.reverse_snd, ?_, ?_⟩
      · rw [DualDart.reverse_dart, crosses_rev]
        exact q.crosses
      · rw [← dualGraph_rev_toDart, hs, rev_rev]

/-- Along two sides `(a, b)` and `(a, c)` of a triangle of `Γ` (or twice the same side), a track
met along `(a, b)` before a vertex `x` is also met along `(a, c)` before `x`, as soon as `x` lies
between `f a` and `f c`; no betweenness is required on the side of `(a, b)`. -/
private theorem TrackBefore.of_isBetween {s : (dualGraph Γ Δ f).E} {a b c : V} {x : Δ.V}
    (h : TrackBefore s a b x) (hac : a = c ∨ Γ.Adj a c) (hbc : b = c ∨ Γ.Adj b c)
    (hx : Δ.IsBetween (f a) x (f c)) : TrackBefore s a c x := by
  obtain ⟨q, rfl, rfl, hq, rfl⟩ := h
  -- The edge `(q.fst, c)` is not a vertex: a dart is crossed from `f q.fst` to `x`.
  have hac : Γ.Adj q.fst c := hac.resolve_left fun h => by
    subst h
    exact not_crosses_self _ _ (isBetween_self_iff.mp hx ▸ hq)
  let q' : DualDart Γ Δ f := ⟨q.fst, c, q.dart, hac, hx.crosses_of_crosses_left hq⟩
  have hl : q.Linked q' := DualDart.linked_iff.mpr ⟨rfl, .inl rfl, hbc, .inl rfl⟩
  exact ⟨q', rfl, rfl, hq, hl.toDart_eq.symm⟩

/-- Before the target of the dart of a crossing `q`, the edge of `q` meets the tracks it meets
before the source of that dart, and the track of `q`. -/
private theorem trackBefore_tgt_iff (hΔ : Δ.IsAcyclic) (q : DualDart Γ Δ f)
    {s : (dualGraph Γ Δ f).E} : TrackBefore s q.fst q.snd (Δ.tgt q.dart) ↔
      TrackBefore s q.fst q.snd (Δ.src q.dart) ∨ s = q.toDart := by
  -- The dart of `q` is crossed from the image of `q.fst` to its own target.
  have ht : Δ.Crosses (f q.fst) (Δ.tgt q.dart) q.dart :=
    crosses_rev.mp (crosses_rev.mpr q.crosses).crosses_src
  -- The only dart crossed along the final segment, from the source to the target of the dart of
  -- `q`, is the dart of `q`.
  have hd {d : Δ.E} : Δ.Crosses (Δ.src q.dart) (Δ.tgt q.dart) d ↔ d = q.dart := by
    simpa using hΔ.crosses_iff_mem_darts (Path.isReduced_toPath Δ (Δ.dart q.dart))
  simp only [TrackBefore, hΔ.crosses_iff_crosses_or_crosses ht.isBetween_src, hd]
  -- A crossing of the edge of `q` over the dart of `q` is `q`.
  refine ⟨fun ⟨q', ha, hb, h, hs⟩ => h.imp (fun h => ⟨q', ha, hb, h, hs⟩) fun h => ?_, ?_⟩
  · rw [← hs, DualDart.ext ha hb h]
  · rintro (⟨q', ha, hb, h, hs⟩ | rfl)
    exacts [⟨q', ha, hb, .inl h, hs⟩, ⟨q, rfl, rfl, .inr rfl, rfl⟩]

/-- The track of a crossing `q` is not met along its edge before the source of its dart. -/
private theorem not_trackBefore_src (q : DualDart Γ Δ f) :
    ¬TrackBefore q.toDart q.fst q.snd (Δ.src q.dart) := by
  rintro ⟨q', ha, hb, hq', hs⟩
  obtain rfl := DualDart.eq_of_fst_eq_of_snd_eq_of_toDart_eq ha.symm hb.symm hs.symm
  exact not_crosses_self _ _ hq'.crosses_src

/-- No track is met along an edge before the image of its first end. -/
private theorem not_trackBefore_self {s : (dualGraph Γ Δ f).E} {a b : V} :
    ¬TrackBefore s a b (f a) :=
  fun ⟨_, _, _, hq, _⟩ => not_crosses_self _ _ hq

section Cochain

variable {A : Type*} [AddCommGroup A]

/-- The signed number of crossings of the edge `(a, b)` with the track of the dart `t` of the dual
graph over darts of `Δ` crossed from `f a` to `x`: `a₀` for a crossing on `t`, `-a₀` for one on
the reverse of `t`. When `Δ` is acyclic and `x` lies between `f a` and `f b`, it counts the
crossings between `a` and the region over `x`. It is the indicator of the set of darts whose
tracks are met, at `t` minus at the reverse of `t`. -/
private noncomputable def trackCount (a₀ : A) (t : (dualGraph Γ Δ f).E) (a b : V) (x : Δ.V) : A :=
  {s | TrackBefore s a b x}.indicator (fun _ => a₀) t -
    {s | TrackBefore s a b x}.indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev t)

variable (a₀ : A) (t : (dualGraph Γ Δ f).E)

/-- Splitting the count of an edge `(a, b)` at a vertex between `f a` and `f b`. -/
private theorem trackCount_eq_sub (hΔ : Δ.IsAcyclic) {a b : V} {x : Δ.V}
    (hx : Δ.IsBetween (f a) x (f b)) :
    trackCount a₀ t a b (f b) = trackCount a₀ t a b x - trackCount a₀ t b a x := by
  -- The tracks met before `f b` are those met before `x` and the reverses of those met along
  -- `(b, a)` before `x`.
  let T : Set (dualGraph Γ Δ f).E := {s | TrackBefore s b a x}
  have h : {s | TrackBefore s a b (f b)} =
      {s | TrackBefore s a b x} ∪ (dualGraph Γ Δ f).rev ⁻¹' T :=
    Set.ext fun _ => trackBefore_iff hΔ hx
  have hd : Disjoint {s | TrackBefore s a b x} ((dualGraph Γ Δ f).rev ⁻¹' T) :=
    Set.disjoint_left.mpr fun _ h₁ h₂ => not_trackBefore_and_trackBefore ⟨h₁, h₂⟩
  have hT (s) : ((dualGraph Γ Δ f).rev ⁻¹' T).indicator (fun _ => a₀) s =
      T.indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev s) :=
    Set.indicator_comp_right (g := fun _ => a₀) _
  simp only [trackCount, h, Set.indicator_union_of_disjoint hd, hT, rev_rev, T]
  abel

/-- Along two sides `(a, b)` and `(a, c)` of a triangle (or twice the same side) the counts before
a vertex between `f a` and both `f b` and `f c` agree. -/
private theorem trackCount_eq_of_isBetween {a b c : V} {x : Δ.V} (hab : a = b ∨ Γ.Adj a b)
    (hac : a = c ∨ Γ.Adj a c) (hbc : b = c ∨ Γ.Adj b c) (hxb : Δ.IsBetween (f a) x (f b))
    (hxc : Δ.IsBetween (f a) x (f c)) : trackCount a₀ t a b x = trackCount a₀ t a c x := by
  have key (s : (dualGraph Γ Δ f).E) : TrackBefore s a b x ↔ TrackBefore s a c x :=
    ⟨fun h => h.of_isBetween hac hbc hxc, fun h => h.of_isBetween hab (hbc.imp Eq.symm .symm) hxb⟩
  simp [trackCount, key]

/-- Crossing the dart of a crossing `q` changes the count along its edge by `a₀` if `q` lies on
`t`, by `-a₀` if it lies on the reverse of `t`, and not at all otherwise. -/
private theorem trackCount_tgt (hΔ : Δ.IsAcyclic) (q : DualDart Γ Δ f) :
    trackCount a₀ t q.fst q.snd (Δ.tgt q.dart) = trackCount a₀ t q.fst q.snd (Δ.src q.dart) +
      (({q.toDart} : Set _).indicator (fun _ => a₀) t -
        ({q.toDart} : Set _).indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev t)) := by
  have h : {s | TrackBefore s q.fst q.snd (Δ.tgt q.dart)} =
      {s | TrackBefore s q.fst q.snd (Δ.src q.dart)} ∪ {q.toDart} :=
    Set.ext fun _ => trackBefore_tgt_iff hΔ q
  have hd : Disjoint {s | TrackBefore s q.fst q.snd (Δ.src q.dart)} {q.toDart} :=
    Set.disjoint_singleton_right.mpr (not_trackBefore_src q)
  simp only [trackCount, h, Set.indicator_union_of_disjoint hd]
  abel

/-- The counts along the edges of `Γ` form a one-cochain of its flag complex: reversing an edge
changes the sign of its count. -/
private theorem trackCount_swap (hΔ : Δ.IsAcyclic) {a b : V} (hab : Nonempty (Δ.Path (f a) (f b))) :
    trackCount a₀ t b a (f a) = -trackCount a₀ t a b (f b) := by
  have h := trackCount_eq_sub a₀ t hΔ (isBetween_left hab)
  -- No track is met along `(a, b)` before `f a`.
  have h0 : trackCount a₀ t a b (f a) = 0 := by simp [trackCount, not_trackBefore_self]
  rw [h, h0, zero_sub, neg_neg]

/-- The cochain of the counts is a cocycle: on a triangle of `Γ`, the counts along two sides add
up to the count along the third side. -/
private theorem trackCount_add (hΔ : Δ.IsAcyclic) {a b c : V}
    (hab' : Nonempty (Δ.Path (f a) (f b))) (hac' : Nonempty (Δ.Path (f a) (f c)))
    (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hac : Γ.Adj a c) :
    trackCount a₀ t a b (f b) + trackCount a₀ t b c (f c) = trackCount a₀ t a c (f c) := by
  -- Split the three sides at the median of the images of the corners.
  obtain ⟨m, ⟨h₁, h₂, h₃⟩, -⟩ := hΔ.existsUnique_isBetween hab' hac'
  simp only [trackCount_eq_sub a₀ t hΔ h₁, trackCount_eq_sub a₀ t hΔ h₂,
    trackCount_eq_sub a₀ t hΔ h₃,
    trackCount_eq_of_isBetween a₀ t (.inr hab) (.inr hac) (.inr hbc) h₁ h₃,
    trackCount_eq_of_isBetween a₀ t (.inr hab.symm) (.inr hbc) (.inr hac) h₁.symm h₂,
    trackCount_eq_of_isBetween a₀ t (.inr hbc.symm) (.inr hac.symm) (.inr hab.symm) h₂.symm
      h₃.symm]
  abel

/-- The colour of a place: the value of `c` at its first end plus the count of its edge before
its vertex of `Δ`. -/
private noncomputable def placeColour (c : V → A) (p : DualPlace Γ Δ f) : A :=
  c p.fst + trackCount a₀ t p.fst p.snd p.pt

/-- When `c` is a primitive of the cochain of the track, exchanging the ends of a place does not
change its colour. -/
private theorem placeColour_swap (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) (p : DualPlace Γ Δ f) :
    placeColour a₀ t c p.swap = placeColour a₀ t c p := by
  obtain ⟨a, b, x, rfl | hab, hx⟩ := p <;>
    simp only [placeColour, DualPlace.swap_fst, DualPlace.swap_snd, DualPlace.swap_pt]
  rw [add_comm (c a)]
  exact sub_eq_sub_iff_add_eq_add.mp ((hc a b hab).symm.trans (trackCount_eq_sub a₀ t hΔ hx))

/-- Two places over the same vertex of `Δ` with the same first end and equal or adjacent second
ends have the same colour. -/
private theorem placeColour_eq_of_fst_eq_of_pt_eq_of_snd_eq_or_adj (c : V → A)
    {p q : DualPlace Γ Δ f} (h₁ : p.fst = q.fst) (h₂ : p.pt = q.pt)
    (h₃ : p.snd = q.snd ∨ Γ.Adj p.snd q.snd) :
    placeColour a₀ t c p = placeColour a₀ t c q := by
  obtain ⟨a, b, x, hab, hx⟩ := p
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂
  rw [placeColour, placeColour,
    trackCount_eq_of_isBetween a₀ t hab q.eq_or_adj h₃ hx q.isBetween]

/-- Linked places have the same colour. -/
private theorem placeColour_eq_of_linked (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) {p q : DualPlace Γ Δ f}
    (h : p.Linked q) : placeColour a₀ t c p = placeColour a₀ t c q := by
  obtain ⟨hpt, h₁₁, h₁₂, h₂₁, h₂₂, h | h | h | h⟩ := DualPlace.linked_iff.mp h
  · exact placeColour_eq_of_fst_eq_of_pt_eq_of_snd_eq_or_adj a₀ t c h hpt h₂₂
  · rw [← placeColour_swap a₀ t hΔ hc q]
    exact placeColour_eq_of_fst_eq_of_pt_eq_of_snd_eq_or_adj a₀ t c (by simpa using h)
      (by simpa using hpt) (by simpa using h₂₁)
  · rw [← placeColour_swap a₀ t hΔ hc p]
    exact placeColour_eq_of_fst_eq_of_pt_eq_of_snd_eq_or_adj a₀ t c (by simpa using h)
      (by simpa using hpt) (by simpa using h₁₂)
  · rw [← placeColour_swap a₀ t hΔ hc p, ← placeColour_swap a₀ t hΔ hc q]
    exact placeColour_eq_of_fst_eq_of_pt_eq_of_snd_eq_or_adj a₀ t c (by simpa using h)
      (by simpa using hpt) (by simpa using h₁₁)

/-- The colour of a vertex of the dual graph: the common colour of its places. -/
private noncomputable def vertexColour (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) :
    (dualGraph Γ Δ f).V → A :=
  DualPlace.liftVertex (placeColour a₀ t c) fun _ _ => placeColour_eq_of_linked a₀ t hΔ hc

@[simp] private theorem vertexColour_toVertex (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) (p : DualPlace Γ Δ f) :
    vertexColour a₀ t hΔ hc p.toVertex = placeColour a₀ t c p :=
  DualPlace.liftVertex_toVertex _ _ p

/-- Across a crossing `q` the colour changes by `a₀` if `q` lies on `t`, by `-a₀` if it lies on
the reverse of `t`, and not at all otherwise. -/
private theorem placeColour_reverse_srcPlace (hΔ : Δ.IsAcyclic) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a) (q : DualDart Γ Δ f) :
    placeColour a₀ t c q.reverse.srcPlace = placeColour a₀ t c q.srcPlace +
      (({q.toDart} : Set _).indicator (fun _ => a₀) t -
        ({q.toDart} : Set _).indicator (fun _ => a₀) ((dualGraph Γ Δ f).rev t)) := by
  rw [← placeColour_swap a₀ t hΔ hc]
  simp only [placeColour, DualPlace.swap_fst, DualPlace.swap_snd, DualPlace.swap_pt,
    DualDart.srcPlace_fst, DualDart.srcPlace_snd, DualDart.srcPlace_pt, DualDart.reverse_fst,
    DualDart.reverse_snd, DualDart.reverse_dart, src_rev, trackCount_tgt a₀ t hΔ q]
  abel

/-- If the cochain of the track of `t` has a primitive `c`, then every path of the dual graph from
the target of `t` back to its source passes through `t` or its reverse: the colour of the places
changes across the track of `t`, and nowhere else. -/
private theorem mem_or_rev_mem_darts_of_primitive (hΔ : Δ.IsAcyclic) (ha₀ : a₀ ≠ 0) {c : V → A}
    (hc : ∀ a b, Γ.Adj a b → trackCount a₀ t a b (f b) = c b - c a)
    (P : (dualGraph Γ Δ f).Path ((dualGraph Γ Δ f).tgt t) ((dualGraph Γ Δ f).src t)) :
    t ∈ Path.darts _ P ∨ (dualGraph Γ Δ f).rev t ∈ Path.darts _ P := by
  obtain ⟨q₀, rfl⟩ := DualDart.toDart_surjective t
  -- The colour changes across `q₀`, and across no crossing off its edge.
  have h₀ : placeColour a₀ q₀.toDart c q₀.reverse.srcPlace =
      placeColour a₀ q₀.toDart c q₀.srcPlace + a₀ := by
    have hne : (dualGraph Γ Δ f).rev q₀.toDart ≠ q₀.toDart := (dualGraph Γ Δ f).rev_ne q₀.toDart
    rw [dualGraph_rev_toDart] at hne
    simp [placeColour_reverse_srcPlace a₀ _ hΔ hc, hne]
  have h₁ {q : DualDart Γ Δ f} (h : q.toDart ≠ q₀.toDart)
      (h' : q.toDart ≠ (dualGraph Γ Δ f).rev q₀.toDart) :
      placeColour a₀ q₀.toDart c q.reverse.srcPlace = placeColour a₀ q₀.toDart c q.srcPlace := by
    rw [dualGraph_rev_toDart] at h'
    simp [placeColour_reverse_srcPlace a₀ _ hΔ hc, Ne.symm h, Ne.symm h']
  -- Leaving the set of vertices of a colour other than that of the source place of `q₀`, the path
  -- crosses a dart which changes the colour.
  let R := {v | vertexColour a₀ q₀.toDart hΔ hc v = placeColour a₀ q₀.toDart c q₀.srcPlace}
  obtain ⟨e, he, hs, ht⟩ := Path.exists_boundary_dart _ P Rᶜ (by simpa [R, h₀] using ha₀)
    (by simp [R])
  suffices e = q₀.toDart ∨ e = (dualGraph Γ Δ f).rev q₀.toDart by
    obtain rfl | rfl := this
    exacts [.inl he, .inr he]
  induction e using dualGraph_dart_cases with | crossing q => ?_
  by_contra! hP
  simp only [R, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, dualGraph_src_toDart,
    dualGraph_tgt_toDart, vertexColour_toVertex, h₁ hP.1 hP.2] at hs ht
  exact hs ht

end Cochain

/-- The graph dual to the pattern of a map to an acyclic graph is acyclic when the images of
adjacent vertices of `Γ` are joined and the flag complex of `Γ` has trivial first cohomology with
coefficients in some nontrivial abelian group `A`, such as `ℤ/2` (as in Dunwoody) or `ℤ`. -/
theorem isAcyclic_dualGraph {A : Type*} [AddCommGroup A] [Nontrivial A] (hΔ : Δ.IsAcyclic)
    (hf : ∀ ⦃a b⦄, Γ.Adj a b → Nonempty (Δ.Path (f a) (f b)))
    (hac : Γ.HasTrivialFlagFirstCohomology A) : (dualGraph Γ Δ f).IsAcyclic := by
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  refine (isAcyclic_iff_forall_mem_or_rev_mem_darts _).mpr fun t P => ?_
  -- The cochain of the track of `t` has a primitive.
  obtain ⟨c, hc⟩ := hac.exists_eq_sub (z := fun a b => trackCount a₀ t a b (f b))
    (fun _ _ h => trackCount_swap a₀ t hΔ (hf h))
    fun _ _ _ h₁ h₂ h₃ => trackCount_add a₀ t hΔ (hf h₁) (hf h₃) h₁ h₂ h₃
  exact mem_or_rev_mem_darts_of_primitive a₀ t hΔ ha₀ hc P

/-- **The dual graph is a tree** (Dunwoody). If `Γ` is a connected graph whose flag complex has
trivial first cohomology with coefficients in a nontrivial abelian group `A`, such as `ℤ/2`, and
`f` maps adjacent vertices of `Γ` to vertices joined in an acyclic graph `Δ` (for instance, `Δ` is
a tree), then the graph dual to the pattern of `f` is a tree. -/
theorem isTree_dualGraph {A : Type*} [AddCommGroup A] [Nontrivial A] (hΔ : Δ.IsAcyclic)
    (hf : ∀ ⦃a b⦄, Γ.Adj a b → Nonempty (Δ.Path (f a) (f b))) (hΓ : Γ.Connected)
    (hac : Γ.HasTrivialFlagFirstCohomology A) : (dualGraph Γ Δ f).IsTree :=
  (isTree_iff _).mpr ⟨dualGraph_connected hf hΓ, isAcyclic_dualGraph hΔ hf hac⟩

end SerreGraph

end TauCeti
