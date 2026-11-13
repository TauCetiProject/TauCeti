/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Walk

/-!
# Trimming directed walks between terminal sets

A directed walk whose source lies in `A` and whose target lies in `B` contains a contiguous
segment from its last vertex in `A` to the first vertex in `B` at or after it, whose internal
vertices avoid both terminal sets. This file packages that extraction as the operation
`TauCeti.ArrowWalk.trimToSets`. The trimmed walk visits only vertices and traverses only arrows of
the original walk, so trimming preserves vertex-disjoint and arrow-disjoint families, and it
trims a path to a path.

The operation permits a walk of length zero when the terminal sets overlap. This is the convention
needed when auxiliary source and sink constructions reduce set-to-set path problems to problems
with two distinguished terminals.

## Main definitions

* `TauCeti.ArrowWalk.trimToSets`: trim a directed walk to a walk between two terminal sets.
* `TauCeti.ArrowWalk.trimToSetsSource` and `TauCeti.ArrowWalk.trimToSetsTarget`: the endpoints of
  the trimmed walk.

## Main results

* `TauCeti.ArrowWalk.exists_eq_comp_trimToSets_comp`: the trimmed walk is a contiguous segment of
  the original walk, beginning at its last vertex in `A`.
* `TauCeti.ArrowWalk.notMem_of_mem_dropLast_vertices_trimToSets`: the trimmed walk ends at the
  first vertex in `B` at or after its source.
* `TauCeti.ArrowWalk.notMem_of_mem_tail_vertices_trimToSets`: the trimmed walk contains no vertex
  of `A` after its source.
* `TauCeti.ArrowWalk.isPath_trimToSets`: trimming a path produces a path.
* `TauCeti.ArrowWalk.vertices_trimToSets_subset` and
  `TauCeti.ArrowWalk.arrows_trimToSets_subset`: trimming introduces no vertices or arrows.
* `TauCeti.ArrowWalk.notMem_and_notMem_of_mem_vertices_trimToSets`: internal vertices of the
  trimmed walk lie in neither terminal set.
* `TauCeti.ArrowWalk.length_trimToSets_eq_zero_iff` and
  `TauCeti.ArrowWalk.trimToSetsSource_eq_trimToSetsTarget_iff_trimToSetsSource_mem`: the trimmed
  walk has length zero exactly when its source already belongs to both terminal sets.
* `TauCeti.ArrowWalk.trimToSets_heq_of_eq_comp_comp`: the trimmed walk is the unique such
  segment, so any segment with these properties identifies it.
* `TauCeti.ArrowWalk.trimToSets_heq_of_forall_notMem`: trimming leaves a walk unchanged when no
  vertex after its first lies in `A` and no vertex before its last lies in `B`; in particular,
  trimming is idempotent.
* `TauCeti.ArrowWalk.pairwise_disjoint_vertices_trimToSets` and
  `TauCeti.ArrowWalk.pairwise_disjoint_arrows_trimToSets`: trimming preserves disjoint families.

## References

* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapter 9.
-/

public section

namespace TauCeti

namespace ArrowWalk

universe u v

variable {V : Type u} {Q : V → V → Type v} {A B : Set V} {s t : V}

private noncomputable def trimToSetsData (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    {x : Σ a, Σ b, ArrowWalk Q a b //
      x.1 ∈ A ∧ x.2.1 ∈ B ∧
        (∃ (before : ArrowWalk Q s x.1) (after : ArrowWalk Q x.2.1 t),
          p = before.comp (x.2.2.comp after) ∧ ∀ z ∈ (x.2.2.comp after).vertices.tail, z ∉ A) ∧
        ∀ z ∈ x.2.2.vertices.dropLast, z ∉ B} :=
  Classical.choice <| by
    obtain ⟨a, ha, b, hb, q, before, after, hfactor, hA, hB⟩ :=
      p.exists_eq_comp_comp_interior_notMem hs ht
    exact ⟨⟨⟨a, b, q⟩, ha, hb, ⟨before, after, hfactor, hA⟩, hB⟩⟩

/-- The source of the walk obtained by trimming `p` between the terminal sets `A` and `B`. -/
noncomputable def trimToSetsSource (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) : V :=
  (trimToSetsData p hs ht).1.1

/-- The target of the walk obtained by trimming `p` between the terminal sets `A` and `B`. -/
noncomputable def trimToSetsTarget (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) : V :=
  (trimToSetsData p hs ht).1.2.1

/-- Trim a directed walk from a vertex of `A` to a vertex of `B` to its segment from its last
vertex in `A` to the first vertex in `B` at or after it. The internal vertices of the result lie
in neither terminal set. -/
noncomputable def trimToSets (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    ArrowWalk Q (p.trimToSetsSource hs ht) (p.trimToSetsTarget hs ht) :=
  (trimToSetsData p hs ht).1.2.2

/-- The source of a walk trimmed between `A` and `B` belongs to `A`. -/
@[simp]
theorem trimToSetsSource_mem (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    p.trimToSetsSource hs ht ∈ A :=
  (trimToSetsData p hs ht).2.1

/-- The target of a walk trimmed between `A` and `B` belongs to `B`. -/
@[simp]
theorem trimToSetsTarget_mem (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    p.trimToSetsTarget hs ht ∈ B :=
  (trimToSetsData p hs ht).2.2.1

/-- A trimmed walk is a contiguous segment of the original walk, beginning at its last vertex in
`A`. -/
theorem exists_eq_comp_trimToSets_comp (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    ∃ (before : ArrowWalk Q s (p.trimToSetsSource hs ht))
      (after : ArrowWalk Q (p.trimToSetsTarget hs ht) t),
      p = before.comp ((p.trimToSets hs ht).comp after) ∧
        ∀ z ∈ ((p.trimToSets hs ht).comp after).vertices.tail, z ∉ A :=
  (trimToSetsData p hs ht).2.2.2.1

/-- A walk trimmed between `A` and `B` ends at its first vertex in `B`. -/
theorem notMem_of_mem_dropLast_vertices_trimToSets (p : ArrowWalk Q s t) (hs : s ∈ A)
    (ht : t ∈ B) {z : V} (hz : z ∈ (p.trimToSets hs ht).vertices.dropLast) : z ∉ B :=
  (trimToSetsData p hs ht).2.2.2.2 z hz

/-- A walk trimmed between `A` and `B` contains no vertex of `A` after its source. -/
theorem notMem_of_mem_tail_vertices_trimToSets (p : ArrowWalk Q s t) (hs : s ∈ A)
    (ht : t ∈ B) {z : V} (hz : z ∈ (p.trimToSets hs ht).vertices.tail) : z ∉ A :=
  let ⟨_, after, _, hA⟩ := p.exists_eq_comp_trimToSets_comp hs ht
  hA z (tail_vertices_subset_tail_vertices_comp _ after hz)

/-- Trimming a path between terminal sets produces a path. -/
@[simp]
theorem isPath_trimToSets {p : ArrowWalk Q s t} (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) :
    (p.trimToSets hs ht).IsPath := by
  obtain ⟨before, after, h, -⟩ := p.exists_eq_comp_trimToSets_comp hs ht
  rw [h] at hp
  exact hp.of_comp_right.of_comp_left

/-- A trimmed walk visits only vertices of the original walk. -/
theorem vertices_trimToSets_subset (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    (p.trimToSets hs ht).vertices ⊆ p.vertices :=
  let ⟨_, _, h, _⟩ := p.exists_eq_comp_trimToSets_comp hs ht
  vertices_subset_of_eq_comp_comp h

/-- A trimmed walk traverses only arrows of the original walk. -/
theorem arrows_trimToSets_subset (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    (p.trimToSets hs ht).arrows ⊆ p.arrows :=
  let ⟨_, _, h, _⟩ := p.exists_eq_comp_trimToSets_comp hs ht
  arrows_subset_of_eq_comp_comp h

/-- The source of a trimmed walk is a vertex of the original walk. -/
@[simp]
theorem trimToSetsSource_mem_vertices (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    p.trimToSetsSource hs ht ∈ p.vertices :=
  p.vertices_trimToSets_subset hs ht (@Quiver.Path.start_mem_vertices V ⟨Q⟩ _ _ _)

/-- The target of a trimmed walk is a vertex of the original walk. -/
@[simp]
theorem trimToSetsTarget_mem_vertices (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    p.trimToSetsTarget hs ht ∈ p.vertices :=
  p.vertices_trimToSets_subset hs ht (@Quiver.Path.end_mem_vertices V ⟨Q⟩ _ _ _)

/-- Apart from its source, a walk trimmed between `A` and `B` contains no vertex of `A`. -/
theorem notMem_of_mem_vertices_trimToSets_of_ne_trimToSetsSource (p : ArrowWalk Q s t)
    (hs : s ∈ A) (ht : t ∈ B) {z : V} (hz : z ∈ (p.trimToSets hs ht).vertices)
    (hza : z ≠ p.trimToSetsSource hs ht) : z ∉ A :=
  let ⟨_, after, _, hA⟩ := p.exists_eq_comp_trimToSets_comp hs ht
  hA z (tail_vertices_subset_tail_vertices_comp _ after (mem_tail_vertices_of_ne hz hza))

/-- Apart from its target, a walk trimmed between `A` and `B` contains no vertex of `B`. -/
theorem notMem_of_mem_vertices_trimToSets_of_ne_trimToSetsTarget (p : ArrowWalk Q s t)
    (hs : s ∈ A) (ht : t ∈ B) {z : V} (hz : z ∈ (p.trimToSets hs ht).vertices)
    (hzb : z ≠ p.trimToSetsTarget hs ht) : z ∉ B :=
  p.notMem_of_mem_dropLast_vertices_trimToSets hs ht (mem_dropLast_vertices_of_ne hz hzb)

/-- Every non-endpoint vertex of a walk trimmed between `A` and `B` lies in neither terminal
set. -/
theorem notMem_and_notMem_of_mem_vertices_trimToSets (p : ArrowWalk Q s t) (hs : s ∈ A)
    (ht : t ∈ B) {z : V} (hz : z ∈ (p.trimToSets hs ht).vertices)
    (hza : z ≠ p.trimToSetsSource hs ht) (hzb : z ≠ p.trimToSetsTarget hs ht) :
    z ∉ A ∧ z ∉ B :=
  ⟨p.notMem_of_mem_vertices_trimToSets_of_ne_trimToSetsSource hs ht hz hza,
    p.notMem_of_mem_vertices_trimToSets_of_ne_trimToSetsTarget hs ht hz hzb⟩

/-- The endpoints of a trimmed walk coincide exactly when its source also belongs to the right
terminal set. -/
theorem trimToSetsSource_eq_trimToSetsTarget_iff_trimToSetsSource_mem (p : ArrowWalk Q s t)
    (hs : s ∈ A) (ht : t ∈ B) :
    p.trimToSetsSource hs ht = p.trimToSetsTarget hs ht ↔ p.trimToSetsSource hs ht ∈ B := by
  refine ⟨fun h ↦ h ▸ p.trimToSetsTarget_mem hs ht, fun h ↦ ?_⟩
  by_contra hne
  exact p.notMem_of_mem_vertices_trimToSets_of_ne_trimToSetsTarget hs ht
    (@Quiver.Path.start_mem_vertices V ⟨Q⟩ _ _ _) hne h

/-- The endpoints of a trimmed walk coincide exactly when its target also belongs to the left
terminal set. -/
theorem trimToSetsSource_eq_trimToSetsTarget_iff_trimToSetsTarget_mem (p : ArrowWalk Q s t)
    (hs : s ∈ A) (ht : t ∈ B) :
    p.trimToSetsSource hs ht = p.trimToSetsTarget hs ht ↔ p.trimToSetsTarget hs ht ∈ A := by
  refine ⟨fun h ↦ h ▸ p.trimToSetsSource_mem hs ht, fun h ↦ ?_⟩
  by_contra hne
  exact p.notMem_of_mem_vertices_trimToSets_of_ne_trimToSetsSource hs ht
    (@Quiver.Path.end_mem_vertices V ⟨Q⟩ _ _ _) (Ne.symm hne) h

/-- A trimmed walk has length zero exactly when its endpoints coincide. -/
theorem length_trimToSets_eq_zero_iff (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B) :
    (p.trimToSets hs ht).length = 0 ↔ p.trimToSetsSource hs ht = p.trimToSetsTarget hs ht := by
  refine ⟨@Quiver.Path.eq_of_length_zero V ⟨Q⟩ _ _ _, fun h ↦ ?_⟩
  by_contra hlen
  exact p.notMem_of_mem_dropLast_vertices_trimToSets hs ht (start_mem_dropLast_vertices hlen)
    (h ▸ p.trimToSetsTarget_mem hs ht)

private theorem trimToSets_spec_of_eq_comp_comp {a b : V} {p : ArrowWalk Q s t}
    (hs : s ∈ A) (ht : t ∈ B) {before : ArrowWalk Q s a} {q : ArrowWalk Q a b}
    {after : ArrowWalk Q b t} (h : p = before.comp (q.comp after)) (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ z ∈ (q.comp after).vertices.tail, z ∉ A) (hB : ∀ z ∈ q.vertices.dropLast, z ∉ B) :
    p.trimToSetsSource hs ht = a ∧ p.trimToSetsTarget hs ht = b ∧ HEq (p.trimToSets hs ht) q :=
  let ⟨_, _, h', hA'⟩ := p.exists_eq_comp_trimToSets_comp hs ht
  eq_comp_comp_inj_of_forall_notMem h' h (p.trimToSetsSource_mem hs ht) ha
    (p.trimToSetsTarget_mem hs ht) hb hA' hA
    (fun _ ↦ p.notMem_of_mem_dropLast_vertices_trimToSets hs ht) hB

/-- The source of a trimmed walk is the start of any segment of the walk that begins at its last
vertex in `A` and ends at the first vertex in `B` at or after it. -/
theorem trimToSetsSource_eq_of_eq_comp_comp {a b : V} {p : ArrowWalk Q s t} (hs : s ∈ A)
    (ht : t ∈ B) {before : ArrowWalk Q s a} {q : ArrowWalk Q a b} {after : ArrowWalk Q b t}
    (h : p = before.comp (q.comp after)) (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ z ∈ (q.comp after).vertices.tail, z ∉ A) (hB : ∀ z ∈ q.vertices.dropLast, z ∉ B) :
    p.trimToSetsSource hs ht = a :=
  (trimToSets_spec_of_eq_comp_comp hs ht h ha hb hA hB).1

/-- The target of a trimmed walk is the end of any segment of the walk that begins at its last
vertex in `A` and ends at the first vertex in `B` at or after it. -/
theorem trimToSetsTarget_eq_of_eq_comp_comp {a b : V} {p : ArrowWalk Q s t} (hs : s ∈ A)
    (ht : t ∈ B) {before : ArrowWalk Q s a} {q : ArrowWalk Q a b} {after : ArrowWalk Q b t}
    (h : p = before.comp (q.comp after)) (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ z ∈ (q.comp after).vertices.tail, z ∉ A) (hB : ∀ z ∈ q.vertices.dropLast, z ∉ B) :
    p.trimToSetsTarget hs ht = b :=
  (trimToSets_spec_of_eq_comp_comp hs ht h ha hb hA hB).2.1

/-- A trimmed walk is any segment of the walk that begins at its last vertex in `A` and ends at
the first vertex in `B` at or after it. -/
theorem trimToSets_heq_of_eq_comp_comp {a b : V} {p : ArrowWalk Q s t} (hs : s ∈ A)
    (ht : t ∈ B) {before : ArrowWalk Q s a} {q : ArrowWalk Q a b} {after : ArrowWalk Q b t}
    (h : p = before.comp (q.comp after)) (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ z ∈ (q.comp after).vertices.tail, z ∉ A) (hB : ∀ z ∈ q.vertices.dropLast, z ∉ B) :
    HEq (p.trimToSets hs ht) q :=
  (trimToSets_spec_of_eq_comp_comp hs ht h ha hb hA hB).2.2

/-- Trimming keeps the source of a walk none of whose vertices after the first lies in `A` and
none of whose vertices before the last lies in `B`. -/
theorem trimToSetsSource_eq_of_forall_notMem {p : ArrowWalk Q s t} (hs : s ∈ A) (ht : t ∈ B)
    (hA : ∀ z ∈ p.vertices.tail, z ∉ A) (hB : ∀ z ∈ p.vertices.dropLast, z ∉ B) :
    p.trimToSetsSource hs ht = s :=
  trimToSetsSource_eq_of_eq_comp_comp hs ht (after := nil t)
    (@Quiver.Path.nil_comp V ⟨Q⟩ _ _ p).symm hs ht hA hB

/-- Trimming keeps the target of a walk none of whose vertices after the first lies in `A` and
none of whose vertices before the last lies in `B`. -/
theorem trimToSetsTarget_eq_of_forall_notMem {p : ArrowWalk Q s t} (hs : s ∈ A) (ht : t ∈ B)
    (hA : ∀ z ∈ p.vertices.tail, z ∉ A) (hB : ∀ z ∈ p.vertices.dropLast, z ∉ B) :
    p.trimToSetsTarget hs ht = t :=
  trimToSetsTarget_eq_of_eq_comp_comp hs ht (after := nil t)
    (@Quiver.Path.nil_comp V ⟨Q⟩ _ _ p).symm hs ht hA hB

/-- Trimming leaves unchanged a walk none of whose vertices after the first lies in `A` and none
of whose vertices before the last lies in `B`. -/
theorem trimToSets_heq_of_forall_notMem {p : ArrowWalk Q s t} (hs : s ∈ A) (ht : t ∈ B)
    (hA : ∀ z ∈ p.vertices.tail, z ∉ A) (hB : ∀ z ∈ p.vertices.dropLast, z ∉ B) :
    HEq (p.trimToSets hs ht) p :=
  trimToSets_heq_of_eq_comp_comp hs ht (after := nil t)
    (@Quiver.Path.nil_comp V ⟨Q⟩ _ _ p).symm hs ht hA hB

/-- A trimmed walk whose source also belongs to the right terminal set is the walk of length
zero at that source. -/
theorem trimToSets_heq_nil_of_trimToSetsSource_mem (p : ArrowWalk Q s t) (hs : s ∈ A)
    (ht : t ∈ B) (h : p.trimToSetsSource hs ht ∈ B) :
    HEq (p.trimToSets hs ht) (nil (p.trimToSetsSource hs ht) : ArrowWalk Q _ _) :=
  heq_nil_of_length_eq_zero <| (p.length_trimToSets_eq_zero_iff hs ht).2 <|
    (p.trimToSetsSource_eq_trimToSetsTarget_iff_trimToSetsSource_mem hs ht).2 h

/-- Trimming the walk of length zero at a vertex of both terminal sets keeps its source. -/
@[simp]
theorem trimToSetsSource_nil (hs : s ∈ A) (hs' : s ∈ B) :
    (nil s : ArrowWalk Q s s).trimToSetsSource hs hs' = s :=
  trimToSetsSource_eq_of_forall_notMem hs hs' (by simp) (by simp)

/-- Trimming the walk of length zero at a vertex of both terminal sets keeps its target. -/
@[simp]
theorem trimToSetsTarget_nil (hs : s ∈ A) (hs' : s ∈ B) :
    (nil s : ArrowWalk Q s s).trimToSetsTarget hs hs' = s :=
  trimToSetsTarget_eq_of_forall_notMem hs hs' (by simp) (by simp)

/-- Trimming the walk of length zero at a vertex of both terminal sets leaves it unchanged. -/
@[simp]
theorem trimToSets_nil_heq (hs : s ∈ A) (hs' : s ∈ B) :
    HEq ((nil s : ArrowWalk Q s s).trimToSets hs hs') (nil s : ArrowWalk Q s s) :=
  trimToSets_heq_of_forall_notMem hs hs' (by simp) (by simp)


/-- Trimming an already trimmed walk keeps its source. -/
@[simp]
theorem trimToSetsSource_trimToSets (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B)
    (hs' : p.trimToSetsSource hs ht ∈ A) (ht' : p.trimToSetsTarget hs ht ∈ B) :
    (p.trimToSets hs ht).trimToSetsSource hs' ht' = p.trimToSetsSource hs ht :=
  trimToSetsSource_eq_of_forall_notMem hs' ht'
    (fun _ ↦ p.notMem_of_mem_tail_vertices_trimToSets hs ht)
    fun _ ↦ p.notMem_of_mem_dropLast_vertices_trimToSets hs ht

/-- Trimming an already trimmed walk keeps its target. -/
@[simp]
theorem trimToSetsTarget_trimToSets (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B)
    (hs' : p.trimToSetsSource hs ht ∈ A) (ht' : p.trimToSetsTarget hs ht ∈ B) :
    (p.trimToSets hs ht).trimToSetsTarget hs' ht' = p.trimToSetsTarget hs ht :=
  trimToSetsTarget_eq_of_forall_notMem hs' ht'
    (fun _ ↦ p.notMem_of_mem_tail_vertices_trimToSets hs ht)
    fun _ ↦ p.notMem_of_mem_dropLast_vertices_trimToSets hs ht

/-- Trimming is idempotent. -/
@[simp]
theorem trimToSets_trimToSets_heq (p : ArrowWalk Q s t) (hs : s ∈ A) (ht : t ∈ B)
    (hs' : p.trimToSetsSource hs ht ∈ A) (ht' : p.trimToSetsTarget hs ht ∈ B) :
    HEq ((p.trimToSets hs ht).trimToSets hs' ht') (p.trimToSets hs ht) :=
  trimToSets_heq_of_forall_notMem hs' ht' (fun _ ↦ p.notMem_of_mem_tail_vertices_trimToSets hs ht)
    fun _ ↦ p.notMem_of_mem_dropLast_vertices_trimToSets hs ht

/-- Trimming two vertex-disjoint walks preserves their vertex-disjointness. -/
theorem disjoint_vertices_trimToSets {s₁ t₁ s₂ t₂ : V} {p : ArrowWalk Q s₁ t₁}
    {q : ArrowWalk Q s₂ t₂} (h : p.vertices.Disjoint q.vertices) (hs₁ : s₁ ∈ A) (ht₁ : t₁ ∈ B)
    (hs₂ : s₂ ∈ A) (ht₂ : t₂ ∈ B) :
    (p.trimToSets hs₁ ht₁).vertices.Disjoint (q.trimToSets hs₂ ht₂).vertices :=
  fun _ hz₁ hz₂ ↦ h (p.vertices_trimToSets_subset hs₁ ht₁ hz₁)
    (q.vertices_trimToSets_subset hs₂ ht₂ hz₂)

/-- Trimming two arrow-disjoint walks preserves their arrow-disjointness. -/
theorem disjoint_arrows_trimToSets {s₁ t₁ s₂ t₂ : V} {p : ArrowWalk Q s₁ t₁}
    {q : ArrowWalk Q s₂ t₂} (h : p.arrows.Disjoint q.arrows) (hs₁ : s₁ ∈ A) (ht₁ : t₁ ∈ B)
    (hs₂ : s₂ ∈ A) (ht₂ : t₂ ∈ B) :
    (p.trimToSets hs₁ ht₁).arrows.Disjoint (q.trimToSets hs₂ ht₂).arrows :=
  fun _ ha₁ ha₂ ↦ h (p.arrows_trimToSets_subset hs₁ ht₁ ha₁)
    (q.arrows_trimToSets_subset hs₂ ht₂ ha₂)

/-- Trimming a pairwise vertex-disjoint family of walks preserves pairwise vertex-disjointness. -/
theorem pairwise_disjoint_vertices_trimToSets {I : Type*} {s t : I → V}
    {p : ∀ i, ArrowWalk Q (s i) (t i)}
    (h : Pairwise fun i j ↦ (p i).vertices.Disjoint (p j).vertices)
    (hs : ∀ i, s i ∈ A) (ht : ∀ i, t i ∈ B) :
    Pairwise fun i j ↦ ((p i).trimToSets (hs i) (ht i)).vertices.Disjoint
      ((p j).trimToSets (hs j) (ht j)).vertices :=
  fun _ _ hij ↦ disjoint_vertices_trimToSets (h hij) _ _ _ _

/-- Trimming a pairwise arrow-disjoint family of walks preserves pairwise arrow-disjointness. -/
theorem pairwise_disjoint_arrows_trimToSets {I : Type*} {s t : I → V}
    {p : ∀ i, ArrowWalk Q (s i) (t i)}
    (h : Pairwise fun i j ↦ (p i).arrows.Disjoint (p j).arrows)
    (hs : ∀ i, s i ∈ A) (ht : ∀ i, t i ∈ B) :
    Pairwise fun i j ↦ ((p i).trimToSets (hs i) (ht i)).arrows.Disjoint
      ((p j).trimToSets (hs j) (ht j)).arrows :=
  fun _ _ hij ↦ disjoint_arrows_trimToSets (h hij) _ _ _ _

end ArrowWalk

end TauCeti
