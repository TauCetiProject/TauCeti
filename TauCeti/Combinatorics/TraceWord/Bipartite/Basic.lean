/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import TauCeti.Data.Fin.Sum
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Sum

/-!
# Vertex and edge counts of bipartite trace words

The trace of `(X Xᴴ) ^ k` for a rectangular matrix `X` expands over the closed words

`u 0, v 0, u 1, v 1, …, u (k - 1), v (k - 1), u 0`

alternating between row indices `u : Fin k → α` and column indices `v : Fin k → β`
(`Matrix.trace_mul_conjTranspose_pow_eq_sum_prod`). Such a word has `2 * k` steps. The step
from `u t` to `v t` reads the entry of `X` at `(u t, v t)`, and the step from `v t` back to
`u (t + 1)` reads the entry at `(u (t + 1), v t)`; `TauCeti.bipartiteEdge u v` records these
positions, which are the edges of the bipartite graph traversed by the word.

A connected graph has at most one more vertex than edges, so a bipartite word visits at most
one more row and column index than it reads positions. When no position is read exactly once,
the word reads at most `k` positions, and hence visits at most `k + 1` row and column indices in
total. In the moment method for sample covariance matrices these are the words left in the
expected trace expansion of a matrix with independent centred entries, and the bound controls
the number of their labellings by `p` row and `n` column indices.

The same word is also a cyclic word `TauCeti.bipartiteWord u v : Fin (2 * k) → α ⊕ β` on the
disjoint union of the row and column indices, indexed through the interleaving
`TauCeti.finSumFinInterleaveEquiv`, which places `u` at the even positions and `v` at the odd
positions. Its unordered edges are the positions `bipartiteEdge u v` read by its steps, so the
vertex and edge counts of cyclic trace words in `TauCeti.Combinatorics.TraceWord.Counting` apply to
bipartite words.

An open bipartite path `TauCeti.bipartitePath` interleaves the row and column vertices and
appends a terminal row vertex. It has no immediate reversals exactly when consecutive row
vertices and consecutive column vertices differ.

## Main declarations

* `TauCeti.bipartiteEdge`: the positions read by the steps of a bipartite word.
* `TauCeti.card_image_add_card_image_le_card_image_bipartiteEdge_add_one`: a bipartite word
  visits at most one more row and column index than it reads positions.
* `TauCeti.card_image_bipartiteEdge_le_of_no_singleton_edge`: a bipartite word of half-length
  `k` reading no position exactly once reads at most `k` positions.
* `TauCeti.card_image_add_card_image_le_add_one_of_no_singleton_edge`: such a word visits at
  most `k + 1` row and column indices.
* `TauCeti.bipartiteWord`: the bipartite word as a cyclic word on `α ⊕ β`, which determines
  `u` and `v` (`TauCeti.bipartiteWord_inj`).
* `TauCeti.bipartitePath`: the open alternating word with one extra row vertex.
* `TauCeti.BipartiteNonbacktracking`: the condition that reversals are allowed only at
  joins of the constituent walks of a cyclic bipartite word.
* `TauCeti.sym2_bipartiteWord`: its unordered edges are the positions read by its steps.
* `TauCeti.card_image_bipartiteWord`: it visits `#(image u) + #(image v)` vertices.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a
  review*, Statistica Sinica 9 (1999), §2.2.1, the moment method for sample covariance matrices.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, the counting argument for the moment method.
* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, second
  edition, Springer (2010), §3.1.2: the graphs of the moment method for sample covariance
  matrices.
-/

public section

open Finset

namespace TauCeti

variable {α β : Type*} {k : ℕ}

/-- The positions read by the steps of the closed bipartite word
`u 0, v 0, u 1, v 1, …, v (k - 1), u 0`: the step `inl t` from `u t` to `v t` reads `(u t, v t)`
and the step `inr t` from `v t` to `u (t + 1)` reads `(u (t + 1), v t)`, the row indices being
read cyclically. -/
def bipartiteEdge (u : Fin k → α) (v : Fin k → β) : Fin k ⊕ Fin k → α × β :=
  Sum.elim (fun t ↦ (u t, v t)) fun t ↦ (u (finRotate k t), v t)

/-- The edge map as a function on the two kinds of steps. -/
theorem bipartiteEdge_def (u : Fin k → α) (v : Fin k → β) :
    bipartiteEdge u v = Sum.elim (fun t ↦ (u t, v t))
      (fun t ↦ (u (finRotate k t), v t)) := (rfl)

@[simp, grind =]
theorem bipartiteEdge_inl (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteEdge u v (.inl t) = (u t, v t) := by
  simp [bipartiteEdge]

@[simp, grind =]
theorem bipartiteEdge_inr (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteEdge u v (.inr t) = (u (finRotate k t), v t) := by
  simp [bipartiteEdge]

/-- The closed bipartite word `u 0 → v 0 → u 1 → v 1 → ⋯ → u (k - 1) → v (k - 1) → u 0` on
`α ⊕ β`, as a cyclic word of length `2 * k`: its even positions visit `u` and its odd positions
visit `v`. -/
def bipartiteWord (u : Fin k → α) (v : Fin k → β) (s : Fin (2 * k)) : α ⊕ β :=
  Sum.map u v ((finSumFinInterleaveEquiv k).symm s)

@[simp]
theorem bipartiteWord_inl (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteWord u v (finSumFinInterleaveEquiv k (.inl t)) = .inl (u t) := by
  simp [bipartiteWord]

@[simp]
theorem bipartiteWord_inr (u : Fin k → α) (v : Fin k → β) (t : Fin k) :
    bipartiteWord u v (finSumFinInterleaveEquiv k (.inr t)) = .inr (v t) := by
  simp [bipartiteWord]

/-- The labels available to a bipartite trace word at time `t`: rows at even times and columns
at odd times. -/
def bipartiteVertexFinset [Fintype α] [Fintype β] (t : ℕ) : Finset (α ⊕ β) :=
  if t % 2 = 0 then (univ : Finset α).map .inl else (univ : Finset β).map .inr

/-- The vertex finset is the row finset at an even time and the column finset at an odd time. -/
theorem bipartiteVertexFinset_def [Fintype α] [Fintype β] (t : ℕ) :
    bipartiteVertexFinset (α := α) (β := β) t =
      if t % 2 = 0 then (univ : Finset α).map .inl else (univ : Finset β).map .inr := (rfl)

/-- Membership in the prescribed vertex finset is determined by the parity of the time. -/
@[simp]
theorem mem_bipartiteVertexFinset [Fintype α] [Fintype β] {t : ℕ} {x : α ⊕ β} :
    x ∈ bipartiteVertexFinset t ↔ if t % 2 = 0 then x.isLeft else x.isRight := by
  cases x <;> by_cases ht : t % 2 = 0 <;> simp [bipartiteVertexFinset_def, ht]

/-- The prescribed vertex finset has the cardinality of the row or column type at that time. -/
@[simp]
theorem card_bipartiteVertexFinset [Fintype α] [Fintype β] (t : ℕ) :
    #(bipartiteVertexFinset (α := α) (β := β) t) =
      if t % 2 = 0 then Fintype.card α else Fintype.card β := by
  by_cases ht : t % 2 = 0 <;> simp [bipartiteVertexFinset_def, ht]

/-- A bipartite word visits a label on the prescribed side at each time. -/
theorem bipartiteWord_mem_bipartiteVertexFinset [Fintype α] [Fintype β]
    (u : Fin k → α) (v : Fin k → β) (t : Fin (2 * k)) :
    bipartiteWord u v t ∈ bipartiteVertexFinset t.val := by
  obtain ⟨a, rfl⟩ := (finSumFinInterleaveEquiv k).surjective t
  cases a <;> simp

/-- A cyclic bipartite word determines its row and column indices. -/
@[simp]
theorem bipartiteWord_inj {u u' : Fin k → α} {v v' : Fin k → β} :
    bipartiteWord u v = bipartiteWord u' v' ↔ u = u' ∧ v = v' := by
  refine ⟨fun h ↦ ⟨funext fun t ↦ ?_, funext fun t ↦ ?_⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
  · simpa using congrFun h (finSumFinInterleaveEquiv k (.inl t))
  · simpa using congrFun h (finSumFinInterleaveEquiv k (.inr t))

/-- The unordered edge of the cyclic bipartite word at the step `a` is the position
`bipartiteEdge u v a` read by that step, joining a row index to a column index. -/
theorem sym2_bipartiteWord (u : Fin k → α) (v : Fin k → β) (a : Fin k ⊕ Fin k) :
    s(bipartiteWord u v (finSumFinInterleaveEquiv k a),
        bipartiteWord u v (finRotate (2 * k) (finSumFinInterleaveEquiv k a))) =
      s(.inl (bipartiteEdge u v a).1, .inr (bipartiteEdge u v a).2) := by
  cases a
  · simp only [finRotate_finSumFinInterleaveEquiv_inl, bipartiteWord_inl, bipartiteWord_inr,
      bipartiteEdge_inl]
  · simp only [finRotate_finSumFinInterleaveEquiv_inr, bipartiteWord_inl, bipartiteWord_inr,
      bipartiteEdge_inr, Sym2.eq_swap]

/-- If every entry position read by a bipartite word is read at least twice, then each unordered
edge of its cyclic word is also traversed at least twice. -/
theorem bipartiteWord_no_singleton_edge {u : Fin k → α} {v : Fin k → β}
    (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) (t : Fin (2 * k)) :
    ∃ s ≠ t, s(bipartiteWord u v s, bipartiteWord u v (finRotate (2 * k) s)) =
      s(bipartiteWord u v t, bipartiteWord u v (finRotate (2 * k) t)) := by
  let e := finSumFinInterleaveEquiv k
  obtain ⟨a, rfl⟩ := e.surjective t
  obtain ⟨b, hba, hb⟩ := h a
  exact ⟨e b, e.injective.ne hba, by simp only [e, sym2_bipartiteWord, hb]⟩

/-- A closed bipartite word is non-backtracking in blocks of `k + 1` row visits if consecutive
rows always differ and consecutive columns differ except at block joins. -/
def BipartiteNonbacktracking {r : ℕ} (k : ℕ) (u : Fin (r * (k + 1)) → α)
    (v : Fin (r * (k + 1)) → β) : Prop :=
  ∀ t, u t ≠ u (finRotate _ t) ∧ (t.modNat ≠ Fin.last k → v t ≠ v (finRotate _ t))

/-- The non-backtracking condition is expressed by inequalities at cyclic successors. -/
theorem bipartiteNonbacktracking_iff {r k : ℕ} (u : Fin (r * (k + 1)) → α)
    (v : Fin (r * (k + 1)) → β) :
    BipartiteNonbacktracking k u v ↔
      ∀ t, u t ≠ u (finRotate _ t) ∧ (t.modNat ≠ Fin.last k → v t ≠ v (finRotate _ t)) :=
  (Iff.rfl)

/-- Interleave the row and column vertices and append the final row vertex. -/
def bipartitePath (u : Fin (k + 1) → α) (v : Fin k → β) :
    Fin (2 * k + 1) → α ⊕ β :=
  Fin.snoc (bipartiteWord (u ∘ Fin.castSucc) v) (.inl (u (Fin.last k)))

/-- The even positions of a bipartite path are its row vertices. -/
@[simp]
theorem bipartitePath_even (u : Fin (k + 1) → α) (v : Fin k → β)
    (t : Fin (k + 1)) :
    bipartitePath u v ⟨2 * t, by omega⟩ = .inl (u t) := by
  induction t using Fin.lastCases with
  | last =>
    have h : (⟨2 * (Fin.last k : ℕ), by simp⟩ : Fin (2 * k + 1)) = Fin.last (2 * k) := by
      ext
      simp
    rw [h]
    simp [bipartitePath]
  | cast t =>
    have h : (⟨2 * (t : ℕ), by omega⟩ : Fin (2 * k + 1)) =
        (finSumFinInterleaveEquiv k (.inl t)).castSucc := by ext; simp
    simp [bipartitePath, h]

/-- A bipartite path starts at its first row vertex. -/
@[simp]
theorem bipartitePath_zero (u : Fin (k + 1) → α) (v : Fin k → β) :
    bipartitePath u v 0 = .inl (u 0) :=
  bipartitePath_even u v 0

/-- A bipartite path ends at its final row vertex. -/
@[simp]
theorem bipartitePath_last (u : Fin (k + 1) → α) (v : Fin k → β) :
    bipartitePath u v (Fin.last (2 * k)) = .inl (u (Fin.last k)) := by
  simp [bipartitePath]

/-- The odd positions of a bipartite path are its column vertices. -/
@[simp]
theorem bipartitePath_odd (u : Fin (k + 1) → α) (v : Fin k → β)
    (t : Fin k) :
    bipartitePath u v ⟨2 * t + 1, by omega⟩ = .inr (v t) := by
  have h : (⟨2 * (t : ℕ) + 1, by omega⟩ : Fin (2 * k + 1)) =
      (finSumFinInterleaveEquiv k (.inr t)).castSucc := by ext; simp
  simp [bipartitePath, h]

/-- A bipartite path determines both of its tuples of vertices. -/
theorem bipartitePath_injective :
    Function.Injective (fun uv : (Fin (k + 1) → α) × (Fin k → β) ↦
      bipartitePath uv.1 uv.2) := by
  intro u v huv
  refine Prod.ext (funext fun t ↦ ?_) (funext fun t ↦ ?_)
  · simpa only [bipartitePath_even, Sum.inl.injEq] using congrFun huv ⟨2 * t, by omega⟩
  · simpa only [bipartitePath_odd, Sum.inr.injEq] using congrFun huv ⟨2 * t + 1, by omega⟩

/-- A word with row vertices at the even positions and column vertices at the odd positions
is represented by a bipartite path. -/
theorem exists_eq_bipartitePath (w : Fin (2 * k + 1) → α ⊕ β)
    (h : ∀ t, (w t).isLeft = decide ((t : ℕ) % 2 = 0)) :
    ∃ (u : Fin (k + 1) → α) (v : Fin k → β), bipartitePath u v = w := by
  let u (t : Fin (k + 1)) := (w ⟨2 * t, by omega⟩).getLeft (by
    rw [h]
    exact decide_eq_true (by simp))
  let v (t : Fin k) := (w ⟨2 * t + 1, by omega⟩).getRight (by
    rw [← Sum.not_isLeft, h]
    simp)
  refine ⟨u, v, funext fun t ↦ ?_⟩
  by_cases ht : (t : ℕ) % 2 = 0
  · let j : Fin (k + 1) := ⟨t / 2, by omega⟩
    have hEq : t = ⟨2 * j, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hEq, bipartitePath_even]
    exact Sum.inl_getLeft _ _
  · let j : Fin k := ⟨t / 2, by omega⟩
    have hEq : t = ⟨2 * j + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hEq, bipartitePath_odd]
    exact Sum.inr_getRight _ _

/-- A bipartite path has no immediate reversals exactly when adjacent row vertices differ
and adjacent column vertices differ. -/
theorem bipartitePath_nonbacktracking_iff (u : Fin (k + 1) → α)
    (v : Fin k → β) :
    (∀ s t : Fin (2 * k + 1), (s : ℕ) + 2 = t → bipartitePath u v s ≠ bipartitePath u v t) ↔
      (∀ t : Fin k, u t.castSucc ≠ u t.succ) ∧
        ∀ s t : Fin k, (s : ℕ) + 1 = t → v s ≠ v t := by
  constructor
  · intro h
    constructor
    · intro t
      simpa only [bipartitePath_even, ne_eq, Sum.inl.injEq] using
        h ⟨2 * (t.castSucc : ℕ), by omega⟩ ⟨2 * (t.succ : ℕ), by omega⟩ (by simp; omega)
    · intro s t hst
      simpa only [bipartitePath_odd, ne_eq, Sum.inr.injEq] using
        h ⟨2 * s + 1, by omega⟩ ⟨2 * t + 1, by omega⟩ (by dsimp; omega)
  · rintro ⟨hu, hv⟩ s t hst
    by_cases hs : (s : ℕ) % 2 = 0
    · let j : Fin k := ⟨s / 2, by omega⟩
      have hs' : s = ⟨2 * (j.castSucc : ℕ), by omega⟩ := Fin.ext (by dsimp [j]; omega)
      have ht' : t = ⟨2 * (j.succ : ℕ), by omega⟩ := Fin.ext (by dsimp [j]; omega)
      simpa only [hs', ht', bipartitePath_even, ne_eq, Sum.inl.injEq] using hu j
    · let j : Fin k := ⟨s / 2, by omega⟩
      let j' : Fin k := ⟨t / 2, by omega⟩
      have hs' : s = ⟨2 * j + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      have ht' : t = ⟨2 * j' + 1, by omega⟩ := Fin.ext (by dsimp [j']; omega)
      simpa only [hs', ht', bipartitePath_odd, ne_eq, Sum.inr.injEq] using
        hv j j' (by dsimp [j, j']; omega)

variable [DecidableEq α] [DecidableEq β]

/-- A cyclic bipartite word visits `#(image u) + #(image v)` vertices: the row indices of `u` and
the column indices of `v`, which lie on different sides of `α ⊕ β`. -/
theorem card_image_bipartiteWord (u : Fin k → α) (v : Fin k → β) :
    #(univ.image (bipartiteWord u v)) = #(univ.image u) + #(univ.image v) := by
  rw [← card_disjSum]
  congr 1
  ext (a | b) <;>
    simp [(finSumFinInterleaveEquiv k).surjective.exists, bipartiteWord]

/-- A bipartite word visits at most one more row and column index than it reads positions.
The word may revisit indices and positions. -/
theorem card_image_add_card_image_le_card_image_bipartiteEdge_add_one (u : Fin k → α)
    (v : Fin k → β) :
    #(univ.image u) + #(univ.image v) ≤ #(univ.image (bipartiteEdge u v)) + 1 := by
  -- Read the alternating word as an ordinary cyclic word.
  let w := bipartiteWord u v
  have hedges : (({i | w i ≠ w (finRotate (2 * k) i)} : Finset (Fin (2 * k))).image
      fun i ↦ s(w i, w (finRotate (2 * k) i))) ⊆
        (univ.image (bipartiteEdge u v)).image fun p ↦ s(.inl p.1, .inr p.2) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    obtain ⟨a, rfl⟩ := (finSumFinInterleaveEquiv k).surjective i
    exact mem_image.2 ⟨bipartiteEdge u v a, mem_image_of_mem _ (mem_univ a),
      (sym2_bipartiteWord u v a).symm⟩
  have hcyclic := card_image_le_card_nonloop_cyclic_edges_add_one w
  rw [card_image_bipartiteWord] at hcyclic
  exact hcyclic.trans (Nat.add_le_add_right ((card_le_card hedges).trans card_image_le) 1)

/-- A bipartite word of half-length `k` that reads no position exactly once reads at most `k`
distinct positions. -/
theorem card_image_bipartiteEdge_le_of_no_singleton_edge {u : Fin k → α} {v : Fin k → β}
    (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) :
    #(univ.image (bipartiteEdge u v)) ≤ k := by
  have hcount := two_mul_card_image_le_of_no_singleton_fiber h
  simp only [Fintype.card_sum, Fintype.card_fin] at hcount
  omega

/-- A bipartite word of half-length `k` that reads no position exactly once visits at most
`k + 1` row and column indices in total. -/
theorem card_image_add_card_image_le_add_one_of_no_singleton_edge {u : Fin k → α}
    {v : Fin k → β} (h : ∀ a, ∃ b ≠ a, bipartiteEdge u v b = bipartiteEdge u v a) :
    #(univ.image u) + #(univ.image v) ≤ k + 1 :=
  (card_image_add_card_image_le_card_image_bipartiteEdge_add_one u v).trans
    (Nat.add_le_add_right (card_image_bipartiteEdge_le_of_no_singleton_edge h) 1)

end TauCeti
