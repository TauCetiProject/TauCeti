/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Vertex and edge counts of trace words

A trace word is a cyclic sequence of vertices. Its edges are unordered pairs of consecutive
vertices, including loops. Words with no singleton edge are the ones left in the expected trace
expansion of a matrix with independent centred entries. Such a word of length `k` visits at most
`k / 2 + 1` vertices. At length `2 * m`, attaining `m + 1` vertices forces every edge to be
traversed exactly twice and excludes loops.

The underlying counting estimate is valid for arbitrary paths: the number of visited vertices
is at most one plus the number of distinct nonloop edges. It does not require a graph structure,
so diagonal matrix entries (loops) are not silently discarded.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, the counting argument for the moment method.
-/

public section

open Finset

namespace TauCeti

variable {α : Type*} [DecidableEq α]

/-- A path with `n` steps visits at most one more vertex than its number of distinct nonloop
edges. The path may repeat vertices and may have loops. -/
theorem card_image_range_le_card_nonloop_edges_add_one (w : ℕ → α) (n : ℕ) :
    #((range (n + 1)).image w) ≤
      #(((range n).filter fun i => w i ≠ w (i + 1)).image fun i => s(w i, w (i + 1))) + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmono :
        (((range n).filter fun i => w i ≠ w (i + 1)).image fun i => s(w i, w (i + 1))) ⊆
        (((range (n + 1)).filter fun i => w i ≠ w (i + 1)).image fun i => s(w i, w (i + 1))) :=
      image_subset_image (filter_subset_filter _ (range_mono (by omega)))
    rw [range_add_one, image_insert]
    by_cases hv : w (n + 1) ∈ (range (n + 1)).image w
    · rw [insert_eq_of_mem hv]
      exact ih.trans (Nat.add_le_add_right (card_le_card hmono) 1)
    · have hne : w n ≠ w (n + 1) := by
        intro h
        exact hv (mem_image.mpr ⟨n, mem_range.mpr (by omega), h⟩)
      have he : s(w n, w (n + 1)) ∉
          (((range n).filter fun i => w i ≠ w (i + 1)).image fun i => s(w i, w (i + 1))) := by
        rintro h
        obtain ⟨i, hi, he⟩ := mem_image.mp h
        have hi' : i < n := mem_range.mp (mem_filter.mp hi).1
        have hm : w (n + 1) ∈ s(w i, w (i + 1)) := he ▸ Sym2.mem_mk_right _ _
        rcases Sym2.mem_iff.mp hm with h | h
        · exact hv (mem_image.mpr ⟨i, mem_range.mpr (by omega), h.symm⟩)
        · exact hv (mem_image.mpr ⟨i + 1, mem_range.mpr (by omega), h.symm⟩)
      rw [card_insert_of_notMem hv]
      simpa [range_add_one, filter_insert, hne, he] using Nat.add_le_add_right ih 1

/-- A cyclic word visits at most one more vertex than its number of distinct nonloop edges. -/
theorem card_image_le_card_nonloop_cyclic_edges_add_one {k : ℕ} (w : Fin k → α) :
    #(univ.image w) ≤
      #(({i | w i ≠ w (finRotate k i)} : Finset (Fin k)).image
        fun i => s(w i, w (finRotate k i))) + 1 := by
  cases k with
  | zero => simp
  | succ k =>
    let v : ℕ → α := fun i => w (Fin.ofNat (k + 1) i)
    have hvertices : (range (k + 2)).image v = univ.image w := by
      ext x
      constructor
      · rintro hx
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        exact mem_image.mpr ⟨_, mem_univ _, rfl⟩
      · rintro hx
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        exact mem_image.mpr ⟨i.val, mem_range.mpr (by omega), by simp [v]⟩
    have hnext (i : ℕ) :
        Fin.ofNat (k + 1) (i + 1) = finRotate (k + 1) (Fin.ofNat (k + 1) i) := by
      rw [finRotate_apply]
      apply Fin.ext
      simp [Fin.val_add, Fin.ofNat_eq_cast, Nat.add_mod]
    have hedges :
        (((range (k + 1)).filter fun i => v i ≠ v (i + 1)).image fun i => s(v i, v (i + 1))) ⊆
          (({i | w i ≠ w (finRotate (k + 1) i)} : Finset (Fin (k + 1))).image
            fun i => s(w i, w (finRotate (k + 1) i))) := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      refine mem_image.mpr ⟨Fin.ofNat (k + 1) i, ?_, ?_⟩
      · exact mem_filter.mpr ⟨mem_univ _, by
          simpa only [v, hnext] using (mem_filter.mp hi).2⟩
      · simp only [v, hnext]
    have h := card_image_range_le_card_nonloop_edges_add_one v (k + 1)
    rw [hvertices] at h
    exact h.trans (Nat.add_le_add_right (card_le_card hedges) 1)

private theorem two_le_card_cyclic_edge_fiber_of_no_singleton_edge {k : ℕ} (w : Fin k → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate k j)) = s(w i, w (finRotate k i)))
    (e : Sym2 α) (he : e ∈ univ.image fun i => s(w i, w (finRotate k i))) :
    2 ≤ #{i | s(w i, w (finRotate k i)) = e} := by
  obtain ⟨i, -, rfl⟩ := mem_image.mp he
  obtain ⟨j, hji, hj⟩ := h i
  exact one_lt_card.mpr ⟨i, by simp, j, mem_filter.mpr ⟨mem_univ _, hj⟩, hji.symm⟩

/-- A cyclic word with no singleton edge has at most half as many distinct unordered edges
as steps. Loops count as edges. -/
theorem two_mul_card_cyclic_edges_le_of_no_singleton_edge {k : ℕ} (w : Fin k → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate k j)) = s(w i, w (finRotate k i))) :
    2 * #(univ.image fun i => s(w i, w (finRotate k i))) ≤ k := by
  simpa only [card_univ, Fintype.card_fin] using
    mul_card_image_le_card (univ : Finset (Fin k)) 2
      (two_le_card_cyclic_edge_fiber_of_no_singleton_edge w h)

/-- A word of length `k` with no singleton edge visits at most `k / 2 + 1` vertices.
Edges are unordered, and loops count as edges. -/
theorem card_image_le_div_two_add_one_of_no_singleton_edge {k : ℕ} (w : Fin k → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate k j)) = s(w i, w (finRotate k i))) :
    #(univ.image w) ≤ k / 2 + 1 := by
  have hcount := two_mul_card_cyclic_edges_le_of_no_singleton_edge w h
  have hvertices := card_image_le_card_nonloop_cyclic_edges_add_one w
  have hsub :
      (({i | w i ≠ w (finRotate k i)} : Finset (Fin k)).image fun i => s(w i, w (finRotate k i))) ⊆
        (univ.image fun i => s(w i, w (finRotate k i))) := image_subset_image (filter_subset _ _)
  have := card_le_card hsub
  omega

/-- In a word of length `2 * m` with no singleton edge and `m + 1` visited vertices,
there are no loops and every unordered edge is traversed exactly twice. These are necessary
conditions for a word to contribute at leading order in the moment method. -/
theorem ne_and_card_edge_fiber_eq_two_of_no_singleton_edge_of_card_image_eq {m : ℕ}
    (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    (∀ i, w i ≠ w (finRotate (2 * m) i)) ∧
      ∀ i, #{j | s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))} = 2 := by
  let e : Fin (2 * m) → Sym2 α := fun i => s(w i, w (finRotate (2 * m) i))
  let E := univ.image e
  let N := ({i | w i ≠ w (finRotate (2 * m) i)} : Finset (Fin (2 * m))).image e
  have hfiber := two_le_card_cyclic_edge_fiber_of_no_singleton_edge w h
  have hsub : N ⊆ E := image_subset_image (filter_subset _ _)
  have hvertices := card_image_le_card_nonloop_cyclic_edges_add_one w
  have hcount := two_mul_card_cyclic_edges_le_of_no_singleton_edge w h
  have hcard : #E = m ∧ #N = m := by
    have := card_le_card hsub
    have hE : 2 * #E ≤ 2 * m := hcount
    have hN : m + 1 ≤ #N + 1 := by
      simpa only [N, e, hv] using hvertices
    omega
  have hNE : N = E := eq_of_subset_of_card_le hsub (by omega)
  have hsum : (∑ _a ∈ E, 2) = ∑ a ∈ E, #{i | e i = a} := by
    rw [← card_eq_sum_card_image e univ]
    simp [hcard.1, Nat.mul_comm]
  have heq := (sum_eq_sum_iff_of_le hfiber).mp hsum
  refine ⟨?_, fun i => (heq (e i) (mem_image.mpr ⟨i, mem_univ _, rfl⟩)).symm⟩
  intro i hi
  have hiN : e i ∈ N := hNE.symm ▸ mem_image.mpr ⟨i, mem_univ _, rfl⟩
  obtain ⟨j, hj, hji⟩ := mem_image.mp hiN
  have hjne := (mem_filter.mp hj).2
  have he : w j = w (finRotate (2 * m) j) := by
    have := Sym2.eq_iff.mp hji
    rcases this with hh | hh <;> grind
  exact hjne he

end TauCeti
