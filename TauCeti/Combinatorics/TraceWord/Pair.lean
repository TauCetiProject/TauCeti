/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import TauCeti.Data.Fintype.SmallRange
import TauCeti.Algebra.Order.BigOperators.Group.Finset

/-!
# Vertex and pair counts for coupled trace words

In the variance computation for empirical moments of Wigner matrices, expanding the covariance of
two length-`k` cyclic trace words `w₁, w₂ : Fin k → α` leaves only pairs `(w₁, w₂)` that share at
least one unordered edge (otherwise the two walk products are independent) and whose combined
`2 * k` steps have no singleton unordered edge (otherwise one of the centered expectations
vanishes).

Deleting a shared unordered edge from each cycle and concatenating the remaining `(k - 1)`-step
paths shows that such a pair visits at most `k` vertices in total, rather than `k + 1`. Combined
with `TauCeti.card_filter_card_image_le`, at most `|α| ^ k * k ^ (2 * k)` such pairs exist,
producing the `O(n⁻²)` variance bound for normalized traces.

## Main results

* `TauCeti.card_image_union_le_of_shared_edge_of_no_singleton_edge`: two length-`k` cyclic words
  sharing an unordered edge whose combined steps have no singleton unordered edge visit at most `k`
  distinct vertices together.
* `TauCeti.card_filter_shared_edge_and_no_singleton_edge_le`: on a finite alphabet `α`, at most
  `Fintype.card α ^ k * k ^ (2 * k)` such pairs of length-`k` words exist.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.7.
-/

public section

open Finset

namespace TauCeti

variable {α : Type*} [DecidableEq α]

/-- Unrolling a cyclic word `w : Fin (m + 1) → α` by deleting step `t` produces an `m`-step path
from `w (finRotate (m + 1) t)` to `w t` that visits all vertices of `w` and uses only cyclic edges
at indices other than `t`. -/
private theorem exists_path_of_cyclic_erase_forward {m : ℕ} (w : Fin (m + 1) → α)
    (t : Fin (m + 1)) :
    ∃ p : ℕ → α, p 0 = w (finRotate (m + 1) t) ∧ p m = w t ∧
      (range (m + 1)).image p = univ.image w ∧
      ∀ j < m, ∃ s ≠ t, s(p j, p (j + 1)) = s(w s, w (finRotate (m + 1) s)) := by
  let idx : ℕ → Fin (m + 1) := fun j ↦ Fin.ofNat (m + 1) (t.val + 1 + j)
  have hstep (i : ℕ) : Fin.ofNat (m + 1) (i + 1) = finRotate (m + 1) (Fin.ofNat (m + 1) i) := by
    simp [finRotate_apply, Fin.ext_iff, Fin.val_add, Fin.ofNat_eq_cast, Nat.add_mod]
  have hnext (j : ℕ) : idx (j + 1) = finRotate (m + 1) (idx j) := by
    simpa only [idx, Nat.add_assoc] using hstep (t.val + 1 + j)
  refine ⟨fun j ↦ w (idx j), ?_, ?_, ?_, ?_⟩
  · dsimp only
    refine congrArg w ((hstep t.val).trans (congrArg (finRotate (m + 1)) ?_))
    ext
    simp
  · dsimp only
    refine congrArg w ?_
    ext
    simp [idx, Nat.add_assoc, Nat.add_comm 1 m]
  · ext x
    constructor
    · rintro hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact mem_image_of_mem _ (mem_univ _)
    · rintro hx
      obtain ⟨s, -, rfl⟩ := mem_image.mp hx
      let j := (s.val + (m + 1) - (t.val + 1)) % (m + 1)
      have hj : j < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)
      have hidx : idx j = s := by
        ext
        simp only [idx, j, Fin.val_ofNat]
        have : (t.val + 1 + (s.val + (m + 1) - (t.val + 1)) % (m + 1)) % (m + 1) =
            (t.val + 1 + (s.val + (m + 1) - (t.val + 1))) % (m + 1) := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [this]
        have hle : t.val + 1 ≤ s.val + (m + 1) := by omega
        have heq : t.val + 1 + (s.val + (m + 1) - (t.val + 1)) = s.val + (m + 1) := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]
      exact mem_image.mpr ⟨j, mem_range.mpr hj, congrArg w hidx⟩
  · intro j hj
    refine ⟨idx j, ?_, by dsimp only; rw [hnext]⟩
    intro hEq
    have hval := congrArg Fin.val hEq
    simp only [idx, Fin.val_ofNat] at hval
    have ht := t.isLt
    by_cases hlt : t.val + 1 + j < m + 1
    · rw [Nat.mod_eq_of_lt hlt] at hval
      omega
    · rw [Nat.mod_eq_sub_mod (Nat.not_lt.mp hlt), Nat.mod_eq_of_lt (by omega)] at hval
      omega

/-- Deleting step `t` from a cyclic word `w : Fin (m + 1) → α` gives an `m`-step path starting at
either endpoint `x₀ ∈ s(w t, w (finRotate (m + 1) t))`, visiting all vertices of `w`, and using
only cyclic edges at indices other than `t`. -/
private theorem exists_path_of_cyclic_erase {m : ℕ} (w : Fin (m + 1) → α) (t : Fin (m + 1))
    {x₀ : α} (hx₀ : x₀ ∈ s(w t, w (finRotate (m + 1) t))) :
    ∃ p : ℕ → α, p 0 = x₀ ∧ (range (m + 1)).image p = univ.image w ∧
      ∀ j < m, ∃ s ≠ t, s(p j, p (j + 1)) = s(w s, w (finRotate (m + 1) s)) := by
  obtain ⟨p, hp0, hpm, himg, hedge⟩ := exists_path_of_cyclic_erase_forward w t
  rcases Sym2.mem_iff.mp hx₀ with rfl | rfl
  · refine ⟨fun j ↦ p (m - j), by simpa using hpm, ?_, ?_⟩
    · rw [← himg]
      ext x
      simp only [mem_image, mem_range]
      exact ⟨fun ⟨j, hj, hx⟩ ↦ ⟨m - j, by omega, hx⟩,
        fun ⟨j, hj, hx⟩ ↦ ⟨m - j, by omega, by simpa [show m - (m - j) = j by omega] using hx⟩⟩
    · intro j hj
      obtain ⟨s, hst, hs⟩ := hedge (m - 1 - j) (by omega)
      refine ⟨s, hst, ?_⟩
      have h1 : m - j = m - 1 - j + 1 := by omega
      have h2 : m - (j + 1) = m - 1 - j := by omega
      dsimp only
      rw [h1, h2, Sym2.eq_swap]
      exact hs
  · exact ⟨p, hp0, himg, hedge⟩

/-- Concatenating two `m`-step paths extracted by deleting a shared unordered edge from `w₁` and
`w₂` yields a `2 * m`-step path covering `univ.image w₁ ∪ univ.image w₂` and avoiding both deleted
step indices. -/
private theorem exists_path_union_of_shared_edge {m : ℕ} (w₁ w₂ : Fin (m + 1) → α)
    (t₁ t₂ : Fin (m + 1))
    (hshare : s(w₁ t₁, w₁ (finRotate (m + 1) t₁)) = s(w₂ t₂, w₂ (finRotate (m + 1) t₂))) :
    ∃ p : ℕ → α, (range (2 * m + 1)).image p = univ.image w₁ ∪ univ.image w₂ ∧
      ∀ j < 2 * m, ∃ s ∈ ((univ.erase (.inl t₁)).erase (.inr t₂) :
          Finset (Fin (m + 1) ⊕ Fin (m + 1))),
        s(p j, p (j + 1)) = Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) s := by
  obtain ⟨p₁, -, hp₁m, himg₁, hedge₁⟩ := exists_path_of_cyclic_erase_forward w₁ t₁
  have hx₀ : w₁ t₁ ∈ s(w₂ t₂, w₂ (finRotate (m + 1) t₂)) := hshare ▸ Sym2.mem_mk_left _ _
  obtain ⟨p₂, hp₂0, himg₂, hedge₂⟩ := exists_path_of_cyclic_erase w₂ t₂ hx₀
  let p : ℕ → α := fun j ↦ if j ≤ m then p₁ j else p₂ (j - m)
  refine ⟨p, ?_, ?_⟩
  · rw [← himg₁, ← himg₂]
    ext x
    simp only [mem_union, mem_image, mem_range, p]
    constructor
    · rintro ⟨j, hj, rfl⟩
      by_cases hjm : j ≤ m
      · exact Or.inl ⟨j, by omega, by simp [hjm]⟩
      · exact Or.inr ⟨j - m, by omega, by simp [hjm]⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨j, by omega, by simp [show j ≤ m by omega]⟩
      · rcases eq_or_ne j 0 with rfl | hj0
        · exact ⟨m, by omega, by simp [hp₁m, hp₂0]⟩
        · exact ⟨m + j, by omega, by simp [show ¬ m + j ≤ m by omega]⟩
  · intro j hj
    by_cases hjm : j < m
    · obtain ⟨s, hst, hs⟩ := hedge₁ j hjm
      refine ⟨.inl s, by simp [hst], ?_⟩
      simpa [p, show j ≤ m by omega, show j + 1 ≤ m by omega] using hs
    · obtain ⟨s, hst, hs⟩ := hedge₂ (j - m) (by omega)
      refine ⟨.inr s, by simp [hst], ?_⟩
      rcases eq_or_lt_of_le (Nat.not_lt.mp hjm) with rfl | hjgt
      · simpa [p, hp₁m, hp₂0, show ¬ m + 1 ≤ m by omega] using hs
      · have h1 : ¬ j ≤ m := by omega
        have h2 : ¬ j + 1 ≤ m := by omega
        have h3 : j + 1 - m = j - m + 1 := by omega
        simpa [p, h1, h2, h3] using hs

/-- Two cyclic words `w₁, w₂ : Fin k → α` that share an unordered edge and whose combined `2 * k`
steps have no singleton unordered edge visit at most `k` distinct vertices together. -/
theorem card_image_union_le_of_shared_edge_of_no_singleton_edge {k : ℕ}
    (w₁ w₂ : Fin k → α)
    (hshare : ∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂)))
    (hno : ∀ s : Fin k ⊕ Fin k, ∃ s' ≠ s,
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k t))) s' =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k t))) s) :
    #(univ.image w₁ ∪ univ.image w₂) ≤ k := by
  obtain ⟨t₁, t₂, hsh⟩ := hshare
  rcases k with _ | m
  · exact t₁.elim0
  let e : Fin (m + 1) ⊕ Fin (m + 1) → Sym2 α :=
    Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
      (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t)))
  let U : Finset (Fin (m + 1) ⊕ Fin (m + 1)) := (univ.erase (.inl t₁)).erase (.inr t₂)
  obtain ⟨p, hpimg, hpedge⟩ := exists_path_union_of_shared_edge w₁ w₂ t₁ t₂ hsh
  have hpath := card_image_range_le_card_nonloop_edges_add_one p (2 * m)
  rw [hpimg] at hpath
  have hsubM : (((range (2 * m)).filter fun j ↦ p j ≠ p (j + 1)).image
      fun j ↦ s(p j, p (j + 1))) ⊆ U.image e := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    obtain ⟨s, hsU, hs⟩ := hpedge j (mem_range.mp (mem_filter.mp hj).1)
    exact hs ▸ mem_image_of_mem e hsU
  have hfib (b : Sym2 α) (hb : b ∈ univ.image e) : 2 ≤ #{s | e s = b} := by
    obtain ⟨s, -, rfl⟩ := mem_image.mp hb
    obtain ⟨s', hs', heq⟩ := hno s
    exact one_lt_card.mpr ⟨s, by simp, s', mem_filter.mpr ⟨mem_univ _, heq⟩, hs'.symm⟩
  have hUcard : #(U.image e) ≤ m := by
    have h2 := univ.two_mul_card_image_erase_erase_add_one_le_card
      (mem_univ (.inl t₁)) (mem_univ (.inr t₂)) (by simp) hsh hfib
    have huniv : #(univ : Finset (Fin (m + 1) ⊕ Fin (m + 1))) = 2 * (m + 1) := by
      simp [Nat.two_mul]
    dsimp only [U]
    omega
  exact hpath.trans (Nat.add_le_add_right ((card_le_card hsubM).trans hUcard) 1)

/-- On a finite type `α`, at most `Fintype.card α ^ k * k ^ (2 * k)` pairs of length-`k` cyclic
words share an unordered edge and have no singleton unordered edge in their combined `2 * k`
steps. -/
theorem card_filter_shared_edge_and_no_singleton_edge_le [Fintype α] (k : ℕ) :
    #({p : (Fin k → α) × (Fin k → α) |
        (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))) ∧
          ∀ s : Fin k ⊕ Fin k, ∃ s' ≠ s,
            Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
              (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s' =
            Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
              (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s} : Finset _) ≤
      Fintype.card α ^ k * k ^ (2 * k) := by
  cases isEmpty_or_nonempty α
  · rw [filter_eq_empty_iff.mpr fun p _ ⟨⟨t₁, _, _⟩, _⟩ ↦ isEmptyElim (p.1 t₁), card_empty]
    exact Nat.zero_le _
  have hinj : Set.InjOn (fun p : (Fin k → α) × (Fin k → α) ↦ Sum.elim p.1 p.2)
      ↑({p : (Fin k → α) × (Fin k → α) |
        (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))) ∧
          ∀ s : Fin k ⊕ Fin k, ∃ s' ≠ s,
            Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
              (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s' =
            Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
              (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s} : Finset _) := by
    intro p _ q _ hpq
    ext t
    · exact congrFun hpq (.inl t)
    · exact congrFun hpq (.inr t)
  have hmaps : Set.MapsTo (fun p : (Fin k → α) × (Fin k → α) ↦ Sum.elim p.1 p.2)
      ↑({p : (Fin k → α) × (Fin k → α) |
        (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))) ∧
          ∀ s : Fin k ⊕ Fin k, ∃ s' ≠ s,
            Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
              (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s' =
            Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
              (fun t ↦ s(p.2 t, p.2 (finRotate k t))) s} : Finset _)
      ↑({f : Fin k ⊕ Fin k → α | #(univ.image f) ≤ k} : Finset _) := by
    intro p hp
    obtain ⟨hsh, hno⟩ := (mem_filter.mp hp).2
    have himg : univ.image (Sum.elim p.1 p.2) = univ.image p.1 ∪ univ.image p.2 := by
      ext x
      simp only [mem_image, mem_univ, true_and, mem_union, Sum.exists, Sum.elim_inl, Sum.elim_inr]
    rw [mem_coe, mem_filter]
    exact ⟨mem_univ _, himg ▸ card_image_union_le_of_shared_edge_of_no_singleton_edge
      p.1 p.2 hsh hno⟩
  calc
    _ ≤ #({f : Fin k ⊕ Fin k → α | #(univ.image f) ≤ k} : Finset _) :=
      card_le_card_of_injOn _ hmaps hinj
    _ ≤ Fintype.card α ^ k * k ^ Fintype.card (Fin k ⊕ Fin k) :=
      card_filter_card_image_le k
    _ = Fintype.card α ^ k * k ^ (2 * k) := by simp [Nat.two_mul]

end TauCeti
