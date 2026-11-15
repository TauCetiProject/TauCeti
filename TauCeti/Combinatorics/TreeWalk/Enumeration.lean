/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Combinatorics.TreeWalk.Relabeling

/-!
# Enumeration of closed tree paths and leading cyclic words

A *closed tree path* of length `2 * m` on a vertex type `α` is a closed path
`v : Fin (2 * m + 1) → α` (`v (2 * m) = v 0`) that visits `m + 1` distinct vertices and traverses
every unordered edge `s(v i, v (i + 1))` twice. For `m ≠ 0`, a *leading cyclic word* of length
`2 * m` on `α` is a cyclic word `w : Fin (2 * m) → α` with no singleton unordered edge and `m + 1`
distinct visited vertices.

This file proves that both families have exact cardinality
`catalan m * (Nat.card α).descFactorial (m + 1)` (for `m ≠ 0` in the cyclic-word case). In the
expected trace `E[tr(Hₙ ^ (2m))]` of an `n × n` Wigner matrix, each leading cyclic word contributes
`n⁻ᵐ`, so multiplying this exact count by `n⁻ᵐ` and normalizing by `n⁻¹` yields the semicircle
moment `catalan m` as `n → ∞`.

## Main results

* `TauCeti.TreeWalk.card_closed_tree_path_eq`,
  `TauCeti.TreeWalk.card_filter_closed_tree_path_eq`: exact count
  `catalan m * n.descFactorial (m + 1)` of closed tree paths of length `2 * m` on `n` vertices.
* `TauCeti.TreeWalk.card_leading_cyclic_word_eq`,
  `TauCeti.TreeWalk.card_filter_leading_cyclic_word_eq`: for `m ≠ 0`, exact count
  `catalan m * n.descFactorial (m + 1)` of leading cyclic words of positive even length `2 * m` on
  `n` vertices.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

section Enumeration

variable {α : Type*} [DecidableEq α]

private theorem card_closed_tree_path_eq_of_finite [Finite α] (m : ℕ) :
    Nat.card {v : Fin (2 * m + 1) → α //
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  let _ : Fintype (ClosedTreeWalk m) := Fintype.ofEquiv _ (closedTreeWalkEquiv m).symm
  let P (v : Fin (2 * m + 1) → α) : Prop :=
    v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
      ∀ i : Fin (2 * m),
        #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2
  let proj : Subtype P → ClosedTreeWalk m := fun v ↦
    ⟨canonicalWalk v.1, (isTreeWalk_canonicalWalk_iff v.1).mpr v.2,
      fun _ hi ↦ canonicalWalk_eq_zero v.1 hi⟩
  have hfib (w : ClosedTreeWalk m) :
      Nat.card {v : Subtype P // proj v = w} = (Nat.card α).descFactorial (m + 1) := by
    let uw : Fin (2 * m + 1) → ℕ := fun i ↦ w.1 i
    have huw_card : #(univ.image uw) = m + 1 :=
      ((isTreeWalk_canonicalWalk_iff uw).mp
        (by simpa only [uw, canonicalWalk_closedTreeWalk] using w.2.1)).2.1
    let e : {v : Subtype P // proj v = w} ≃
        {v : Fin (2 * m + 1) → α // canonicalWalk v = canonicalWalk uw} :=
      { toFun := fun x ↦ ⟨x.1.1, (congrArg Subtype.val x.2).trans
          (canonicalWalk_closedTreeWalk w).symm⟩
        invFun := fun y ↦
          have hyw : canonicalWalk y.1 = w.1 := y.2.trans (canonicalWalk_closedTreeWalk w)
          ⟨⟨y.1, (isTreeWalk_canonicalWalk_iff y.1).mp (hyw.symm ▸ w.2.1)⟩, Subtype.ext hyw⟩
        left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
    rw [Nat.card_congr e, card_canonicalWalk_eq uw, huw_card]
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv proj), Nat.card_sigma]
  simp [hfib, ← Nat.card_eq_fintype_card, card_closedTreeWalk]

/-- On any vertex type `α`, there are `catalan m * (Nat.card α).descFactorial (m + 1)` closed
paths of length `2 * m` visiting `m + 1` vertices and traversing every unordered edge twice (both
sides are `0` when `α` is infinite). -/
theorem card_closed_tree_path_eq (m : ℕ) :
    Nat.card {v : Fin (2 * m + 1) → α //
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  by_cases hfin : Finite α
  · exact card_closed_tree_path_eq_of_finite m
  · have : Infinite α := not_finite_iff_infinite.mp hfin
    let _ : Fintype (ClosedTreeWalk m) := Fintype.ofEquiv _ (closedTreeWalkEquiv m).symm
    have hc_pos : 0 < catalan m := pos_of_mul_pos_right
      (succ_mul_catalan_eq_centralBinom m ▸ Nat.centralBinom_pos m) (Nat.zero_le _)
    obtain ⟨w₀⟩ : Nonempty (ClosedTreeWalk m) := Fintype.card_pos_iff.mp
      (by rw [← Nat.card_eq_fintype_card, card_closedTreeWalk]; exact hc_pos)
    let f (k : ℕ) : {v : Fin (2 * m + 1) → α //
        v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
          ∀ i : Fin (2 * m),
            #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} :=
      let v : Fin (2 * m + 1) → α := fun i ↦ Infinite.natEmbedding α (w₀.1 i + k)
      have hcw : canonicalWalk v = w₀.1 :=
        (canonicalWalk_comp (fun i : Fin (2 * m + 1) ↦ w₀.1 i)
          (fun x ↦ Infinite.natEmbedding α (x + k))
          (fun _ _ _ _ h ↦ Nat.add_right_cancel ((Infinite.natEmbedding α).injective h))).trans
          (canonicalWalk_closedTreeWalk w₀)
      ⟨v, (isTreeWalk_canonicalWalk_iff v).mp (hcw.symm ▸ w₀.2.1)⟩
    have hf_inj : Function.Injective f := fun a b hab ↦ by
      simpa [f, w₀.2.1.root] using
        (Infinite.natEmbedding α).injective (congrFun (congrArg Subtype.val hab) 0)
    have := Infinite.of_injective f hf_inj
    rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite,
      Nat.descFactorial_of_lt (Nat.zero_lt_succ m), mul_zero]

/-- `Finset.card` form of `card_closed_tree_path_eq`. -/
theorem card_filter_closed_tree_path_eq [Fintype α] (m : ℕ) :
    #{v : Fin (2 * m + 1) → α |
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} =
      catalan m * (Fintype.card α).descFactorial (m + 1) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, card_closed_tree_path_eq,
    Nat.card_eq_fintype_card]

private theorem leading_cyclic_word_of_closed_tree_path {m : ℕ} [NeZero m]
    {v : Fin (2 * m + 1) → α} (hc : v (Fin.last (2 * m)) = v 0) (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) :
    let w : Fin (2 * m) → α := fun i ↦ v i.castSucc
    cyclicPath w = v ∧
      ((∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1) := by
  intro w
  have hcw : cyclicPath w = v := funext fun i ↦
    Fin.lastCases (by simp [w, hc]) (fun _ ↦ by simp [w]) i
  refine ⟨hcw, fun t ↦ ?_, by rw [← image_cyclicPath w, hcw, hv]⟩
  have hw_edge (s : Fin (2 * m)) :
      s(w s, w (finRotate (2 * m) s)) = s(v s.castSucc, v s.succ) := by
    rw [← cyclicPath_castSucc w s, ← cyclicPath_succ w s, hcw]
  obtain ⟨s, hs, hst⟩ := exists_mem_ne ((he t).symm ▸ one_lt_two) t
  exact ⟨s, hst, by rw [hw_edge, hw_edge]; exact (mem_filter.mp hs).2⟩

private def leadingCyclicWordEquiv (m : ℕ) [NeZero m] :
    {w : Fin (2 * m) → α //
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} ≃
    {v : Fin (2 * m + 1) → α //
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} where
  toFun w := ⟨cyclicPath w.1, by simp, by simpa using w.2.2,
    card_edge_fiber_cyclicPath w.1 w.2.1 w.2.2⟩
  invFun v := ⟨fun i ↦ v.1 i.castSucc,
    (leading_cyclic_word_of_closed_tree_path v.2.1 v.2.2.1 v.2.2.2).2⟩
  left_inv w := Subtype.ext (funext fun i ↦ cyclicPath_castSucc w.1 i)
  right_inv v := Subtype.ext (leading_cyclic_word_of_closed_tree_path v.2.1 v.2.2.1 v.2.2.2).1

/-- `Nat.card` count of leading cyclic trace words of positive even length `2 * m` on any vertex
type `α` (both sides are `0` when `α` is infinite). -/
theorem card_leading_cyclic_word_eq (m : ℕ) [NeZero m] :
    Nat.card {w : Fin (2 * m) → α //
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  rw [Nat.card_congr (leadingCyclicWordEquiv m), card_closed_tree_path_eq]

/-- On a `Fintype` vertex set `α`, there are `catalan m * (Fintype.card α).descFactorial (m + 1)`
leading cyclic trace words of positive even length `2 * m` (those with no singleton unordered edge
and `m + 1` distinct visited vertices). -/
theorem card_filter_leading_cyclic_word_eq [Fintype α] (m : ℕ) [NeZero m] :
    #{w : Fin (2 * m) → α |
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} =
      catalan m * (Fintype.card α).descFactorial (m + 1) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, card_leading_cyclic_word_eq,
    Nat.card_eq_fintype_card]

end Enumeration

end TauCeti.TreeWalk
