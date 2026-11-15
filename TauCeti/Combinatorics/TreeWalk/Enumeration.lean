/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Combinatorics.TreeWalk.Relabeling
import Mathlib.Data.Fintype.BigOperators

/-!
# Enumeration of closed tree paths, leading cyclic words, and coupled walks

Grouping closed walks on a vertex set `α` by their first-visit canonical labeling
(`canonicalWalk`) fibers the leading words of length `2 * m` over `ClosedTreeWalk m`, with each
fiber of size `(Nat.card α).descFactorial (m + 1)`. Combining `card_closedTreeWalk` and
`card_canonicalWalk_eq` yields the exact count `catalan m * (Nat.card α).descFactorial (m + 1)`
both for closed paths of length `2 * m` and (for `m ≠ 0`) for leading cyclic trace words.

For variance bounds in the Wigner moment method, we also bound the total number of distinct
vertices visited by a pair of cyclic words `(w₁, w₂)` of length `k` that share at least one
unordered edge and whose combined edge multiset has no singleton nonloop edge: together they visit
at most `k` vertices (`card_union_image_le_of_shared_edge_of_no_singleton_nonloop_edge`). Splicing
cyclic rotations of `w₁` and `w₂` at a shared vertex produces a single cyclic word `W` of length
`2 * k` with no singleton nonloop edge; attaining `k + 1` vertices would force `W` to be a loop-free
leading tree walk that returns to its root at the midpoint `k`, which separates the subtrees before
and after time `k` and contradicts the shared edge.

## Main results

* `TauCeti.TreeWalk.canonicalWalk_closedTreeWalk`: a `ClosedTreeWalk` is fixed by `canonicalWalk`.
* `TauCeti.TreeWalk.isTreeWalk_canonicalWalk_iff`: characterization of paths whose first-visit
  canonical walk is a tree walk.
* `TauCeti.TreeWalk.card_closedTreePath_eq`, `TauCeti.TreeWalk.card_filter_closedTreePath`: exact
  count `catalan m * n.descFactorial (m + 1)` of closed tree paths on `n` vertices.
* `TauCeti.TreeWalk.card_leadingCyclicWords_eq`, `TauCeti.TreeWalk.card_filter_leadingCyclicWords`:
  exact count `catalan m * n.descFactorial (m + 1)` of leading cyclic words of length `2 * m`.
* `TauCeti.TreeWalk.card_union_image_le_of_shared_edge_of_no_singleton_nonloop_edge`: two
  edge-sharing cyclic words of length `k` with no combined singleton nonloop edge visit at most `k`
  distinct vertices.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemmas 2.1.6 and 2.1.7.
-/

public section

open Finset

namespace TauCeti.TreeWalk

section Enumeration

/-- A closed tree walk in first-visit labeling is equal to the `canonicalWalk` of its restriction
to `Fin (2 * m + 1)`. -/
@[simp]
theorem canonicalWalk_closedTreeWalk {m : ℕ} (w : ClosedTreeWalk m) :
    canonicalWalk (fun i : Fin (2 * m + 1) ↦ w.1 i) = w.1 := by
  set u : Fin (2 * m + 1) → ℕ := fun i ↦ w.1 i
  funext i
  rcases lt_or_ge (2 * m) i with hi | hi
  · rw [canonicalWalk_eq_zero u hi, w.2.2 i hi]
  · have hi' : i < 2 * m + 1 := Nat.lt_succ_of_le hi
    have hc_le : w.1 i ≤ i := w.2.1.le_self i hi
    have hc' : w.1 i < 2 * m + 1 := hc_le.trans_lt hi'
    have hu_eq : u ⟨w.1 i, hc'⟩ = u ⟨i, hi'⟩ := w.2.1.idem hi
    have hcw_eq : canonicalWalk u i = canonicalWalk u (w.1 i) :=
      ((canonicalWalk_eq_iff u ⟨w.1 i, hc'⟩ ⟨i, hi'⟩).mpr hu_eq).symm
    have hle : canonicalWalk u i ≤ w.1 i := hcw_eq ▸ canonicalWalk_le u (w.1 i)
    have hk' : canonicalWalk u i < 2 * m + 1 := hle.trans_lt hc'
    have hwk : w.1 (canonicalWalk u i) = w.1 i :=
      (canonicalWalk_eq_iff u ⟨canonicalWalk u i, hk'⟩ ⟨i, hi'⟩).mp (canonicalWalk_idem u i)
    have hge : w.1 i ≤ canonicalWalk u i :=
      hwk ▸ w.2.1.le_self (canonicalWalk u i) (hle.trans (hc_le.trans hi))
    exact le_antisymm hle hge

variable {α : Type*} [DecidableEq α]

/-- The `canonicalWalk` of `v : Fin (2 * m + 1) → α` is a closed tree walk if and only if `v` is
closed, visits `m + 1` distinct vertices, and traverses every unordered edge twice. -/
theorem isTreeWalk_canonicalWalk_iff {m : ℕ} (v : Fin (2 * m + 1) → α) :
    IsTreeWalk m (canonicalWalk v) ↔
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2 := by
  refine ⟨fun hw ↦ ⟨?_, ?_, ?_⟩, fun ⟨hc, hv, he⟩ ↦ isTreeWalk_canonicalWalk v hc hv he⟩
  · exact (canonicalWalk_eq_iff v (Fin.last (2 * m)) 0).mp (hw.closed.trans hw.root.symm)
  · exact (card_fixed_canonicalWalk v).symm.trans hw.card_vertices
  · intro i
    have hedge (a b : Fin (2 * m)) :
        s(canonicalWalk v a.castSucc, canonicalWalk v a.succ) =
          s(canonicalWalk v b.castSucc, canonicalWalk v b.succ) ↔
        s(v a.castSucc, v a.succ) = s(v b.castSucc, v b.succ) := by
      simp only [Sym2.eq_iff, canonicalWalk_eq_iff]
    refine Eq.trans ?_ (hw.card_edge i i.isLt)
    apply card_bij (fun j _ ↦ j.val)
    · intro j hj
      refine mem_filter.mpr ⟨mem_range.mpr j.isLt, ?_⟩
      simpa only [Fin.val_castSucc, Fin.val_succ] using (hedge j i).mpr (mem_filter.mp hj).2
    · exact fun _ _ _ _ h ↦ Fin.ext h
    · intro j hj
      obtain ⟨hj_lt, hj_eq⟩ := mem_filter.mp hj
      refine ⟨⟨j, mem_range.mp hj_lt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact (hedge ⟨j, mem_range.mp hj_lt⟩ i).mp
        (by simpa only [Fin.val_castSucc, Fin.val_succ] using hj_eq)

private theorem card_closedTreePath_eq_of_finite [Finite α] (m : ℕ) :
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
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Nat.card_congr e, card_canonicalWalk_eq uw, huw_card]
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv proj), Nat.card_sigma]
  simp only [hfib, sum_const, card_univ, ← Nat.card_eq_fintype_card, card_closedTreeWalk,
    smul_eq_mul]

/-- On any vertex type `α`, there are `catalan m * (Nat.card α).descFactorial (m + 1)` closed
paths of length `2 * m` visiting `m + 1` vertices and traversing every unordered edge twice (both
sides are `0` when `α` is infinite). -/
theorem card_closedTreePath_eq (m : ℕ) :
    Nat.card {v : Fin (2 * m + 1) → α //
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  by_cases hfin : Finite α
  · exact card_closedTreePath_eq_of_finite m
  · have : Infinite α := not_finite_iff_infinite.mp hfin
    let _ : Fintype (ClosedTreeWalk m) := Fintype.ofEquiv _ (closedTreeWalkEquiv m).symm
    have hc_pos : 0 < catalan m := by
      have h := Nat.centralBinom_pos m
      rw [← succ_mul_catalan_eq_centralBinom] at h
      exact pos_of_mul_pos_right h (Nat.zero_le _)
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
      have h0 := congrFun (congrArg Subtype.val hab) 0
      simpa [f, w₀.2.1.root] using (Infinite.natEmbedding α).injective h0
    have := Infinite.of_injective f hf_inj
    rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite,
      Nat.descFactorial_of_lt (Nat.zero_lt_succ m), mul_zero]

/-- `Finset.card` form of `card_closedTreePath_eq`. -/
theorem card_filter_closedTreePath [Fintype α] (m : ℕ) :
    #{v : Fin (2 * m + 1) → α |
      v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} =
      catalan m * (Fintype.card α).descFactorial (m + 1) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, card_closedTreePath_eq,
    Nat.card_eq_fintype_card]

private theorem isLeadingCyclicWord_of_closedTreePath {m : ℕ} [NeZero m]
    {v : Fin (2 * m + 1) → α} (hc : v (Fin.last (2 * m)) = v 0) (hv : #(univ.image v) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) :
    let w : Fin (2 * m) → α := fun i ↦ v i.castSucc
    cyclicPath w = v ∧
      ((∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1) := by
  intro w
  have hcw : cyclicPath w = v := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [w, hc]
    · simp [w]
  refine ⟨hcw, ?_, by rw [← image_cyclicPath w, hcw, hv]⟩
  intro t
  have hw_edge (s : Fin (2 * m)) :
      s(w s, w (finRotate (2 * m) s)) = s(v s.castSucc, v s.succ) := by
    rw [← cyclicPath_castSucc w s, ← cyclicPath_succ w s, hcw]
  have hcard : #{s : Fin (2 * m) |
      s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))} = 2 := by
    simp_rw [hw_edge]
    exact he t
  obtain ⟨a, b, hab, hpair⟩ := card_eq_two.mp hcard
  by_cases hat : a = t
  · refine ⟨b, fun hbt ↦ hab (hat.trans hbt.symm), ?_⟩
    simpa using (Finset.ext_iff.mp hpair b).mpr (by simp)
  · refine ⟨a, hat, ?_⟩
    simpa using (Finset.ext_iff.mp hpair a).mpr (by simp)

private def leadingCyclicWordEquivClosedTreePath (m : ℕ) [NeZero m] :
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
    (isLeadingCyclicWord_of_closedTreePath v.2.1 v.2.2.1 v.2.2.2).2⟩
  left_inv w := Subtype.ext (funext fun i ↦ cyclicPath_castSucc w.1 i)
  right_inv v := Subtype.ext (isLeadingCyclicWord_of_closedTreePath v.2.1 v.2.2.1 v.2.2.2).1

/-- `Nat.card` count of leading cyclic trace words of positive even length `2 * m` on any vertex
type `α` (both sides are `0` when `α` is infinite). -/
theorem card_leadingCyclicWords_eq (m : ℕ) [NeZero m] :
    Nat.card {w : Fin (2 * m) → α //
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  rw [Nat.card_congr (leadingCyclicWordEquivClosedTreePath m), card_closedTreePath_eq]

/-- On a `Fintype` vertex set `α`, there are `catalan m * (Fintype.card α).descFactorial (m + 1)`
leading cyclic trace words of positive even length `2 * m` (those with no singleton unordered edge
and `m + 1` distinct visited vertices). -/
theorem card_filter_leadingCyclicWords [Fintype α] (m : ℕ) [NeZero m] :
    #{w : Fin (2 * m) → α |
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} =
      catalan m * (Fintype.card α).descFactorial (m + 1) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, card_leadingCyclicWords_eq,
    Nat.card_eq_fintype_card]

end Enumeration

section CoupledWalks

/-- If a closed tree walk returns to the root `0` at time `m`, then every vertex visited at time
`j ∈ [m, 2 * k]` is either `0` or first discovered strictly after time `m`. -/
theorem IsTreeWalk.eq_zero_or_lt_of_eq_zero {k m : ℕ} {w : ℕ → ℕ} (hw : IsTreeWalk k w)
    (hm0 : w m = 0) :
    ∀ {j : ℕ}, m ≤ j → j ≤ 2 * k → w j = 0 ∨ m < w j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hmj hjk
    rcases eq_or_lt_of_le hmj with rfl | hlt
    · exact .inl hm0
    · cases j with
      | zero => omega
      | succ t =>
        by_cases hup : w (t + 1) = t + 1
        · exact .inr (by omega)
        · obtain ⟨hpos, hpar, -⟩ := hw.step_down (by omega) hup
          have hmt : m < w t := (ih t (by omega) (by omega) (by omega)).resolve_left (by omega)
          have hle : w t ≤ t := hw.le_self t (by omega)
          rw [hpar]
          exact ih (w t - 1) (by omega) (by omega) (by omega)

private def spliceEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) where
  toFun
    | .inl i => ⟨i.val, by omega⟩
    | .inr i => ⟨i.val + n, by omega⟩
  invFun j := if h : j.val < n then .inl ⟨j.val, h⟩ else .inr ⟨j.val - n, by omega⟩
  left_inv
    | .inl i => by simp [i.isLt]
    | .inr i => by
      have hnot : ¬ i.val + n < n := by omega
      simp [hnot]
  right_inv j := by
    by_cases h : j.val < n <;> simp [h, Fin.ext_iff]
    omega

variable {α : Type*}

private def spliceWords {n : ℕ} (u₁ u₂ : Fin n → α) (j : Fin (2 * n)) : α :=
  if h : j.val < n then u₁ ⟨j.val, h⟩ else u₂ ⟨j.val - n, by omega⟩

private theorem image_spliceWords [DecidableEq α] {n : ℕ} (u₁ u₂ : Fin n → α) :
    univ.image (spliceWords u₁ u₂) = univ.image u₁ ∪ univ.image u₂ := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases h : j.val < n
    · exact .inl ⟨⟨j.val, h⟩, by simp [spliceWords, h]⟩
    · exact .inr ⟨⟨j.val - n, by omega⟩, by simp [spliceWords, h]⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨⟨i.val, by omega⟩, by simp [spliceWords, i.isLt]⟩
    · have hnot : ¬ i.val + n < n := by omega
      exact ⟨⟨i.val + n, by omega⟩, by simp [spliceWords, hnot]⟩

private theorem spliceWords_edge {m : ℕ} {u₁ u₂ : Fin (m + 1) → α} (h0 : u₁ 0 = u₂ 0)
    (x : Fin (m + 1) ⊕ Fin (m + 1)) :
    s(spliceWords u₁ u₂ (spliceEquiv (m + 1) x),
        spliceWords u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) x))) =
      Sum.elim (fun t ↦ s(u₁ t, u₁ (finRotate (m + 1) t)))
        (fun t ↦ s(u₂ t, u₂ (finRotate (m + 1) t))) x := by
  have hrot2 (j : Fin (2 * (m + 1))) :
      (finRotate (2 * (m + 1)) j : ℕ) = (j.val + 1) % (2 * (m + 1)) := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hrot1 (i : Fin (m + 1)) : (finRotate (m + 1) i : ℕ) = (i.val + 1) % (m + 1) := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  cases x with
  | inl i =>
    have hfirst : spliceWords u₁ u₂ (spliceEquiv (m + 1) (.inl i)) = u₁ i := by
      simp [spliceWords, spliceEquiv, i.isLt]
    have hsecond : spliceWords u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inl i))) =
        u₁ (finRotate (m + 1) i) := by
      have hv : (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inl i)) : ℕ) = i.val + 1 := by
        rw [hrot2]; dsimp [spliceEquiv]; exact Nat.mod_eq_of_lt (by omega)
      by_cases hi : i.val + 1 < m + 1
      · simp only [spliceWords, hv, hi, dite_true]
        congr 1; ext; rw [hrot1, Nat.mod_eq_of_lt hi]
      · have hi_eq : i.val + 1 = m + 1 := by omega
        simp only [spliceWords, hv, hi_eq, lt_irrefl, dite_false, Nat.sub_self]
        have hr0 : finRotate (m + 1) i = 0 := by ext; rw [hrot1, hi_eq, Nat.mod_self]; rfl
        rw [hr0]
        exact h0.symm
    rw [hfirst, hsecond]; rfl
  | inr i =>
    have hnot0 : ¬ i.val + (m + 1) < m + 1 := by omega
    have hfirst : spliceWords u₁ u₂ (spliceEquiv (m + 1) (.inr i)) = u₂ i := by
      simp [spliceWords, spliceEquiv, hnot0]
    have hsecond : spliceWords u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inr i))) =
        u₂ (finRotate (m + 1) i) := by
      by_cases hi : i.val + 1 < m + 1
      · have hv : (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inr i)) : ℕ) =
            i.val + 1 + (m + 1) := by
          rw [hrot2]; dsimp [spliceEquiv]
          rw [show i.val + (m + 1) + 1 = i.val + 1 + (m + 1) by omega]
          exact Nat.mod_eq_of_lt (by omega)
        have hnot : ¬ i.val + 1 + (m + 1) < m + 1 := by omega
        simp only [spliceWords, hv, hnot, dite_false, Nat.add_sub_cancel]
        congr 1; ext; rw [hrot1, Nat.mod_eq_of_lt hi]
      · have hi_eq : i.val + 1 = m + 1 := by omega
        have hv : (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (.inr i)) : ℕ) = 0 := by
          rw [hrot2]; dsimp [spliceEquiv]
          rw [show i.val + (m + 1) + 1 = 2 * (m + 1) by omega, Nat.mod_self]
        simp only [spliceWords, hv, Nat.zero_lt_succ, dite_true]
        have hr0 : finRotate (m + 1) i = 0 := by ext; rw [hrot1, hi_eq, Nat.mod_self]; rfl
        rw [hr0]
        exact h0
    rw [hfirst, hsecond]; rfl

private theorem rotateWord_image [DecidableEq α] {m : ℕ} (w : Fin (m + 1) → α) (r : Fin (m + 1)) :
    univ.image (fun i ↦ w (i + r)) = univ.image w := by
  ext x
  simp only [mem_image, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨i + r, hi⟩, fun ⟨j, hj⟩ ↦ ⟨j - r, by simpa using hj⟩⟩

private theorem rotateWord_edge {m : ℕ} (w : Fin (m + 1) → α) (r i : Fin (m + 1)) :
    s(w (i + r), w (finRotate (m + 1) i + r)) =
      s(w (i + r), w (finRotate (m + 1) (i + r))) := by
  rw [finRotate_apply, finRotate_apply, add_right_comm]

private theorem spliceWords_shifted_edge_and_no_singleton_nonloop {m : ℕ} {w₁ w₂ : Fin (m + 1) → α}
    {t₁ r₂ : Fin (m + 1)} (hr₂ : w₁ t₁ = w₂ r₂)
    (hns : ∀ x : Fin (m + 1) ⊕ Fin (m + 1),
      Sum.elim w₁ w₂ x ≠ Sum.elim (w₁ ∘ finRotate (m + 1)) (w₂ ∘ finRotate (m + 1)) x →
      ∃ y ≠ x,
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) y =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) x) :
    let W := spliceWords (fun i ↦ w₁ (i + t₁)) (fun i ↦ w₂ (i + r₂))
    let shiftSum := Equiv.sumCongr (Equiv.addRight t₁) (Equiv.addRight r₂)
    (∀ j : Fin (2 * (m + 1)),
      s(W j, W (finRotate (2 * (m + 1)) j)) =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t)))
          (shiftSum ((spliceEquiv (m + 1)).symm j))) ∧
    (∀ j : Fin (2 * (m + 1)), W j ≠ W (finRotate (2 * (m + 1)) j) →
      ∃ j' ≠ j, s(W j', W (finRotate (2 * (m + 1)) j')) =
        s(W j, W (finRotate (2 * (m + 1)) j))) := by
  intro W shiftSum
  have hu0 : (fun i ↦ w₁ (i + t₁)) 0 = (fun i ↦ w₂ (i + r₂)) 0 := by simpa using hr₂
  have hW_edge (j : Fin (2 * (m + 1))) :
      s(W j, W (finRotate (2 * (m + 1)) j)) =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t)))
          (shiftSum ((spliceEquiv (m + 1)).symm j)) := by
    set x := (spliceEquiv (m + 1)).symm j
    have hj : j = spliceEquiv (m + 1) x := ((spliceEquiv (m + 1)).apply_symm_apply j).symm
    rw [hj, spliceWords_edge hu0 x]
    cases x with
    | inl i => exact rotateWord_edge w₁ t₁ i
    | inr i => exact rotateWord_edge w₂ r₂ i
  refine ⟨hW_edge, fun j hj_ne ↦ ?_⟩
  set z := shiftSum ((spliceEquiv (m + 1)).symm j)
  have hz_ne : Sum.elim w₁ w₂ z ≠
      Sum.elim (w₁ ∘ finRotate (m + 1)) (w₂ ∘ finRotate (m + 1)) z := by
    intro hz_eq
    have hdiag : s(W j, W (finRotate (2 * (m + 1)) j)) = s(Sum.elim w₁ w₂ z, Sum.elim w₁ w₂ z) := by
      have hsum : ∀ x : Fin (m + 1) ⊕ Fin (m + 1),
          Sum.elim w₁ w₂ x = Sum.elim (w₁ ∘ finRotate (m + 1)) (w₂ ∘ finRotate (m + 1)) x →
          Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m + 1) t)))
            (fun t ↦ s(w₂ t, w₂ (finRotate (m + 1) t))) x =
            s(Sum.elim w₁ w₂ x, Sum.elim w₁ w₂ x)
        | .inl t, h => congrArg (fun b ↦ s(w₁ t, b)) h.symm
        | .inr t, h => congrArg (fun b ↦ s(w₂ t, b)) h.symm
      exact (hW_edge j).trans (hsum z hz_eq)
    rcases Sym2.eq_iff.mp hdiag with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hj_ne (h1.trans h2.symm)
  obtain ⟨y, hy_ne, hy_eq⟩ := hns z hz_ne
  refine ⟨spliceEquiv (m + 1) (shiftSum.symm y), fun h ↦ hy_ne ?_, ?_⟩
  · simp [z, ← h]
  · rw [hW_edge, hW_edge]; simpa [z] using hy_eq

private theorem not_card_image_eq_of_midpoint_root [DecidableEq α] {m : ℕ}
    {W : Fin (2 * (m + 1)) → α}
    (hW_ns : ∀ j, ∃ j' ≠ j, s(W j', W (finRotate (2 * (m + 1)) j')) =
      s(W j, W (finRotate (2 * (m + 1)) j)))
    (hW_eq : #(univ.image W) = (m + 1) + 1) (hW_mid : W ⟨m + 1, by omega⟩ = W 0)
    {j₁ j₂ : Fin (2 * (m + 1))} (hj₁ : j₁.val < m + 1) (hj₂ : m + 1 ≤ j₂.val)
    (hW12 : s(W j₁, W (finRotate (2 * (m + 1)) j₁)) = s(W j₂, W (finRotate (2 * (m + 1)) j₂))) :
    False := by
  have htree : IsTreeWalk (m + 1) (canonicalWalk (cyclicPath W)) :=
    isTreeWalk_canonicalWalk_cyclic W hW_ns hW_eq
  have hmid0 : canonicalWalk (cyclicPath W) (m + 1) = 0 := by
    refine Eq.trans ?_ (canonicalWalk_zero (cyclicPath W))
    apply (canonicalWalk_eq_iff (cyclicPath W)
      ((⟨m + 1, by omega⟩ : Fin (2 * (m + 1))).castSucc) 0).mpr
    rw [cyclicPath_castSucc, cyclicPath_zero]
    exact hW_mid
  have hj_edge : s(canonicalWalk (cyclicPath W) j₁.val, canonicalWalk (cyclicPath W) (j₁.val + 1)) =
      s(canonicalWalk (cyclicPath W) j₂.val, canonicalWalk (cyclicPath W) (j₂.val + 1)) := by
    rw [← cyclicPath_castSucc W j₁, ← cyclicPath_succ W j₁,
      ← cyclicPath_castSucc W j₂, ← cyclicPath_succ W j₂] at hW12
    simpa only [Sym2.eq_iff, ← canonicalWalk_eq_iff (cyclicPath W),
      Fin.val_castSucc, Fin.val_succ] using hW12
  have hj1_le1 : canonicalWalk (cyclicPath W) j₁.val ≤ m + 1 :=
    (htree.le_self _ (by omega)).trans (by omega)
  have hj1_le2 : canonicalWalk (cyclicPath W) (j₁.val + 1) ≤ m + 1 :=
    (htree.le_self _ (by omega)).trans (by omega)
  have hj2_or1 := htree.eq_zero_or_lt_of_eq_zero hmid0 (j := j₂.val) hj₂ (by omega)
  have hj2_or2 := htree.eq_zero_or_lt_of_eq_zero hmid0 (j := j₂.val + 1) (by omega) (by omega)
  have hj2_eq : canonicalWalk (cyclicPath W) j₂.val =
      canonicalWalk (cyclicPath W) (j₂.val + 1) := by rw [Sym2.eq_iff] at hj_edge; omega
  have hloop : W j₂ = W (finRotate (2 * (m + 1)) j₂) := by
    rw [← cyclicPath_castSucc W j₂, ← cyclicPath_succ W j₂]
    exact (canonicalWalk_eq_iff (cyclicPath W) j₂.castSucc j₂.succ).mp hj2_eq
  exact (ne_and_card_edge_fiber_eq_two_of_no_singleton_edge_of_card_image_eq W hW_ns hW_eq).1
    j₂ hloop

/-- **Coupled two-walk vertex bound.** If two cyclic words `w₁, w₂ : Fin k → α` share at least one
unordered edge and their combined `2 * k`-step edge multiset on `Fin k ⊕ Fin k` has no singleton
nonloop edge, then together they visit at most `k` distinct vertices. -/
theorem card_union_image_le_of_shared_edge_of_no_singleton_nonloop_edge [DecidableEq α] {k : ℕ}
    (w₁ w₂ : Fin k → α)
    (hshare : ∃ t₁ t₂ : Fin k,
      s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂)))
    (hns : ∀ x : Fin k ⊕ Fin k,
      Sum.elim w₁ w₂ x ≠ Sum.elim (w₁ ∘ finRotate k) (w₂ ∘ finRotate k) x →
      ∃ y ≠ x,
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate k t))) y =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate k t))) x) :
    #(univ.image w₁ ∪ univ.image w₂) ≤ k := by
  rcases k with _ | m
  · obtain ⟨t₁, -⟩ := hshare; exact Fin.elim0 t₁
  obtain ⟨t₁, t₂, hedge_eq⟩ := hshare
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : Fin (m + 1), w₁ t₁ = w₂ r₂ := by
    rcases Sym2.mem_iff.mp (hedge_eq ▸ Sym2.mem_mk_left _ _) with h | h
    · exact ⟨t₂, h⟩
    · exact ⟨finRotate (m + 1) t₂, h⟩
  let W := spliceWords (fun i ↦ w₁ (i + t₁)) (fun i ↦ w₂ (i + r₂))
  obtain ⟨hW_edge, hW_ns_nl⟩ := spliceWords_shifted_edge_and_no_singleton_nonloop hr₂ hns
  have hW_img : univ.image W = univ.image w₁ ∪ univ.image w₂ := by
    rw [image_spliceWords, rotateWord_image, rotateWord_image]
  have hW_le : #(univ.image W) ≤ m + 2 := by
    simpa [Nat.mul_div_right _ two_pos] using
      card_image_le_div_two_add_one_of_no_singleton_nonloop_edge W hW_ns_nl
  rw [← hW_img]
  by_contra hgt
  have hW_eq : #(univ.image W) = (m + 1) + 1 := by omega
  have hW_ns := (no_singleton_edge_of_no_singleton_nonloop_edge_of_card_image_eq W hW_ns_nl hW_eq).2
  exact not_card_image_eq_of_midpoint_root hW_ns hW_eq (by simp [W, spliceWords, hr₂])
    (j₁ := spliceEquiv (m + 1) (.inl 0)) (j₂ := spliceEquiv (m + 1) (.inr (t₂ - r₂)))
    (by dsimp [spliceEquiv]; omega) (by dsimp [spliceEquiv]; omega)
    (by rw [hW_edge, hW_edge]; simpa using hedge_eq)

end CoupledWalks

end TauCeti.TreeWalk
