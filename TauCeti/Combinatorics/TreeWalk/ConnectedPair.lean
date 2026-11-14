/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Data.Fintype.SmallRange

/-!
# Vertex and counting bounds for connected pairs of trace words

In the variance and covariance expansions for traces of powers of Wigner matrices, pairs of cyclic
words `(w₁, w₂)` with disjoint sets of unordered edges cancel by independence, while pairs whose
combined step set has a singleton unordered edge have vanishing expectation when entries are
centered. Every remaining pair shares at least one unordered edge and traverses every combined
unordered edge at least twice.

Concatenating two such cyclic words at a shared vertex produces a single singleton-free cyclic word
of length `k₁ + k₂`. When `k₁ + k₂ = 2 * m`, the single-word bound gives at most `m + 1` combined
vertices. Equality `#V = m + 1` is impossible: canonicalizing the concatenated walk would yield a
closed double-traversal tree walk that returns to the root at the concatenation time `k₁` while
sharing an unordered edge between `[0, k₁)` and `[k₁, 2 * m)`, contradicting the fact that every
edge discovered before returning to the root must already have been closed before that return.
Hence `(w₁, w₂)` visits at most `m` distinct vertices in total, and on an `n`-element vertex set
there are at most `n ^ m * m ^ (2 * m)` such pairs.

## Main results

* `TauCeti.TreeWalk.IsTreeWalk.ne_edge_of_lt_of_le`: if a tree walk returns to the root at time
  `r`, no step before `r` shares an unordered edge with a step at or after `r`.
* `TauCeti.TreeWalk.card_image_sumElim_le_of_add_eq_two_mul` and
  `TauCeti.TreeWalk.card_image_sumElim_le`: two edge-sharing cyclic words without combined
  singleton edges and of total length `2 * m` (in particular, two length-`k` words with `m = k`)
  visit at most `m` vertices together.
* `TauCeti.TreeWalk.card_filter_connectedPair_le_of_add_eq_two_mul` and
  `TauCeti.TreeWalk.card_filter_connectedPair_le`: at most `|α| ^ m * m ^ (2 * m)` pairs `(w₁, w₂)`
  of total length `2 * m` share an unordered edge and have no combined singleton unordered edge.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open Finset

namespace TauCeti.TreeWalk

private theorem iterate_pred_apply_zero {w : ℕ → ℕ} (h0 : w 0 = 0) :
    ∀ n, (fun v ↦ w (v - 1))^[n] 0 = 0
  | 0 => rfl
  | n + 1 => by simp [Function.iterate_succ_apply, h0, iterate_pred_apply_zero h0 n]

/-- When a closed double-traversal tree walk returns to the root `0` at time `r`, every edge
discovered before `r` is already closed before `r`, so no step in `[0, r)` can traverse the same
unordered edge as a step in `[r, 2 * m)`. -/
theorem IsTreeWalk.ne_edge_of_lt_of_le {m r a b : ℕ} {w : ℕ → ℕ} (hw : IsTreeWalk m w)
    (hr : w r = 0) (ha : a < r) (hrb : r ≤ b) (hb : b < 2 * m) :
    s(w a, w (a + 1)) ≠ s(w b, w (b + 1)) := by
  intro hab
  obtain ⟨i, hi, hup, hae⟩ := hw.exists_up_edge (ha.trans (hrb.trans_lt hb))
  have hie : s(w i, w (i + 1)) = s(w i, i + 1) := by rw [hup]
  obtain ⟨j, hj, hj1, -, hpair⟩ := hw.exists_edge_fiber_eq_pair hi hup
  have ha_mem : a ∈ ({i, j} : Finset ℕ) := by
    rw [← hpair]
    exact mem_filter.mpr ⟨mem_range.mpr (ha.trans (hrb.trans_lt hb)), hae.trans hie.symm⟩
  have hb_mem : b ∈ ({i, j} : Finset ℕ) := by
    rw [← hpair]
    exact mem_filter.mpr ⟨mem_range.mpr hb, hab.symm.trans (hae.trans hie.symm)⟩
  have hij : i < j := by
    have := hw.le_self j hj.le
    omega
  simp only [mem_insert, mem_singleton] at ha_mem hb_mem
  have hia : i = a := by omega
  have hjb : j = b := by omega
  let p : ℕ → ℕ := fun v ↦ w (v - 1)
  have hdesc : ∀ d, i + 1 + d ≤ r → ∃ n, p^[n] (w (i + 1 + d)) = i + 1 := by
    intro d
    induction d with
    | zero =>
      intro _
      exact ⟨0, hup⟩
    | succ d ih =>
      intro hd
      set t := i + 1 + d
      obtain ⟨n, hn⟩ := ih (by omega)
      have ht2m : t < 2 * m := by omega
      have hsub : i + 1 + (d + 1) = t + 1 := by omega
      rw [hsub]
      by_cases htup : w (t + 1) = t + 1
      · refine ⟨n + 1, ?_⟩
        rw [Function.iterate_succ_apply, htup]
        exact hn
      · obtain ⟨-, hpar, -⟩ := hw.step_down ht2m htup
        cases n with
        | zero =>
          exfalso
          have hwt : w t = i + 1 := hn
          have hwt1 : w (t + 1) = w i := by simpa [hwt] using hpar
          have hte : s(w t, w (t + 1)) = s(w i, w (i + 1)) := by
            rw [hwt, hwt1, hup, Sym2.eq_swap]
          have ht_mem : t ∈ ({i, j} : Finset ℕ) := by
            rw [← hpair]
            exact mem_filter.mpr ⟨mem_range.mpr ht2m, hte⟩
          simp only [mem_insert, mem_singleton] at ht_mem
          omega
        | succ n =>
          refine ⟨n, ?_⟩
          have hpar' : w (t + 1) = p (w t) := hpar
          rw [hpar', ← Function.iterate_succ_apply]
          exact hn
  obtain ⟨n, hn⟩ := hdesc (r - (i + 1)) (by omega)
  rw [Nat.add_sub_of_le (by omega : i + 1 ≤ r), hr, iterate_pred_apply_zero hw.root n] at hn
  omega

section CyclicPairs

variable {α : Type*}

private theorem finRotate_add_right {k : ℕ} (j r : Fin k) :
    finRotate k (j + r) = finRotate k j + r := by
  have := j.neZero
  simp only [finRotate_apply, add_right_comm]

variable [DecidableEq α]

/-- Two cyclic words `w₁ : Fin k₁ → α` and `w₂ : Fin k₂ → α` of total length `k₁ + k₂ = 2 * m`
that share at least one unordered edge and have no singleton unordered edge in their combined step
family visit at most `m` distinct vertices together. -/
theorem card_image_sumElim_le_of_add_eq_two_mul {k₁ k₂ m : ℕ}
    (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α) (hk : k₁ + k₂ = 2 * m)
    (hshare : ∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k₁ t₁)) = s(w₂ t₂, w₂ (finRotate k₂ t₂)))
    (hns : ∀ x : Fin k₁ ⊕ Fin k₂, ∃ y ≠ x,
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) y =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) x) :
    #(univ.image (Sum.elim w₁ w₂)) ≤ m := by
  obtain ⟨t₁, t₂, ht₁₂⟩ := hshare
  cases k₁ with
  | zero => exact t₁.elim0
  | succ m₁ =>
  cases k₂ with
  | zero => exact t₂.elim0
  | succ m₂ =>
  have hm : m ≠ 0 := by omega
  have : NeZero m := ⟨hm⟩
  have : NeZero (2 * m) := ⟨by omega⟩
  -- Extract a vertex shared between `w₁` and `w₂` from the shared unordered edge.
  have hvtx : ∃ (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)), w₁ r₁ = w₂ r₂ := by
    rcases Sym2.eq_iff.mp ht₁₂ with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨t₁, t₂, h⟩
    · exact ⟨t₁, finRotate (m₂ + 1) t₂, h⟩
  obtain ⟨r₁, r₂, hr₁₂⟩ := hvtx
  let w₁' : Fin (m₁ + 1) → α := fun i ↦ w₁ (i + r₁)
  let w₂' : Fin (m₂ + 1) → α := fun i ↦ w₂ (i + r₂)
  have hw0 : w₁' 0 = w₂' 0 := by simpa [w₁', w₂'] using hr₁₂
  -- Concatenate the rotated words into a single cyclic word of length `2 * m`.
  let e : Fin (m₁ + 1) ⊕ Fin (m₂ + 1) ≃ Fin (2 * m) :=
    finSumFinEquiv.trans (finCongr hk)
  let W : Fin (2 * m) → α := Sum.elim w₁' w₂' ∘ e.symm
  let stepEquiv : Fin (m₁ + 1) ⊕ Fin (m₂ + 1) ≃ Fin (2 * m) :=
    (Equiv.sumCongr (Equiv.addRight r₁).symm (Equiv.addRight r₂).symm).trans e
  have hW_inl (i : Fin (m₁ + 1)) : W (e (.inl i)) = w₁' i := by simp [W]
  have hW_inr (i : Fin (m₂ + 1)) : W (e (.inr i)) = w₂' i := by simp [W]
  -- Compare each step of `W` with the corresponding rotated step of `w₁` or `w₂`.
  have hedge_e (x : Fin (m₁ + 1) ⊕ Fin (m₂ + 1)) :
      s(W (e x), W (finRotate (2 * m) (e x))) =
        Sum.elim (fun i ↦ s(w₁' i, w₁' (finRotate (m₁ + 1) i)))
          (fun i ↦ s(w₂' i, w₂' (finRotate (m₂ + 1) i))) x := by
    have h1lt : 1 < 2 * m := by omega
    have hrot_mod (u : Fin (2 * m)) : (finRotate (2 * m) u).val = (u.val + 1) % (2 * m) := by
      rw [finRotate_apply, Fin.add_def, Fin.val_one' (2 * m), Nat.mod_eq_of_lt h1lt]
    cases x with
    | inl i =>
      simp only [Sum.elim_inl, hW_inl]
      have heval : (e (.inl i)).val = i.val := by simp [e]
      have hlt2m : (e (.inl i)).val + 1 < 2 * m := by omega
      have hnext_val : (finRotate (2 * m) (e (.inl i))).val = i.val + 1 := by
        rw [hrot_mod, Nat.mod_eq_of_lt hlt2m, heval]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hi | hi
      · have htarget : finRotate (2 * m) (e (.inl i)) = e (.inl (finRotate (m₁ + 1) i)) := by
          ext
          rw [hnext_val]
          simp [e, finRotate_of_lt hi]
        rw [htarget, hW_inl]
      · have hilast : i = Fin.last m₁ := Fin.ext hi
        have htarget : finRotate (2 * m) (e (.inl i)) = e (.inr 0) := by
          ext
          rw [hnext_val, hi]
          simp [e]
        rw [htarget, hW_inr, hilast, finRotate_last, hw0]
    | inr i =>
      simp only [Sum.elim_inr, hW_inr]
      have heval : (e (.inr i)).val = (m₁ + 1) + i.val := by simp [e]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hi | hi
      · have hlt2m : (e (.inr i)).val + 1 < 2 * m := by omega
        have htarget : finRotate (2 * m) (e (.inr i)) = e (.inr (finRotate (m₂ + 1) i)) := by
          ext
          rw [hrot_mod, Nat.mod_eq_of_lt hlt2m, heval]
          simp [e, finRotate_of_lt hi, Nat.add_assoc]
        rw [htarget, hW_inr]
      · have hilast : i = Fin.last m₂ := Fin.ext hi
        have hsum2m : (e (.inr i)).val + 1 = 2 * m := by omega
        have htarget : finRotate (2 * m) (e (.inr i)) = e (.inl 0) := by
          ext
          rw [hrot_mod, hsum2m, Nat.mod_self]
          simp [e]
        rw [htarget, hW_inl, hilast, finRotate_last, hw0]
  have hedge_step (x : Fin (m₁ + 1) ⊕ Fin (m₂ + 1)) :
      s(W (stepEquiv x), W (finRotate (2 * m) (stepEquiv x))) =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m₁ + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m₂ + 1) t))) x := by
    cases x with
    | inl t =>
      simp only [stepEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.addRight_symm_apply, hedge_e, Sum.elim_inl, w₁']
      rw [finRotate_add_right, neg_add_cancel_right, neg_add_cancel_right]
    | inr t =>
      simp only [stepEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.addRight_symm_apply, hedge_e, Sum.elim_inr, w₂']
      rw [finRotate_add_right, neg_add_cancel_right, neg_add_cancel_right]
  -- `W` inherits the no-singleton-edge property and the combined vertex set.
  have hW_ns : ∀ a : Fin (2 * m), ∃ b ≠ a,
      s(W b, W (finRotate (2 * m) b)) = s(W a, W (finRotate (2 * m) a)) := by
    intro a
    obtain ⟨y, hy, hyeq⟩ := hns (stepEquiv.symm a)
    refine ⟨stepEquiv y, ?_, ?_⟩
    · intro h
      exact hy (stepEquiv.symm_apply_eq.mpr h.symm).symm
    · rw [hedge_step y, ← stepEquiv.apply_symm_apply a, hedge_step (stepEquiv.symm a)]
      exact hyeq
  have himage : univ.image W = univ.image (Sum.elim w₁ w₂) := by
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      rcases ha : e.symm a with i | i
      · exact ⟨.inl (i + r₁), by simp [W, ha, w₁']⟩
      · exact ⟨.inr (i + r₂), by simp [W, ha, w₂']⟩
    · rintro ⟨x, rfl⟩
      cases x with
      | inl t => exact ⟨stepEquiv (.inl t), by simp [W, stepEquiv, w₁']⟩
      | inr t => exact ⟨stepEquiv (.inr t), by simp [W, stepEquiv, w₂']⟩
  have hle : #(univ.image W) ≤ m + 1 := by
    simpa [Nat.mul_div_right m (by omega : 0 < 2)] using
      card_image_le_div_two_add_one_of_no_singleton_edge W hW_ns
  rw [← himage]
  by_contra hgt
  have heq_card : #(univ.image W) = m + 1 := by omega
  have htree : IsTreeWalk m (canonicalWalk (cyclicPath W)) :=
    isTreeWalk_canonicalWalk_cyclic W hW_ns heq_card
  -- At time `m₁ + 1`, `W` visits `w₂' 0 = w₁' 0 = W 0`, so `canonicalWalk (cyclicPath W)` is `0`.
  let mid : Fin (2 * m) := e (.inr 0)
  have hmid_val : mid.val = m₁ + 1 := by simp [mid, e]
  have hroot_mid : canonicalWalk (cyclicPath W) (m₁ + 1) = 0 := by
    have hmid_eq : cyclicPath W mid.castSucc = cyclicPath W 0 := by
      have h0_eq : (0 : Fin (2 * m)) = e (.inl 0) := by ext; simp [e]
      rw [cyclicPath_castSucc, cyclicPath_zero, h0_eq, hW_inl, hW_inr, hw0]
    have hc := (canonicalWalk_eq_iff (cyclicPath W) mid.castSucc 0).mpr hmid_eq
    simpa [Fin.val_castSucc, hmid_val] using hc
  -- The shared edge gives steps in `[0, m₁ + 1)` and `[m₁ + 1, 2 * m)` traversing the same edge.
  let a := stepEquiv (.inl t₁)
  let b := stepEquiv (.inr t₂)
  have ha_lt : a.val < m₁ + 1 := by
    simp only [a, stepEquiv, e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.addRight_symm_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast,
      Fin.val_castAdd]
    exact (t₁ + -r₁).isLt
  have hb_ge : m₁ + 1 ≤ b.val := by simp [b, stepEquiv, e]
  have hab_edge : s(W a, W (finRotate (2 * m) a)) = s(W b, W (finRotate (2 * m) b)) := by
    rw [hedge_step (.inl t₁), hedge_step (.inr t₂)]
    exact ht₁₂
  have hab_canon :
      s(canonicalWalk (cyclicPath W) a.val, canonicalWalk (cyclicPath W) (a.val + 1)) =
        s(canonicalWalk (cyclicPath W) b.val, canonicalWalk (cyclicPath W) (b.val + 1)) := by
    have hca : s(cyclicPath W a.castSucc, cyclicPath W a.succ) =
        s(cyclicPath W b.castSucc, cyclicPath W b.succ) := by
      simpa only [cyclicPath_castSucc, cyclicPath_succ] using hab_edge
    simpa only [Sym2.eq_iff, ← canonicalWalk_eq_iff (cyclicPath W),
      Fin.val_castSucc, Fin.val_succ] using hca
  exact htree.ne_edge_of_lt_of_le hroot_mid ha_lt hb_ge b.isLt hab_canon

/-- Two cyclic words `w₁, w₂ : Fin k → α` that share an unordered edge and have no singleton
unordered edge in their combined step family visit at most `k` distinct vertices together. -/
theorem card_image_sumElim_le {k : ℕ} (w₁ w₂ : Fin k → α)
    (hshare : ∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k t₁)) = s(w₂ t₂, w₂ (finRotate k t₂)))
    (hns : ∀ x : Fin k ⊕ Fin k, ∃ y ≠ x,
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k t))) y =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k t))) x) :
    #(univ.image (Sum.elim w₁ w₂)) ≤ k :=
  card_image_sumElim_le_of_add_eq_two_mul w₁ w₂ (two_mul k).symm hshare hns

/-- On a finite vertex type `α`, there are at most `|α| ^ m * m ^ (2 * m)` pairs `(w₁, w₂)` of
cyclic words of lengths `k₁` and `k₂` with `k₁ + k₂ = 2 * m` that share an unordered edge and
have no singleton unordered edge in their combined step family. -/
theorem card_filter_connectedPair_le_of_add_eq_two_mul [Fintype α] {k₁ k₂ m : ℕ}
    (hk : k₁ + k₂ = 2 * m) :
    #({p : (Fin k₁ → α) × (Fin k₂ → α) |
      (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k₁ t₁)) = s(p.2 t₂, p.2 (finRotate k₂ t₂))) ∧
        ∀ x : Fin k₁ ⊕ Fin k₂, ∃ y ≠ x,
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k₁ t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k₂ t))) y =
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k₁ t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k₂ t))) x}) ≤
      Fintype.card α ^ m * m ^ (2 * m) := by
  rcases eq_or_ne k₁ 0 with rfl | hk₁
  · simp
  rcases eq_or_ne k₂ 0 with rfl | hk₂
  · simp
  cases isEmpty_or_nonempty α with
  | inl hα =>
    have : Nonempty (Fin k₁) := ⟨⟨0, Nat.pos_of_ne_zero hk₁⟩⟩
    have hm : m ≠ 0 := by omega
    simp [Finset.eq_empty_of_isEmpty, hm]
  | inr hα =>
    let eqv := Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) α
    let S : Finset ((Fin k₁ → α) × (Fin k₂ → α)) :=
      {p | (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k₁ t₁)) = s(p.2 t₂, p.2 (finRotate k₂ t₂))) ∧
        ∀ x : Fin k₁ ⊕ Fin k₂, ∃ y ≠ x,
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k₁ t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k₂ t))) y =
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k₁ t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k₂ t))) x}
    let T : Finset (Fin k₁ ⊕ Fin k₂ → α) := {f | #(univ.image f) ≤ m}
    have hmaps : Set.MapsTo eqv.symm (↑S) (↑T) := by
      intro p hp
      obtain ⟨hshare, hns⟩ := (mem_filter.mp hp).2
      exact mem_filter.mpr ⟨mem_univ _,
        card_image_sumElim_le_of_add_eq_two_mul p.1 p.2 hk hshare hns⟩
    exact (card_le_card_of_injOn eqv.symm hmaps (fun _ _ _ _ h ↦ eqv.symm.injective h)).trans (by
      simpa [T, hk] using card_filter_card_image_le (α := Fin k₁ ⊕ Fin k₂) (β := α) m)

/-- On a finite vertex type `α`, at most `|α| ^ k * k ^ (2 * k)` pairs `(w₁, w₂)` of cyclic words
of length `k` share an unordered edge and have no singleton unordered edge in their combined step
family. -/
theorem card_filter_connectedPair_le [Fintype α] (k : ℕ) :
    #({p : (Fin k → α) × (Fin k → α) |
      (∃ t₁ t₂, s(p.1 t₁, p.1 (finRotate k t₁)) = s(p.2 t₂, p.2 (finRotate k t₂))) ∧
        ∀ x : Fin k ⊕ Fin k, ∃ y ≠ x,
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k t))) y =
          Sum.elim (fun t ↦ s(p.1 t, p.1 (finRotate k t)))
            (fun t ↦ s(p.2 t, p.2 (finRotate k t))) x}) ≤
      Fintype.card α ^ k * k ^ (2 * k) :=
  card_filter_connectedPair_le_of_add_eq_two_mul (two_mul k).symm

end CyclicPairs

end TauCeti.TreeWalk
