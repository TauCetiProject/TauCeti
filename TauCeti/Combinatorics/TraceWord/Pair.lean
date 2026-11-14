/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Data.Fintype.SmallRange

/-!
# Connected pairs of cyclic trace words

When computing the variance of a random matrix trace `tr(H^k)`, products of centered expectations
expand over pairs `(w₁, w₂)` of cyclic words of length `k`. Pairs with disjoint unordered edge sets
have zero covariance by entry independence, while any pair whose combined multiset of steps contains
a singleton nonloop unordered edge vanishes by centering.

Every remaining pair shares at least one unordered edge and has no singleton nonloop edge across the
combined step index `Fin k ⊕ Fin k`. Rotating both words to start at a common vertex of a shared
edge and splicing them into a single closed walk of length `2 * k` shows that their union visits at
most `k` vertices: visiting `k + 1` vertices would force the spliced walk to canonicalize to a
closed tree walk returning to its root at time `k`, which cannot share an unordered edge between its
two halves by `IsTreeWalk.edge_ne_of_eq_zero`. Factoring through `Fin k` then bounds the number of
contributing pairs over a finite alphabet `α` by `|α|^k * k^(2 * k)`.
-/

public section

namespace TauCeti

open Finset TauCeti.TreeWalk

variable {α : Type*}

private def spliceEquiv (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
  finSumFinEquiv.trans (finCongr (two_mul k).symm)

private abbrev spliceWord {k : ℕ} (u₁ u₂ : Fin k → α) : Fin (2 * k) → α :=
  Sum.elim u₁ u₂ ∘ (spliceEquiv k).symm

private abbrev pairEdge {k : ℕ} (u₁ u₂ : Fin k → α) : Fin k ⊕ Fin k → Sym2 α :=
  Sum.elim (fun i ↦ s(u₁ i, u₁ (finRotate k i))) (fun i ↦ s(u₂ i, u₂ (finRotate k i)))

private theorem spliceEquiv_inl_val {k : ℕ} (i : Fin k) :
    (spliceEquiv k (Sum.inl i)).val = i.val := by simp [spliceEquiv]

private theorem spliceEquiv_inr_val {k : ℕ} (i : Fin k) :
    (spliceEquiv k (Sum.inr i)).val = k + i.val := by simp [spliceEquiv]; omega

private theorem splice_finRotate_inl {m : ℕ} (u₁ u₂ : Fin (m + 1) → α) (h0 : u₁ 0 = u₂ 0)
    (i : Fin (m + 1)) :
    spliceWord u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (Sum.inl i))) =
      u₁ (finRotate (m + 1) i) := by
  have : NeZero (2 * (m + 1)) := ⟨by omega⟩
  by_cases hi : i = Fin.last m
  · subst hi
    have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (Sum.inl (Fin.last m))) =
        spliceEquiv (m + 1) (Sum.inr 0) := by
      ext; rw [finRotate_apply, Fin.val_add, spliceEquiv_inl_val, spliceEquiv_inr_val, Fin.val_one',
        Nat.mod_eq_of_lt (by omega : 1 < 2 * (m + 1)), Fin.val_last, Nat.mod_eq_of_lt (by omega)]
      simp
    simp [spliceWord, hrot, h0]
  · have hlt : i.val < m := Nat.lt_of_le_of_ne (Fin.le_last i) (Fin.val_ne_of_ne hi)
    have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (Sum.inl i)) =
        spliceEquiv (m + 1) (Sum.inl (finRotate (m + 1) i)) := by
      ext; rw [finRotate_apply, Fin.val_add, spliceEquiv_inl_val, spliceEquiv_inl_val,
        coe_finRotate_of_ne_last hi, Fin.val_one',
        Nat.mod_eq_of_lt (by omega : 1 < 2 * (m + 1)), Nat.mod_eq_of_lt (by omega)]
    simp [spliceWord, hrot]

private theorem splice_finRotate_inr {m : ℕ} (u₁ u₂ : Fin (m + 1) → α) (h0 : u₁ 0 = u₂ 0)
    (j : Fin (m + 1)) :
    spliceWord u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (Sum.inr j))) =
      u₂ (finRotate (m + 1) j) := by
  have : NeZero (2 * (m + 1)) := ⟨by omega⟩
  by_cases hj : j = Fin.last m
  · subst hj
    have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (Sum.inr (Fin.last m))) =
        spliceEquiv (m + 1) (Sum.inl 0) := by
      ext; rw [finRotate_apply, Fin.val_add, spliceEquiv_inr_val, spliceEquiv_inl_val,
        Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2 * (m + 1)), Fin.val_last]
      have hsum : m + 1 + m + 1 = 2 * (m + 1) := by omega
      simp [hsum]
    simp [spliceWord, hrot, h0]
  · have hlt : j.val < m := Nat.lt_of_le_of_ne (Fin.le_last j) (Fin.val_ne_of_ne hj)
    have hrot : finRotate (2 * (m + 1)) (spliceEquiv (m + 1) (Sum.inr j)) =
        spliceEquiv (m + 1) (Sum.inr (finRotate (m + 1) j)) := by
      ext; rw [finRotate_apply, Fin.val_add, spliceEquiv_inr_val, spliceEquiv_inr_val,
        coe_finRotate_of_ne_last hj, Fin.val_one',
        Nat.mod_eq_of_lt (by omega : 1 < 2 * (m + 1)), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [spliceWord, hrot]

private theorem edge_splice_apply {m : ℕ} (u₁ u₂ : Fin (m + 1) → α) (h0 : u₁ 0 = u₂ 0)
    (x : Fin (m + 1) ⊕ Fin (m + 1)) :
    s(spliceWord u₁ u₂ (spliceEquiv (m + 1) x),
        spliceWord u₁ u₂ (finRotate (2 * (m + 1)) (spliceEquiv (m + 1) x))) =
      pairEdge u₁ u₂ x := by
  rcases x with i | j
  · rw [splice_finRotate_inl u₁ u₂ h0 i]; simp [spliceWord, pairEdge]
  · rw [splice_finRotate_inr u₁ u₂ h0 j]; simp [spliceWord, pairEdge]

private theorem image_union_eq_image_splice [DecidableEq α] {k : ℕ} (u₁ u₂ : Fin k → α) :
    univ.image u₁ ∪ univ.image u₂ = univ.image (spliceWord u₁ u₂) := by
  ext a
  simp only [mem_union, mem_image, mem_univ, true_and, spliceWord, Function.comp_apply]
  exact (Sum.exists (p := fun s ↦ Sum.elim u₁ u₂ s = a)).symm.trans
    ((spliceEquiv k).symm.surjective.exists)

private theorem not_card_image_splice_eq [DecidableEq α] {m : ℕ}
    (u₁ u₂ : Fin (m + 1) → α) (h0 : u₁ 0 = u₂ 0)
    (hshare : ∃ i j : Fin (m + 1),
      s(u₁ i, u₁ (finRotate (m + 1) i)) = s(u₂ j, u₂ (finRotate (m + 1) j)))
    (hW : ∀ t : Fin (2 * (m + 1)),
      spliceWord u₁ u₂ t ≠ spliceWord u₁ u₂ (finRotate (2 * (m + 1)) t) →
      ∃ s ≠ t,
        s(spliceWord u₁ u₂ s, spliceWord u₁ u₂ (finRotate (2 * (m + 1)) s)) =
        s(spliceWord u₁ u₂ t, spliceWord u₁ u₂ (finRotate (2 * (m + 1)) t))) :
    #(univ.image (spliceWord u₁ u₂)) ≠ m + 1 + 1 := by
  intro hv
  have : NeZero (2 * (m + 1)) := ⟨by omega⟩
  let σ := spliceEquiv (m + 1)
  let W := spliceWord u₁ u₂
  have hnoloop :=
    (ne_and_card_edge_fiber_eq_two_of_no_singleton_nonloop_edge_of_card_image_eq W hW hv).1
  have htree : IsTreeWalk (m + 1) (canonicalWalk (cyclicPath W)) :=
    isTreeWalk_canonicalWalk_cyclic W (fun t ↦ hW t (hnoloop t)) hv
  have hc0 : canonicalWalk (cyclicPath W) (m + 1) = 0 := by
    have hk : Fin.ofNat (2 * (m + 1)) (m + 1) = σ (Sum.inr 0) := by
      ext; simp [σ, spliceEquiv_inr_val, Fin.ofNat_eq_cast,
        Nat.mod_eq_of_lt (by omega : m + 1 < 2 * (m + 1))]
    have h0' : (0 : Fin (2 * (m + 1))) = σ (Sum.inl 0) := by ext; simp [σ, spliceEquiv_inl_val]
    have hkW : cyclicPath W ⟨m + 1, by omega⟩ = cyclicPath W 0 := by
      rw [cyclicPath_apply, hk, cyclicPath_zero, h0']; simp [W, σ, spliceWord, h0]
    exact ((canonicalWalk_eq_iff (cyclicPath W) ⟨m + 1, by omega⟩ 0).mpr hkW).trans
      (canonicalWalk_zero (cyclicPath W))
  obtain ⟨i, j, hij⟩ := hshare
  have hW_ij : s(W (σ (Sum.inl i)), W (finRotate (2 * (m + 1)) (σ (Sum.inl i)))) =
      s(W (σ (Sum.inr j)), W (finRotate (2 * (m + 1)) (σ (Sum.inr j)))) := by
    dsimp only [W, σ]
    rw [edge_splice_apply u₁ u₂ h0, edge_splice_apply u₁ u₂ h0]
    exact hij
  have hceq : s(canonicalWalk (cyclicPath W) (σ (Sum.inl i)).val,
        canonicalWalk (cyclicPath W) ((σ (Sum.inl i)).val + 1)) =
      s(canonicalWalk (cyclicPath W) (σ (Sum.inr j)).val,
        canonicalWalk (cyclicPath W) ((σ (Sum.inr j)).val + 1)) := by
    have hcast : s(canonicalWalk (cyclicPath W) (σ (Sum.inl i)).castSucc,
          canonicalWalk (cyclicPath W) (σ (Sum.inl i)).succ) =
        s(canonicalWalk (cyclicPath W) (σ (Sum.inr j)).castSucc,
          canonicalWalk (cyclicPath W) (σ (Sum.inr j)).succ) := by
      simpa only [Sym2.eq_iff, canonicalWalk_eq_iff, cyclicPath_castSucc, cyclicPath_succ]
        using hW_ij
    simpa only [Fin.val_castSucc, Fin.val_succ] using hcast
  exact htree.edge_ne_of_eq_zero hc0 (i := (σ (Sum.inl i)).val) (j := (σ (Sum.inr j)).val)
    (by rw [spliceEquiv_inl_val]; exact i.isLt) (by rw [spliceEquiv_inr_val]; omega)
    (by rw [spliceEquiv_inr_val]; omega) hceq

private theorem card_image_union_le_of_eq_zero [DecidableEq α] {m : ℕ}
    (u₁ u₂ : Fin (m + 1) → α) (h0 : u₁ 0 = u₂ 0)
    (hshare : ∃ i j : Fin (m + 1),
      s(u₁ i, u₁ (finRotate (m + 1) i)) = s(u₂ j, u₂ (finRotate (m + 1) j)))
    (hpair : ∀ t, ¬(pairEdge u₁ u₂ t).IsDiag → ∃ s ≠ t, pairEdge u₁ u₂ s = pairEdge u₁ u₂ t) :
    #(univ.image u₁ ∪ univ.image u₂) ≤ m + 1 := by
  have hW : ∀ t : Fin (2 * (m + 1)),
      spliceWord u₁ u₂ t ≠ spliceWord u₁ u₂ (finRotate (2 * (m + 1)) t) →
      ∃ s ≠ t,
        s(spliceWord u₁ u₂ s, spliceWord u₁ u₂ (finRotate (2 * (m + 1)) s)) =
        s(spliceWord u₁ u₂ t, spliceWord u₁ u₂ (finRotate (2 * (m + 1)) t)) := by
    intro t ht
    have hnd : ¬(pairEdge u₁ u₂ ((spliceEquiv (m + 1)).symm t)).IsDiag := by
      rw [← edge_splice_apply u₁ u₂ h0 ((spliceEquiv (m + 1)).symm t),
        (spliceEquiv (m + 1)).apply_symm_apply, Sym2.mk_isDiag_iff]
      exact ht
    obtain ⟨s, hs, heq⟩ := hpair ((spliceEquiv (m + 1)).symm t) hnd
    refine ⟨spliceEquiv (m + 1) s,
      fun h ↦ hs ((spliceEquiv (m + 1)).symm_apply_eq.mpr h.symm).symm, ?_⟩
    rw [edge_splice_apply u₁ u₂ h0 s, heq,
      ← edge_splice_apply u₁ u₂ h0 ((spliceEquiv (m + 1)).symm t),
      (spliceEquiv (m + 1)).apply_symm_apply]
  rw [image_union_eq_image_splice u₁ u₂]
  have hle : #(univ.image (spliceWord u₁ u₂)) ≤ m + 1 + 1 := by
    simpa using card_image_le_div_two_add_one_of_no_singleton_nonloop_edge _ hW
  have hne := not_card_image_splice_eq u₁ u₂ h0 hshare hW
  omega

/-- Two cyclic trace words of length `k` that share at least one unordered edge and have no
singleton nonloop unordered edge across their combined steps `Fin k ⊕ Fin k` visit at most `k`
distinct vertices in total. -/
theorem card_image_union_le_of_shared_edge_of_no_singleton_nonloop_edge
    [DecidableEq α] {k : ℕ} (w₁ w₂ : Fin k → α)
    (hshare : ∃ i j : Fin k, s(w₁ i, w₁ (finRotate k i)) = s(w₂ j, w₂ (finRotate k j)))
    (hpair : ∀ t : Fin k ⊕ Fin k,
      ¬(Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k i)))
          (fun i ↦ s(w₂ i, w₂ (finRotate k i))) t).IsDiag →
        ∃ s ≠ t,
          Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k i)))
            (fun i ↦ s(w₂ i, w₂ (finRotate k i))) s =
          Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k i)))
            (fun i ↦ s(w₂ i, w₂ (finRotate k i))) t) :
    #(univ.image w₁ ∪ univ.image w₂) ≤ k := by
  rcases k with _ | m
  · obtain ⟨i, -⟩ := hshare
    exact Fin.elim0 i
  · obtain ⟨i₀, j₀, hij₀⟩ := hshare
    obtain ⟨r₁, r₂, hr⟩ : ∃ r₁ r₂ : Fin (m + 1), w₁ r₁ = w₂ r₂ := by
      rcases Sym2.eq_iff.mp hij₀ with ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨i₀, j₀, h⟩
      · exact ⟨i₀, finRotate (m + 1) j₀, h⟩
    let u₁ : Fin (m + 1) → α := fun i ↦ w₁ (i + r₁)
    let u₂ : Fin (m + 1) → α := fun j ↦ w₂ (j + r₂)
    have himg (w : Fin (m + 1) → α) (r : Fin (m + 1)) :
        univ.image (fun i ↦ w (i + r)) = univ.image w := by
      ext a; simp only [mem_image, mem_univ, true_and]
      exact ((Equiv.addRight r).surjective.exists (p := fun i ↦ w i = a)).symm
    rw [← himg w₁ r₁, ← himg w₂ r₂]
    let τ : Fin (m + 1) ⊕ Fin (m + 1) ≃ Fin (m + 1) ⊕ Fin (m + 1) :=
      Equiv.sumCongr (Equiv.addRight r₁) (Equiv.addRight r₂)
    have hτ (x : Fin (m + 1) ⊕ Fin (m + 1)) : pairEdge u₁ u₂ x = pairEdge w₁ w₂ (τ x) := by
      rcases x with i | j <;> simp [pairEdge, τ, u₁, u₂, finRotate_apply, add_right_comm]
    have hshare' : s(u₁ (i₀ - r₁), u₁ (finRotate (m + 1) (i₀ - r₁))) =
        s(u₂ (j₀ - r₂), u₂ (finRotate (m + 1) (j₀ - r₂))) := by
      have h1 := hτ (Sum.inl (i₀ - r₁))
      have h2 := hτ (Sum.inr (j₀ - r₂))
      simp only [pairEdge, Sum.elim_inl, Sum.elim_inr, τ, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Equiv.coe_addRight, sub_add_cancel] at h1 h2
      exact h1.trans (hij₀.trans h2.symm)
    refine card_image_union_le_of_eq_zero u₁ u₂ (by simp [u₁, u₂, hr])
      ⟨i₀ - r₁, j₀ - r₂, hshare'⟩ fun t ht ↦ ?_
    obtain ⟨s, hs, heq⟩ := hpair (τ t) (by change ¬(pairEdge w₁ w₂ (τ t)).IsDiag; rwa [← hτ t])
    refine ⟨τ.symm s, fun h ↦ hs (τ.eq_symm_apply.mp h.symm).symm, ?_⟩
    change pairEdge w₁ w₂ s = pairEdge w₁ w₂ (τ t) at heq
    simpa only [hτ, τ.apply_symm_apply] using heq

/-- Over a finite vertex set `α`, there are at most `|α|^k * k^(2 * k)` pairs of cyclic trace words
of length `k` that share an unordered edge and have no singleton nonloop unordered edge across
`Fin k ⊕ Fin k`. -/
theorem card_filter_pair_le_of_shared_edge_of_no_singleton_nonloop_edge
    [Fintype α] [DecidableEq α] (k : ℕ) :
    #{p : (Fin k → α) × (Fin k → α) |
      (∃ i j : Fin k, s(p.1 i, p.1 (finRotate k i)) = s(p.2 j, p.2 (finRotate k j))) ∧
        ∀ t : Fin k ⊕ Fin k,
          ¬(Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k i)))
              (fun i ↦ s(p.2 i, p.2 (finRotate k i))) t).IsDiag →
            ∃ s ≠ t,
              Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k i)))
                (fun i ↦ s(p.2 i, p.2 (finRotate k i))) s =
              Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k i)))
                (fun i ↦ s(p.2 i, p.2 (finRotate k i))) t} ≤
      Fintype.card α ^ k * k ^ (2 * k) := by
  rcases k with _ | m
  · simp
  · rcases isEmpty_or_nonempty α with hα | hα
    · simp
    · refine (card_le_card_of_injOn
        (t := {f : Fin (m + 1) ⊕ Fin (m + 1) → α | #(univ.image f) ≤ m + 1})
        (fun p ↦ Sum.elim p.1 p.2) (fun p hp ↦ ?_) ?_).trans ?_
      · simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        have himg : univ.image (Sum.elim p.1 p.2) = univ.image p.1 ∪ univ.image p.2 := by
          ext a; simp [Sum.exists]
        rw [himg]
        exact card_image_union_le_of_shared_edge_of_no_singleton_nonloop_edge p.1 p.2 hp.1 hp.2
      · intro p₁ _ p₂ _ heq
        exact (Equiv.sumArrowEquivProdArrow (Fin (m + 1)) (Fin (m + 1)) α).symm.injective heq
      · simpa [Fintype.card_sum, two_mul] using
          card_filter_card_image_le (α := Fin (m + 1) ⊕ Fin (m + 1)) (β := α) (m + 1)

end TauCeti
