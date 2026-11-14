/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Data.Fintype.SmallRange
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Vertex and counting bounds for connected pairs of trace words

In the variance and covariance expansions for traces of powers of Wigner matrices, pairs of cyclic
words `(w₁, w₂)` with disjoint sets of unordered edges cancel by independence, while pairs whose
combined step set has a singleton unordered edge have vanishing expectation when entries are
centered. Every remaining pair shares at least one unordered edge and traverses every combined
unordered edge at least twice (`TauCeti.TreeWalk.IsConnectedPair`).

Concatenating two such cyclic words at a shared vertex produces a single singleton-free cyclic word
of length `k₁ + k₂`. When `k₁ + k₂ = 2 * m`, the single-word bound gives at most `m + 1` combined
vertices. Equality `#V = m + 1` is impossible: canonicalizing the concatenated walk would yield a
closed double-traversal tree walk that returns to the root at the concatenation time `k₁` while
sharing an unordered edge between `[0, k₁)` and `[k₁, 2 * m)`, contradicting
`TauCeti.TreeWalk.IsTreeWalk.ne_edge_of_lt_of_le`. Hence `(w₁, w₂)` visits at most `m` distinct
vertices in total, and on an `n`-element vertex set there are at most `n ^ m * m ^ (2 * m)` such
pairs.

## Main definitions

* `TauCeti.TreeWalk.IsConnectedPair`: two cyclic words share at least one unordered step edge and
  traverse every unordered edge in their combined step multiset at least twice.

## Main results

* `TauCeti.TreeWalk.card_image_sumElim_le_of_add_eq_two_mul` and
  `TauCeti.TreeWalk.card_image_sumElim_le`: two connected singleton-free cyclic words of total
  length `2 * m` (in particular, two length-`k` words with `m = k`) visit at most `m` vertices
  together.
* `TauCeti.TreeWalk.card_filter_connectedPair_le_of_add_eq_two_mul` and
  `TauCeti.TreeWalk.card_filter_connectedPair_le`: at most `|α| ^ m * m ^ (2 * m)` pairs `(w₁, w₂)`
  of total length `2 * m` satisfy `IsConnectedPair`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.
-/

public section

open Finset

namespace TauCeti.TreeWalk

section CyclicPairs

variable {α : Type*}

/-- Two cyclic trace words `w₁` and `w₂` form a connected singleton-free pair when they share at
least one unordered step edge and every unordered step edge in their combined step multiset occurs
at least twice. -/
abbrev IsConnectedPair {k₁ k₂ : ℕ} (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α) : Prop :=
  (∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k₁ t₁)) = s(w₂ t₂, w₂ (finRotate k₂ t₂))) ∧
    ∀ x : Fin k₁ ⊕ Fin k₂, ∃ y ≠ x,
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) y =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) x

/-- Appending two nonempty tuples that agree at `0` commutes with `finRotate` via `finSumPerm`. -/
private theorem append_comp_finRotate_of_eq_zero {m₁ m₂ : ℕ}
    (u : Fin (m₁ + 1) → α) (v : Fin (m₂ + 1) → α) (h0 : u 0 = v 0) :
    Fin.append u v ∘ finRotate ((m₁ + 1) + (m₂ + 1)) =
      Fin.append (u ∘ finRotate (m₁ + 1)) (v ∘ finRotate (m₂ + 1)) := by
  have hswap : Fin.append u v ∘
      Equiv.swap (Fin.castAdd (m₂ + 1) 0) (Fin.natAdd (m₁ + 1) 0) = Fin.append u v := by
    funext x
    rw [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs with hx₁ hx₂
    · rw [hx₁, Fin.append_left, Fin.append_right, h0]
    · rw [hx₂, Fin.append_right, Fin.append_left, h0]
    · rfl
  rw [Equiv.Perm.finRotate_add_eq_swap_mul_finSumPerm, Equiv.Perm.coe_mul, ← Function.comp_assoc,
    hswap, Fin.append_comp_finSumPerm]

/-- Splicing two cyclic words `w₁` and `w₂` at shared vertices `w₁ r₁ = w₂ r₂` into a cyclic word
on `Fin ((m₁ + 1) + (m₂ + 1))`. -/
private def spliceWord {m₁ m₂ : ℕ} (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) : Fin ((m₁ + 1) + (m₂ + 1)) → α :=
  Fin.append (fun i ↦ w₁ (i + r₁)) (fun j ↦ w₂ (j + r₂))

/-- Equivalence identifying combined step indices of `w₁` and `w₂` with those of `spliceWord`. -/
private def spliceStepEquiv {m₁ m₂ : ℕ} (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) :
    Fin (m₁ + 1) ⊕ Fin (m₂ + 1) ≃ Fin ((m₁ + 1) + (m₂ + 1)) :=
  (Equiv.sumCongr (Equiv.addRight r₁).symm (Equiv.addRight r₂).symm).trans finSumFinEquiv

/-- Each unordered step edge of `spliceWord` matches the corresponding step edge of `w₁` or `w₂`. -/
private theorem spliceWord_edge_stepEquiv {m₁ m₂ : ℕ}
    (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    {r₁ : Fin (m₁ + 1)} {r₂ : Fin (m₂ + 1)} (hr : w₁ r₁ = w₂ r₂)
    (x : Fin (m₁ + 1) ⊕ Fin (m₂ + 1)) :
    let u := spliceWord w₁ w₂ r₁ r₂
    let s := spliceStepEquiv r₁ r₂ x
    s(u s, u (finRotate ((m₁ + 1) + (m₂ + 1)) s)) =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m₁ + 1) t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate (m₂ + 1) t))) x := by
  have hrot (a : Fin ((m₁ + 1) + (m₂ + 1))) :
      spliceWord w₁ w₂ r₁ r₂ (finRotate ((m₁ + 1) + (m₂ + 1)) a) =
        Fin.append ((fun i ↦ w₁ (i + r₁)) ∘ finRotate (m₁ + 1))
          ((fun j ↦ w₂ (j + r₂)) ∘ finRotate (m₂ + 1)) a :=
    congrFun (append_comp_finRotate_of_eq_zero (fun i ↦ w₁ (i + r₁))
      (fun j ↦ w₂ (j + r₂)) (by simpa using hr)) a
  cases x with
  | inl t =>
    dsimp only
    rw [hrot]
    simp only [spliceWord, spliceStepEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.addRight_symm_apply, finSumFinEquiv_apply_left, Fin.append_left, Function.comp_apply,
      Fin.finRotate_add_right, neg_add_cancel_right, Sum.elim_inl]
  | inr t =>
    dsimp only
    rw [hrot]
    simp only [spliceWord, spliceStepEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.addRight_symm_apply, finSumFinEquiv_apply_right, Fin.append_right, Function.comp_apply,
      Fin.finRotate_add_right, neg_add_cancel_right, Sum.elim_inr]

variable [DecidableEq α]

/-- `spliceWord` visits the exact same vertex set as `Sum.elim w₁ w₂`. -/
private theorem image_spliceWord {m₁ m₂ : ℕ}
    (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) :
    univ.image (spliceWord w₁ w₂ r₁ r₂) = univ.image (Sum.elim w₁ w₂) := by
  ext v
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Fin.addCases with
    | left i => exact ⟨.inl (i + r₁), by simp [spliceWord]⟩
    | right j => exact ⟨.inr (j + r₂), by simp [spliceWord]⟩
  · rintro ⟨x, rfl⟩
    cases x with
    | inl t => exact ⟨spliceStepEquiv r₁ r₂ (.inl t), by simp [spliceWord, spliceStepEquiv]⟩
    | inr t => exact ⟨spliceStepEquiv r₁ r₂ (.inr t), by simp [spliceWord, spliceStepEquiv]⟩

private theorem finCongr_symm_finRotate {n₁ n₂ : ℕ} (h : n₁ = n₂) (a : Fin n₂) :
    (finCongr h).symm (finRotate n₂ a) = finRotate n₁ ((finCongr h).symm a) := by
  cases h; rfl

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
  have : NeZero m := ⟨by omega⟩
  have : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨r₁, r₂, hr₁₂⟩ : ∃ (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)), w₁ r₁ = w₂ r₂ := by
    rcases Sym2.eq_iff.mp ht₁₂ with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨t₁, t₂, h⟩
    · exact ⟨t₁, finRotate (m₂ + 1) t₂, h⟩
  let W : Fin (2 * m) → α := spliceWord w₁ w₂ r₁ r₂ ∘ (finCongr hk).symm
  let stepEquiv : Fin (m₁ + 1) ⊕ Fin (m₂ + 1) ≃ Fin (2 * m) :=
    (spliceStepEquiv r₁ r₂).trans (finCongr hk)
  have hedge_step (x : Fin (m₁ + 1) ⊕ Fin (m₂ + 1)) :
      s(W (stepEquiv x), W (finRotate (2 * m) (stepEquiv x))) =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m₁ + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m₂ + 1) t))) x := by
    simp only [W, stepEquiv, Function.comp_apply, finCongr_symm_finRotate hk, Equiv.trans_apply,
      Equiv.symm_apply_apply]
    exact spliceWord_edge_stepEquiv w₁ w₂ hr₁₂ x
  have hW_ns : ∀ a : Fin (2 * m), ∃ b ≠ a,
      s(W b, W (finRotate (2 * m) b)) = s(W a, W (finRotate (2 * m) a)) := by
    intro a
    obtain ⟨y, hy, hyeq⟩ := hns (stepEquiv.symm a)
    refine ⟨stepEquiv y, fun h ↦ hy (stepEquiv.symm_apply_eq.mpr h.symm).symm, ?_⟩
    rw [hedge_step y, ← stepEquiv.apply_symm_apply a, hedge_step (stepEquiv.symm a), hyeq]
  have himage : univ.image W = univ.image (Sum.elim w₁ w₂) := by
    rw [← image_spliceWord w₁ w₂ r₁ r₂]
    ext v
    simp only [W, mem_image, mem_univ, true_and, Function.comp_apply]
    exact (finCongr hk).symm.exists_congr_left
  have hle : #(univ.image W) ≤ m + 1 := by
    simpa [Nat.mul_div_right m (by omega : 0 < 2)] using
      card_image_le_div_two_add_one_of_no_singleton_edge W hW_ns
  rw [← himage]
  by_contra hgt
  have htree : IsTreeWalk m (canonicalWalk (cyclicPath W)) :=
    isTreeWalk_canonicalWalk_cyclic W hW_ns (by omega)
  -- `W` revisits `W 0` at index `m₁ + 1`, so `canonicalWalk (cyclicPath W)` returns to `0` there.
  let mid : Fin (2 * m) := finCongr hk (Fin.natAdd (m₁ + 1) 0)
  have hroot_mid : canonicalWalk (cyclicPath W) (m₁ + 1) = 0 := by
    have hmid_eq : cyclicPath W mid.castSucc = cyclicPath W (0 : Fin (2 * m)).castSucc := by
      rw [cyclicPath_castSucc, cyclicPath_castSucc]
      have h0 : (finCongr hk).symm 0 = Fin.castAdd (m₂ + 1) 0 := by ext; simp
      have hm : (finCongr hk).symm mid = Fin.natAdd (m₁ + 1) 0 := (finCongr hk).symm_apply_apply _
      dsimp only [W, Function.comp_apply]
      rw [hm, h0]
      simp [spliceWord, hr₁₂]
    simpa [mid, Fin.val_castSucc] using
      (canonicalWalk_eq_iff (cyclicPath W) mid.castSucc (0 : Fin (2 * m)).castSucc).mpr hmid_eq
  -- `stepEquiv (.inl t₁) < m₁ + 1 ≤ stepEquiv (.inr t₂)` share an edge, contradicting `htree`.
  let a := stepEquiv (.inl t₁)
  let b := stepEquiv (.inr t₂)
  have hab_canon :
      s(canonicalWalk (cyclicPath W) a.val, canonicalWalk (cyclicPath W) (a.val + 1)) =
        s(canonicalWalk (cyclicPath W) b.val, canonicalWalk (cyclicPath W) (b.val + 1)) := by
    have hca : s(cyclicPath W a.castSucc, cyclicPath W a.succ) =
        s(cyclicPath W b.castSucc, cyclicPath W b.succ) := by
      simpa only [cyclicPath_castSucc, cyclicPath_succ, a, b, hedge_step,
        Sum.elim_inl, Sum.elim_inr] using ht₁₂
    simpa only [Sym2.eq_iff, ← canonicalWalk_eq_iff (cyclicPath W),
      Fin.val_castSucc, Fin.val_succ] using hca
  have ha_lt : a.val < m₁ + 1 := by
    simp only [a, stepEquiv, spliceStepEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_castAdd]
    exact Fin.is_lt _
  have hb_ge : m₁ + 1 ≤ b.val := by
    simp [b, stepEquiv, spliceStepEquiv]
  exact htree.ne_edge_of_lt_of_le hroot_mid ha_lt hb_ge b.isLt hab_canon

/-- Two cyclic words `w₁, w₂ : Fin k → α` that share an unordered edge and have no singleton
unordered edge in their combined step family visit at most `k` distinct vertices together. -/
theorem card_image_sumElim_le {k : ℕ} (w₁ w₂ : Fin k → α) (h : IsConnectedPair w₁ w₂) :
    #(univ.image (Sum.elim w₁ w₂)) ≤ k :=
  card_image_sumElim_le_of_add_eq_two_mul w₁ w₂ (two_mul k).symm h.1 h.2

/-- On a finite vertex type `α`, there are at most `|α| ^ m * m ^ (2 * m)` pairs `(w₁, w₂)` of
cyclic words of lengths `k₁` and `k₂` with `k₁ + k₂ = 2 * m` that share an unordered edge and
have no singleton unordered edge in their combined step family. -/
theorem card_filter_connectedPair_le_of_add_eq_two_mul [Fintype α] {k₁ k₂ m : ℕ}
    (hk : k₁ + k₂ = 2 * m) :
    #({p : (Fin k₁ → α) × (Fin k₂ → α) | IsConnectedPair p.1 p.2}) ≤
      Fintype.card α ^ m * m ^ (2 * m) := by
  rcases eq_or_ne k₁ 0 with rfl | hk₁
  · simp [IsConnectedPair]
  rcases eq_or_ne k₂ 0 with rfl | hk₂
  · simp [IsConnectedPair]
  cases isEmpty_or_nonempty α with
  | inl hα =>
    have : Nonempty (Fin k₁) := ⟨⟨0, Nat.pos_of_ne_zero hk₁⟩⟩
    have hm : m ≠ 0 := by omega
    simp [Finset.eq_empty_of_isEmpty, hm]
  | inr hα =>
    let eqv := Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) α
    let S : Finset ((Fin k₁ → α) × (Fin k₂ → α)) := {p | IsConnectedPair p.1 p.2}
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
    #({p : (Fin k → α) × (Fin k → α) | IsConnectedPair p.1 p.2}) ≤
      Fintype.card α ^ k * k ^ (2 * k) :=
  card_filter_connectedPair_le_of_add_eq_two_mul (two_mul k).symm

end CyclicPairs

end TauCeti.TreeWalk
