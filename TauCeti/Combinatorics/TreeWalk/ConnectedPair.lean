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

Splicing two cyclic words `(w₁, w₂)` of total length `k₁ + k₂ = 2 * m` satisfying `IsConnectedPair`
at a shared vertex yields a singleton-free cyclic word returning to its root at `k₁`;
`IsTreeWalk.ne_edge_of_lt_of_le` forces `#V ≤ m`, giving at most `|α| ^ m * m ^ (2 * m)` pairs.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
-/

public section

open Finset

namespace TauCeti.TreeWalk

section CyclicPairs

variable {α : Type*}

/-- Two cyclic trace words form a connected singleton-free pair when they share an unordered edge
and every unordered edge in their combined step family occurs at least twice. -/
abbrev IsConnectedPair {k₁ k₂ : ℕ} (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α) : Prop :=
  (∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k₁ t₁)) = s(w₂ t₂, w₂ (finRotate k₂ t₂))) ∧
    ∀ x : Fin k₁ ⊕ Fin k₂, ∃ y ≠ x,
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) y =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) x

private theorem append_comp_finRotate_of_eq_zero {m₁ m₂ : ℕ}
    (u : Fin (m₁ + 1) → α) (v : Fin (m₂ + 1) → α) (h0 : u 0 = v 0) :
    Fin.append u v ∘ finRotate ((m₁ + 1) + (m₂ + 1)) =
      Fin.append (u ∘ finRotate (m₁ + 1)) (v ∘ finRotate (m₂ + 1)) := by
  have hswap : Fin.append u v ∘
      Equiv.swap (Fin.castAdd (m₂ + 1) 0) (Fin.natAdd (m₁ + 1) 0) = Fin.append u v := by
    funext x; rw [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs with hx₁ hx₂ <;> simp [*]
  rw [Equiv.Perm.finRotate_add_eq_swap_mul_finSumPerm, Equiv.Perm.coe_mul, ← Function.comp_assoc,
    hswap, Fin.append_comp_finSumPerm]

private def spliceWord {m₁ m₂ : ℕ} (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) : Fin ((m₁ + 1) + (m₂ + 1)) → α :=
  Fin.append (fun i ↦ w₁ (i + r₁)) (fun j ↦ w₂ (j + r₂))

private def spliceStepEquiv {m₁ m₂ : ℕ} (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) :
    Fin (m₁ + 1) ⊕ Fin (m₂ + 1) ≃ Fin ((m₁ + 1) + (m₂ + 1)) :=
  (Equiv.sumCongr (Equiv.addRight r₁).symm (Equiv.addRight r₂).symm).trans finSumFinEquiv

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
        Fin.append (fun i ↦ w₁ (finRotate (m₁ + 1) i + r₁))
          (fun j ↦ w₂ (finRotate (m₂ + 1) j + r₂)) a :=
    congrFun (append_comp_finRotate_of_eq_zero (fun i ↦ w₁ (i + r₁))
      (fun j ↦ w₂ (j + r₂)) (by simpa using hr)) a
  cases x <;> dsimp only <;> rw [hrot] <;>
    simp only [spliceWord, spliceStepEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr, Equiv.addRight_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.append_left, Fin.append_right, Fin.finRotate_add_right, neg_add_cancel_right,
      Sum.elim_inl, Sum.elim_inr]

variable [DecidableEq α]

private theorem image_spliceWord {m₁ m₂ : ℕ} (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) :
    univ.image (spliceWord w₁ w₂ r₁ r₂) = univ.image (Sum.elim w₁ w₂) := by
  ext v; simp only [mem_image, mem_univ, true_and]
  refine ⟨fun ⟨a, ha⟩ ↦ ha ▸ Fin.addCases (fun i ↦ ⟨.inl (i + r₁), by simp [spliceWord]⟩)
      (fun j ↦ ⟨.inr (j + r₂), by simp [spliceWord]⟩) a,
    fun ⟨x, hx⟩ ↦ hx ▸ ⟨spliceStepEquiv r₁ r₂ x, by cases x <;> simp [spliceWord, spliceStepEquiv]⟩⟩

private theorem finCongr_symm_finRotate {n₁ n₂ : ℕ} (h : n₁ = n₂) (a : Fin n₂) :
    (finCongr h).symm (finRotate n₂ a) = finRotate n₁ ((finCongr h).symm a) := by cases h; rfl

/-- Two cyclic words `w₁` and `w₂` of total length `k₁ + k₂ = 2 * m` sharing an unordered edge
without combined singleton unordered edges visit at most `m` distinct vertices together. -/
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
  cases k₁ with | zero => exact t₁.elim0 | succ m₁ =>
  cases k₂ with | zero => exact t₂.elim0 | succ m₂ =>
  have : NeZero m := ⟨by omega⟩; have : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨r₁, r₂, hr₁₂⟩ : ∃ (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)), w₁ r₁ = w₂ r₂ := by
    rcases Sym2.eq_iff.mp ht₁₂ with ⟨h, -⟩ | ⟨h, -⟩; exacts [⟨t₁, t₂, h⟩, ⟨t₁, _, h⟩]
  let W : Fin (2 * m) → α := spliceWord w₁ w₂ r₁ r₂ ∘ (finCongr hk).symm
  let stepEquiv := (spliceStepEquiv r₁ r₂).trans (finCongr hk)
  have hedge_step (x : Fin (m₁ + 1) ⊕ Fin (m₂ + 1)) :
      s(W (stepEquiv x), W (finRotate (2 * m) (stepEquiv x))) =
        Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m₁ + 1) t)))
          (fun t ↦ s(w₂ t, w₂ (finRotate (m₂ + 1) t))) x := by
    simp only [W, stepEquiv, Function.comp_apply, finCongr_symm_finRotate hk, Equiv.trans_apply,
      Equiv.symm_apply_apply]
    exact spliceWord_edge_stepEquiv w₁ w₂ hr₁₂ x
  have hW_ns : ∀ a : Fin (2 * m), ∃ b ≠ a,
      s(W b, W (finRotate (2 * m) b)) = s(W a, W (finRotate (2 * m) a)) := fun a ↦ by
    obtain ⟨y, hy, hyeq⟩ := hns (stepEquiv.symm a)
    exact ⟨stepEquiv y, fun h ↦ hy (stepEquiv.symm_apply_eq.mpr h.symm).symm, by
      rw [hedge_step y, ← stepEquiv.apply_symm_apply a, hedge_step (stepEquiv.symm a), hyeq]⟩
  have himage : univ.image W = univ.image (Sum.elim w₁ w₂) := by
    rw [← image_spliceWord w₁ w₂ r₁ r₂]; ext v
    simp only [W, mem_image, mem_univ, true_and, Function.comp_apply]
    exact ((finCongr hk).symm.surjective.exists (p := (spliceWord w₁ w₂ r₁ r₂ · = v))).symm
  have hle : #(univ.image W) ≤ m + 1 := by
    simpa [Nat.mul_div_right m (by omega : 0 < 2)] using
      card_image_le_div_two_add_one_of_no_singleton_edge W hW_ns
  rw [← himage]; by_contra hgt
  have htree := isTreeWalk_canonicalWalk_cyclic W hW_ns (by omega)
  have hroot_mid : canonicalWalk (cyclicPath W) (m₁ + 1) = 0 := by
    simpa [Fin.val_castSucc] using (canonicalWalk_eq_iff (cyclicPath W)
      (finCongr hk (Fin.natAdd (m₁ + 1) 0)).castSucc (0 : Fin (2 * m)).castSucc).mpr (by
      simp only [cyclicPath_castSucc, W, Function.comp_apply, (finCongr hk).symm_apply_apply,
        show (finCongr hk).symm 0 = Fin.castAdd (m₂ + 1) 0 by ext; simp, spliceWord,
        Fin.append_right, Fin.append_left, zero_add, hr₁₂])
  let a := stepEquiv (.inl t₁); let b := stepEquiv (.inr t₂)
  have hab_canon : s(canonicalWalk (cyclicPath W) a.val, canonicalWalk (cyclicPath W) (a.val + 1)) =
      s(canonicalWalk (cyclicPath W) b.val, canonicalWalk (cyclicPath W) (b.val + 1)) := by
    have hca : s(cyclicPath W a.castSucc, cyclicPath W a.succ) =
        s(cyclicPath W b.castSucc, cyclicPath W b.succ) := by
      simpa only [cyclicPath_castSucc, cyclicPath_succ, a, b, hedge_step,
        Sum.elim_inl, Sum.elim_inr] using ht₁₂
    simpa only [Sym2.eq_iff, ← canonicalWalk_eq_iff (cyclicPath W),
      Fin.val_castSucc, Fin.val_succ] using hca
  exact htree.ne_edge_of_lt_of_le hroot_mid
    (by simpa [a, stepEquiv, spliceStepEquiv] using (t₁ + -r₁).isLt)
    (by simp [b, stepEquiv, spliceStepEquiv]) b.isLt hab_canon

/-- Connected singleton-free pairs of length-`k` cyclic words visit at most `k` vertices. -/
theorem card_image_sumElim_le {k : ℕ} (w₁ w₂ : Fin k → α) (h : IsConnectedPair w₁ w₂) :
    #(univ.image (Sum.elim w₁ w₂)) ≤ k :=
  card_image_sumElim_le_of_add_eq_two_mul w₁ w₂ (two_mul k).symm h.1 h.2

/-- On a finite vertex type `α`, at most `|α| ^ m * m ^ (2 * m)` pairs `(w₁, w₂)` of total length
`k₁ + k₂ = 2 * m` satisfy `IsConnectedPair`. -/
theorem card_filter_connectedPair_le_of_add_eq_two_mul [Fintype α] {k₁ k₂ m : ℕ}
    (hk : k₁ + k₂ = 2 * m) :
    #({p : (Fin k₁ → α) × (Fin k₂ → α) | IsConnectedPair p.1 p.2}) ≤
      Fintype.card α ^ m * m ^ (2 * m) := by
  rcases eq_or_ne k₁ 0 with rfl | hk₁; · simp [IsConnectedPair]
  rcases eq_or_ne k₂ 0 with rfl | hk₂; · simp [IsConnectedPair]
  rcases isEmpty_or_nonempty α with hα | hα
  · have : Nonempty (Fin k₁) := ⟨⟨0, Nat.pos_of_ne_zero hk₁⟩⟩
    simp [Finset.eq_empty_of_isEmpty, show m ≠ 0 by omega]
  · let eqv := Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) α
    refine (card_le_card_of_injOn eqv.symm (fun p hp ↦ ?_)
      fun _ _ _ _ h ↦ eqv.symm.injective h).trans (by
      simpa [hk] using card_filter_card_image_le (α := Fin k₁ ⊕ Fin k₂) (β := α) m)
    obtain ⟨hshare, hns⟩ := (mem_filter.mp hp).2
    exact mem_filter.mpr ⟨mem_univ _, card_image_sumElim_le_of_add_eq_two_mul p.1 p.2 hk hshare hns⟩

/-- On a finite vertex type `α`, at most `|α| ^ k * k ^ (2 * k)` pairs of length-`k` cyclic words
satisfy `IsConnectedPair`. -/
theorem card_filter_connectedPair_le [Fintype α] (k : ℕ) :
    #({p : (Fin k → α) × (Fin k → α) | IsConnectedPair p.1 p.2}) ≤
      Fintype.card α ^ k * k ^ (2 * k) :=
  card_filter_connectedPair_le_of_add_eq_two_mul (two_mul k).symm

end CyclicPairs

end TauCeti.TreeWalk
