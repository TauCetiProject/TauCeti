/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Data.Fintype.SmallRange
import TauCeti.Data.Fin.Basic

/-!
# Vertex and counting bounds for connected pairs of trace words

Splicing two cyclic words `(w₁, w₂)` of total length `k₁ + k₂ = 2 * m` satisfying `IsConnectedPair`
(characterized by `isConnectedPair_iff`) at a shared vertex yields a singleton-free cyclic word
returning to its root at `k₁`; `IsTreeWalk.ne_edge_of_lt_of_le` forces `#V ≤ m`, giving at most
`|α| ^ m * m ^ (2 * m)` pairs.

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
structure IsConnectedPair {k₁ k₂ : ℕ} (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α) : Prop where
  /-- The two cyclic words share at least one unordered step edge. -/
  shared_edge : ∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k₁ t₁)) = s(w₂ t₂, w₂ (finRotate k₂ t₂))
  /-- Every unordered step edge in the combined step family occurs at least twice. -/
  no_singleton_edge : ∀ x : Fin k₁ ⊕ Fin k₂, ∃ y ≠ x,
    Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
      (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) y =
    Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
      (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) x

/-- Characterization of `IsConnectedPair` by a shared unordered edge and combined
singleton-freeness. -/
theorem isConnectedPair_iff {k₁ k₂ : ℕ} {w₁ : Fin k₁ → α} {w₂ : Fin k₂ → α} :
    IsConnectedPair w₁ w₂ ↔
      (∃ t₁ t₂, s(w₁ t₁, w₁ (finRotate k₁ t₁)) = s(w₂ t₂, w₂ (finRotate k₂ t₂))) ∧
        ∀ x : Fin k₁ ⊕ Fin k₂, ∃ y ≠ x,
          Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
            (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) y =
          Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate k₁ t)))
            (fun t ↦ s(w₂ t, w₂ (finRotate k₂ t))) x :=
  ⟨fun h ↦ ⟨h.shared_edge, h.no_singleton_edge⟩,
   fun ⟨hshare, hns⟩ ↦ ⟨hshare, hns⟩⟩

instance instDecidableIsConnectedPair [DecidableEq α] {k₁ k₂ : ℕ}
    (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α) :
    Decidable (IsConnectedPair w₁ w₂) :=
  decidable_of_iff _ isConnectedPair_iff.symm

/-- An empty left cyclic word cannot form a connected pair, as it has no step edge to share. -/
@[simp] theorem not_isConnectedPair_zero_left {k₂ : ℕ} (w₁ : Fin 0 → α) (w₂ : Fin k₂ → α) :
    ¬ IsConnectedPair w₁ w₂ :=
  fun h ↦ let ⟨t₁, _, _⟩ := h.shared_edge; t₁.elim0

/-- An empty right cyclic word cannot form a connected pair, as it has no step edge to share. -/
@[simp] theorem not_isConnectedPair_zero_right {k₁ : ℕ} (w₁ : Fin k₁ → α) (w₂ : Fin 0 → α) :
    ¬ IsConnectedPair w₁ w₂ :=
  fun h ↦ let ⟨_, t₂, _⟩ := h.shared_edge; t₂.elim0

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
    congrFun (Fin.append_comp_finRotate_of_eq_zero (fun i ↦ w₁ (i + r₁))
      (fun j ↦ w₂ (j + r₂)) (by simpa using hr)) a
  cases x <;> dsimp only <;> rw [hrot] <;>
    simp only [spliceWord, spliceStepEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr, Equiv.addRight_symm_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Fin.append_left, Fin.append_right, Fin.finRotate_add_right, neg_add_cancel_right,
      Sum.elim_inl, Sum.elim_inr]

/-- The spliced cyclic word reindexed along `hk : (m₁ + 1) + (m₂ + 1) = k`. -/
private def spliceWordCast {m₁ m₂ k : ℕ} (hk : (m₁ + 1) + (m₂ + 1) = k)
    (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) : Fin k → α :=
  spliceWord w₁ w₂ r₁ r₂ ∘ (finCongr hk).symm

/-- Step bijection between `Fin (m₁ + 1) ⊕ Fin (m₂ + 1)` and `Fin k` induced by splicing. -/
private def spliceStepEquivCast {m₁ m₂ k : ℕ} (hk : (m₁ + 1) + (m₂ + 1) = k)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) :
    Fin (m₁ + 1) ⊕ Fin (m₂ + 1) ≃ Fin k :=
  (spliceStepEquiv r₁ r₂).trans (finCongr hk)

/-- The reindexed spliced word preserves the unordered edge at every step under
`spliceStepEquivCast`. -/
private theorem spliceWordCast_edge_stepEquiv {m₁ m₂ k : ℕ} (hk : (m₁ + 1) + (m₂ + 1) = k)
    (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    {r₁ : Fin (m₁ + 1)} {r₂ : Fin (m₂ + 1)} (hr : w₁ r₁ = w₂ r₂)
    (x : Fin (m₁ + 1) ⊕ Fin (m₂ + 1)) :
    let W := spliceWordCast hk w₁ w₂ r₁ r₂
    let s := spliceStepEquivCast hk r₁ r₂ x
    s(W s, W (finRotate k s)) =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m₁ + 1) t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate (m₂ + 1) t))) x := by
  simp only [spliceWordCast, spliceStepEquivCast, Function.comp_apply, Equiv.trans_apply,
    finCongr_symm_apply, finCongr_apply, Fin.cast_finRotate hk.symm, Fin.cast_cast, Fin.cast_refl]
  exact spliceWord_edge_stepEquiv w₁ w₂ hr x

/-- Combined singleton-freeness of `(w₁, w₂)` transfers across `spliceStepEquivCast` to the
spliced cyclic word. -/
private theorem spliceWordCast_no_singleton_edge {m₁ m₂ k : ℕ} (hk : (m₁ + 1) + (m₂ + 1) = k)
    (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    {r₁ : Fin (m₁ + 1)} {r₂ : Fin (m₂ + 1)} (hr : w₁ r₁ = w₂ r₂)
    (hns : ∀ x : Fin (m₁ + 1) ⊕ Fin (m₂ + 1), ∃ y ≠ x,
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m₁ + 1) t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate (m₂ + 1) t))) y =
      Sum.elim (fun t ↦ s(w₁ t, w₁ (finRotate (m₁ + 1) t)))
        (fun t ↦ s(w₂ t, w₂ (finRotate (m₂ + 1) t))) x)
    (a : Fin k) :
    let W := spliceWordCast hk w₁ w₂ r₁ r₂
    ∃ b ≠ a, s(W b, W (finRotate k b)) = s(W a, W (finRotate k a)) := by
  let e := spliceStepEquivCast hk r₁ r₂
  obtain ⟨y, hy, hyeq⟩ := hns (e.symm a)
  exact ⟨e y, fun h ↦ hy (e.symm_apply_eq.mpr h.symm).symm, by
    rw [spliceWordCast_edge_stepEquiv hk w₁ w₂ hr y, ← e.apply_symm_apply a,
      spliceWordCast_edge_stepEquiv hk w₁ w₂ hr (e.symm a), hyeq]⟩

variable [DecidableEq α]

private theorem image_spliceWord {m₁ m₂ : ℕ} (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) :
    univ.image (spliceWord w₁ w₂ r₁ r₂) = univ.image (Sum.elim w₁ w₂) := by
  ext v; simp only [mem_image, mem_univ, true_and]
  refine ⟨fun ⟨a, ha⟩ ↦ ha ▸ Fin.addCases (fun i ↦ ⟨.inl (i + r₁), by simp [spliceWord]⟩)
      (fun j ↦ ⟨.inr (j + r₂), by simp [spliceWord]⟩) a,
    fun ⟨x, hx⟩ ↦ hx ▸ ⟨spliceStepEquiv r₁ r₂ x, by cases x <;> simp [spliceWord, spliceStepEquiv]⟩⟩

/-- Splicing preserves the set of visited vertices. -/
private theorem image_spliceWordCast {m₁ m₂ k : ℕ} (hk : (m₁ + 1) + (m₂ + 1) = k)
    (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)) :
    univ.image (spliceWordCast hk w₁ w₂ r₁ r₂) = univ.image (Sum.elim w₁ w₂) := by
  rw [← image_spliceWord w₁ w₂ r₁ r₂]; ext v
  simp only [spliceWordCast, mem_image, mem_univ, true_and, Function.comp_apply]
  exact ((finCongr hk).symm.surjective.exists (p := (spliceWord w₁ w₂ r₁ r₂ · = v))).symm

/-- Because `w₁ r₁ = w₂ r₂`, the canonicalized spliced walk returns to the root `0` at step
`m₁ + 1`. -/
private theorem canonicalWalk_spliceWordCast_mid {m₁ m₂ k : ℕ} [NeZero k]
    (hk : (m₁ + 1) + (m₂ + 1) = k) (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    {r₁ : Fin (m₁ + 1)} {r₂ : Fin (m₂ + 1)} (hr : w₁ r₁ = w₂ r₂) :
    canonicalWalk (cyclicPath (spliceWordCast hk w₁ w₂ r₁ r₂)) (m₁ + 1) = 0 := by
  have hzero : (finCongr hk).symm 0 = Fin.castAdd (m₂ + 1) 0 := by ext; simp
  have heq := (canonicalWalk_eq_iff (cyclicPath (spliceWordCast hk w₁ w₂ r₁ r₂))
    (finCongr hk (Fin.natAdd (m₁ + 1) 0)).castSucc (0 : Fin k).castSucc).mpr (by
      simp only [cyclicPath_castSucc, spliceWordCast, Function.comp_apply,
        (finCongr hk).symm_apply_apply, hzero, spliceWord, Fin.append_right, Fin.append_left,
        zero_add, hr])
  simpa [Fin.val_castSucc] using heq

/-- A shared unordered edge between steps `t₁` of `w₁` and `t₂` of `w₂` maps to an identical
unordered edge in the canonicalized spliced walk. -/
private theorem canonicalWalk_spliceWordCast_edge_eq {m₁ m₂ k : ℕ} [NeZero k]
    (hk : (m₁ + 1) + (m₂ + 1) = k) (w₁ : Fin (m₁ + 1) → α) (w₂ : Fin (m₂ + 1) → α)
    {r₁ : Fin (m₁ + 1)} {r₂ : Fin (m₂ + 1)} (hr : w₁ r₁ = w₂ r₂)
    {t₁ : Fin (m₁ + 1)} {t₂ : Fin (m₂ + 1)}
    (ht : s(w₁ t₁, w₁ (finRotate (m₁ + 1) t₁)) = s(w₂ t₂, w₂ (finRotate (m₂ + 1) t₂))) :
    let W := spliceWordCast hk w₁ w₂ r₁ r₂
    let a := spliceStepEquivCast hk r₁ r₂ (.inl t₁)
    let b := spliceStepEquivCast hk r₁ r₂ (.inr t₂)
    s(canonicalWalk (cyclicPath W) a.val, canonicalWalk (cyclicPath W) (a.val + 1)) =
      s(canonicalWalk (cyclicPath W) b.val, canonicalWalk (cyclicPath W) (b.val + 1)) := by
  let W := spliceWordCast hk w₁ w₂ r₁ r₂
  let a := spliceStepEquivCast hk r₁ r₂ (.inl t₁)
  let b := spliceStepEquivCast hk r₁ r₂ (.inr t₂)
  have hca : s(cyclicPath W a.castSucc, cyclicPath W a.succ) =
      s(cyclicPath W b.castSucc, cyclicPath W b.succ) := by
    simpa only [cyclicPath_castSucc, cyclicPath_succ, a, b, W,
      spliceWordCast_edge_stepEquiv hk w₁ w₂ hr, Sum.elim_inl, Sum.elim_inr] using ht
  simpa only [Sym2.eq_iff, ← canonicalWalk_eq_iff (cyclicPath W),
    Fin.val_castSucc, Fin.val_succ] using hca

/-- Two cyclic words `w₁` and `w₂` of total length `k₁ + k₂ = 2 * m` forming a connected
singleton-free pair visit at most `m` distinct vertices together. -/
theorem card_image_sumElim_le_of_add_eq_two_mul {k₁ k₂ m : ℕ}
    (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α) (hk : k₁ + k₂ = 2 * m)
    (h : IsConnectedPair w₁ w₂) :
    #(univ.image (Sum.elim w₁ w₂)) ≤ m := by
  obtain ⟨t₁, t₂, ht₁₂⟩ := h.shared_edge
  cases k₁ with | zero => exact t₁.elim0 | succ m₁ =>
  cases k₂ with | zero => exact t₂.elim0 | succ m₂ =>
  have : NeZero m := ⟨by omega⟩; have : NeZero (2 * m) := ⟨by omega⟩
  -- Pick a shared vertex `w₁ r₁ = w₂ r₂` from the shared unordered edge to splice the two cycles.
  obtain ⟨r₁, r₂, hr₁₂⟩ : ∃ (r₁ : Fin (m₁ + 1)) (r₂ : Fin (m₂ + 1)), w₁ r₁ = w₂ r₂ := by
    rcases Sym2.eq_iff.mp ht₁₂ with ⟨he, -⟩ | ⟨he, -⟩; exacts [⟨t₁, t₂, he⟩, ⟨t₁, _, he⟩]
  let W := spliceWordCast hk w₁ w₂ r₁ r₂
  have hW_ns := spliceWordCast_no_singleton_edge hk w₁ w₂ hr₁₂ h.no_singleton_edge
  have hle : #(univ.image W) ≤ m + 1 := by
    simpa [Nat.mul_div_right m (by omega : 0 < 2)] using
      card_image_le_div_two_add_one_of_no_singleton_edge W hW_ns
  have himg : univ.image (Sum.elim w₁ w₂) = univ.image W :=
    (image_spliceWordCast hk w₁ w₂ r₁ r₂).symm
  rw [himg]
  -- If `#(univ.image W) = m + 1`, the canonicalized splice is a tree walk returning to the root
  -- at step `m₁ + 1`, contradicting the shared edge crossing `[0, m₁ + 1)` and `[m₁ + 1, 2 * m)`.
  by_contra hgt
  have htree := isTreeWalk_canonicalWalk_cyclic W hW_ns (by omega)
  have hroot_mid := canonicalWalk_spliceWordCast_mid hk w₁ w₂ hr₁₂
  let a := spliceStepEquivCast hk r₁ r₂ (.inl t₁)
  let b := spliceStepEquivCast hk r₁ r₂ (.inr t₂)
  exact htree.ne_edge_of_lt_of_le hroot_mid
    (by simpa [a, spliceStepEquivCast, spliceStepEquiv] using (t₁ + -r₁).isLt)
    (by simp [b, spliceStepEquivCast, spliceStepEquiv]) b.isLt
    (canonicalWalk_spliceWordCast_edge_eq hk w₁ w₂ hr₁₂ ht₁₂)

/-- Connected singleton-free pairs of length-`k` cyclic words visit at most `k` vertices. -/
theorem card_image_sumElim_le {k : ℕ} (w₁ w₂ : Fin k → α) (h : IsConnectedPair w₁ w₂) :
    #(univ.image (Sum.elim w₁ w₂)) ≤ k :=
  card_image_sumElim_le_of_add_eq_two_mul w₁ w₂ (two_mul k).symm h

/-- On a finite vertex type `α`, at most `|α| ^ m * m ^ (2 * m)` pairs `(w₁, w₂)` of total length
`k₁ + k₂ = 2 * m` satisfy `IsConnectedPair`. -/
theorem card_filter_connectedPair_le_of_add_eq_two_mul [Fintype α] {k₁ k₂ m : ℕ}
    (hk : k₁ + k₂ = 2 * m) :
    #({p : (Fin k₁ → α) × (Fin k₂ → α) | IsConnectedPair p.1 p.2}) ≤
      Fintype.card α ^ m * m ^ (2 * m) := by
  rcases eq_or_ne k₁ 0 with rfl | hk₁; · simp
  rcases eq_or_ne k₂ 0 with rfl | hk₂; · simp
  rcases isEmpty_or_nonempty α with hα | hα
  · have : Nonempty (Fin k₁) := ⟨⟨0, Nat.pos_of_ne_zero hk₁⟩⟩
    have hm : m ≠ 0 := by omega
    simp [Finset.eq_empty_of_isEmpty, hm]
  · let eqv := Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) α
    refine (card_le_card_of_injOn eqv.symm (fun p hp ↦ ?_)
      fun _ _ _ _ h ↦ eqv.symm.injective h).trans (by
      simpa [hk] using card_filter_card_image_le (α := Fin k₁ ⊕ Fin k₂) (β := α) m)
    exact mem_filter.mpr ⟨mem_univ _,
      card_image_sumElim_le_of_add_eq_two_mul p.1 p.2 hk (mem_filter.mp hp).2⟩

/-- On a finite vertex type `α`, at most `|α| ^ k * k ^ (2 * k)` pairs of length-`k` cyclic words
satisfy `IsConnectedPair`. -/
theorem card_filter_connectedPair_le [Fintype α] (k : ℕ) :
    #({p : (Fin k → α) × (Fin k → α) | IsConnectedPair p.1 p.2}) ≤
      Fintype.card α ^ k * k ^ (2 * k) :=
  card_filter_connectedPair_le_of_add_eq_two_mul (two_mul k).symm

end CyclicPairs

end TauCeti.TreeWalk
