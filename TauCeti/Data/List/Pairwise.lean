/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Prod.Basic

/-!
# Pairwise relations and duplicate-free lists under local modifications

A pairwise relation on a list survives replacing two of its entries and mapping the others,
provided the relation transfers (`List.pairwise_map_append_cons_append_cons`).

For lists of signed letters, that is of pairs `(z, b)` with `b : Bool`: if both signed letters of
`y` occur in a duplicate-free list, then `y` occurs nowhere else
(`List.notMem_map_fst_of_nodup_append_cons_append_cons`), and renaming the letters along an
injective map and inserting the two signed letters of a fresh letter keeps a list duplicate-free
(`List.Nodup.map_prodMap_append_cons_cons`).
-/

public section

namespace List

variable {α β γ : Type*}

/-- Pairwise relations survive replacing two entries `a`, `b` of a list by `a'`, `b'` and the
others by their images under `g`, provided the relations transfer. -/
theorem pairwise_map_append_cons_append_cons {R : β → β → Prop} {S : γ → γ → Prop} {g : β → γ}
    {l₁ l₂ l₃ : List β} {a b : β} {a' b' : γ} (h : (l₁ ++ a :: (l₂ ++ b :: l₃)).Pairwise R)
    (hg : ∀ x y, R x y → S (g x) (g y))
    (ha : ∀ x, (R a x → S a' (g x)) ∧ (R x a → S (g x) a'))
    (hb : ∀ x, (R b x → S b' (g x)) ∧ (R x b → S (g x) b')) (hab : R a b → S a' b') :
    (l₁.map g ++ a' :: (l₂.map g ++ b' :: l₃.map g)).Pairwise S := by
  simp only [List.pairwise_append, List.pairwise_cons, List.pairwise_map, List.mem_append,
    List.mem_cons, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h ⊢
  obtain ⟨h₁, ⟨h₂, h₃, ⟨h₄, h₅⟩, h₆⟩, h₇⟩ := h
  refine ⟨h₁.imp (hg _ _), ⟨?_, h₃.imp (hg _ _), ⟨fun x hx => (hb x).1 (h₄ x hx),
    h₅.imp (hg _ _)⟩, ?_⟩, ?_⟩
  · rintro _ (⟨x, hx, rfl⟩ | rfl | ⟨x, hx, rfl⟩)
    · exact (ha x).1 (h₂ x (Or.inl hx))
    · exact hab (h₂ b (Or.inr (Or.inl rfl)))
    · exact (ha x).1 (h₂ x (Or.inr (Or.inr hx)))
  · rintro x hx _ (rfl | ⟨y, hy, rfl⟩)
    · exact (hb x).2 (h₆ x hx b (Or.inl rfl))
    · exact hg _ _ (h₆ x hx y (Or.inr hy))
  · rintro x hx _ (rfl | ⟨y, hy, rfl⟩ | rfl | ⟨y, hy, rfl⟩)
    · exact (ha x).2 (h₇ x hx a (Or.inl rfl))
    · exact hg _ _ (h₇ x hx y (Or.inr (Or.inl hy)))
    · exact (hb x).2 (h₇ x hx b (Or.inr (Or.inr (Or.inl rfl))))
    · exact hg _ _ (h₇ x hx y (Or.inr (Or.inr (Or.inr hy))))

/-- If the signed letters `(y, c)` and `(y, !c)` occur in a list without repetitions at the
displayed positions, then `y` occurs nowhere else. -/
theorem notMem_map_fst_of_nodup_append_cons_append_cons {L₁ L₂ L₃ : List (α × Bool)} {y : α}
    {c : Bool} (h : (L₁ ++ (y, c) :: (L₂ ++ (y, !c) :: L₃)).Nodup) :
    y ∉ (L₁ ++ L₂ ++ L₃).map Prod.fst := by
  have hp : (L₁ ++ (y, c) :: (L₂ ++ (y, !c) :: L₃)).Perm
      ((y, c) :: (y, !c) :: (L₁ ++ L₂ ++ L₃)) :=
    List.perm_middle.trans (.cons _ (by rw [← List.append_assoc]; exact List.perm_middle))
  have h' := hp.nodup_iff.1 h
  rw [List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at h'
  intro hy
  obtain ⟨⟨_, d⟩, hd, rfl⟩ := List.mem_map.1 hy
  cases d <;> cases c <;> simp_all

/-- Renaming the letters of a list of signed letters without repetitions along an injective map
and inserting the two signed letters of a fresh letter `n` gives a list without repetitions. -/
theorem Nodup.map_prodMap_append_cons_cons {f : α → β} (hf : f.Injective) {n : β}
    (hn : ∀ z, f z ≠ n) {X Y : List (α × Bool)} (h : (X ++ Y).Nodup) :
    (X.map (Prod.map f id) ++ (n, true) :: (n, false) :: Y.map (Prod.map f id)).Nodup := by
  refine (List.perm_middle.trans (.cons _ List.perm_middle)).nodup_iff.2 ?_
  have h' := h.map (hf.prodMap Function.injective_id)
  rw [List.map_append] at h'
  simp [h', hn]

end List
