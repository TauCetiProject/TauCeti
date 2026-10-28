/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Push

/-!
# Orderings of a forest are connected by commutations and rotations

Let `adj` be a symmetric relation on the letters of a duplicate-free list `S`, and call `S` an
*elimination order* (`List.IsElimOrder`) if each letter is adjacent to at most one earlier letter.
A forest admits an elimination order: remove leaves one at a time, and list the vertices in the
reverse order of removal. Such an order gives a way to compare all the orderings of the vertices:
any function `φ` of the orderings of `S` that is invariant under commuting non-adjacent letters
(`List.CommEquiv`) and under rotation `a :: t ↦ t ++ [a]` is constant (`List.eq_of_isElimOrder`).

This applies to words in the generators of a Coxeter group, whose Coxeter graph plays the role of
`adj`.

## Main definitions

* `List.CommEquiv`: `l'` is a reordering of `l` in which only non-adjacent letters change their
  relative order.
* `List.IsElimOrder`: each letter of the list is adjacent to at most one earlier letter.

## Main results

* `List.eq_of_isElimOrder`: a function of the orderings of a duplicate-free elimination order that
  is invariant under commutations and rotations is constant.
* `List.IsElimOrder.append_singleton` builds an elimination order letter by letter, and
  `List.IsElimOrder.map_equiv` transports one along an equivalence.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.16.
-/

public section

namespace List

variable {α β : Type*} {adj : α → α → Prop}

/-- In a list without duplicates, two letters cannot occur in both orders. -/
theorem eq_of_sublist_pair_of_sublist_pair {l : List α} (hnd : l.Nodup) {x y : α}
    (hxy : [x, y].Sublist l) (hyx : [y, x].Sublist l) : x = y := by
  induction l with
  | nil => simp at hxy
  | cons c m ih =>
    rw [nodup_cons] at hnd
    rcases sublist_cons_iff.1 hxy with hxy' | ⟨r, hr, -⟩ <;>
      rcases sublist_cons_iff.1 hyx with hyx' | ⟨s, hs, -⟩
    · exact ih hnd.2 hxy' hyx'
    · obtain ⟨rfl, -⟩ := cons.inj hs
      exact absurd (hxy'.subset (by simp)) hnd.1
    · obtain ⟨rfl, -⟩ := cons.inj hr
      exact absurd (hyx'.subset (by simp)) hnd.1
    · exact (cons.inj hr).1.trans (cons.inj hs).1.symm

variable (adj) in
/-- `l'` is a reordering of `l` in which only non-adjacent letters change their relative order. -/
def CommEquiv (l l' : List α) : Prop :=
  l.Perm l' ∧ ∀ x y, [x, y].Sublist l → [y, x].Sublist l' → ¬ adj x y

/-- The defining property of `List.CommEquiv`. -/
theorem commEquiv_iff {l l' : List α} :
    CommEquiv adj l l' ↔ l.Perm l' ∧ ∀ x y, [x, y].Sublist l → [y, x].Sublist l' → ¬ adj x y :=
  Iff.rfl

variable (adj) in
/-- `S` is an elimination order for `adj`: each letter is adjacent to at most one earlier
letter. -/
def IsElimOrder (S : List α) : Prop :=
  ∀ S₁ z S₂, S = S₁ ++ z :: S₂ → ∀ x ∈ S₁, ∀ y ∈ S₁, adj z x → adj z y → x = y

/-- The defining property of `List.IsElimOrder`. -/
theorem isElimOrder_iff {S : List α} :
    IsElimOrder adj S ↔
      ∀ S₁ z S₂, S = S₁ ++ z :: S₂ → ∀ x ∈ S₁, ∀ y ∈ S₁, adj z x → adj z y → x = y :=
  Iff.rfl

/-- A pair ending in a letter other than the new last letter is a sublist of the original list. -/
theorem sublist_pair_of_sublist_append_singleton {x y z : α} {m : List α} (hx : x ≠ z)
    (h : [y, x].Sublist (m ++ [z])) : [y, x].Sublist m := by
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := sublist_append_iff.1 h
  rcases l₂ with _ | ⟨w, _ | ⟨w', l₂⟩⟩
  · rw [append_nil] at he; rw [he]; exact h₁
  · have hw : w = z := by simpa using singleton_sublist.1 h₂
    rcases l₁ with _ | ⟨a, _ | ⟨a', l₁⟩⟩ <;> simp_all
  · have := h₂.length_le
    simp at this

/-- A new last letter is not followed by anything. -/
theorem not_sublist_pair_append_singleton {x z : α} {m : List α} (hz : z ∉ m) :
    ¬ [z, x].Sublist (m ++ [z]) := by
  intro h
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := sublist_append_iff.1 h
  rcases l₂ with _ | ⟨w, _ | ⟨w', l₂⟩⟩
  · rw [append_nil] at he; subst he; exact hz (h₁.subset (by simp))
  · rcases l₁ with _ | ⟨a, _ | ⟨a', l₁⟩⟩
    · simp at he
    · simp only [cons_append, nil_append, cons.injEq] at he
      exact hz (h₁.subset (by simp [he.1]))
    · simp at he
  · have := h₂.length_le
    simp at this

/-- A letter that comes after all its neighbours can be commuted to the end. -/
theorem commEquiv_erase_append [DecidableEq α] {l : List α} (hnd : l.Nodup) {z : α} (hz : z ∈ l)
    (hafter : ∀ y, [z, y].Sublist l → ¬ adj z y) :
    CommEquiv adj l (l.erase z ++ [z]) := by
  refine ⟨(perm_cons_erase hz).trans (perm_append_singleton z _).symm, fun x y hxy hyx => ?_⟩
  by_cases hxz : x = z
  · subst hxz; exact hafter y hxy
  · have hyx' := (sublist_pair_of_sublist_append_singleton hxz hyx).trans erase_sublist
    obtain rfl := eq_of_sublist_pair_of_sublist_pair hnd hxy hyx'
    exact absurd hxy (nodup_iff_sublist.1 hnd x)

/-- A letter that comes before all its neighbours (a source) can be commuted to the front. -/
theorem commEquiv_cons_erase [DecidableEq α] {l : List α} (hnd : l.Nodup) {z : α} (hz : z ∈ l)
    (hbefore : ∀ x, [x, z].Sublist l → ¬ adj x z) :
    CommEquiv adj l (z :: l.erase z) := by
  refine ⟨perm_cons_erase hz, fun x y hxy hyx => ?_⟩
  rcases sublist_cons_iff.1 hyx with hyx' | ⟨r, hr, -⟩
  · obtain rfl := eq_of_sublist_pair_of_sublist_pair hnd hxy (hyx'.trans erase_sublist)
    exact absurd hxy (nodup_iff_sublist.1 hnd x)
  · obtain ⟨rfl, -⟩ := cons.inj hr
    exact hbefore x hxy

/-- Commutation equivalence lifts along appending a new last letter. -/
theorem CommEquiv.append_singleton {m m' : List α} (h : CommEquiv adj m m') {z : α}
    (hz : z ∉ m) : CommEquiv adj (m ++ [z]) (m' ++ [z]) := by
  refine ⟨h.1.append_right [z], fun x y hxy hyx => ?_⟩
  by_cases hxz : x = z
  · subst hxz; exact absurd hxy (not_sublist_pair_append_singleton hz)
  have hyx' := sublist_pair_of_sublist_append_singleton hxz hyx
  by_cases hyz : y = z
  · subst hyz; exact absurd (hyx'.subset (by simp)) (fun h' => hz (h.1.symm.subset h'))
  exact h.2 x y (sublist_pair_of_sublist_append_singleton hyz hxy) hyx'

/-- The empty list is an elimination order. -/
theorem isElimOrder_nil : IsElimOrder adj ([] : List α) := fun S₁ z S₂ h => by simp at h

/-- Removing the last letter of an elimination order leaves an elimination order. -/
theorem IsElimOrder.of_append_singleton {S : List α} {z : α} (h : IsElimOrder adj (S ++ [z])) :
    IsElimOrder adj S := fun S₁ w S₂ hS =>
  h S₁ w (S₂ ++ [z]) (by rw [hS]; simp)

/-- The last letter of an elimination order is adjacent to at most one earlier letter. -/
theorem IsElimOrder.last {S : List α} {z : α} (h : IsElimOrder adj (S ++ [z])) :
    ∀ x ∈ S, ∀ y ∈ S, adj z x → adj z y → x = y :=
  h S z [] rfl

/-- An elimination order extends by a letter adjacent to at most one letter of it. -/
theorem IsElimOrder.append_singleton {S : List α} {z : α} (h : IsElimOrder adj S)
    (hz : ∀ x ∈ S, ∀ y ∈ S, adj z x → adj z y → x = y) : IsElimOrder adj (S ++ [z]) := by
  intro S₁ w S₂ hS
  rcases eq_nil_or_concat S₂ with rfl | ⟨L, c, rfl⟩
  · obtain ⟨rfl, hzw⟩ := append_inj' hS rfl
    obtain rfl : z = w := by simpa using hzw
    exact hz
  · have hS' : S ++ [z] = (S₁ ++ w :: L) ++ [c] := by rw [hS]; simp
    exact h S₁ w L (append_inj' hS' rfl).1

/-- An elimination order transports along an equivalence of the letters. -/
theorem IsElimOrder.map_equiv {adj' : β → β → Prop} {S : List β} (h : IsElimOrder adj' S)
    (e : α ≃ β) : IsElimOrder (fun x y => adj' (e x) (e y)) (S.map e.symm) := by
  intro S₁ z S₂ hS x hx y hy hxz hyz
  have hS' : S = S₁.map e ++ e z :: S₂.map e := by
    simpa [map_map] using congrArg (map e) hS
  exact e.injective (h _ _ _ hS' (e x) (mem_map_of_mem hx) (e y) (mem_map_of_mem hy) hxz hyz)

/-- **Orderings of a forest are connected.** If `S` is a duplicate-free elimination order for a
symmetric relation `adj`, then a function of the orderings of `S` that is invariant under
commuting non-adjacent letters and under rotation takes the same value on all of them. -/
theorem eq_of_isElimOrder (hsymm : ∀ x y, adj x y → adj y x)
    {S : List α} (hnd : S.Nodup) (hel : IsElimOrder adj S) (φ : List α → β)
    (hcomm : ∀ l l', l.Perm S → CommEquiv adj l l' → φ l = φ l')
    (hrot : ∀ a t, (a :: t).Perm S → φ (a :: t) = φ (t ++ [a]))
    {l l' : List α} (hl : l.Perm S) (hl' : l'.Perm S) : φ l = φ l' := by
  classical
  induction S using reverseRecOn generalizing φ l l' with
  | nil => rw [perm_nil.1 hl, perm_nil.1 hl']
  | append_singleton S' z ih =>
    obtain ⟨hndS', -, hdisj⟩ := nodup_append.1 hnd
    have hzS' : z ∉ S' := fun h => hdisj z h z (by simp) rfl
    have hmem : ∀ {L : List α} {x : α}, L.Perm (S' ++ [z]) → x ∈ L → x ≠ z → x ∈ S' :=
      fun hp hx hxz => by
        simpa [hxz] using hp.subset hx
    -- every ordering can be brought to the form `m ++ [z]`
    have stepA : ∀ L, L.Perm (S' ++ [z]) → φ L = φ (L.erase z ++ [z]) := by
      intro L hp
      have hndL : L.Nodup := hp.nodup_iff.2 hnd
      have hzL : z ∈ L := hp.symm.subset (by simp)
      by_cases hb : ∃ u, [u, z].Sublist L ∧ adj u z
      · obtain ⟨u, hu, hadj⟩ := hb
        refine hcomm L _ hp (commEquiv_erase_append hndL hzL fun y hzy hadjy => ?_)
        have huz : u ≠ z := by
          rintro rfl; exact nodup_iff_sublist.1 hndL u hu
        have hyz : y ≠ z := by
          rintro rfl; exact nodup_iff_sublist.1 hndL y hzy
        have hu' := hmem hp (hu.subset (by simp)) huz
        have hy' := hmem hp (hzy.subset (by simp)) hyz
        obtain rfl := hel.last u hu' y hy' (hsymm _ _ hadj) hadjy
        exact huz (eq_of_sublist_pair_of_sublist_pair hndL hu hzy)
      · push Not at hb
        rw [hcomm L _ hp (commEquiv_cons_erase hndL hzL hb)]
        exact hrot z (L.erase z) ((perm_cons_erase hzL).symm.trans hp)
    have herase : ∀ {L : List α}, L.Perm (S' ++ [z]) → (L.erase z).Perm S' := fun hp => by
      simpa [erase_append_right _ hzS'] using hp.erase z
    -- a rotation of `m` lifts to `m ++ [z]`
    have hψ := ih hndS' hel.of_append_singleton (fun m => φ (m ++ [z]))
      (fun m m' hm hce => hcomm _ _ (hm.append_right [z])
        (hce.append_singleton fun h => hzS' (hm.subset h)))
      (fun a t hat => by
        have hzt : z ∉ t := fun h => hzS' (hat.subset (mem_cons_of_mem a h))
        have hp1 : (a :: (t ++ [z])).Perm (S' ++ [z]) := hat.append_right [z]
        have hp2 : (t ++ [z] ++ [a]).Perm (S' ++ [z]) :=
          (perm_append_singleton a _).trans hp1
        simp only [cons_append]
        rw [hrot a (t ++ [z]) hp1, stepA _ hp2, append_assoc, erase_append_right _ hzt]
        simp)
      (herase hl) (herase hl')
    exact (stepA l hl).trans (hψ.trans (stepA l' hl').symm)

end List

end
