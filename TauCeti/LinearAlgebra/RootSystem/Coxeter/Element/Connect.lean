/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Reorder
public import Mathlib.Data.List.Induction

/-!
# Orderings of a forest are connected by commutations and rotations

Let `adj` be a symmetric relation (the Dynkin diagram) on the letters of a duplicate-free list `S`,
and suppose `S` is an *elimination order*: each letter is adjacent to at most one earlier letter.
This is exactly the condition for the diagram on `S` to be a forest. Then any function `φ` of the
orderings of `S` that is invariant under commuting non-adjacent letters
(`TauCeti.Coxeter.CommEquiv`) and under rotation `a :: t ↦ t ++ [a]` is constant
(`TauCeti.Coxeter.eq_of_isElimOrder`).

The induction removes the last letter `z`, a leaf: every ordering can be brought to the form
`m ++ [z]` (`z` is either a source or comes after its only neighbour), and a rotation of `m` lifts
to `· ++ [z]` by the same step.
-/

@[expose] public section

namespace TauCeti.Coxeter

variable {α : Type*} (adj : α → α → Prop)

/-- `l'` is a reordering of `l` in which only non-adjacent letters change their relative order. -/
def CommEquiv (l l' : List α) : Prop :=
  l.Perm l' ∧ ∀ x y, List.Sublist [x, y] l → List.Sublist [y, x] l' → ¬ adj x y

/-- `S` is an elimination order for `adj`: each letter is adjacent to at most one earlier
letter. -/
def IsElimOrder (S : List α) : Prop :=
  ∀ S₁ z S₂, S = S₁ ++ z :: S₂ → ∀ x ∈ S₁, ∀ y ∈ S₁, adj z x → adj z y → x = y

variable {adj}

theorem sublist_pair_of_sublist_append_singleton {x y z : α} {m : List α} (hx : x ≠ z)
    (h : List.Sublist [y, x] (m ++ [z])) : List.Sublist [y, x] m := by
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.1 h
  rcases l₂ with _ | ⟨w, _ | ⟨w', l₂⟩⟩
  · rw [List.append_nil] at he; rw [he]; exact h₁
  · have hw : w = z := by simpa using List.singleton_sublist.1 h₂
    rcases l₁ with _ | ⟨a, _ | ⟨a', l₁⟩⟩ <;> simp_all
  · have := h₂.length_le
    simp at this

theorem not_sublist_pair_append_singleton {x z : α} {m : List α} (hz : z ∉ m) :
    ¬ List.Sublist [z, x] (m ++ [z]) := by
  intro h
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.1 h
  rcases l₂ with _ | ⟨w, _ | ⟨w', l₂⟩⟩
  · rw [List.append_nil] at he; subst he; exact hz (h₁.subset (by simp))
  · rcases l₁ with _ | ⟨a, _ | ⟨a', l₁⟩⟩
    · simp at he
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact hz (h₁.subset (by simp [he.1]))
    · simp at he
  · have := h₂.length_le
    simp at this

/-- A letter that comes after all its neighbours can be commuted to the end. -/
theorem commEquiv_erase_append [DecidableEq α] {l : List α} (hnd : l.Nodup) {z : α} (hz : z ∈ l)
    (hafter : ∀ y, List.Sublist [z, y] l → ¬ adj z y) :
    CommEquiv adj l (l.erase z ++ [z]) := by
  refine ⟨(List.perm_cons_erase hz).trans (List.perm_append_singleton z _).symm,
    fun x y hxy hyx => ?_⟩
  by_cases hxz : x = z
  · subst hxz; exact hafter y hxy
  · have hyx' := (sublist_pair_of_sublist_append_singleton hxz hyx).trans List.erase_sublist
    obtain rfl := eq_of_sublist_pair_of_sublist_pair hnd hxy hyx'
    exact absurd hxy (List.nodup_iff_sublist.1 hnd x)

/-- A letter that comes before all its neighbours (a source) can be commuted to the front. -/
theorem commEquiv_cons_erase [DecidableEq α] {l : List α} (hnd : l.Nodup) {z : α} (hz : z ∈ l)
    (hbefore : ∀ x, List.Sublist [x, z] l → ¬ adj x z) :
    CommEquiv adj l (z :: l.erase z) := by
  refine ⟨List.perm_cons_erase hz, fun x y hxy hyx => ?_⟩
  rcases List.sublist_cons_iff.1 hyx with hyx' | ⟨r, hr, -⟩
  · obtain rfl := eq_of_sublist_pair_of_sublist_pair hnd hxy (hyx'.trans List.erase_sublist)
    exact absurd hxy (List.nodup_iff_sublist.1 hnd x)
  · obtain ⟨rfl, -⟩ := List.cons.inj hr
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

theorem IsElimOrder.of_append_singleton {S : List α} {z : α} (h : IsElimOrder adj (S ++ [z])) :
    IsElimOrder adj S := fun S₁ w S₂ hS =>
  h S₁ w (S₂ ++ [z]) (by rw [hS]; simp)

theorem IsElimOrder.last {S : List α} {z : α} (h : IsElimOrder adj (S ++ [z])) :
    ∀ x ∈ S, ∀ y ∈ S, adj z x → adj z y → x = y :=
  h S z [] rfl

/-- **Orderings of a forest are connected.** If `S` is a duplicate-free elimination order for a
symmetric relation `adj`, then a function of the orderings of `S` that is invariant under
commuting non-adjacent letters and under rotation takes the same value on all of them. -/
theorem eq_of_isElimOrder (hsymm : ∀ x y, adj x y → adj y x) {β : Type*}
    {S : List α} (hnd : S.Nodup) (hel : IsElimOrder adj S) (φ : List α → β)
    (hcomm : ∀ l l', l.Perm S → CommEquiv adj l l' → φ l = φ l')
    (hrot : ∀ a t, (a :: t).Perm S → φ (a :: t) = φ (t ++ [a]))
    {l l' : List α} (hl : l.Perm S) (hl' : l'.Perm S) : φ l = φ l' := by
  classical
  induction S using List.reverseRecOn generalizing φ l l' with
  | nil => rw [List.perm_nil.1 hl, List.perm_nil.1 hl']
  | append_singleton S' z ih =>
    obtain ⟨hndS', -, hdisj⟩ := List.nodup_append.1 hnd
    have hzS' : z ∉ S' := fun h => hdisj z h z (by simp) rfl
    have hmem : ∀ {L : List α} {x : α}, L.Perm (S' ++ [z]) → x ∈ L → x ≠ z → x ∈ S' :=
      fun hp hx hxz => by
        simpa [hxz] using hp.subset hx
    -- every ordering can be brought to the form `m ++ [z]`
    have stepA : ∀ L, L.Perm (S' ++ [z]) → φ L = φ (L.erase z ++ [z]) := by
      intro L hp
      have hndL : L.Nodup := hp.nodup_iff.2 hnd
      have hzL : z ∈ L := hp.symm.subset (by simp)
      by_cases hb : ∃ u, List.Sublist [u, z] L ∧ adj u z
      · obtain ⟨u, hu, hadj⟩ := hb
        refine hcomm L _ hp (commEquiv_erase_append hndL hzL fun y hzy hadjy => ?_)
        have huz : u ≠ z := by
          rintro rfl; exact List.nodup_iff_sublist.1 hndL u hu
        have hyz : y ≠ z := by
          rintro rfl; exact List.nodup_iff_sublist.1 hndL y hzy
        have hu' := hmem hp (hu.subset (by simp)) huz
        have hy' := hmem hp (hzy.subset (by simp)) hyz
        obtain rfl := hel.last u hu' y hy' (hsymm _ _ hadj) hadjy
        exact huz (eq_of_sublist_pair_of_sublist_pair hndL hu hzy)
      · push Not at hb
        rw [hcomm L _ hp (commEquiv_cons_erase hndL hzL hb)]
        exact hrot z (L.erase z) ((List.perm_cons_erase hzL).symm.trans hp)
    have herase : ∀ {L : List α}, L.Perm (S' ++ [z]) → (L.erase z).Perm S' := fun hp => by
      simpa [List.erase_append_right _ hzS'] using hp.erase z
    -- a rotation of `m` lifts to `m ++ [z]`
    have hψ := ih hndS' hel.of_append_singleton (fun m => φ (m ++ [z]))
      (fun m m' hm hce => hcomm _ _ (hm.append_right [z])
        (hce.append_singleton fun h => hzS' (hm.subset h)))
      (fun a t hat => by
        have hzt : z ∉ t := fun h => hzS' (hat.subset (List.mem_cons_of_mem a h))
        have hp1 : (a :: (t ++ [z])).Perm (S' ++ [z]) := hat.append_right [z]
        have hp2 : (t ++ [z] ++ [a]).Perm (S' ++ [z]) :=
          (List.perm_append_singleton a _).trans hp1
        change φ (a :: (t ++ [z])) = φ (t ++ [a] ++ [z])
        rw [hrot a (t ++ [z]) hp1, stepA _ hp2, List.append_assoc,
          List.erase_append_right _ hzt]
        simp)
      (herase hl) (herase hl')
    exact (stepA l hl).trans (hψ.trans (stepA l' hl').symm)

end TauCeti.Coxeter

end
