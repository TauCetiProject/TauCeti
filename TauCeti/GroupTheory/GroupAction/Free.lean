/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Preorder.Finite

/-!
# A descent principle for free actions

Let a monoid `G` act freely on `X`, and let `E, P ⊆ G` with `1 ∈ P` be such that `e * p ∈ P` and
`e * p ≠ 1` for all `e ∈ E` and `p ∈ P`. Then a finite subset `s ⊆ X` in which every point is
moved back into `s` by some element of `E` is empty: following such moves from a point of `s`,
some point must return to itself under a product `e * p ≠ 1`, which freeness forbids.

## Main results

* `TauCeti.MulAction.eq_empty_of_forall_exists_smul_mem`: the descent principle.

## References

This is the descent in the proof of Lemma 2 of A. Popa and D. Zagier, *An elementary proof of the
Eichler–Selberg trace formula*, J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327,
§3, with `G = PSL(2, ℤ)`, `E = {T, T′}` and `P` the classes of matrices with non-negative entries.
-/

public section

namespace TauCeti.MulAction

variable {G X : Type*} [Monoid G] [MulAction G X]

/-- **Descent for free actions.** If `G` acts freely on `X`, `1 ∈ P`, and `e * p ∈ P` with
`e * p ≠ 1` for all `e ∈ E`, `p ∈ P`, then a finite set `s` in which every point is moved back
into `s` by an element of `E` is empty. -/
theorem eq_empty_of_forall_exists_smul_mem [IsCancelSMul G X] {E P : Set G} (hP : 1 ∈ P)
    (hE : ∀ e ∈ E, ∀ p ∈ P, e * p ∈ P ∧ e * p ≠ 1) {s : Finset X}
    (hs : ∀ x ∈ s, ∃ e ∈ E, e • x ∈ s) : s = ∅ := by
  choose! e he hes using hs
  set f : X → X := fun x ↦ e x • x
  -- every iterate of `f` stays in `s` and is the action of an element of `P`
  have hiter (m : ℕ) : ∀ x ∈ s, f^[m] x ∈ s ∧ ∃ p ∈ P, f^[m] x = p • x := by
    induction m with
    | zero => exact fun x hx ↦ ⟨hx, 1, hP, by simp⟩
    | succ m ih =>
      intro x hx
      obtain ⟨hmem, p, hp, hpx⟩ := ih x hx
      rw [Function.iterate_succ_apply']
      exact ⟨hes _ hmem, e (f^[m] x) * p, (hE _ (he _ hmem) p hp).1, by rw [mul_smul, ← hpx]⟩
  -- by pigeonhole some `y = f^[i] x` returns to itself, under an element `e * p ≠ 1`
  refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨i, j, hij, heq⟩ := s.finite_toSet.exists_lt_map_eq_of_forall_mem
    (f := fun m ↦ f^[m] x) fun m ↦ (hiter m x hx).1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
  obtain ⟨hmem, p, hp, hpx⟩ := hiter m _ (hiter i x hx).1
  rw [add_assoc i m 1, add_comm i (m + 1), Function.iterate_add_apply,
    Function.iterate_succ_apply'] at heq
  refine (hE _ (he _ hmem) p hp).2 (IsCancelSMul.eq_one_of_smul (x := f^[i] x) ?_)
  rw [mul_smul, ← hpx]
  exact heq.symm

end TauCeti.MulAction
