/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutation invariance on finite tuples

This file provides `Fin.comp_perm_eq_of_cons_of_swap`: a family of maps `F` on tuples `Fin j → α`
for which prepending an entry (`Fin.cons v`) respects `F j`-equality and swapping the first two
entries leaves `F` invariant is invariant under every permutation of `Fin j`.
-/

public section

namespace Fin

/-- Any family of maps `F` on tuples `Fin j → α` such that prepending an entry via `Fin.cons`
respects `F j`-equality (`F j m = F j m' → F (j + 1) (cons v m) = F (j + 1) (cons v m')`) and `F`
is invariant under `Equiv.swap 0 1` is invariant under every permutation of `Fin j`. -/
theorem comp_perm_eq_of_cons_of_swap {α : Sort*} {β : ℕ → Sort*}
    (F : ∀ j, (Fin j → α) → β j)
    (hcons : ∀ j (v : α) (m m' : Fin j → α), F j m = F j m' →
      F (j + 1) (cons v m : Fin (j + 1) → α) = F (j + 1) (cons v m' : Fin (j + 1) → α))
    (hswap : ∀ j (m : Fin (j + 2) → α), F (j + 2) (m ∘ Equiv.swap 0 1) = F (j + 2) m) :
    ∀ (j : ℕ) (m : Fin j → α) (σ : Equiv.Perm (Fin j)), F j (m ∘ σ) = F j m
  | 0, m, σ => by
      have hm : m ∘ σ = m := funext fun i => i.elim0
      rw [hm]
  | j + 1, m, σ => by
      have hadj : ∀ (n : ℕ) (i : Fin n) (a : Fin (n + 1) → α),
          F (n + 1) (a ∘ Equiv.swap i.castSucc i.succ) = F (n + 1) a := by
        intro n
        induction n with
        | zero => intro i; exact i.elim0
        | succ n ih =>
          intro i a
          refine cases ?_ (fun q => ?_) i
          · simpa using hswap n a
          · conv_lhs => rw [← cons_self_tail a, ← succ_castSucc, cons_comp_swap_succ]
            exact (hcons (n + 1) (a 0) _ _ (ih q (tail a))).trans
              (congrArg (F (n + 2)) (cons_self_tail a))
      revert m
      refine Submonoid.induction_of_closure_eq_top_left
        (Equiv.Perm.mclosure_swap_castSucc_succ j) σ (fun m => by simp) ?_
      rintro _ ⟨i, rfl⟩ τ ih m
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ih, hadj]

end Fin
