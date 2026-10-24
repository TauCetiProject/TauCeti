/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Basic

/-!
# Lifted relations between multisets as parallel enumerations

Mathlib's `Multiset.Rel r s t` lifts a relation `r` to multisets: it holds when the elements of
`s` and `t` can be paired off one-to-one with each pair related by `r`. This file records the
corresponding statement in terms of enumerations: `Multiset.Rel r s t` holds exactly when `s` and
`t` are enumerated by one family indexed by `Fin n`, with entries of equal index related.

This is the form in which a matching of two multisets of roots is usually produced, by
enumerating the roots of two polynomials in parallel.
-/

public section

namespace Multiset

variable {α β : Type*} {r : α → β → Prop}

/-- Two multisets are related by `Multiset.Rel r` exactly when they can be enumerated in
parallel, by families indexed by the same `Fin n`, with entries of equal index related by `r`. -/
theorem rel_iff_exists_fin {s : Multiset α} {t : Multiset β} :
    Rel r s t ↔ ∃ (n : ℕ) (a : Fin n → α) (b : Fin n → β),
      s = Finset.univ.val.map a ∧ t = Finset.univ.val.map b ∧ ∀ i, r (a i) (b i) := by
  refine ⟨fun h => ?_, fun ⟨n, a, b, hs, ht, hab⟩ => ?_⟩
  · induction h with
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp, by simp, fun i => i.elim0⟩
    | @cons x y _ _ hxy _ ih =>
      obtain ⟨n, a, b, rfl, rfl, hab⟩ := ih
      exact ⟨n + 1, Fin.cons x a, Fin.cons y b, by simp [List.ofFn_succ],
        by simp [List.ofFn_succ], Fin.cases hxy hab⟩
  · subst hs ht
    exact rel_map.2 (rel_refl_of_refl_on fun i _ => hab i)

end Multiset
