/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.List
import Mathlib.Basic.Finite.Prod

/-!
# Finitely many words of bounded degree

A word `l : List (α × ℕ)` over a finite alphabet `α`, whose letters `(a, n)` carry degree `n + 1`,
has total degree `(l.map fun p => p.2 + 1).sum`. This file shows that there are only finitely many
words of bounded total degree.

## Main results

* `List.finite_setOf_sum_map_snd_add_one_le`: over a finite alphabet, the words of total degree
  at most `K` form a finite set.
-/

public section

namespace List

/-- Over a finite alphabet `α`, there are finitely many words `l : List (α × ℕ)` whose total
degree `(l.map fun p => p.2 + 1).sum` is at most `K`. -/
theorem finite_setOf_sum_map_snd_add_one_le (α : Type*) [Finite α] (K : ℕ) :
    {l : List (α × ℕ) | (l.map fun p => p.2 + 1).sum ≤ K}.Finite := by
  refine ((List.finite_length_le (α × Fin (K + 1)) K).image
    (List.map fun p => (p.1, (p.2 : ℕ)))).subset fun l hl => ?_
  suffices ∀ l : List (α × ℕ), (l.map fun p => p.2 + 1).sum ≤ K →
      ∃ l' : List (α × Fin (K + 1)), l'.length ≤ (l.map fun p => p.2 + 1).sum ∧
        l'.map (fun p => (p.1, (p.2 : ℕ))) = l by
    obtain ⟨l', hlen, hl'⟩ := this l hl
    exact ⟨l', hlen.trans hl, hl'⟩
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], by simp⟩
  | cons p l ih =>
    intro hp
    simp only [List.map_cons, List.sum_cons] at hp ⊢
    obtain ⟨l', hlen, hl'⟩ := ih (by omega)
    exact ⟨(p.1, ⟨p.2, by omega⟩) :: l', by rw [List.length_cons]; omega, by simp [hl']⟩

end List
