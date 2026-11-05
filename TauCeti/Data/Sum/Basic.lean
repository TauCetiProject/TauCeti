/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sum.Basic
public import Mathlib.Basic.Nontrivial.Defs

/-!
# Elements of a doubled type in distinct pairs

In `α ⊕ α`, each label `p` has a partner `p.swap` with the same underlying element of `α`. Two
labels that are neither equal nor partners have distinct underlying elements, so `α` has at least
two elements.

## Main results

* `Sum.nontrivial_of_ne_of_ne_swap`: if `q ≠ p` and `q ≠ p.swap` in `α ⊕ α`, then `α` is
  nontrivial.
-/

public section

namespace Sum

variable {α : Type*}

/-- If two labels of `α ⊕ α` are neither equal nor partners under `Sum.swap`, then their underlying
elements of `α` differ, so `α` is nontrivial. -/
theorem nontrivial_of_ne_of_ne_swap {p q : α ⊕ α} (h : q ≠ p) (h' : q ≠ p.swap) :
    Nontrivial α := by
  rcases p with a | a <;> rcases q with b | b <;>
    exact ⟨b, a, fun hba => by subst hba; simp_all⟩

end Sum
