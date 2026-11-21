/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Induction on `ℤ/N`

For `N ≠ 0`, every residue in `ZMod N` is reached from `0` by adding `1` finitely often, so a
property that holds at `0` and passes from `i` to `i + 1` holds everywhere (`ZMod.induction_on`).
In particular a sequence indexed by `ZMod N` that follows a recursion `z (i + 1) = G i (z i)` is
determined by its value at `0` (`ZMod.eq_of_forall_add_one`).
-/

public section

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- **Induction on `ℤ/N`.** For `N ≠ 0`, a property of residues that holds at `0` and passes from
`i` to `i + 1` holds at every residue. -/
@[elab_as_elim]
theorem induction_on {P : ZMod N → Prop} (i : ZMod N) (zero : P 0)
    (add_one : ∀ i, P i → P (i + 1)) : P i := by
  have key (n : ℕ) : P n := by
    induction n with
    | zero => simpa using zero
    | succ n ih => simpa using add_one _ ih
  simpa using key i.val

/-- A sequence indexed by `ℤ/N`, `N ≠ 0`, with `z (i + 1) = G i (z i)` is determined by `z 0`. -/
theorem eq_of_forall_add_one {α : Type*} {G : ZMod N → α → α} {z z' : ZMod N → α}
    (hz : ∀ i, G i (z i) = z (i + 1)) (hz' : ∀ i, G i (z' i) = z' (i + 1)) (h0 : z 0 = z' 0) :
    z = z' :=
  funext fun i ↦ i.induction_on h0 fun i ih ↦ by rw [← hz, ← hz', ih]

end ZMod
