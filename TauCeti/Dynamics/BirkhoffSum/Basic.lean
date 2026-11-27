/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic

/-!
# Birkhoff sums of iterates and of coboundaries

The Birkhoff sums of `birkhoffSum f g k` along the iterate `f^[k]` are the Birkhoff sums of `g`
along `f` at the times `k * n`, and the Birkhoff sums of a coboundary `ψ ∘ T - ψ` telescope: at
time `n` and point `x` they equal `ψ (T^[n] x) - ψ x`.

## Main results

* `TauCeti.birkhoffSum_iterate_birkhoffSum`:
  `birkhoffSum (f^[k]) (birkhoffSum f g k) n x = birkhoffSum f g (k * n) x`.
* `TauCeti.birkhoffSum_comp_sub_self_apply`: `birkhoffSum T (ψ ∘ T - ψ) n x = ψ (T^[n] x) - ψ x`.
-/

public section

namespace TauCeti

variable {α M : Type*} [AddCommMonoid M]

/-- The Birkhoff sums of `birkhoffSum f g k` along `f^[k]` at time `n` are the Birkhoff sums of `g`
along `f` at time `k * n`. -/
@[simp]
theorem birkhoffSum_iterate_birkhoffSum (f : α → α) (g : α → M) (k n : ℕ) (x : α) :
    birkhoffSum (f^[k]) (birkhoffSum f g k) n x = birkhoffSum f g (k * n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ih, ← Function.iterate_mul, Nat.mul_succ,
      birkhoffSum_add_right_apply]

/-- The Birkhoff sums of a coboundary `ψ ∘ T - ψ` telescope: at time `n` they equal
`ψ (T^[n] x) - ψ x`. -/
@[simp]
theorem birkhoffSum_comp_sub_self_apply {X G : Type*} [AddCommGroup G] (T : X → X) (ψ : X → G)
    (n : ℕ) (x : X) :
    birkhoffSum T (ψ ∘ T - ψ) n x = ψ (T^[n] x) - ψ x := by
  rw [birkhoffSum_sub_apply, birkhoffSum_comp_apply, birkhoffSum_apply_sub_birkhoffSum]

end TauCeti
