/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Birkhoff sums of iterates, scalar multiples and coboundaries

The Birkhoff sums of `birkhoffSum f g k` along the iterate `f^[k]` are the Birkhoff sums of `g`
along `f` at the times `k * n`, Birkhoff sums commute with scalar multiplication of the observable,
and the Birkhoff sums of a coboundary `ψ ∘ T - ψ` telescope: at time `n` and point `x` they equal
`ψ (T^[n] x) - ψ x`.

## Main results

* `TauCeti.birkhoffSum_iterate_birkhoffSum`:
  `birkhoffSum (f^[k]) (birkhoffSum f g k) n x = birkhoffSum f g (k * n) x`.
* `TauCeti.birkhoffSum_smul_apply` and `TauCeti.birkhoffSum_smul`:
  `birkhoffSum f (c • g) = c • birkhoffSum f g`.
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

/-- The Birkhoff sums of a scalar multiple `c • g` are the scalar multiples of the Birkhoff sums of
`g`. -/
theorem birkhoffSum_smul_apply {R : Type*} [DistribSMul R M] (f : α → α) (c : R) (g : α → M)
    (n : ℕ) (x : α) : birkhoffSum f (c • g) n x = c • birkhoffSum f g n x := by
  simp [birkhoffSum, Finset.smul_sum]

/-- The Birkhoff sums of a scalar multiple `c • g` are the scalar multiples of the Birkhoff sums of
`g`. -/
theorem birkhoffSum_smul {R : Type*} [DistribSMul R M] (f : α → α) (c : R) (g : α → M) :
    birkhoffSum f (c • g) = c • birkhoffSum f g :=
  funext₂ <| birkhoffSum_smul_apply f c g

/-- The Birkhoff sums of a coboundary `ψ ∘ T - ψ` telescope: at time `n` they equal
`ψ (T^[n] x) - ψ x`. -/
@[simp]
theorem birkhoffSum_comp_sub_self_apply {X G : Type*} [AddCommGroup G] (T : X → X) (ψ : X → G)
    (n : ℕ) (x : X) :
    birkhoffSum T (ψ ∘ T - ψ) n x = ψ (T^[n] x) - ψ x := by
  rw [birkhoffSum_sub_apply, birkhoffSum_comp_apply, birkhoffSum_apply_sub_birkhoffSum]

end TauCeti
