/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Limits in adically Hausdorff modules

Let `I` be an ideal of a commutative ring `R` and `M` an `I`-adically Hausdorff `R`-module. An
`I`-adic limit of a sequence in `M` is unique, and `R`-linear maps preserve `I`-adic convergence,
since they map `I ^ n • M` into `I ^ n • M`. Consequently a linear map fixing every term of a
sequence fixes its `I`-adic limit. This is how a fixed-point equation such as `c * x = x` passes
from the terms of an `I`-adically convergent sequence in an algebra to its limit.

The coordinates of an element of the completion `AdicCompletion I M` are compatible: a
representative of its coordinate modulo `I ^ n` also represents its coordinate modulo `I ^ m` for
every `m ≤ n`.

## Main results

* `IsHausdorff.map_eq_of_forall_sub_mem`: an `R`-linear endomorphism of an `I`-adically Hausdorff
  module that fixes every term of a sequence fixes its `I`-adic limit.
* `AdicCompletion.transitionMap_mk`: the transition maps send the class of an element to its
  class.
* `AdicCompletion.val_eq_mk_of_le`: a representative of a coordinate of an element of the
  completion represents all its lower coordinates.
-/

public section

variable {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]

/-- In an `I`-adically Hausdorff module, an `R`-linear endomorphism that fixes every term of a
sequence fixes its `I`-adic limit. -/
theorem IsHausdorff.map_eq_of_forall_sub_mem [IsHausdorff I M] (g : M →ₗ[R] M) {L : M}
    {x : ℕ → M} (hx : ∀ n, g (x n) = x n) (hL : ∀ n, L - x n ∈ I ^ n • (⊤ : Submodule R M)) :
    g L = L := by
  refine sub_eq_zero.mp <| IsHausdorff.haus' (I := I) (g L - L) fun n ↦ SModEq.sub_mem.mpr ?_
  have hsplit : g L - L - 0 = g (L - x n) - (L - x n) := by
    rw [map_sub, hx n, sub_zero, sub_sub_sub_cancel_right]
  rw [hsplit]
  exact sub_mem (Submodule.smul_top_le_comap_smul_top _ g (hL n)) (hL n)

/-- The transition map `M ⧸ I ^ n • M → M ⧸ I ^ m • M` sends the class of `a` to the class
of `a`. -/
@[simp]
theorem AdicCompletion.transitionMap_mk {m n : ℕ} (hmn : m ≤ n) (a : M) :
    transitionMap I M hmn (Submodule.Quotient.mk a) = Submodule.Quotient.mk a :=
  rfl

/-- A representative of the coordinate modulo `I ^ n` of an element of the `I`-adic completion
also represents its coordinate modulo `I ^ m` for every `m ≤ n`. -/
theorem AdicCompletion.val_eq_mk_of_le {x : AdicCompletion I M} {m n : ℕ} (hmn : m ≤ n) {a : M}
    (ha : x.val n = Submodule.Quotient.mk a) : x.val m = Submodule.Quotient.mk a := by
  rw [← x.property hmn, ha, AdicCompletion.transitionMap_mk]
