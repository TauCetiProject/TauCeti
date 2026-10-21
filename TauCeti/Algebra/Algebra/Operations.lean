/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products of elements of a submodule

For a submodule `M` of a commutative `R`-algebra `A`, a product of `k` elements of `M` lies in
the power `Mᵏ`. This is the submodule analogue of `Submodule.pow_mem_pow` for products of distinct
elements.

## Main results

* `Submodule.prod_mem_pow_card`: `∏_{i ∈ s} xᵢ ∈ M^{#s}` when every `xᵢ` lies in `M`.
* `Submodule.mul_prod_erase_mem_pow_card`: `y ∏_{j ∈ s, j ≠ i} xⱼ ∈ M^{#s}` for `i ∈ s`, when `y`
  and every `xⱼ` with `j ≠ i` lie in `M`.
-/

public section

open Finset

namespace Submodule

variable {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {M : Submodule R A}

/-- A product of `#s` elements of `M` lies in `M^{#s}`. -/
theorem prod_mem_pow_card {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ M) :
    ∏ i ∈ s, x i ∈ M ^ #s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, card_empty, pow_zero]
    exact one_le.mp le_rfl
  | insert i s hi ih =>
    rw [prod_insert hi, card_insert_of_notMem hi, pow_succ']
    exact mul_mem_mul (hx i (mem_insert_self i s)) (ih fun j hj ↦ hx j (mem_insert_of_mem hj))

/-- Replacing the factor at `i ∈ s` of a product of `#s` elements by another element `y` of `M`
gives an element of `M^{#s}`. -/
theorem mul_prod_erase_mem_pow_card [DecidableEq ι] {s : Finset ι} {x : ι → A} {i : ι}
    (hi : i ∈ s) {y : A} (hy : y ∈ M) (hx : ∀ j ∈ s.erase i, x j ∈ M) :
    y * ∏ j ∈ s.erase i, x j ∈ M ^ #s := by
  rw [← card_erase_add_one hi, pow_succ']
  exact mul_mem_mul hy (prod_mem_pow_card hx)

end Submodule
