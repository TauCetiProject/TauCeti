/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Pointwise
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Principal ideals of a subsemiring

For a subsemiring `s` of a commutative semiring `A` (for instance a subring or a subalgebra) and
an element `a ∈ s`, the principal ideal `a s` of `s` consists of the elements of `s` that are `a`
times an element of `s`. Read inside `A`, its `n`-th power is cut out of `s` by the scaled copy
`aⁿ • s`.

## Main results

* `SubsemiringClass.mem_span_singleton_iff`: `x ∈ a s` exactly when `x = a * y` for some
  `y ∈ s`.
* `SubsemiringClass.coe_span_singleton_pow`: `(a s)ⁿ` is the preimage in `s` of
  `aⁿ • s ⊆ A`.
-/

public section

open scoped Pointwise

namespace SubsemiringClass

variable {A S : Type*} [CommSemiring A] [SetLike S A] [SubsemiringClass S A] (s : S) {a : A}

/-- Membership in the principal ideal `a s` of a subsemiring `s ∋ a`: an element of `s` lies in
it exactly when it is `a` times an element of `s`. -/
theorem mem_span_singleton_iff (ha : a ∈ s) {x : s} :
    x ∈ Ideal.span {(⟨a, ha⟩ : s)} ↔ ∃ y ∈ s, a * y = x := by
  simp [Ideal.mem_span_singleton', Subtype.ext_iff, mul_comm]

/-- The `n`-th power of the principal ideal `a s` of a subsemiring `s ∋ a` is cut out of `s` by
the scaled copy `aⁿ • s`. -/
theorem coe_span_singleton_pow (ha : a ∈ s) (n : ℕ) :
    ((Ideal.span {(⟨a, ha⟩ : s)} ^ n : Ideal s) : Set s) =
      Subtype.val ⁻¹' ((a ^ n) • (s : Set A)) := by
  ext x
  simp [Ideal.span_singleton_pow, mem_span_singleton_iff s (pow_mem ha n), Set.mem_smul_set]

end SubsemiringClass
