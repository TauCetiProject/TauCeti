/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Pointwise
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Principal ideals of a subring

For a subring `S` of a commutative ring `A` and an element `a ∈ S`, the principal ideal `a S` of
`S` consists of the elements of `S` that are `a` times an element of `S`. Read inside `A`, its
`n`-th power is cut out of `S` by the scaled copy `aⁿ • S`.

## Main results

* `Subring.mem_span_singleton_iff`: `x ∈ a S` exactly when `x = a * y` for some `y ∈ S`.
* `Subring.coe_span_singleton_pow`: `(a S)ⁿ` is the preimage in `S` of `aⁿ • S ⊆ A`.
-/

public section

open scoped Pointwise

namespace Subring

variable {A : Type*} [CommRing A] (S : Subring A) {a : A}

/-- Membership in the principal ideal `a S` of a subring `S ∋ a`: an element of `S` lies in it
exactly when it is `a` times an element of `S`. -/
theorem mem_span_singleton_iff (ha : a ∈ S) {x : S} :
    x ∈ Ideal.span {(⟨a, ha⟩ : S)} ↔ ∃ y ∈ S, a * y = x := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp [mul_comm]⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simp [← hxy, mul_comm])⟩

/-- The `n`-th power of the principal ideal `a S` of a subring `S ∋ a` is cut out of `S` by the
scaled copy `aⁿ • S`. -/
theorem coe_span_singleton_pow (ha : a ∈ S) (n : ℕ) :
    ((Ideal.span {(⟨a, ha⟩ : S)} ^ n : Ideal S) : Set S) =
      Subtype.val ⁻¹' ((a ^ n) • (S : Set A)) := by
  ext x
  rw [Ideal.span_singleton_pow, SetLike.mem_coe, SubmonoidClass.mk_pow,
    mem_span_singleton_iff S (pow_mem ha n), Set.mem_preimage, Set.mem_smul_set]
  simp only [smul_eq_mul, SetLike.mem_coe]

end Subring
