/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Associator
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Linearity of the associator

In a possibly nonassociative algebra `A` over a semiring `R`, the associator
`associator a b c = (a * b) * c - a * (b * c)` is `R`-linear in each of its three arguments, and in
a unital algebra it vanishes when one argument is `1`. By linearity it vanishes on the whole span
of a set as soon as it vanishes on triples of elements of that set: to check that a submodule
spanned by a set `s` is associative, it is enough to check the triples from `s`.

This is how associativity of a subalgebra spanned by a few explicit elements is proved, for
instance in Artin's theorem that two elements of the octonions generate an associative
subalgebra.

## Main results

* `TauCeti.associator_add_left`, `TauCeti.associator_smul_left` and their `middle` and `right`
  versions: the associator is linear in each argument.
* `TauCeti.associator_zero_left`, `TauCeti.associator_zero_middle` and
  `TauCeti.associator_zero_right`: the associator vanishes as soon as one argument is `0`.
* `TauCeti.associator_one_left`, `TauCeti.associator_one_middle` and
  `TauCeti.associator_one_right`: in a unital ring the associator vanishes as soon as one argument
  is `1`.
* `TauCeti.associator_eq_zero_of_mem_span`: if the associator vanishes on triples from `s`, it
  vanishes on triples from `Submodule.span R s`.
-/

public section

namespace TauCeti

section Ring

variable {A : Type*} [NonUnitalNonAssocRing A] (a a' b b' c c' : A)

/-- The associator is additive in its first argument. -/
theorem associator_add_left : associator (a + a') b c = associator a b c + associator a' b c := by
  simp only [associator_apply, add_mul]
  abel

/-- The associator is additive in its second argument. -/
theorem associator_add_middle :
    associator a (b + b') c = associator a b c + associator a b' c := by
  simp only [associator_apply, add_mul, mul_add]
  abel

/-- The associator is additive in its third argument. -/
theorem associator_add_right :
    associator a b (c + c') = associator a b c + associator a b c' := by
  simp only [associator_apply, mul_add]
  abel

/-- The associator vanishes when its first argument is `0`. -/
@[simp]
theorem associator_zero_left : associator 0 b c = 0 := by
  simp [associator_apply]

/-- The associator vanishes when its second argument is `0`. -/
@[simp]
theorem associator_zero_middle : associator a 0 c = 0 := by
  simp [associator_apply]

/-- The associator vanishes when its third argument is `0`. -/
@[simp]
theorem associator_zero_right : associator a b 0 = 0 := by
  simp [associator_apply]

end Ring

section Unital

variable {A : Type*} [NonAssocRing A] (a b : A)

/-- The associator vanishes when its first argument is `1`. -/
@[simp]
theorem associator_one_left : associator 1 a b = 0 := by
  simp [associator_apply]

/-- The associator vanishes when its second argument is `1`. -/
@[simp]
theorem associator_one_middle : associator a 1 b = 0 := by
  simp [associator_apply]

/-- The associator vanishes when its third argument is `1`. -/
@[simp]
theorem associator_one_right : associator a b 1 = 0 := by
  simp [associator_apply]

end Unital

section Module

variable {R A : Type*} [Monoid R] [NonUnitalNonAssocRing A] [DistribMulAction R A]

/-- The associator commutes with scalars in its first argument. -/
theorem associator_smul_left [IsScalarTower R A A] (r : R) (a b c : A) :
    associator (r • a) b c = r • associator a b c := by
  simp only [associator_apply, smul_mul_assoc, smul_sub]

/-- The associator commutes with scalars in its second argument. -/
theorem associator_smul_middle [IsScalarTower R A A] [SMulCommClass R A A] (r : R) (a b c : A) :
    associator a (r • b) c = r • associator a b c := by
  simp only [associator_apply, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The associator commutes with scalars in its third argument. -/
theorem associator_smul_right [SMulCommClass R A A] (r : R) (a b c : A) :
    associator a b (r • c) = r • associator a b c := by
  simp only [associator_apply, mul_smul_comm, smul_sub]

end Module

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] {s : Set A}

/-- If the associator vanishes on triples of elements of a set `s`, then it vanishes on triples of
elements of the span of `s`, the associator being linear in each argument. -/
theorem associator_eq_zero_of_mem_span (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, associator a b c = 0)
    {a b c : A} (ha : a ∈ Submodule.span R s) (hb : b ∈ Submodule.span R s)
    (hc : c ∈ Submodule.span R s) : associator a b c = 0 := by
  -- Each argument in turn is reduced from the span to the generators.
  induction ha using Submodule.span_induction generalizing b c with
  | mem a ha =>
    induction hb using Submodule.span_induction generalizing c with
    | mem b hb =>
      induction hc using Submodule.span_induction with
      | mem c hc => exact h a ha b hb c hc
      | zero => exact associator_zero_right a b
      | add c c' _ _ h₁ h₂ => rw [associator_add_right, h₁, h₂, add_zero]
      | smul r c _ h₁ => rw [associator_smul_right, h₁, smul_zero]
    | zero => exact associator_zero_middle a c
    | add b b' _ _ h₁ h₂ => rw [associator_add_middle, h₁ hc, h₂ hc, add_zero]
    | smul r b _ h₁ => rw [associator_smul_middle, h₁ hc, smul_zero]
  | zero => exact associator_zero_left b c
  | add a a' _ _ h₁ h₂ => rw [associator_add_left, h₁ hb hc, h₂ hb hc, add_zero]
  | smul r a _ h₁ => rw [associator_smul_left, h₁ hb hc, smul_zero]

end TauCeti
