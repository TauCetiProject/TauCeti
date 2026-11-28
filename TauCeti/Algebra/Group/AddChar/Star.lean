/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Invertible

/-!
# Additive characters invariant under a star operation

Let `A` be an additive group with a star operation and `ψ` an additive character of `A` with
`ψ (star a) = ψ a` for every `a`. Then `ψ` takes the value `1` at every `b - star b`. When `A` is a
module over a semiring `R` in which `2` is invertible, every skew-adjoint `a` (with
`star a = -a`) is `b - star b` for `b = ⅟2 • a`, so `ψ` is trivial on the skew-adjoint elements.

For a CM field `E`, the standard additive characters of the finite and infinite adeles of `E` are
invariant under complex conjugation, and this is how they become trivial on the skew-hermitian
adeles, which makes `ψ (y* S x)` a Heisenberg datum for a skew-hermitian matrix `S`.

## Main results

* `AddChar.map_sub_star_eq_one`: a star-invariant character is trivial on `b - star b`.
* `AddChar.map_eq_one_of_mem_skewAdjoint`: a star-invariant character of a module over a
  semiring in which `2` is invertible is trivial on the skew-adjoint elements.
-/

public section

namespace AddChar

variable {A M : Type*} [Monoid M]

/-- A character invariant under `star` takes the value `1` at `b - star b`. -/
theorem map_sub_star_eq_one [AddGroup A] [Star A] (ψ : AddChar A M)
    (hψ : ∀ a, ψ (star a) = ψ a) (b : A) : ψ (b - star b) = 1 := by
  rw [sub_eq_add_neg, map_add_eq_mul, ← hψ b, ← map_add_eq_mul, add_neg_cancel, map_zero_eq_one]

/-- A character invariant under `star` of a module `A` over a semiring `R` in which `2` is
invertible is trivial on the skew-adjoint elements `star a = -a`: such an `a` is `b - star b` for
`b = ⅟2 • a`. -/
theorem map_eq_one_of_mem_skewAdjoint [AddCommGroup A] [StarAddMonoid A] (R : Type*) [Semiring R]
    [Invertible (2 : R)] [Module R A]
    (ψ : AddChar A M) (hψ : ∀ a, ψ (star a) = ψ a) {a : A} (ha : a ∈ skewAdjoint A) :
    ψ a = 1 := by
  have hhalf : (⅟2 : R) • a + (⅟2 : R) • a = a := by
    rw [← add_smul, invOf_two_add_invOf_two, one_smul]
  -- Halves are unique in `A`, so `star` commutes with halving.
  have hstar : star ((⅟2 : R) • a) = (⅟2 : R) • star a := by
    conv_rhs => rw [← hhalf, star_add, ← two_smul R, smul_smul, invOf_mul_self, one_smul]
  have hb : (⅟2 : R) • a - star ((⅟2 : R) • a) = a := by
    rw [hstar, skewAdjoint.mem_iff.1 ha, smul_neg, sub_neg_eq_add, hhalf]
  rw [← hb, map_sub_star_eq_one ψ hψ]

end AddChar
