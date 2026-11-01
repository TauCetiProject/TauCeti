/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.CayleyDickson.Basic

/-!
# The octonions as the Cayley–Dickson double of the quaternions

The Cayley–Dickson double `CayleyDickson ℍ[R]` of Hamilton's quaternions over a commutative ring
`R` is a free `R`-module of rank eight with a bilinear, in general nonassociative, product
`⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩` and the involution
`star ⟨a, b⟩ = ⟨star a, -b⟩`. For `R = ℝ` it is the algebra of **octonions**, the eight-dimensional
real division algebra, `TauCeti.DivisionOctonionReal`; this is its compact real form, unlike the
split octonions `TauCeti.Octonion ℝ`.

This file proves the composition-algebra identities of the double over an arbitrary commutative
ring; over a field of characteristic other than two, where the norm is nondegenerate, they make the
double a composition algebra. Its **norm** `N ⟨a, b⟩ = N a + N b`, the sum of the quaternion norms,
and its **trace** `T ⟨a, b⟩ = 2 re a` satisfy

* `x * star x = star x * x = N x • 1` and `x + star x = T x • 1`, so every element satisfies its
  rank-two equation `x * x = T x • x - N x • 1`;
* `N (x * y) = N x * N y`, Degen's eight-square identity;
* the **inverse properties** `star x * (x * y) = N x • y` and `x * y * star y = N y • x`, with
  their conjugate forms;
* the **alternative laws** `x * x * y = x * (x * y)` and `x * y * y = x * (y * y)` and the
  **flexible law** `x * y * x = x * (y * x)`.

Over a linearly ordered ring the norm is positive definite, so the double has no zero divisors, and
over a linearly ordered field every nonzero `x` has the two-sided inverse `x⁻¹ = (N x)⁻¹ • star x`,
for which both cancellation laws hold on either side.

## Main definitions

* `TauCeti.CayleyDickson.normSq`: the norm `N ⟨a, b⟩ = N a + N b`, a multiplicative map.
* `TauCeti.CayleyDickson.trace`: the trace `T ⟨a, b⟩ = 2 re a`, an `R`-linear map.
* `TauCeti.DivisionOctonionReal`: the real octonions, the double of `ℍ[ℝ]`.

## Main results

* `TauCeti.CayleyDickson.self_mul_star` and `TauCeti.CayleyDickson.self_add_star`: the norm and the
  trace are the scalars `x * star x` and `x + star x`.
* `TauCeti.CayleyDickson.normSq_mul`: the norm is **multiplicative**.
* `TauCeti.CayleyDickson.star_mul_mul_left` and `TauCeti.CayleyDickson.mul_mul_star_right`: the
  inverse properties.
* `TauCeti.CayleyDickson.left_alternative`, `TauCeti.CayleyDickson.right_alternative`,
  `TauCeti.CayleyDickson.flexible`: the double of the quaternions is **alternative**.
* `TauCeti.CayleyDickson.normSq_eq_zero`: over a linearly ordered ring the norm is definite, and
  the double has no zero divisors.
* `TauCeti.CayleyDickson.mul_inv_cancel₀`, `TauCeti.CayleyDickson.inv_mul_cancel₀` and the four
  cancellation laws `TauCeti.CayleyDickson.inv_mul_cancel_left₀`, …: over a linearly ordered field
  every nonzero element is invertible, and multiplying by it can be undone on either side.
* `TauCeti.DivisionOctonionReal.finrank_eq_eight`: the real octonions are eight-dimensional.
* `TauCeti.DivisionOctonionReal.exists_mul_mul_ne`: the real octonions are not associative.

## Implementation notes

The polynomial identities of the double are proved in coordinates: `ext` splits
an equation into the four real and imaginary parts of each of the two quaternion coordinates, the
quaternion product and conjugation are expanded by their `simp` lemmas, and `ring` closes the
resulting polynomial identity over `R`. This works over every commutative ring, with no hypothesis
on `2`, and the inverse properties and the alternative laws are uniform instances of it.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §2.2.
* R. D. Schafer, *An Introduction to Nonassociative Algebras*, Academic Press (1966), Chapter III,
  §4: the Cayley–Dickson process and the alternative laws of the octonions.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), §1.5: the doubling of a composition algebra and its norm.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace CayleyDickson

/-! ### Scalars

The instance `SMulCommClass R (CayleyDickson A) (CayleyDickson A)` of
`TauCeti.Algebra.CayleyDickson.Basic` asks for a `StarModule`, which needs an involution on the
scalars; a general commutative ring carries none, so the double of a quaternion algebra gets it here
directly, from `QuaternionAlgebra.star_smul`. -/

section Scalars

variable {R : Type*} [CommRing R] {c₁ c₂ c₃ : R}

/-- Scalars commute with left multiplication in the double of a quaternion algebra over any
commutative ring. -/
instance : SMulCommClass R (CayleyDickson ℍ[R,c₁,c₂,c₃]) (CayleyDickson ℍ[R,c₁,c₂,c₃]) where
  smul_comm r x y := by
    ext <;> simp [QuaternionAlgebra.star_smul, smul_sub, smul_add]

end Scalars

/-! ### The norm and the trace -/

section CommRing

variable {R : Type*} [CommRing R] (x y z : CayleyDickson ℍ[R])

/-- The **norm** of the double of the quaternions, `N ⟨a, b⟩ = N a + N b`, the sum of the
quaternion norms of the two coordinates. It is multiplicative over every commutative ring `R`; over
a field of characteristic other than two it is also nondegenerate, so the double is a composition
algebra. -/
def normSq : CayleyDickson ℍ[R] →*₀ R where
  toFun x := Quaternion.normSq x.fst + Quaternion.normSq x.snd
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by
    simp [Quaternion.normSq_def']
    ring

theorem normSq_def : normSq x = Quaternion.normSq x.fst + Quaternion.normSq x.snd := (rfl)

/-- **The norm is multiplicative**: this is Degen's eight-square identity. -/
theorem normSq_mul : normSq (x * y) = normSq x * normSq y := map_mul normSq x y

@[simp]
theorem normSq_star : normSq (star x) = normSq x := by simp [normSq_def]

@[simp]
theorem normSq_neg : normSq (-x) = normSq x := by simp [normSq_def]

theorem normSq_smul (r : R) : normSq (r • x) = r ^ 2 * normSq x := by
  simp [normSq_def, Quaternion.normSq_smul, mul_add]

/-- The **trace** of the double of the quaternions, `T ⟨a, b⟩ = 2 re a`. -/
def trace : CayleyDickson ℍ[R] →ₗ[R] R where
  toFun x := 2 * x.fst.re
  map_add' x y := by simp [mul_add]
  map_smul' r x := by simp [mul_left_comm]

@[simp]
theorem trace_apply : trace x = 2 * x.fst.re := (rfl)

/-- The trace of `1` is `2`. Not a `simp` lemma, because `TauCeti.CayleyDickson.trace_apply`
already takes its left-hand side apart. -/
theorem trace_one : trace (1 : CayleyDickson ℍ[R]) = 2 := by simp

/-- Conjugation preserves the trace. Not a `simp` lemma, for the same reason as
`TauCeti.CayleyDickson.trace_one`. -/
theorem trace_star : trace (star x) = trace x := by simp

/-! ### The norm and the trace as products and sums with the involution -/

/-- An element times its conjugate is its norm. -/
theorem self_mul_star : x * star x = normSq x • 1 := by
  ext <;> simp [normSq_def, Quaternion.normSq_def'] <;> ring

/-- The conjugate of an element times the element is its norm. -/
theorem star_mul_self : star x * x = normSq x • 1 := by
  ext <;> simp [normSq_def, Quaternion.normSq_def'] <;> ring

/-- An element plus its conjugate is its trace. -/
theorem self_add_star : x + star x = trace x • 1 := by
  ext <;> simp
  ring

/-- The conjugate of an element plus the element is its trace. -/
theorem star_add_self : star x + x = trace x • 1 := by
  rw [add_comm, self_add_star]

/-- Conjugation is `x ↦ T x • 1 - x`. -/
theorem star_eq_trace_smul_one_sub : star x = trace x • 1 - x := by
  rw [← self_add_star, add_sub_cancel_left]

/-- **The rank-two equation** `x * x = T x • x - N x • 1`: every element of the double is a root
of the quadratic polynomial `X ^ 2 - T x * X + N x`. -/
theorem mul_self : x * x = trace x • x - normSq x • 1 := by
  ext <;> simp [normSq_def, Quaternion.normSq_def'] <;> ring

/-! ### The inverse properties -/

/-- Multiplying on the left by an element and then by its conjugate is multiplication by its
norm. -/
theorem star_mul_mul_left : star x * (x * y) = normSq x • y := by
  ext <;> simp [normSq_def, Quaternion.normSq_def'] <;> ring

/-- Multiplying on the left by the conjugate of an element and then by the element is
multiplication by its norm. -/
theorem mul_star_mul_left : x * (star x * y) = normSq x • y := by
  simpa using star_mul_mul_left (star x) y

/-- Multiplying on the right by an element and then by its conjugate is multiplication by its
norm. -/
theorem mul_mul_star_right : x * y * star y = normSq y • x := by
  ext <;> simp [normSq_def, Quaternion.normSq_def'] <;> ring

/-- Multiplying on the right by the conjugate of an element and then by the element is
multiplication by its norm. -/
theorem mul_star_mul_right : x * star y * y = normSq y • x := by
  simpa using mul_mul_star_right x (star y)

/-! ### The alternative and flexible laws -/

/-- **The left alternative law** of the octonions. -/
theorem left_alternative : x * x * y = x * (x * y) := by
  ext <;> simp <;> ring

/-- **The right alternative law** of the octonions. -/
theorem right_alternative : x * y * y = x * (y * y) := by
  ext <;> simp <;> ring

/-- **The flexible law** of the octonions. -/
theorem flexible : x * y * x = x * (y * x) := by
  ext <;> simp <;> ring

end CommRing

/-! ### Definiteness of the norm -/

section LinearOrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {x : CayleyDickson ℍ[R]}

theorem normSq_nonneg : 0 ≤ normSq x :=
  add_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg

/-- **The norm is definite**: only `0` has norm zero. -/
@[simp]
theorem normSq_eq_zero : normSq x = 0 ↔ x = 0 := by
  rw [normSq_def, add_eq_zero_iff_of_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg,
    Quaternion.normSq_eq_zero, Quaternion.normSq_eq_zero, CayleyDickson.ext_iff, zero_fst,
    zero_snd]

theorem normSq_ne_zero : normSq x ≠ 0 ↔ x ≠ 0 :=
  normSq_eq_zero.not

@[simp]
theorem normSq_pos : 0 < normSq x ↔ x ≠ 0 :=
  normSq_nonneg.lt_iff_ne'.trans normSq_ne_zero

/-- Over a linearly ordered ring the double of the quaternions has no zero divisors, the norm being
multiplicative and definite. -/
instance : NoZeroDivisors (CayleyDickson ℍ[R]) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have : normSq x * normSq y = 0 := by rw [← normSq_mul, h, map_zero]
    exact (mul_eq_zero.mp this).imp normSq_eq_zero.mp normSq_eq_zero.mp

end LinearOrderedCommRing

/-! ### Inverses -/

section Field

variable {R : Type*} [Field R]

/-- The inverse `x⁻¹ = (N x)⁻¹ • star x` of an element of the double of the quaternions over a
field, a two-sided inverse of every nonzero element over a linearly ordered field. -/
instance : Inv (CayleyDickson ℍ[R]) := ⟨fun x => (normSq x)⁻¹ • star x⟩

theorem inv_def (x : CayleyDickson ℍ[R]) : x⁻¹ = (normSq x)⁻¹ • star x := (rfl)

@[simp]
theorem inv_zero : (0 : CayleyDickson ℍ[R])⁻¹ = 0 := by simp [inv_def]

variable [LinearOrder R] [IsStrictOrderedRing R] {x : CayleyDickson ℍ[R]} (y : CayleyDickson ℍ[R])

/-- Over a linearly ordered field, the inverse of a nonzero element is a right inverse. -/
@[simp]
theorem mul_inv_cancel₀ (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  rw [inv_def, mul_smul_comm, self_mul_star, inv_smul_smul₀ (normSq_ne_zero.mpr hx)]

/-- Over a linearly ordered field, the inverse of a nonzero element is a left inverse. -/
@[simp]
theorem inv_mul_cancel₀ (hx : x ≠ 0) : x⁻¹ * x = 1 := by
  rw [inv_def, smul_mul_assoc, star_mul_self, inv_smul_smul₀ (normSq_ne_zero.mpr hx)]

/-- Left multiplication by a nonzero element is undone by left multiplication by its inverse. -/
@[simp]
theorem inv_mul_cancel_left₀ (hx : x ≠ 0) : x⁻¹ * (x * y) = y := by
  rw [inv_def, smul_mul_assoc, star_mul_mul_left, inv_smul_smul₀ (normSq_ne_zero.mpr hx)]

/-- Left multiplication by the inverse of a nonzero element is undone by left multiplication by the
element. -/
@[simp]
theorem mul_inv_cancel_left₀ (hx : x ≠ 0) : x * (x⁻¹ * y) = y := by
  rw [inv_def, smul_mul_assoc, mul_smul_comm, mul_star_mul_left,
    inv_smul_smul₀ (normSq_ne_zero.mpr hx)]

/-- Right multiplication by a nonzero element is undone by right multiplication by its inverse. -/
@[simp]
theorem mul_inv_cancel_right₀ (hx : x ≠ 0) : y * x * x⁻¹ = y := by
  rw [inv_def, mul_smul_comm, mul_mul_star_right, inv_smul_smul₀ (normSq_ne_zero.mpr hx)]

/-- Right multiplication by the inverse of a nonzero element is undone by right multiplication by
the element. -/
@[simp]
theorem inv_mul_cancel_right₀ (hx : x ≠ 0) : y * x⁻¹ * x = y := by
  rw [inv_def, mul_smul_comm, smul_mul_assoc, mul_star_mul_right,
    inv_smul_smul₀ (normSq_ne_zero.mpr hx)]

end Field

end CayleyDickson

/-- The **real octonions**, the eight-dimensional real division algebra, realized as the
Cayley–Dickson double of the quaternions `ℍ[ℝ]`. Its involution `star ⟨a, b⟩ = ⟨star a, -b⟩` is
positive: `x * star x = normSq x • 1`, with `0 < normSq x` for every nonzero `x`. It is the compact
real form of the octonions, not the split form `TauCeti.Octonion ℝ`. -/
abbrev DivisionOctonionReal : Type := CayleyDickson ℍ[ℝ]

/-- **The real octonions are eight-dimensional.** -/
theorem DivisionOctonionReal.finrank_eq_eight : Module.finrank ℝ DivisionOctonionReal = 8 := by
  rw [CayleyDickson.finrank_eq, Quaternion.finrank_eq_four]

/-- **The real octonions are not associative**: for the quaternion units `i` and `j` and the
doubling unit `l = ⟨0, 1⟩`, the products `(i * j) * l = ⟨0, k⟩` and `i * (j * l) = ⟨0, -k⟩`
differ. -/
theorem DivisionOctonionReal.exists_mul_mul_ne :
    ∃ x y z : DivisionOctonionReal, x * y * z ≠ x * (y * z) := by
  refine ⟨⟨⟨0, 1, 0, 0⟩, 0⟩, ⟨⟨0, 0, 1, 0⟩, 0⟩, ⟨0, 1⟩, fun h => ?_⟩
  have h' := congrArg (fun x : DivisionOctonionReal => x.snd.imK) h
  norm_num at h'

end TauCeti
