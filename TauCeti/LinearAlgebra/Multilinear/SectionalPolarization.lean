/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic.LinearCombination

/-!
# Polarization of curvature-type tensors

Let `T(x, y, z, w)` be a quadrilinear form on a module which is antisymmetric in its first pair
and in its last pair of arguments and satisfies the first Bianchi identity
`T(x, y, z, w) + T(y, z, x, w) + T(z, x, y, w) = 0`. These are the algebraic symmetries of a
Riemann curvature tensor `Rm(x, y, z, w) = ⟨R(x, y)z, w⟩`. The values `T(x, y, y, x)`, which
for a Riemann curvature tensor are the numerators of the sectional curvatures, determine `6 T`,
and hence `T` itself whenever multiplication by `6` is injective on the scalars. Explicitly,
writing `k(x, y) = T(x, y, y, x)`,

`6 T(x, y, z, w) = k(x + w, y + z) - k(x + z, y + w) - k(x, y + z) - k(w, y + z)`
`    + k(x, y + w) + k(z, y + w) - k(x + w, y) + k(x + z, y) - k(x + w, z) + k(x + z, w)`
`    + k(w, y) - k(z, y) + k(x, z) - k(x, w)`.

This identity holds over every commutative ring. When multiplication by `6` is injective on the
scalars, it can be cancelled, so two such tensors with the same values `T(x, y, y, x)` are
equal. Over a domain in which `6 ≠ 0` it is enough to compare these values on linearly
independent pairs, that is, on the pairs spanning a plane, since both sides vanish on dependent
pairs. This is how the sectional curvatures of a Riemannian manifold determine its curvature
tensor.

## Main declarations

* `LinearMap.six_mul_apply_eq_of_cyclic_eq_zero`: the polarization identity, expressing `6 T`
  through the values `T(x, y, y, x)`.
* `LinearMap.eq_of_cyclic_eq_zero`: two curvature-type tensors with the same values
  `T(x, y, y, x)` are equal when multiplication by `6` is injective.
* `LinearMap.apply_apply_apply_apply_eq_zero_of_not_linearIndependent`: `T(x, y, y, x) = 0` on
  linearly dependent pairs.
* `LinearMap.eq_of_cyclic_eq_zero_of_linearIndependent`: two curvature-type tensors agreeing on
  `T(x, y, y, x)` for linearly independent pairs are equal.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 8, Proposition 8.31.
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] R}

/-- The polarization identity for curvature-type tensors: for a quadrilinear form `T`
antisymmetric in its first and in its last pair of arguments and satisfying the first Bianchi
identity, `6 T(x, y, z, w)` is an explicit combination of values `T(a, b, b, a)`. This recovers
`T` itself only when multiplication by `6` is injective, see `LinearMap.eq_of_cyclic_eq_zero`. -/
theorem six_mul_apply_eq_of_cyclic_eq_zero
    (h₁ : ∀ x y z w, T x y z w = -T y x z w) (h₂ : ∀ x y z w, T x y z w = -T x y w z)
    (h₃ : ∀ x y z w, T x y z w + T y z x w + T z x y w = 0) (x y z w : M) :
    6 * T x y z w =
      T (x + w) (y + z) (y + z) (x + w) - T (x + z) (y + w) (y + w) (x + z) -
        T x (y + z) (y + z) x - T w (y + z) (y + z) w + T x (y + w) (y + w) x +
        T z (y + w) (y + w) z - T (x + w) y y (x + w) + T (x + z) y y (x + z) -
        T (x + w) z z (x + w) + T (x + z) w w (x + z) + T w y y w - T z y y z +
        T x z z x - T x w w x := by
  simp only [map_add, add_apply]
  linear_combination 3 * h₂ x y z w + 2 * h₃ x y z w - 2 * h₃ x y w z - 2 * h₁ x z y w +
    h₂ x z y w - h₃ x z w y + 2 * h₁ x w y z - h₂ x w y z + h₁ x w z y - 2 * h₂ y z x w +
    2 * h₁ y z w x + 2 * h₂ y w x z - h₁ y w z x - h₃ y w z x + h₁ z w z w +
    h₂ z w x y - h₂ z w z w

/-- Two quadrilinear forms antisymmetric in their first and in their last pair of arguments and
satisfying the first Bianchi identity are equal as soon as `T₁(x, y, y, x) = T₂(x, y, y, x)` for
all `x, y`, provided multiplication by `6` is injective on the scalars. -/
theorem eq_of_cyclic_eq_zero (h6 : IsLeftRegular (6 : R))
    {T₁ T₂ : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] R}
    (h₁ : ∀ x y z w, T₁ x y z w = -T₁ y x z w) (h₂ : ∀ x y z w, T₁ x y z w = -T₁ x y w z)
    (h₃ : ∀ x y z w, T₁ x y z w + T₁ y z x w + T₁ z x y w = 0)
    (h₁' : ∀ x y z w, T₂ x y z w = -T₂ y x z w) (h₂' : ∀ x y z w, T₂ x y z w = -T₂ x y w z)
    (h₃' : ∀ x y z w, T₂ x y z w + T₂ y z x w + T₂ z x y w = 0)
    (hT : ∀ x y, T₁ x y y x = T₂ x y y x) : T₁ = T₂ := by
  ext x y z w
  refine h6 ?_
  simp only [six_mul_apply_eq_of_cyclic_eq_zero h₁ h₂ h₃,
    six_mul_apply_eq_of_cyclic_eq_zero h₁' h₂' h₃', hT]

/-- A quadrilinear form antisymmetric in its first pair of arguments has `T(x, y, y, x) = 0`
whenever `x` and `y` are linearly dependent, provided the scalars have no zero divisors and
`2 ≠ 0`. -/
theorem apply_apply_apply_apply_eq_zero_of_not_linearIndependent [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) (h₁ : ∀ x y z w, T x y z w = -T y x z w) {x y : M}
    (hxy : ¬LinearIndependent R ![x, y]) : T x y y x = 0 := by
  -- `T(a, a, c, d)` vanishes, since `2 ≠ 0` and there are no zero divisors.
  have hd (a c d : M) : T a a c d = 0 :=
    (mul_eq_zero.1 (by linear_combination h₁ a a c d : (2 : R) * T a a c d = 0)).resolve_left h2
  -- A dependence `s x + t y = 0` with `(s, t) ≠ (0, 0)` gives `s² k = 0` and `t² k = 0`.
  obtain ⟨s, t, hst, hne⟩ : ∃ s t : R, s • x + t • y = 0 ∧ ¬(s = 0 ∧ t = 0) := by
    simpa [LinearIndependent.pair_iff] using hxy
  have hx : s * s * T x y y x = 0 := by
    have := congrArg (fun v ↦ T v y y (s • x)) hst
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hd, map_zero,
      zero_apply] at this
    linear_combination this
  have hy : t * t * T x y y x = 0 := by
    have := congrArg (fun v ↦ T x v (t • y) x) hst
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hd, map_zero,
      zero_apply] at this
    linear_combination this
  by_cases hs : s = 0
  · exact (mul_eq_zero.1 hy).resolve_left (mul_ne_zero (fun ht ↦ hne ⟨hs, ht⟩)
      fun ht ↦ hne ⟨hs, ht⟩)
  · exact (mul_eq_zero.1 hx).resolve_left (mul_ne_zero hs hs)

/-- Two quadrilinear forms antisymmetric in their first and in their last pair of arguments and
satisfying the first Bianchi identity are equal as soon as `T₁(x, y, y, x) = T₂(x, y, y, x)` for
every linearly independent pair `x, y`, provided the scalars have no zero divisors and `6 ≠ 0`.
Over a field these pairs are the bases of the two-dimensional subspaces. -/
theorem eq_of_cyclic_eq_zero_of_linearIndependent [NoZeroDivisors R] (h6 : (6 : R) ≠ 0)
    {T₁ T₂ : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] R}
    (h₁ : ∀ x y z w, T₁ x y z w = -T₁ y x z w) (h₂ : ∀ x y z w, T₁ x y z w = -T₁ x y w z)
    (h₃ : ∀ x y z w, T₁ x y z w + T₁ y z x w + T₁ z x y w = 0)
    (h₁' : ∀ x y z w, T₂ x y z w = -T₂ y x z w) (h₂' : ∀ x y z w, T₂ x y z w = -T₂ x y w z)
    (h₃' : ∀ x y z w, T₂ x y z w + T₂ y z x w + T₂ z x y w = 0)
    (hT : ∀ x y, LinearIndependent R ![x, y] → T₁ x y y x = T₂ x y y x) : T₁ = T₂ := by
  have h2 : (2 : R) ≠ 0 := fun h ↦ h6 <| by linear_combination 3 * h
  refine eq_of_cyclic_eq_zero (IsRegular.of_ne_zero' h6).left h₁ h₂ h₃ h₁' h₂' h₃' fun x y ↦ ?_
  by_cases hxy : LinearIndependent R ![x, y]
  · exact hT x y hxy
  · rw [apply_apply_apply_apply_eq_zero_of_not_linearIndependent h2 h₁ hxy,
      apply_apply_apply_apply_eq_zero_of_not_linearIndependent h2 h₁' hxy]

end LinearMap
