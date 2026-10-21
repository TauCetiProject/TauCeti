/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Regular.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Polarization for curvature-type tensors

Let `T(x, y, z, w)` be a quadrilinear form which is antisymmetric in its first pair and in its
last pair of arguments and satisfies the first Bianchi identity
`T(x, y, z, w) + T(y, z, x, w) + T(z, x, y, w) = 0`, as the Riemann curvature tensor
`Rm(x, y, z, w) = ⟨R(x, y)z, w⟩` of a metric-compatible torsion-free connection does.
Then `T` is determined by its sectional values `T(u, v, v, u)`: this file proves the explicit
polarization identity expressing `6 T(a, b, c, d)` as a signed sum of fourteen sectional values,
and deduces that two such tensors with the same sectional values agree once `6` is a regular
scalar.

For an inner product space the sectional value `T(u, v, v, u)` is the numerator of the sectional
curvature of the plane spanned by `u` and `v`, so the identity says that sectional curvature
determines the curvature tensor.

The identity holds over an arbitrary commutative ring and uses no pair-interchange symmetry.

## Main declarations

* `LinearMap.six_mul_apply_polarization`: the polarization identity.
* `LinearMap.eq_of_forall_sectional_eq`: a curvature-type tensor is determined by its sectional
  values.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 8, where sectional curvature is shown to determine an algebraic curvature tensor.
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The polarization identity for curvature-type tensors: a quadrilinear form `T` which is
antisymmetric in its first and in its last pair of arguments and satisfies the first Bianchi
identity is recovered from its sectional values `Q(u, v) = T(u, v, v, u)` by
`6 T(a, b, c, d) = Q(a + d, b + c) - Q(a + c, b + d) - Q(a + d, b) - Q(a + d, c)
  + Q(a + c, b) + Q(a + c, d) - Q(a, b + c) + Q(a, b + d) - Q(d, b + c) + Q(c, b + d)
  + Q(a, c) - Q(a, d) + Q(d, b) - Q(c, b)`. -/
theorem six_mul_apply_polarization {T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] R}
    (h₁ : ∀ x y z w, T x y z w = -T y x z w) (h₂ : ∀ x y z w, T x y z w = -T x y w z)
    (h₃ : ∀ x y z w, T x y z w + T y z x w + T z x y w = 0) (a b c d : M) :
    6 * T a b c d =
      T (a + d) (b + c) (b + c) (a + d) - T (a + c) (b + d) (b + d) (a + c)
        - T (a + d) b b (a + d) - T (a + d) c c (a + d)
        + T (a + c) b b (a + c) + T (a + c) d d (a + c)
        - T a (b + c) (b + c) a + T a (b + d) (b + d) a
        - T d (b + c) (b + c) d + T c (b + d) (b + d) c
        + T a c c a - T a d d a + T d b b d - T c b b c := by
  simp only [map_add, add_apply]
  -- After expanding, four Bianchi identities give the result; the antisymmetries bring the
  -- remaining terms to a common normal form.
  linear_combination 2 * h₃ a b c d - 2 * h₃ a b d c - h₃ a c d b + h₃ b c d a
    - 2 * h₁ c a b d + 2 * h₁ d a b c + h₁ d a c b - h₁ d c b a - 2 * h₁ d b c a
    + h₁ c b d a + h₁ d c c d + 3 * h₂ a b c d + h₂ c d a b + 2 * h₂ b d a c
    - 2 * h₂ b c a d + h₂ a c b d - h₂ a d b c - h₂ c d c d

/-- A curvature-type tensor is determined by its sectional values: two quadrilinear forms which are
antisymmetric in their first and in their last pair of arguments, satisfy the first Bianchi
identity and agree on every `(u, v, v, u)` are equal, provided multiplication by `6` is injective
on the scalars. -/
theorem eq_of_forall_sectional_eq (h6 : IsLeftRegular (6 : R))
    {T T' : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] R}
    (h₁ : ∀ x y z w, T x y z w = -T y x z w) (h₂ : ∀ x y z w, T x y z w = -T x y w z)
    (h₃ : ∀ x y z w, T x y z w + T y z x w + T z x y w = 0)
    (h₁' : ∀ x y z w, T' x y z w = -T' y x z w) (h₂' : ∀ x y z w, T' x y z w = -T' x y w z)
    (h₃' : ∀ x y z w, T' x y z w + T' y z x w + T' z x y w = 0)
    (h : ∀ u v, T u v v u = T' u v v u) : T = T' := by
  ext a b c d
  exact h6 <| by
    simp only [six_mul_apply_polarization h₁ h₂ h₃, six_mul_apply_polarization h₁' h₂' h₃', h]

end LinearMap
