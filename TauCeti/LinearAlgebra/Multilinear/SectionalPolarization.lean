/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.GroupWithZero.Action.Regular
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Polarization of curvature-type tensors

Let `T(x, y, z, w)` be a quadrilinear map from a module `M` to a module `N` which is
antisymmetric in its first pair and in its last pair of arguments and satisfies the first Bianchi
identity `T(x, y, z, w) + T(y, z, x, w) + T(z, x, y, w) = 0`. These are the algebraic symmetries
of a Riemann curvature tensor `Rm(x, y, z, w) = ⟨R(x, y)z, w⟩`. The values `T(x, y, y, x)`, which
for a Riemann curvature tensor are the numerators of the sectional curvatures, determine `6 • T`,
and hence `T` itself whenever multiplication by `6` is injective on `N`. Explicitly,
writing `k(x, y) = T(x, y, y, x)`,

`6 • T(x, y, z, w) = k(x + w, y + z) - k(x + z, y + w) - k(x, y + z) - k(w, y + z)`
`    + k(x, y + w) + k(z, y + w) - k(x + w, y) + k(x + z, y) - k(x + w, z) + k(x + z, w)`
`    + k(w, y) - k(z, y) + k(x, z) - k(x, w)`.

This identity holds over every commutative semiring of scalars and for values in every module
that is an additive group. When multiplication by `6` is injective on the values, it can be
cancelled, so two such tensors with the same values `T(x, y, y, x)` are equal. When `6 ≠ 0` in
the scalars and unequal scalars act differently on every nonzero value, as over a domain with
torsion-free values, it is enough to compare these values on linearly independent pairs, since
both sides vanish on dependent pairs by `LinearMap.IsAlt.eq_zero_of_not_linearIndependent`. Over
a field, the linearly independent pairs are the pairs spanning a plane, and this is how the
sectional curvatures of a Riemannian manifold determine its curvature tensor.

There is also a mixed-difference formula requiring no division. With
`B(x, w; y, z) = k(x + w, y + z) - k(x + w, y - z)`
`    - k(x - w, y + z) + k(x - w, y - z)`, it reads
`24 • T(x, y, z, w) = B(x, w; y, z) - B(y, w; x, z)`.
It holds in the same generality, now with `M` an additive group so that the differences make
sense, including when `2` or `3` is a zero divisor on the values.

## Main declarations

* `LinearMap.six_nsmul_apply_eq_of_cyclic_eq_zero`: the polarization identity, expressing `6 • T`
  through the values `T(x, y, y, x)`.
* `LinearMap.twentyFour_nsmul_apply_eq_of_cyclic_eq_zero`: the mixed-difference polarization,
  expressing `24 • T` through eight such values.
* `LinearMap.eq_of_apply_self_eq`: two curvature-type tensors with the same values
  `T(x, y, y, x)` are equal when multiplication by `6` is injective on the values.
* `LinearMap.eq_of_apply_self_eq_of_linearIndependent`: two curvature-type tensors agreeing on
  `T(x, y, y, x)` for linearly independent pairs are equal, provided `6 ≠ 0` and unequal scalars
  act differently on every nonzero value.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 8, Proposition 8.31.
* B. Andrews, *Lectures on Differential Geometry*,
  [Lecture 16: Curvature](https://maths-people.anu.edu.au/andrews/DG/DG_chap16.pdf),
  Proposition 16.2.1, p. 154.
  The mixed-difference formula uses `T(x, y, y, x)` rather than Andrews's slot order
  `T(x, y, x, y)` for the sectional-curvature numerator.
* The module-valued statements with natural-number multiples `6 •` and `24 •` follow Mathlib's
  `QuadraticMap` API, where `QuadraticMap.polar_self` states `polar Q x x = 2 • Q x`.
-/

public section

namespace LinearMap

variable {R M N : Type*}

section CommSemiring

variable [CommSemiring R] [AddCommGroup N] [Module R N]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]

/-- The polarization identity for curvature-type tensors: for a quadrilinear map `T`
antisymmetric in its first and in its last pair of arguments and satisfying the first Bianchi
identity, `6 • T(x, y, z, w)` is an explicit combination of values `T(a, b, b, a)`. When
multiplication by `6` is injective on the values, it can be cancelled to recover `T`, see
`LinearMap.eq_of_apply_self_eq`. -/
theorem six_nsmul_apply_eq_of_cyclic_eq_zero (T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    (h₁ : ∀ x y z w, T x y z w = -T y x z w) (h₂ : ∀ x y z w, T x y z w = -T x y w z)
    (h₃ : ∀ x y z w, T x y z w + T y z x w + T z x y w = 0) (x y z w : M) :
    6 • T x y z w =
      T (x + w) (y + z) (y + z) (x + w) - T (x + z) (y + w) (y + w) (x + z) -
        T x (y + z) (y + z) x - T w (y + z) (y + z) w + T x (y + w) (y + w) x +
        T z (y + w) (y + w) z - T (x + w) y y (x + w) + T (x + z) y y (x + z) -
        T (x + w) z z (x + w) + T (x + z) w w (x + z) + T w y y w - T z y y z +
        T x z z x - T x w w x := by
  -- Normalization is slow to compare the atoms `T a b c d`, so replace `T` by an opaque function.
  obtain ⟨t, ht⟩ : ∃ t : M → M → M → M → N, ∀ a b c d, T a b c d = t a b c d :=
    ⟨fun a b c d ↦ T a b c d, fun _ _ _ _ ↦ rfl⟩
  simp only [map_add, LinearMap.add_apply, ht] at h₁ h₂ h₃ ⊢
  linear_combination (norm := module) 3 • h₂ x y z w + 2 • h₃ x y z w - 2 • h₃ x y w z -
    2 • h₁ x z y w + h₂ x z y w - h₃ x z w y + 2 • h₁ x w y z - h₂ x w y z + h₁ x w z y -
    2 • h₂ y z x w + 2 • h₁ y z w x + 2 • h₂ y w x z - h₁ y w z x - h₃ y w z x + h₁ z w z w +
    h₂ z w x y - h₂ z w z w

/-- Two quadrilinear maps antisymmetric in their first and in their last pair of arguments and
satisfying the first Bianchi identity are equal as soon as `T₁(x, y, y, x) = T₂(x, y, y, x)` for
all `x, y`, provided multiplication by `6` is injective on the values. -/
theorem eq_of_apply_self_eq (T₁ : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    {T₂ : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N} (h6 : IsSMulRegular N (6 : ℕ))
    (h₁ : ∀ x y z w, T₁ x y z w = -T₁ y x z w) (h₂ : ∀ x y z w, T₁ x y z w = -T₁ x y w z)
    (h₃ : ∀ x y z w, T₁ x y z w + T₁ y z x w + T₁ z x y w = 0)
    (h₁' : ∀ x y z w, T₂ x y z w = -T₂ y x z w) (h₂' : ∀ x y z w, T₂ x y z w = -T₂ x y w z)
    (h₃' : ∀ x y z w, T₂ x y z w + T₂ y z x w + T₂ z x y w = 0)
    (hT : ∀ x y, T₁ x y y x = T₂ x y y x) : T₁ = T₂ := by
  ext x y z w
  refine h6 ?_
  simp only [T₁.six_nsmul_apply_eq_of_cyclic_eq_zero h₁ h₂ h₃,
    T₂.six_nsmul_apply_eq_of_cyclic_eq_zero h₁' h₂' h₃', hT]

/-- Two quadrilinear maps antisymmetric in their first and in their last pair of arguments and
satisfying the first Bianchi identity are equal as soon as `T₁(x, y, y, x) = T₂(x, y, y, x)` for
every linearly independent pair `x, y`, provided `6 ≠ 0` and unequal scalars act differently on
every nonzero value. Over a field these pairs are the bases of the two-dimensional subspaces. -/
theorem eq_of_apply_self_eq_of_linearIndependent (T₁ : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    {T₂ : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N}
    (hN : ∀ n : N, n ≠ 0 → Function.Injective fun r : R ↦ r • n) (h6 : (6 : R) ≠ 0)
    (h₁ : ∀ x y z w, T₁ x y z w = -T₁ y x z w) (h₂ : ∀ x y z w, T₁ x y z w = -T₁ x y w z)
    (h₃ : ∀ x y z w, T₁ x y z w + T₁ y z x w + T₁ z x y w = 0)
    (h₁' : ∀ x y z w, T₂ x y z w = -T₂ y x z w) (h₂' : ∀ x y z w, T₂ x y z w = -T₂ x y w z)
    (h₃' : ∀ x y z w, T₂ x y z w + T₂ y z x w + T₂ z x y w = 0)
    (hT : ∀ x y, LinearIndependent R ![x, y] → T₁ x y y x = T₂ x y y x) : T₁ = T₂ := by
  -- Multiplication by `6 : ℕ` on the values is the scalar `6 ≠ 0`, which kills no nonzero value.
  have h6' : IsSMulRegular N (6 : ℕ) := .of_right_eq_zero_of_smul fun n hn ↦ by
    by_contra hn0
    exact h6 <| hN n hn0 <| by simpa only [ofNat_smul_eq_nsmul, zero_smul] using hn
  -- On a dependent pair `x, y`, both sides vanish: by `h₁`, the bilinear slice
  -- `(a, b) ↦ T(a, b, y, x)` is skew-symmetric, hence alternating since doubling is injective.
  have hdep (T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N) (h₁ : ∀ x y z w, T x y z w = -T y x z w)
      {x y : M} (hxy : ¬LinearIndependent R ![x, y]) : T x y y x = 0 := by
    let ω := (T.compr₂ (applyₗ y)).compr₂ (applyₗ x)
    have hω : ω.IsAlt := .of_neg (h6'.of_mul (a := 3) (b := 2)) fun a b ↦ by
      simpa only [ω, compr₂_apply, applyₗ_apply_apply] using (h₁ b a y x).symm
    simpa only [ω, compr₂_apply, applyₗ_apply_apply] using
      hω.eq_zero_of_not_linearIndependent hN hxy
  refine T₁.eq_of_apply_self_eq h6' h₁ h₂ h₃ h₁' h₂' h₃' fun x y ↦ ?_
  by_cases hxy : LinearIndependent R ![x, y]
  · exact hT x y hxy
  · rw [hdep T₁ h₁ hxy, hdep T₂ h₁' hxy]

end AddCommMonoid

variable [AddCommGroup M] [Module R M]

/-- The mixed-difference polarization identity for a curvature-type quadrilinear map.
Writing `Q(a, b) = T(a, b, b, a)` and
`B(x, w; y, z) = Q(x + w, y + z) - Q(x + w, y - z)`
`    - Q(x - w, y + z) + Q(x - w, y - z)`, the identity is
`24 • T(x, y, z, w) = B(x, w; y, z) - B(y, w; x, z)`.

Only the two skew symmetries and the first Bianchi identity are needed. In particular this
formula holds without cancelling `2`, `3`, or `24`, and all its arguments may be dependent. -/
theorem twentyFour_nsmul_apply_eq_of_cyclic_eq_zero (T : M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] N)
    (h₁ : ∀ x y z w, T x y z w = -T y x z w) (h₂ : ∀ x y z w, T x y z w = -T x y w z)
    (h₃ : ∀ x y z w, T x y z w + T y z x w + T z x y w = 0) (x y z w : M) :
    24 • T x y z w =
      (T (x + w) (y + z) (y + z) (x + w) -
          T (x + w) (y - z) (y - z) (x + w) -
        T (x - w) (y + z) (y + z) (x - w) +
          T (x - w) (y - z) (y - z) (x - w)) -
      (T (y + w) (x + z) (x + z) (y + w) -
          T (y + w) (x - z) (x - z) (y + w) -
        T (y - w) (x + z) (x + z) (y - w) +
          T (y - w) (x - z) (x - z) (y - w)) := by
  -- Each mixed difference `B` is four times an add-only cross term, and the sixfold identity is
  -- the difference of two such cross terms. Align the slot order of the second difference with
  -- the sixfold identity by the symmetry `T(a, b, b, a) = T(b, a, a, b)`.
  have hk (a b : M) : T a b b a = T b a a b := by rw [h₁, h₂, neg_neg]
  rw [show (24 : ℕ) = 4 * 6 from rfl, mul_nsmul', T.six_nsmul_apply_eq_of_cyclic_eq_zero h₁ h₂ h₃,
    hk (y + w) (x + z), hk (y + w) (x - z), hk (y - w) (x + z), hk (y - w) (x - z)]
  -- What remains is multilinearity, up to the symmetry of `T(z, w, w, z)`. As in the sixfold
  -- identity, opaque atoms keep the normalization small.
  obtain ⟨t, ht⟩ : ∃ t : M → M → M → M → N, ∀ a b c d, T a b c d = t a b c d :=
    ⟨fun a b c d ↦ T a b c d, fun _ _ _ _ ↦ rfl⟩
  have hzw := hk z w
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, ht] at hzw ⊢
  linear_combination (norm := module) 4 • hzw

end CommSemiring

end LinearMap
