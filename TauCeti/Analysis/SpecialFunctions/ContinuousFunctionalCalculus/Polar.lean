/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Algebra.Algebra.StrictPositivity

/-!
# The polar decomposition of an invertible element

Let `A` be a unital star algebra with a real continuous functional calculus and a compatible
order, for instance a unital C⋆-algebra or the algebra `Matrix n n 𝕜` of square matrices over
`ℝ` or `ℂ`. Every invertible `a : Aˣ` factors uniquely as

`a = √(a a⋆) * u = u * √(a⋆ a)`

with `u` unitary, the *polar decomposition* of `a`. The positive factors are the square roots
`CFC.sqrt (a * star a)` and `CFC.sqrt (star a * a)` of the continuous functional calculus; they
are strictly positive, hence invertible, and the unitary factor is
`Units.polarUnitary a = (√(a a⋆))⁻¹ * a`.

The factorization is unique in the strongest sense: if `a = p * v` with `p ≥ 0` and `v` unitary,
then `p = √(a a⋆)` and `v = Units.polarUnitary a`, and likewise for `a = v * p`. Consequently
the polar decomposition is equivariant for unitary multiplication on either side: for unitaries
`v`, `w`, the positive factor of `v a w` is the conjugate `v √(a a⋆) v⋆`, and its unitary factor
is `v u w`. The unitary factor of `a⋆` is `u⋆`.

For matrices, this is the decomposition of an invertible real matrix into a positive-definite
symmetric matrix times an orthogonal one, and of an invertible complex matrix into a
positive-definite Hermitian matrix times a unitary one; see
`TauCeti/Analysis/Matrix/Polar.lean`.

Operators on Hilbert spaces and linear maps between inner product spaces have their own polar
decomposition `T = U |T|` with a partial isometry `U`, for maps that need not be invertible
(`ContinuousLinearMap.polarFactor`, `LinearMap.polarFactor`). This file instead works in an
abstract algebra, where invertibility makes the factor an element of the unitary submonoid
`unitary A`, as needed for groups of units such as `GL(n, ℂ)` and their unitary subgroups.

## Main declarations

* `CFC.sqrt_unitary_mul_mul_star`: the square root commutes with conjugation by a unitary.
* `Units.polarUnitary a`: the unitary factor of the polar decomposition of `a`.
* `Units.sqrt_mul_star_mul_polarUnitary`, `Units.polarUnitary_mul_sqrt_star_mul`: the left and
  right polar decompositions `a = √(a a⋆) u` and `a = u √(a⋆ a)`.
* `Units.mul_eq_iff_sqrt_mul_star_eq_and_polarUnitary_eq`,
  `Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`: uniqueness of both factorizations;
  `Units.sqrt_star_mul_eq`: the two positive factors are conjugate by the unitary factor.
* `Units.polarUnitary_unitary_mul_mul_unitary`, `Units.sqrt_unitary_mul_mul_unitary`: unitary
  equivariance.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5 (the polar decomposition of `GL(n, ℝ)` and
  `GL(n, ℂ)`).
* Kenneth R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6, American
  Mathematical Society, 1996, Section I.5 (the polar decomposition of an invertible element).
-/

public section

noncomputable section

open Ring

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]

variable [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

namespace CFC

/-- The square root commutes with conjugation by a unitary: `√(u x u⋆) = u √x u⋆`. Both sides
vanish when `x` is not nonnegative. -/
theorem sqrt_unitary_mul_mul_star (u : unitary A) (x : A) :
    sqrt ((u : A) * x * star (u : A)) = u * sqrt x * star (u : A) := by
  by_cases hx : 0 ≤ x
  · refine sqrt_unique ?_ (star_right_conjugate_nonneg (sqrt_nonneg x) _)
    calc (u : A) * sqrt x * star (u : A) * ((u : A) * sqrt x * star (u : A))
        = u * sqrt x * (star (u : A) * u) * sqrt x * star (u : A) := by noncomm_ring
      _ = u * x * star (u : A) := by
        rw [Unitary.star_mul_self_of_mem u.2, mul_one, mul_assoc (u : A) (sqrt x),
          sqrt_mul_sqrt_self x]
  · have hux : ¬0 ≤ (u : A) * x * star (u : A) := by
      rwa [Unitary.isUnit_coe.star_right_conjugate_nonneg_iff]
    rw [sqrt_of_not_nonneg hx, sqrt_of_not_nonneg hux, mul_zero, zero_mul]

end CFC

namespace Units

variable (a : Aˣ)

/-- The positive factor `√(a a⋆)` of the polar decomposition of a unit is strictly positive. -/
theorem isStrictlyPositive_sqrt_mul_star :
    IsStrictlyPositive (CFC.sqrt ((a : A) * star (a : A))) :=
  (isStrictlyPositive_mul_star a).sqrt

/-- The positive factor `√(a⋆ a)` of the right polar decomposition of a unit is strictly
positive. -/
theorem isStrictlyPositive_sqrt_star_mul :
    IsStrictlyPositive (CFC.sqrt (star (a : A) * a)) :=
  (isStrictlyPositive_star_mul a).sqrt

/-- The unitary factor `u = (√(a a⋆))⁻¹ a` of the polar decomposition `a = √(a a⋆) u` of a
unit `a`. -/
def polarUnitary : unitary A :=
  ⟨(CFC.sqrt ((a : A) * star (a : A)))⁻¹ʳ * a, by
    -- `p = √(a a⋆)` is invertible and self-adjoint with `p p = a a⋆`, so `p⁻¹ a (p⁻¹ a)⋆ = 1`.
    have key {p : A} (hp : IsUnit p) (hps : IsSelfAdjoint p) (hpp : p * p = a * star (a : A)) :
        p⁻¹ʳ * a ∈ unitary A := by
      refine (hp.ringInverse.mul a.isUnit).mem_unitary_iff_mul_star_self.2 ?_
      rw [star_mul, ← inverse_star, hps.star_eq, mul_assoc, ← mul_assoc (a : A), ← hpp,
        ← mul_assoc, ← mul_assoc, inverse_mul_cancel _ hp, one_mul, mul_inverse_cancel _ hp]
    exact key (isStrictlyPositive_sqrt_mul_star a).isUnit (CFC.sqrt_nonneg _).isSelfAdjoint
      (CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg (a : A)))⟩

/-- The unitary factor of `a` is `(√(a a⋆))⁻¹ a`. -/
theorem coe_polarUnitary :
    (a.polarUnitary : A) = (CFC.sqrt ((a : A) * star (a : A)))⁻¹ʳ * a :=
  (rfl)

/-- **The polar decomposition** `a = √(a a⋆) u` of a unit, with `u = a.polarUnitary` unitary. -/
@[simp]
theorem sqrt_mul_star_mul_polarUnitary :
    CFC.sqrt ((a : A) * star (a : A)) * a.polarUnitary = a := by
  rw [coe_polarUnitary, ← mul_assoc,
    mul_inverse_cancel _ (isStrictlyPositive_sqrt_mul_star a).isUnit, one_mul]

/-- **Uniqueness of the positive factor.** If `a = p v` with `p ≥ 0` and `v` unitary, then `p`
is `√(a a⋆)`. -/
theorem sqrt_mul_star_eq_of_mul_eq {p : A} (hp : 0 ≤ p) {v : unitary A} (h : p * v = a) :
    CFC.sqrt ((a : A) * star (a : A)) = p := by
  refine CFC.sqrt_unique ?_ hp
  rw [← h, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (v : A),
    Unitary.mul_star_self_of_mem v.2, one_mul]

/-- **Uniqueness of the unitary factor.** If `a = p v` with `p ≥ 0` and `v` unitary, then `v`
is `a.polarUnitary`. -/
theorem polarUnitary_eq_of_mul_eq {p : A} (hp : 0 ≤ p) {v : unitary A} (h : p * v = a) :
    a.polarUnitary = v := by
  refine Subtype.ext ?_
  rw [coe_polarUnitary, sqrt_mul_star_eq_of_mul_eq a hp h, ← h, ← mul_assoc,
    inverse_mul_cancel _ ?_, one_mul]
  rw [← sqrt_mul_star_eq_of_mul_eq a hp h]
  exact (isStrictlyPositive_sqrt_mul_star a).isUnit

/-- The polar decomposition characterizes its two factors: `a = p v` with `p ≥ 0` and `v`
unitary exactly when `p = √(a a⋆)` and `v = a.polarUnitary`. -/
theorem mul_eq_iff_sqrt_mul_star_eq_and_polarUnitary_eq {p : A} (hp : 0 ≤ p) {v : unitary A} :
    p * v = a ↔ CFC.sqrt ((a : A) * star (a : A)) = p ∧ a.polarUnitary = v := by
  refine ⟨fun h ↦ ⟨sqrt_mul_star_eq_of_mul_eq a hp h, polarUnitary_eq_of_mul_eq a hp h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩
  exact sqrt_mul_star_mul_polarUnitary a

/-- The two positive factors are conjugate by the unitary factor:
`√(a⋆ a) = u⋆ √(a a⋆) u`. -/
theorem sqrt_star_mul_eq :
    CFC.sqrt (star (a : A) * a) =
      star (a.polarUnitary : A) * CFC.sqrt ((a : A) * star (a : A)) * a.polarUnitary := by
  refine CFC.sqrt_unique ?_ (star_left_conjugate_nonneg (CFC.sqrt_nonneg _) _)
  have hp := (CFC.sqrt_nonneg ((a : A) * star (a : A))).isSelfAdjoint.star_eq
  conv_rhs => rw [← sqrt_mul_star_mul_polarUnitary a]
  rw [star_mul, hp]
  calc star (a.polarUnitary : A) * CFC.sqrt ((a : A) * star (a : A)) * a.polarUnitary *
        (star (a.polarUnitary : A) * CFC.sqrt ((a : A) * star (a : A)) * a.polarUnitary)
      = star (a.polarUnitary : A) * CFC.sqrt ((a : A) * star (a : A)) *
          ((a.polarUnitary : A) * star (a.polarUnitary : A)) *
          CFC.sqrt ((a : A) * star (a : A)) * a.polarUnitary := by noncomm_ring
    _ = _ := by rw [Unitary.mul_star_self_of_mem a.polarUnitary.2, mul_one]; noncomm_ring

/-- **The right polar decomposition** `a = u √(a⋆ a)` of a unit, with the same unitary factor
`u = a.polarUnitary` as the left one. -/
@[simp]
theorem polarUnitary_mul_sqrt_star_mul :
    a.polarUnitary * CFC.sqrt (star (a : A) * a) = a := by
  rw [sqrt_star_mul_eq, ← mul_assoc, ← mul_assoc, Unitary.mul_star_self_of_mem a.polarUnitary.2,
    one_mul, sqrt_mul_star_mul_polarUnitary]

/-- **Uniqueness of the right positive factor.** If `a = v q` with `v` unitary and `q ≥ 0`, then
`q` is `√(a⋆ a)`. -/
theorem sqrt_star_mul_eq_of_mul_eq {q : A} (hq : 0 ≤ q) {v : unitary A} (h : v * q = a) :
    CFC.sqrt (star (a : A) * a) = q := by
  refine CFC.sqrt_unique ?_ hq
  rw [← h, star_mul, hq.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star (v : A)),
    Unitary.star_mul_self_of_mem v.2, one_mul]

/-- **Uniqueness of the unitary factor, on the right.** If `a = v q` with `v` unitary and
`q ≥ 0`, then `v` is `a.polarUnitary`. -/
theorem polarUnitary_eq_of_mul_eq' {q : A} (hq : 0 ≤ q) {v : unitary A} (h : v * q = a) :
    a.polarUnitary = v := by
  refine polarUnitary_eq_of_mul_eq a (star_right_conjugate_nonneg hq (v : A)) ?_
  rw [mul_assoc, Unitary.star_mul_self_of_mem v.2, mul_one, h]

/-- The right polar decomposition characterizes its two factors: `a = v q` with `v` unitary and
`q ≥ 0` exactly when `v = a.polarUnitary` and `q = √(a⋆ a)`. -/
theorem mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq {q : A} (hq : 0 ≤ q) {v : unitary A} :
    v * q = a ↔ a.polarUnitary = v ∧ CFC.sqrt (star (a : A) * a) = q := by
  refine ⟨fun h ↦ ⟨polarUnitary_eq_of_mul_eq' a hq h, sqrt_star_mul_eq_of_mul_eq a hq h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩
  exact polarUnitary_mul_sqrt_star_mul a

/-! ### Special cases and equivariance -/

/-- A unitary is its own unitary factor. -/
@[simp]
theorem polarUnitary_toUnits (v : unitary A) : (Unitary.toUnits v).polarUnitary = v :=
  polarUnitary_eq_of_mul_eq _ zero_le_one (one_mul _)

/-- A nonnegative unit has trivial unitary factor. -/
theorem polarUnitary_eq_one {a : Aˣ} (ha : 0 ≤ (a : A)) : a.polarUnitary = 1 :=
  polarUnitary_eq_of_mul_eq a ha (mul_one _)

/-- The identity has trivial unitary factor. -/
@[simp]
theorem polarUnitary_one : (1 : Aˣ).polarUnitary = 1 :=
  polarUnitary_eq_one zero_le_one

/-- The unitary factor of the adjoint is the adjoint of the unitary factor. -/
@[simp]
theorem polarUnitary_star : (star a).polarUnitary = star a.polarUnitary := by
  refine polarUnitary_eq_of_mul_eq _ (CFC.sqrt_nonneg (star (a : A) * a)) ?_
  have h := congrArg star (polarUnitary_mul_sqrt_star_mul a)
  rw [star_mul, (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq] at h
  rw [Unitary.coe_star, coe_star, h]

/-- The polar decomposition of `v a w`, for unitaries `v` and `w`: it is
`(v √(a a⋆) v⋆) (v u w)`. -/
private theorem unitary_mul_mul_unitary_eq (v w : unitary A) :
    (v : A) * CFC.sqrt ((a : A) * star (a : A)) * star (v : A) *
        ((v * a.polarUnitary * w : unitary A) : A) =
      ((Unitary.toUnits v * a * Unitary.toUnits w : Aˣ) : A) := by
  simp only [Units.val_mul, Unitary.val_toUnits_apply, Submonoid.coe_mul]
  conv_rhs => rw [← sqrt_mul_star_mul_polarUnitary a]
  calc (v : A) * CFC.sqrt ((a : A) * star (a : A)) * star (v : A) *
        ((v : A) * a.polarUnitary * w)
      = v * CFC.sqrt ((a : A) * star (a : A)) * (star (v : A) * v) * a.polarUnitary * w := by
        noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem v.2, mul_one, mul_assoc (v : A)]

/-- **Unitary equivariance of the unitary factor.** For unitaries `v` and `w`, the unitary factor
of `v a w` is `v u w`. -/
@[simp]
theorem polarUnitary_unitary_mul_mul_unitary (v w : unitary A) :
    (Unitary.toUnits v * a * Unitary.toUnits w).polarUnitary = v * a.polarUnitary * w :=
  polarUnitary_eq_of_mul_eq _
    (star_right_conjugate_nonneg (CFC.sqrt_nonneg ((a : A) * star (a : A))) (v : A))
    (unitary_mul_mul_unitary_eq a v w)

/-- **Unitary equivariance of the positive factor.** For unitaries `v` and `w`, the positive
factor of `v a w` is the conjugate `v √(a a⋆) v⋆`. -/
theorem sqrt_unitary_mul_mul_unitary (v w : unitary A) :
    CFC.sqrt (((Unitary.toUnits v * a * Unitary.toUnits w : Aˣ) : A) *
        star ((Unitary.toUnits v * a * Unitary.toUnits w : Aˣ) : A)) =
      v * CFC.sqrt ((a : A) * star (a : A)) * star (v : A) :=
  sqrt_mul_star_eq_of_mul_eq _
    (star_right_conjugate_nonneg (CFC.sqrt_nonneg ((a : A) * star (a : A))) (v : A))
    (unitary_mul_mul_unitary_eq a v w)

end Units
