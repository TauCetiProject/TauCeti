/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
import Mathlib.RingTheory.IntegralDomain

/-!
# The averaging idempotent of a group algebra

For a finite group `G` whose order is invertible in `k`, Mathlib's `GroupAlgebra.average k G` is
the element `e = #G⁻¹ ∑ g` of `k[G]`, and Mathlib records that it is absorbed by every group
element on either side. This file records that `e` is an idempotent and computes its
coefficients: every coefficient of `e` is `#G⁻¹`. More generally, every `x ∈ k[G]` multiplies `e`
on either side by its augmentation, so `e` is central. It also evaluates `e` under characters: the
trivial character (the augmentation) sends `e` to `1`, and a nontrivial character with values in a
domain sends it to `0`, by row orthogonality.

For a subring `R` of `k`, the coefficient computation shows that `e` lies outside `R[G]` when
`#G` is not a unit of `R`, while idempotence makes `e` integral over `R`. Together these show that
the group ring `R[G]` is then not a maximal `R`-order in `k[G]`.
-/

public section

open MonoidAlgebra

namespace GroupAlgebra

variable (k G : Type*) [CommSemiring k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]

/-- Every coefficient of `average k G` is `⅟#G`. -/
@[simp]
theorem coeff_average (g : G) : (average k G).coeff g = ⅟(Fintype.card G : k) := by
  classical
  simp [average, coeff_sum, coeff_single, Finsupp.single_apply]

/-- `average k G` is an idempotent of `k[G]`. -/
theorem isIdempotentElem_average : IsIdempotentElem (average k G) :=
  calc average k G * average k G
      = ⅟(Fintype.card G : k) • ∑ g : G, of k G g * average k G := by
        rw [← Finset.sum_mul, ← Algebra.smul_mul_assoc, ← average.eq_1]
    _ = average k G := by simp [← Nat.cast_smul_eq_nsmul k, smul_smul]

variable {k G}

/-- Multiplying `average k G` on the left by any `x` multiplies it by the augmentation of `x`. -/
theorem mul_average (x : MonoidAlgebra k G) :
    x * average k G = augmentation k G x • average k G := by
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [of_apply, mul_average_left, augmentation_single, one_smul]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, add_smul]
  | smul r x hx =>
    rw [smul_mul_assoc, hx, augmentation_smul, smul_smul]

/-- Multiplying `average k G` on the right by any `x` multiplies it by the augmentation of `x`. -/
theorem average_mul (x : MonoidAlgebra k G) :
    average k G * x = augmentation k G x • average k G := by
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [of_apply, mul_average_right, augmentation_single, one_smul]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_smul]
  | smul r x hx =>
    rw [mul_smul_comm, hx, augmentation_smul, smul_smul]

/-- `average k G` is central in `k[G]`. -/
theorem average_mem_center : average k G ∈ Subalgebra.center k (MonoidAlgebra k G) :=
  Subalgebra.mem_center_iff.mpr fun x ↦ by rw [mul_average, average_mul]

/-- The coefficient-sum augmentation sends `average k G` to `1`. -/
@[simp]
theorem augmentation_average : augmentation k G (average k G) = 1 := by
  simp only [average, augmentation_smul, map_sum, of_apply, augmentation_single,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, invOf_mul_self]

/-- The augmentation sends `average k G` to `1`. -/
@[simp]
theorem lift_one_average {A : Type*} [Semiring A] [Algebra k A] :
    lift k A G 1 (average k G) = 1 := by
  rw [lift_one_apply, augmentation_average, map_one]

/-- A nontrivial character with values in a domain sends `average k G` to `0`. -/
theorem lift_average_of_ne_one {A : Type*} [CommRing A] [IsDomain A] [Algebra k A] {χ : G →* A}
    (hχ : χ ≠ 1) : lift k A G χ (average k G) = 0 := by
  rw [average, map_smul, map_sum]
  simp [sum_hom_units_eq_zero χ hχ]

end GroupAlgebra
