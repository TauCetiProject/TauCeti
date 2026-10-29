/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# The averaging idempotent of a group algebra

For a finite group `G` whose order is invertible in `k`, Mathlib's `GroupAlgebra.average k G` is
the element `e = #G⁻¹ ∑ g` of `k[G]`, and Mathlib records that it is absorbed by every group
element on either side. This file records that `e` is an idempotent and computes its
coefficients: every coefficient of `e` is `#G⁻¹`.

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
theorem isIdempotentElem_average : IsIdempotentElem (average k G) := by
  rw [IsIdempotentElem]
  nth_rw 1 [average]
  simp only [Algebra.smul_mul_assoc, Finset.sum_mul, of_apply, mul_average_left,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self,
    one_smul]

end GroupAlgebra
