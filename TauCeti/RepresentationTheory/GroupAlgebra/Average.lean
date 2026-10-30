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
theorem isIdempotentElem_average : IsIdempotentElem (average k G) :=
  calc average k G * average k G
      = ⅟(Fintype.card G : k) • ∑ g : G, of k G g * average k G := by
        rw [← Finset.sum_mul, ← Algebra.smul_mul_assoc, ← average.eq_1]
    _ = average k G := by simp [← Nat.cast_smul_eq_nsmul k, smul_smul]

end GroupAlgebra
