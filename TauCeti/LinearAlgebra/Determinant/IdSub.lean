/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of `id - f` for an invertible `f`

For endomorphisms `P` and `Q` of a module with `Q ∘ₗ P = id`, the endomorphism `id - Q` factors as
`(-Q) ∘ₗ (id - P)`, and `-Q` has a unit determinant, inverse to that of `-P`. So `det (id - Q)` is
nonzero exactly when `det (id - P)` is, over every commutative ring. For instance, the condition
`det (1 - φ_*) ≠ 0` on the map induced by a homeomorphism `φ` is the same for `φ` and `φ⁻¹`.

## Main results

* `LinearMap.det_id_sub_ne_zero_iff_of_comp_eq_id`: if `Q ∘ₗ P = id`, then `det (id - Q) ≠ 0`
  exactly when `det (id - P) ≠ 0`.
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `Q ∘ₗ P = id`, then `det (id - Q) ≠ 0` exactly when `det (id - P) ≠ 0`, since
`id - Q = (-Q) ∘ₗ (id - P)` and `det (-Q)` is a unit, with inverse `det (-P)`. -/
theorem det_id_sub_ne_zero_iff_of_comp_eq_id {P Q : M →ₗ[R] M} (hQP : Q ∘ₗ P = id) :
    (id - Q).det ≠ 0 ↔ (id - P).det ≠ 0 := by
  have hsplit : id - Q = (-Q) ∘ₗ (id - P) := by
    rw [comp_sub, comp_id, neg_comp, hQP]
    abel
  have hunit : IsUnit (-Q).det :=
    .of_mul_eq_one _ (by rw [← det_comp, neg_comp, comp_neg, neg_neg, hQP, det_id])
  rw [hsplit, det_comp, ne_eq, ne_eq, hunit.mul_right_eq_zero]

end LinearMap
