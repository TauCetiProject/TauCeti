/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Determinants of scalar perturbations of projections

For an idempotent `e`, the operator `1 + c e` acts by `1 + c` on its range and by `1` on
its kernel. Its determinant is therefore `(1 + c) ^ dim (range e)`.
This formula lets a determinant recover the rank of a projection.
-/

public section

namespace LinearMap

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The determinant of a scalar perturbation of an idempotent depends only on its rank. -/
@[simp]
theorem det_one_add_smul_of_isIdempotentElem {e : Module.End K M}
    (he : IsIdempotentElem e) (c : K) :
    (1 + c • e).det = (1 + c) ^ Module.finrank K (range e) := by
  have hfactor : e = (range e).subtype ∘ₗ e.rangeRestrict :=
    e.subtype_comp_rangeRestrict.symm
  have hrestrict : e.rangeRestrict ∘ₗ (range e).subtype = 1 := by
    ext x
    -- The subtype and range-restriction coercions evaluate to `e x` and `x` after extensionality.
    exact (LinearMap.IsIdempotentElem.isProj_range e he).map_id x x.property
  calc
    (1 + c • e).det = (1 + e.rangeRestrict ∘ₗ (c • (range e).subtype)).det := by
      conv_lhs => rw [hfactor, ← LinearMap.smul_comp]
      exact det_one_add_comp_comm _ _
    _ = (1 + c) ^ Module.finrank K (range e) := by
      have hscalar : (1 : Module.End K (range e)) + c • 1 = (1 + c) • 1 := by
        rw [add_smul, one_smul]
      rw [LinearMap.comp_smul, hrestrict, hscalar, det_smul, map_one, mul_one]

end LinearMap
