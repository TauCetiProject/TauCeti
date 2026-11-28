/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The determinant of `1 + c • e` for an idempotent `e`

An idempotent endomorphism `e` of a finite-dimensional vector space splits it as the direct sum of
its range, on which `e` is the identity, and its kernel. So `1 + c • e` is the scalar `1 + c` on
the range and the identity on the kernel, and its determinant is `(1 + c) ^ r` with `r` the
dimension of the range of `e`.

## Main results

* `LinearMap.det_one_add_smul_of_isIdempotentElem`: `det (1 + c • e) = (1 + c) ^ dim (range e)`
  for an idempotent `e`.
-/

public section

open Module

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The determinant of `1 + c • e` for an idempotent `e`** is `(1 + c) ^ r`, where `r` is the
dimension of the range of `e`: in the splitting `V = range e ⊕ ker e`, the endomorphism
`1 + c • e` is the scalar `1 + c` on the first summand and the identity on the second. The
proof factors `c • e` through `range e` and applies the Weinstein–Aronszajn identity
`LinearMap.det_one_add_comp_comm`. -/
theorem det_one_add_smul_of_isIdempotentElem {e : V →ₗ[K] V} (he : IsIdempotentElem e) (c : K) :
    LinearMap.det (1 + c • e) = (1 + c) ^ finrank K (range e) := by
  have hYX : e.rangeRestrict ∘ₗ (c • (range e).subtype) = c • LinearMap.id := by
    ext x
    simp [(IsIdempotentElem.mem_range_iff he).mp x.property]
  have hXY : (c • (range e).subtype) ∘ₗ e.rangeRestrict = c • e := by
    ext x
    simp
  rw [← hXY, det_one_add_comp_comm, hYX, ← Module.End.one_eq_id, ← one_smul K (1 : End K _),
    smul_smul, mul_one, ← add_smul, det_smul, map_one, mul_one]

end LinearMap
