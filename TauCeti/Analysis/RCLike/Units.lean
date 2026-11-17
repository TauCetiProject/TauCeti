/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Units.Real
public import Mathlib.Analysis.RCLike.Basic

/-!
# Positive real scalar units over real and complex normed fields

For an `RCLike` field, positive real scalar units are exactly the units that are positive in
the real partial order. The real and imaginary coordinate criteria are Mathlib's
`RCLike.pos_iff` and `RCLike.nonneg_iff`.

## Main results

* `Units.mem_posRealSubgroup`: membership is positivity in the real partial order.

## References

* Mathlib, `RCLike.pos_iff_exists_ofReal` and `Units.mem_posSubgroup`.
-/

public section

open scoped ComplexOrder

namespace Units

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A unit of a real or complex normed field is a positive real scalar exactly when it is
positive in the real partial order. -/
@[simp]
theorem mem_posRealSubgroup {z : 𝕜ˣ} :
    z ∈ posRealSubgroup 𝕜 ↔ 0 < (z : 𝕜) := by
  rw [mem_posRealSubgroup_iff_exists_algebraMap_eq]
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (RCLike.pos_iff_exists_ofReal (z := (z : 𝕜))).symm

end Units
