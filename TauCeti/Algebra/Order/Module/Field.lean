/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Linear functionals bounded below on the nonnegative cone

Over a linearly ordered field `𝕜`, the nonnegative elements of an ordered `𝕜`-module are a cone:
they are stable under multiplication by nonnegative scalars. A linear functional that is bounded
below on this cone is therefore nonnegative on it, since a negative value at `w` would be scaled
below any bound along the ray through `w`.

## Main results

* `LinearMap.apply_nonneg_of_forall_le`: a linear functional bounded below on the nonnegative
  elements is nonnegative on them.
-/

public section

namespace LinearMap

/-- A linear functional on an ordered module over a linearly ordered field that is bounded below
on the nonnegative elements is nonnegative on them. -/
theorem apply_nonneg_of_forall_le {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommMonoid V] [Preorder V] [Module 𝕜 V] [PosSMulMono 𝕜 V]
    (ψ : V →ₗ[𝕜] 𝕜) {u : 𝕜} (hψ : ∀ w : V, 0 ≤ w → u ≤ ψ w) {w : V} (hw : 0 ≤ w) :
    0 ≤ ψ w := by
  have hu : u ≤ 0 := (hψ 0 le_rfl).trans_eq (map_zero ψ)
  -- `t • w` is nonnegative, so `u ≤ t ψ w`, for every `t ≥ 0`.
  by_contra! hneg
  have ht : 0 ≤ u / ψ w := div_nonneg_of_nonpos hu hneg.le
  have hle := hψ ((u / ψ w + 1) • w) (smul_nonneg (by linarith) hw)
  rw [map_smul, smul_eq_mul] at hle
  have hcancel : (u / ψ w + 1) * ψ w = u + ψ w := by
    field_simp [hneg.ne]
  linarith

end LinearMap
