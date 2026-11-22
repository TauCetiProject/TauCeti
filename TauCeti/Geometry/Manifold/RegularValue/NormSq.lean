/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Manifold.RegularValue

/-!
# Regular values of the squared norm

On a real inner product space every nonzero value of `x ↦ ‖x‖²` is regular
(`TauCeti.isRegularValue_norm_sq`): the derivative at `x` is `v ↦ 2 ⟪x, v⟫`, which is onto as soon
as `x ≠ 0`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every nonzero value of the squared norm on a real inner product space is a regular value:
the derivative `v ↦ 2 ⟪x, v⟫` at a point `x ≠ 0` is onto. -/
theorem isRegularValue_norm_sq {c : ℝ} (hc : c ≠ 0) :
    IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x : E ↦ ‖x‖ ^ 2) c := by
  rw [isRegularValue_iff]
  intro x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hx.symm)
  rw [isRegularPoint_iff_surjective_fderiv, fderiv_norm_sq_apply]
  intro t
  refine ⟨(t / (2 * ‖x‖ ^ 2)) • x, ?_⟩
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx0)
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
    inner_smul_right, real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp [hx2]

end TauCeti
