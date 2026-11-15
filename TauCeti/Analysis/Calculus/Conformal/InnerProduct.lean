/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.InnerProductSpace.ConformalLinearMap

/-!
# Regularity of the reciprocal conformal factor

Let `f` be a map between real inner product spaces whose derivative satisfies
`ρ(x)² ⟪Df(x) u, Df(x) v⟫ = ⟪u, v⟫` on an open set `U`, for a positive function `ρ`: the
reciprocal of the conformal factor. Then `ρ(x) = ‖Df(x) e‖⁻¹` for any unit vector `e`
(`TauCeti.eq_inv_norm_apply_of_sq_mul_inner`), so `ρ` loses one derivative relative to `f`.

## Main results

* `TauCeti.contDiffOn_of_inner_fderiv`: the reciprocal conformal factor of a `C^(m + 1)` map is
  `C^m`.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f : E → F} {ρ : E → ℝ} {U : Set E}

/-- The reciprocal conformal factor of a `C^(m + 1)` map is `C^m`: if `f` is `C^(m + 1)` on an
open set `U` and `ρ(x)² ⟪Df(x) u, Df(x) v⟫ = ⟪u, v⟫` on `U` for a positive function `ρ`, then
`ρ` is `C^m` on `U`. -/
theorem contDiffOn_of_inner_fderiv [Nontrivial E] {m : ℕ}
    (hf : ContDiffOn ℝ (m + 1) f U) (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) : ContDiffOn ℝ m ρ U := by
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  have hne : ∀ x ∈ U, fderiv ℝ f x e ≠ 0 := fun x hx h0 ↦ by
    have := hρ x hx e e
    rw [h0, inner_zero_left, mul_zero, real_inner_self_eq_norm_sq, he] at this
    norm_num at this
  have hd : ContDiffOn ℝ m (fun y ↦ fderiv ℝ f y e) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  refine ContDiffOn.congr (fun x hx ↦ ?_)
    (fun x hx ↦ eq_inv_norm_apply_of_sq_mul_inner (hρ x hx) (hρ0 x hx) he)
  exact (((contDiffAt_norm ℝ (hne x hx)).comp x ((hd x hx).contDiffAt (hU.mem_nhds hx))).inv
    (norm_ne_zero_iff.2 (hne x hx))).contDiffWithinAt

end TauCeti
