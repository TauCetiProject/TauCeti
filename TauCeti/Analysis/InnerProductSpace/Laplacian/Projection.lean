/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The Laplacian of the squared norm of an orthogonal projection

For a subspace `K` of a finite-dimensional real inner product space with orthogonal projection
`P = K.starProjection`, the Laplacian of `y ↦ ‖P y‖²` is the constant `2 dim K`. For `K = ⊤` this
is `TauCeti.laplacian_norm_sq`. Since `dim K + dim Kᗮ = dim E`, the quadratic polynomial
`dim K ‖P_{Kᗮ} y‖² - dim Kᗮ ‖P_K y‖²` is therefore harmonic, which makes it a barrier for
maximum principles adapted to an orthogonal splitting of `E`.

## Main results

* `Submodule.laplacian_norm_starProjection_sq`: `Δ ‖P_K y‖² = 2 dim K`.
-/

public section

namespace Submodule

open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian of the squared norm of an orthogonal projection is twice the rank of the
projection: `Δ ‖P_K y‖² = 2 dim K`. For `K = ⊤` this is `TauCeti.laplacian_norm_sq`. -/
@[simp]
theorem laplacian_norm_starProjection_sq (K : Submodule ℝ E) (x : E) :
    Δ (fun y ↦ ‖K.starProjection y‖ ^ 2) x = 2 * (Module.finrank ℝ K : ℝ) := by
  set P := K.starProjection
  set b := stdOrthonormalBasis ℝ E
  -- `P` is linear, so its own Laplacian vanishes and its derivative is `P`.
  have hΔP : Δ (P : E → E) x = 0 := by
    have hd : fderiv ℝ (P : E → E) = fun _ ↦ P := funext fun _ ↦ P.fderiv
    rw [TauCeti.laplacian_eq_traceL, hd]
    simp
  -- `‖P v‖² = ⟪v, P v⟫`, since `v - P v` is orthogonal to `P v ∈ K`.
  have hsq (v : E) : ‖P v‖ ^ 2 = ⟪v, P v⟫ := by
    have h0 := K.starProjection_inner_eq_zero v (P v) (K.starProjection_apply_mem v)
    rw [inner_sub_left, sub_eq_zero] at h0
    rw [h0]
    exact (real_inner_self_eq_norm_sq _).symm
  -- The trace of the projection is its rank.
  have hproj : LinearMap.IsProj K (P : E →ₗ[ℝ] E) :=
    ⟨fun v ↦ K.starProjection_apply_mem v, fun v hv ↦ K.starProjection_eq_self_iff.2 hv⟩
  rw [P.contDiff.contDiffAt.laplacian_norm_sq b, hΔP, inner_zero_right, mul_zero, add_zero,
    P.fderiv]
  have htr := LinearMap.trace_eq_sum_inner (P : E →ₗ[ℝ] E) b
  simp only [ContinuousLinearMap.coe_coe] at htr
  simp_rw [hsq, ← htr, hproj.trace]

end Submodule
