/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.LinearMapCompletion
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Weak null convergence of orthonormal families

Every orthonormal family `(v i)` in a real or complex inner product space converges weakly to
zero along the cofinite filter (`Orthonormal.tendsto_toWeakSpace_zero_cofinite`), and in
particular every orthonormal sequence converges weakly to zero
(`Orthonormal.tendsto_toWeakSpace_zero_atTop`).

No completeness assumption is needed: each continuous linear functional extends to the Hilbert
space completion, where Riesz representation identifies it with an inner product, and Bessel's
inequality (`Orthonormal.inner_products_summable`) forces the inner products with `(v i)` to be
square-summable and hence tend to zero along the cofinite filter.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, Chapter V, §1.
-/

public section

open Filter Topology
open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every orthonormal family in a real or complex inner product space converges weakly to zero
along the cofinite filter. Completeness is not required. -/
theorem tendsto_toWeakSpace_zero_cofinite {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Tendsto (fun i ↦ toWeakSpace 𝕜 E (v i)) cofinite (𝓝 0) := by
  rw [← map_zero (toWeakSpace 𝕜 E), TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto]
  intro f
  -- Extend `f` to the completion so Riesz representation and Bessel's inequality apply.
  have hcomp : Orthonormal 𝕜 (fun i ↦ (v i : UniformSpace.Completion E)) :=
    ⟨fun i ↦ by simpa only [UniformSpace.Completion.norm_coe] using hv.1 i,
      fun _ _ h ↦ by simpa only [UniformSpace.Completion.inner_coe] using hv.2 h⟩
  let y : UniformSpace.Completion E :=
    (InnerProductSpace.toDual 𝕜 (UniformSpace.Completion E)).symm f.fromCompletion
  have hsq : Tendsto (fun i ↦ ‖⟪(v i : UniformSpace.Completion E), y⟫_𝕜‖ ^ 2) cofinite (𝓝 0) :=
    (hcomp.inner_products_summable y).tendsto_cofinite_zero
  have hnorm : Tendsto (fun i ↦ ‖f (v i)‖) cofinite (𝓝 0) := by
    have hsqrt : Tendsto (fun i ↦ √(‖⟪(v i : UniformSpace.Completion E), y⟫_𝕜‖ ^ 2))
        cofinite (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hsq
    refine hsqrt.congr fun i ↦ ?_
    rw [Real.sqrt_sq (norm_nonneg _), norm_inner_symm]
    simp [y]
  rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact hnorm

/-- Every orthonormal sequence in a real or complex inner product space converges weakly to zero.
Completeness is not required. -/
theorem tendsto_toWeakSpace_zero_atTop {v : ℕ → E} (hv : Orthonormal 𝕜 v) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 E (v n)) atTop (𝓝 0) :=
  Nat.cofinite_eq_atTop ▸ hv.tendsto_toWeakSpace_zero_cofinite

end Orthonormal
