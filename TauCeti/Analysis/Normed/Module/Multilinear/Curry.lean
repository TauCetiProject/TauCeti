/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Evaluating a continuous multilinear map in its last argument

For a fixed vector `h`, evaluating an `(m + 1)`-linear map `M` with `h` in the last argument,
`M ↦ (v ↦ M (v₁, …, v_m, h))`, is a continuous linear map from `(m + 1)`-linear maps to `m`-linear
maps with operator norm at most `‖h‖`. It commutes with fixing the first argument by
`ContinuousMultilinearMap.curryLeft`.

This is the operation that turns the `(m + 1)`-st derivative of a map into the `m`-th derivative
of its directional derivative in the direction `h`, with `h` in the last slot.

## Main declarations

* `ContinuousMultilinearMap.applyLastL`: evaluation with `h` in the last argument, as a
  continuous linear map.
* `ContinuousMultilinearMap.norm_applyLastL_le`: its operator norm is at most `‖h‖`.
* `ContinuousMultilinearMap.applyLastL_comp_curryLeft`: it commutes with `curryLeft`.
-/

public section

noncomputable section

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 F) in
/-- Evaluation of an `(m + 1)`-linear map with `h` in the last argument, as a continuous linear
map to `m`-linear maps. -/
def applyLastL (m : ℕ) (h : E) : (E [×(m + 1)]→L[𝕜] F) →L[𝕜] (E [×m]→L[𝕜] F) :=
  ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin m ↦ E) (E →L[𝕜] F) F
      (ContinuousLinearMap.apply 𝕜 F h) ∘L
    ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).toContinuousLinearEquiv :
      (E [×(m + 1)]→L[𝕜] F) →L[𝕜] (E [×m]→L[𝕜] E →L[𝕜] F))

/-- `applyLastL 𝕜 F m h M` evaluates `M` with `h` in the last argument. -/
@[simp]
theorem applyLastL_apply (m : ℕ) (h : E) (M : E [×(m + 1)]→L[𝕜] F) (v : Fin m → E) :
    applyLastL 𝕜 F m h M v = M (Fin.snoc v h) := by
  simp [applyLastL]

/-- Evaluation with `h` in the last argument has operator norm at most `‖h‖`. -/
theorem norm_applyLastL_le (m : ℕ) (h : E) : ‖applyLastL 𝕜 F m h‖ ≤ ‖h‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h) fun M ↦ ?_
  refine opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [applyLastL_apply]
  refine (M.le_opNorm _).trans_eq ?_
  rw [Fin.prod_univ_castSucc, Fin.snoc_last]
  simp only [Fin.snoc_castSucc]
  ring

/-- Evaluation in the last argument commutes with fixing the first argument. -/
theorem applyLastL_comp_curryLeft (m : ℕ) (h : E) (M : E [×(m + 2)]→L[𝕜] F) :
    (applyLastL 𝕜 F m h).comp M.curryLeft = (applyLastL 𝕜 F (m + 1) h M).curryLeft := by
  ext v w
  simp [Fin.cons_snoc_eq_snoc_cons]

end ContinuousMultilinearMap
