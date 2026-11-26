/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# The derivative of a dilation

The dilation `x ↦ c • x` of a normed space over a nontrivially normed field `𝕜` has derivative
`c • id` at every point. Its operator norm is thus at most `‖c‖`, and its determinant is
`c ^ n`, where `n` is the dimension. These are the bounds that a change of variables by a dilation
needs.

## Main declarations

* `TauCeti.fderiv_const_smul'`: `D(c • ·) = c • id`.
* `TauCeti.norm_fderiv_const_smul_le`: `‖D(c • ·)‖ ≤ ‖c‖`.
* `TauCeti.det_fderiv_const_smul`: `det D(c • ·) = c ^ n`.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The dilation `x ↦ c • x` has derivative `c • id` everywhere: the case `f = id` of
`fderiv_const_smul`. -/
theorem fderiv_const_smul' (c : 𝕜) (x : E) :
    fderiv 𝕜 (fun y : E => c • y) x = c • ContinuousLinearMap.id 𝕜 E :=
  ((hasFDerivAt_id x).const_smul c).fderiv

/-- The derivative `c • id` of the dilation `x ↦ c • x` has operator norm at most `‖c‖`. -/
theorem norm_fderiv_const_smul_le (c : 𝕜) (x : E) :
    ‖fderiv 𝕜 (fun y : E => c • y) x‖ ≤ ‖c‖ := by
  rw [fderiv_const_smul']
  exact (norm_smul_le c _).trans
    (mul_le_of_le_one_right (norm_nonneg c) ContinuousLinearMap.norm_id_le)

/-- The derivative `c • id` of the dilation `x ↦ c • x` has determinant `c ^ n`, where `n` is the
dimension. -/
@[simp]
theorem det_fderiv_const_smul (c : 𝕜) (x : E) :
    (fderiv 𝕜 (fun y : E => c • y) x).det = c ^ Module.finrank 𝕜 E := by
  rw [fderiv_const_smul', ContinuousLinearMap.det_smul,
    ContinuousLinearMap.det_id, mul_one]

end TauCeti
