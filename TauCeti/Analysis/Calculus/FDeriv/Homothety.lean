/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.Module.Determinant
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# The derivative and the Jacobian determinant of a homothety

The map `x ↦ c • x + a` has derivative `c • id` at every point
(`TauCeti.fderiv_smul_add_const`), so its Jacobian determinant is `c ^ finrank 𝕜 E`
(`TauCeti.det_fderiv_smul_add_const`). Over `ℝ` with `c > 0` this is also its absolute value
(`TauCeti.abs_det_fderiv_smul_add_const`), the factor by which the homothety scales volumes in
the change-of-variables formula.
-/

public section

namespace TauCeti

section NormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The derivative of the homothety `x ↦ c • x + a` is `c • id` at every point. -/
theorem fderiv_smul_add_const (c : 𝕜) (a : E) :
    fderiv 𝕜 (fun x : E => c • x + a) = fun _ => c • ContinuousLinearMap.id 𝕜 E :=
  funext fun x => (((hasFDerivAt_id x).const_smul c).add_const a).fderiv

/-- The Jacobian determinant of the homothety `x ↦ c • x + a` is `c ^ finrank 𝕜 E` at every
point. -/
theorem det_fderiv_smul_add_const (c : 𝕜) (a x : E) :
    (fderiv 𝕜 (fun x : E => c • x + a) x).det = c ^ Module.finrank 𝕜 E := by
  rw [fderiv_smul_add_const, ContinuousLinearMap.det_smul, ContinuousLinearMap.det_id, mul_one]

end NormedField

/-- The Jacobian determinant of the homothety `x ↦ ε • x + a` with `ε > 0` has absolute value
`ε ^ finrank ℝ E` at every point. -/
theorem abs_det_fderiv_smul_add_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ε : ℝ} (hε : 0 < ε) (a x : E) :
    |(fderiv ℝ (fun x : E => ε • x + a) x).det| = ε ^ Module.finrank ℝ E := by
  rw [det_fderiv_smul_add_const, abs_of_pos (pow_pos hε _)]

end TauCeti
