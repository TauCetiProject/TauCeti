/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Calculus.FDeriv.Smul

/-!
# Derivatives of scalar multiples

`HasDerivWithinAt.smul_of_eq_zero` and `HasDerivAt.smul_of_eq_zero` differentiate a scalar
multiple at a zero of the scalar factor assuming only continuity of the vector factor. The
scalar factor may take values in a normed algebra over the parameter field.

At a point where the scalar factor `u` is nonzero and `u' = u c`, multiplication by `u` is a gauge
transformation: `HasDerivAt.hasDerivAt_iff_hasDerivAt_smul` states that `η' = u⁻¹ w - c η`
exactly when `(u η)' = w`.

`TauCeti.hasDerivAt_add_smul_add_sq_smul` differentiates a quadratic polynomial
`t ↦ u + t • v + t ^ 2 • w` with vector coefficients at `0`: its derivative there is `v`. This is
how a first variation is read off from an exact quadratic expansion along a line.
-/

public section

variable {𝕜 𝕜' F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- At a zero of a differentiable scalar factor, the vector factor need only be continuous
within the parameter set to differentiate their scalar multiple. -/
theorem HasDerivWithinAt.smul_of_eq_zero {c : 𝕜 → 𝕜'} {c' : 𝕜'} {f : 𝕜 → F}
    {s : Set 𝕜} {x : 𝕜} (hc : HasDerivWithinAt c c' s x)
    (hf : ContinuousWithinAt f s x) (hc0 : c x = 0) :
    HasDerivWithinAt (fun y ↦ c y • f y) (c' • f x) s x := by
  simpa using (hc.hasFDerivWithinAt.smul_of_eq_zero hf hc0).hasDerivWithinAt

/-- At a zero of a differentiable scalar factor, the vector factor need only be continuous
to differentiate their scalar multiple. -/
theorem HasDerivAt.smul_of_eq_zero {c : 𝕜 → 𝕜'} {c' : 𝕜'} {f : 𝕜 → F}
    {x : 𝕜} (hc : HasDerivAt c c' x) (hf : ContinuousAt f x) (hc0 : c x = 0) :
    HasDerivAt (fun y ↦ c y • f y) (c' • f x) x := by
  simpa using (hc.hasFDerivAt.smul_of_eq_zero hf hc0).hasDerivAt

section Gauge

variable {𝕜 𝕜' F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

/-- **The gauge identity.** For a scalar factor `u` with `u x ≠ 0` and `u' = u c` at `x`,
`η' = u⁻¹ w - c η` at `x` exactly when `(u η)' = w` at `x`. -/
theorem HasDerivAt.hasDerivAt_iff_hasDerivAt_smul {u : 𝕜 → 𝕜'} {c : 𝕜'} {η : 𝕜 → F} {w : F}
    {x : 𝕜} (hu : HasDerivAt u (u x * c) x) (hu0 : u x ≠ 0) :
    HasDerivAt η ((u x)⁻¹ • w - c • η x) x ↔ HasDerivAt (fun t ↦ u t • η t) w x := by
  constructor
  · intro h
    refine (hu.smul h).congr_deriv ?_
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hu0, one_smul, smul_smul]
    abel
  · intro h
    -- `η = u⁻¹ (u η)` near `x`, and `u⁻¹` has derivative `-c u⁻¹`.
    have hinv : HasDerivAt (fun t ↦ (u t)⁻¹) (-c * (u x)⁻¹) x := by
      refine (hu.inv hu0).congr_deriv ?_
      field_simp
    refine ((hinv.smul h).congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hu.continuousAt.eventually_ne hu0] with t ht
      rw [Pi.smul_apply', smul_smul, inv_mul_cancel₀ ht, one_smul]
    · rw [smul_smul, mul_assoc, inv_mul_cancel₀ hu0, mul_one, neg_smul]
      abel

end Gauge

namespace TauCeti

/-- A quadratic polynomial `t ↦ u + t • v + t ^ 2 • w` with vector coefficients has derivative `v`
at `0`. -/
theorem hasDerivAt_add_smul_add_sq_smul {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (u v w : F) :
    HasDerivAt (fun t : 𝕜 ↦ u + t • v + t ^ 2 • w) v 0 := by
  convert ((hasDerivAt_const (0 : 𝕜) u).add ((hasDerivAt_id (0 : 𝕜)).smul_const v)).add
    (((hasDerivAt_id (0 : 𝕜)).pow 2).smul_const w) using 1 <;> simp [Pi.add_def]

end TauCeti
