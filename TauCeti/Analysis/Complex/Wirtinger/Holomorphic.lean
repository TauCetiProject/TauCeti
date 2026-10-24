/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Complex.Conformal

/-!
# Holomorphy and the conjugate Wirtinger derivative

For a real-differentiable map from `ℂ` to a complex normed space, vanishing of the conjugate
Wirtinger derivative characterizes complex differentiability. The real-differentiability
hypothesis is essential because the totalized real derivative vanishes at nondifferentiable
points. In one variable the real differential has coefficients `∂f(1)` and `∂̄f(1)` in the
basis `dz`, `dbar z`; testing the latter coefficient alone detects its vanishing.

These statements connect the real differential and its type decomposition with holomorphy.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter II.
-/

public noncomputable section

open Complex
open scoped ComplexConjugate

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- In one variable the real differential is the sum of its `dz` and `dbar z` terms.
This identity also holds for the totalized derivative, without a differentiability assumption. -/
theorem fderiv_eq_wirtingerDeriv_smul_add {f : ℂ → W} (x v : ℂ) :
    fderiv ℝ f x v =
      v • wirtingerDeriv f x 1 + conj v • conjWirtingerDeriv f x 1 := by
  rw [← wirtingerDeriv_add_conjWirtingerDeriv f x v]
  congr 1
  · simpa only [smul_eq_mul, mul_one] using (wirtingerDeriv f x).map_smul v (1 : ℂ)
  · simpa only [smul_eq_mul, mul_one] using (conjWirtingerDeriv f x).map_smulₛₗ v (1 : ℂ)

/-- For a real-differentiable function of one complex variable, the single equation
`∂̄f(1) = 0` characterizes complex differentiability. -/
theorem differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero {f : ℂ → W} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℂ f x ↔ conjWirtingerDeriv f x 1 = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, and_iff_right hf,
    conjWirtingerDeriv_apply, smul_eq_zero_iff_right (by norm_num : (2 : ℂ)⁻¹ ≠ 0)]
  simp only [smul_eq_mul, mul_one]
  constructor
  · intro h
    simp [h, smul_smul]
  · intro h
    have hi := congrArg (fun w : W ↦ I • w) h
    have he : I • fderiv ℝ f x 1 - fderiv ℝ f x I = 0 := by
      simpa [smul_add, smul_smul, sub_eq_add_neg] using hi
    exact (sub_eq_zero.mp he).symm

end TauCeti
