/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Analysis.Bochner.Gaussian.Basic

/-!
# Gaussian, Laplace and inverse multiquadric kernels

On `ℝᵈ`, written `EuclideanSpace ℝ (Fin d)`, this file defines three translation-invariant
kernels of kernel methods in statistics and machine learning:

* the Gaussian kernel `gaussianKernel σ x y = exp (-‖x - y‖² / (2σ²))`;
* the Laplace kernel `laplaceKernel σ x y = exp (-‖x - y‖ / σ)`;
* the inverse multiquadric kernel `imqKernel c β x y = (c² + ‖x - y‖²) ^ (-β)`.

In the parameter ranges of the literature, `σ ≠ 0` for the Gaussian kernel, `σ > 0` for the
Laplace kernel, and `c ≠ 0` and `β > 0` for the inverse multiquadric kernel, all three are scale
mixtures `∫ exp (-t ‖x - y‖²) dρ(t)` of Gaussians, which is how one proves that they are positive
semidefinite and characteristic (Wendland, Theorems 7.13–7.15). This file does not prove these
facts in general. It proves the positive semidefiniteness of the Gaussian kernel, for every `σ`,
as the real part of the complex Gaussian kernel of `TauCeti.posSemidef_cexp_neg_mul_sq_norm`, and
records the elementary properties of all three kernels.

The definitions accept every parameter value, and outside these ranges they are other kernels.
For `σ = 0`, `x / 0 = 0` makes the Gaussian and Laplace kernels the constant kernel `1`. For
`β = 0` the inverse multiquadric kernel is the constant kernel `1`. For `d ≥ 1` the following are
not positive semidefinite: the Laplace kernel `exp (‖x - y‖ / |σ|)` for `σ < 0`; the multiquadric
kernel `(c² + ‖x - y‖²) ^ |β|`, which is `imqKernel c β` for `β < 0`; and `imqKernel 0 β` for
`β > 0`, which vanishes on the diagonal.

## Main definitions

* `TauCeti.gaussianKernel`, `TauCeti.laplaceKernel`, `TauCeti.imqKernel`: the three kernels.

## Main results

* `TauCeti.posSemidef_gaussianKernel`: the Gaussian kernel is positive semidefinite.
* `TauCeti.gaussianKernel_self`, `TauCeti.laplaceKernel_self`, `TauCeti.imqKernel_self`: the
  values on the diagonal.
* `TauCeti.gaussianKernel_comm`, `TauCeti.laplaceKernel_comm`, `TauCeti.imqKernel_comm`: the
  kernels are symmetric.
* `TauCeti.gaussianKernel_pos`, `TauCeti.gaussianKernel_le_one`, `TauCeti.laplaceKernel_pos`,
  `TauCeti.laplaceKernel_le_one`, `TauCeti.imqKernel_pos`: bounds on the values.
* `TauCeti.continuous_gaussianKernel`, `TauCeti.continuous_laplaceKernel`,
  `TauCeti.continuous_imqKernel`: the kernels are jointly continuous.

## References

* H. Wendland, *Scattered Data Approximation*, Cambridge University Press (2005), Theorem 6.10,
  p. 74, and Theorems 7.13–7.15, pp. 93–95.
-/

public section

namespace TauCeti

variable {d : ℕ}

/-! ### The Gaussian kernel -/

/-- The Gaussian kernel `exp (-‖x - y‖² / (2σ²))` on `ℝᵈ` with bandwidth `σ`. -/
noncomputable def gaussianKernel (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))

/-- The defining formula of `gaussianKernel`. -/
theorem gaussianKernel_def (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    gaussianKernel σ x y = Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)) := (rfl)

/-- The Gaussian kernel is `exp (-t ‖x - y‖²)` at the scale `t = (2σ²)⁻¹`. -/
theorem gaussianKernel_eq_exp_neg_mul (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    gaussianKernel σ x y = Real.exp (-((2 * σ ^ 2)⁻¹ * ‖x - y‖ ^ 2)) := by
  rw [gaussianKernel_def, neg_div, div_eq_inv_mul]

/-- The Gaussian kernel is `1` on the diagonal. -/
@[simp]
theorem gaussianKernel_self (σ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : gaussianKernel σ x x = 1 := by
  simp [gaussianKernel_def]

/-- The Gaussian kernel is symmetric. -/
theorem gaussianKernel_comm (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    gaussianKernel σ x y = gaussianKernel σ y x := by
  rw [gaussianKernel_def, gaussianKernel_def, norm_sub_rev]

/-- The Gaussian kernel is positive. -/
theorem gaussianKernel_pos (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : 0 < gaussianKernel σ x y :=
  Real.exp_pos _

/-- The Gaussian kernel is at most `1`. -/
theorem gaussianKernel_le_one (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    gaussianKernel σ x y ≤ 1 := by
  rw [gaussianKernel_eq_exp_neg_mul, Real.exp_le_one_iff, neg_nonpos]
  positivity

/-- The Gaussian kernel is jointly continuous. -/
theorem continuous_gaussianKernel (σ : ℝ) :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      gaussianKernel σ p.1 p.2 := by
  simp only [gaussianKernel_def]
  fun_prop

/-- **The Gaussian kernel is positive semidefinite** (Wendland, Theorem 6.10). For `σ = 0` it is
the constant kernel `1`. -/
theorem posSemidef_gaussianKernel (σ : ℝ) : Matrix.PosSemidef (gaussianKernel (d := d) σ) := by
  have h := posSemidef_exp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin d))
    (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 * σ ^ 2))
  refine (congrArg Matrix.PosSemidef ?_).mp h
  ext x y
  exact (gaussianKernel_eq_exp_neg_mul σ x y).symm

/-! ### The Laplace kernel -/

/-- The Laplace kernel `exp (-‖x - y‖ / σ)` on `ℝᵈ` with bandwidth `σ`. It is the Laplace kernel of
the literature for `σ > 0`; for `σ = 0` it is the constant `1`. -/
noncomputable def laplaceKernel (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (-‖x - y‖ / σ)

/-- The defining formula of `laplaceKernel`. -/
theorem laplaceKernel_def (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    laplaceKernel σ x y = Real.exp (-‖x - y‖ / σ) := (rfl)

/-- The Laplace kernel is `1` on the diagonal. -/
@[simp]
theorem laplaceKernel_self (σ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : laplaceKernel σ x x = 1 := by
  simp [laplaceKernel_def]

/-- The Laplace kernel is symmetric. -/
theorem laplaceKernel_comm (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    laplaceKernel σ x y = laplaceKernel σ y x := by
  rw [laplaceKernel_def, laplaceKernel_def, norm_sub_rev]

/-- The Laplace kernel is positive. -/
theorem laplaceKernel_pos (σ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : 0 < laplaceKernel σ x y :=
  Real.exp_pos _

/-- For a nonnegative bandwidth, the Laplace kernel is at most `1`. -/
theorem laplaceKernel_le_one {σ : ℝ} (hσ : 0 ≤ σ) (x y : EuclideanSpace ℝ (Fin d)) :
    laplaceKernel σ x y ≤ 1 := by
  rw [laplaceKernel_def, Real.exp_le_one_iff, neg_div, neg_nonpos]
  positivity

/-- The Laplace kernel is jointly continuous. -/
theorem continuous_laplaceKernel (σ : ℝ) :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      laplaceKernel σ p.1 p.2 := by
  simp only [laplaceKernel_def]
  fun_prop

/-! ### The inverse multiquadric kernel -/

/-- The inverse multiquadric kernel `(c² + ‖x - y‖²) ^ (-β)` on `ℝᵈ`. It is the inverse
multiquadric kernel of the literature for `c ≠ 0` and `β > 0`; for `β < 0` it is the multiquadric
kernel, and for `β = 0` the constant `1`. -/
noncomputable def imqKernel (c β : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (c ^ 2 + ‖x - y‖ ^ 2) ^ (-β)

/-- The defining formula of `imqKernel`. -/
theorem imqKernel_def (c β : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    imqKernel c β x y = (c ^ 2 + ‖x - y‖ ^ 2) ^ (-β) := (rfl)

/-- The inverse multiquadric kernel is `(c²) ^ (-β)` on the diagonal. -/
@[simp]
theorem imqKernel_self (c β : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    imqKernel c β x x = (c ^ 2) ^ (-β) := by
  simp [imqKernel_def]

/-- The inverse multiquadric kernel is symmetric. -/
theorem imqKernel_comm (c β : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    imqKernel c β x y = imqKernel c β y x := by
  rw [imqKernel_def, imqKernel_def, norm_sub_rev]

/-- For `c ≠ 0`, the inverse multiquadric kernel is positive. -/
theorem imqKernel_pos {c : ℝ} (hc : c ≠ 0) (β : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    0 < imqKernel c β x y :=
  Real.rpow_pos_of_pos (by positivity) _

/-- For `c ≠ 0`, the inverse multiquadric kernel is jointly continuous. -/
theorem continuous_imqKernel {c : ℝ} (hc : c ≠ 0) (β : ℝ) :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
      imqKernel c β p.1 p.2 := by
  simp only [imqKernel_def]
  exact Continuous.rpow_const (by fun_prop) fun _ ↦ Or.inl (by positivity)

end TauCeti
