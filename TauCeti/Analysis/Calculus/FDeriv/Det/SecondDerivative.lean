/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.Deriv.Matrix
import TauCeti.Analysis.Calculus.FDeriv.Adjugate
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Second derivative of the determinant and its square root

We compute second derivatives along matrix curves at an invertible matrix, using only
first derivatives near the parameter and a second derivative at that parameter. The determinant
formula holds over any nontrivially normed field, without completeness; the square-root formula
is real and requires positive determinant at the parameter.

At the identity, a `C²` matrix curve satisfies
`(det A)'' = tr A'' + (tr A')² - tr ((A')²)` and
`(√(det A))'' = (1 / 2) * tr A'' - (1 / 2) * tr ((A')²) + (1 / 4) * (tr A')²`.
Applied to a metric Gram matrix curve in an orthonormal frame at the base parameter,
these formulas supply the matrix-calculus input to the second variation of volume.
-/

public noncomputable section

open Filter
open scoped Topology ContDiff Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The second derivative of the determinant at an invertible matrix, from a germ of
matrix velocities and its derivative at the parameter. No scalar completeness is needed. -/
theorem hasDerivAt_deriv_det {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {A A' : 𝕜 → Matrix ι ι 𝕜} {A'' : Matrix ι ι 𝕜} {a : 𝕜}
    (hA : ∀ᶠ t in 𝓝 a, HasDerivAt A (A' t) t) (hA' : HasDerivAt A' A'' a)
    (hdet : IsUnit (A a).det) :
    HasDerivAt (deriv (fun t ↦ (A t).det))
      ((A a).det * (((A a)⁻¹ * A'').trace + ((A a)⁻¹ * A' a).trace ^ 2 -
        ((A a)⁻¹ * A' a * ((A a)⁻¹ * A' a)).trace)) a := by
  have hdA := hA.self_of_nhds
  have hd := hdA.matrix_det hdet
  have hne := hd.continuousAt.eventually_ne hdet.ne_zero
  -- Entrywise adjugate calculus gives differentiability of the inverse without a Banach
  -- algebra assumption. Differentiating A * A⁻¹ = 1 then determines its derivative.
  have hAdj : DifferentiableAt 𝕜 (fun t ↦ (A t).adjugate) a := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact differentiableAt_adjugate_apply A a
      (fun k l ↦ (differentiableAt_pi.mp (differentiableAt_pi.mp hdA.differentiableAt k) l)) i j
  have hInv : DifferentiableAt 𝕜 (fun t ↦ (A t)⁻¹) a := by
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using!
      (hd.differentiableAt.inv hdet.ne_zero).fun_smul hAdj
  have hmul : (fun t ↦ A t * (A t)⁻¹) =ᶠ[𝓝 a] fun _ ↦ 1 := by
    filter_upwards [hne] with t ht
    exact mul_nonsing_inv (A t) ht.isUnit
  have hzero := (hdA.fun_mul hInv.hasDerivAt).congr_of_eventuallyEq hmul.symm
  have hInv' : HasDerivAt (fun t ↦ (A t)⁻¹)
      (-((A a)⁻¹ * A' a * (A a)⁻¹)) a := by
    apply hInv.hasDerivAt.congr_deriv
    have hz : A' a * (A a)⁻¹ + A a * deriv (fun t ↦ (A t)⁻¹) a = 0 := by
      simpa using! hzero.unique (hasDerivAt_const a (1 : Matrix ι ι 𝕜))
    have hz' := congrArg (fun M ↦ (A a)⁻¹ * M) hz
    simpa [mul_add, ← Matrix.mul_assoc, nonsing_inv_mul _ hdet,
      eq_neg_iff_add_eq_zero, add_comm] using! hz'
  -- Differentiate Jacobi's first-derivative formula and identify it with deriv near a.
  have htr := (hInv'.fun_mul hA').matrix_trace
  have heq : deriv (fun t ↦ (A t).det) =ᶠ[𝓝 a]
      fun t ↦ (A t).det * ((A t)⁻¹ * A' t).trace := by
    filter_upwards [hA, hne] with t ht hdt
    exact (ht.matrix_det hdt.isUnit).deriv
  convert (hd.mul htr).congr_of_eventuallyEq heq using 1
  simp only [neg_mul, trace_add, trace_neg, Matrix.mul_assoc]
  ring

/-- The second derivative of the determinant along a `C²` matrix curve through the identity. -/
theorem hasDerivAt_deriv_det_of_eq_one {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {A : 𝕜 → Matrix ι ι 𝕜} {a : 𝕜}
    (hA : ContDiffAt 𝕜 2 A a) (hA_one : A a = 1) :
    HasDerivAt (deriv (fun t ↦ (A t).det))
      ((deriv (deriv A) a).trace + (deriv A a).trace ^ 2 -
        (deriv A a * deriv A a).trace) a := by
  simpa [hA_one] using! hasDerivAt_deriv_det
    ((hA.eventually_differentiableAt one_le_two).mono fun _ ht ↦ ht.hasDerivAt)
    hA.differentiableAt_deriv_two.hasDerivAt (by simp [hA_one])

/-- The second derivative of the square root of the determinant at a positive determinant,
from a germ of matrix velocities and its derivative at the parameter. -/
theorem hasDerivAt_deriv_sqrt_det {A A' : ℝ → Matrix ι ι ℝ} {A'' : Matrix ι ι ℝ} {a : ℝ}
    (hA : ∀ᶠ t in 𝓝 a, HasDerivAt A (A' t) t) (hA' : HasDerivAt A' A'' a)
    (hdet : 0 < (A a).det) :
    HasDerivAt (deriv (fun t ↦ Real.sqrt (A t).det))
      (Real.sqrt (A a).det * ((1 / 2) * ((A a)⁻¹ * A'').trace -
        (1 / 2) * ((A a)⁻¹ * A' a * ((A a)⁻¹ * A' a)).trace +
        (1 / 4) * ((A a)⁻¹ * A' a).trace ^ 2)) a := by
  have hd := hA.self_of_nhds.matrix_det hdet.ne'.isUnit
  have hs := hd.sqrt hdet.ne'
  have hdd := hasDerivAt_deriv_det hA hA' hdet.ne'.isUnit
  have hq := hdd.div (hs.const_mul 2) (mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hdet).ne')
  have heq : deriv (fun t ↦ Real.sqrt (A t).det) =ᶠ[𝓝 a]
      fun t ↦ deriv (fun s ↦ (A s).det) t / (2 * Real.sqrt (A t).det) := by
    filter_upwards [hA, hd.continuousAt.eventually_ne hdet.ne'] with t ht hdt
    exact deriv_sqrt ((differentiable_det (A t)).fun_comp' t ht.differentiableAt) hdt
  convert hq.congr_of_eventuallyEq heq using 1
  rw [hd.deriv]
  have hsne := (Real.sqrt_pos.2 hdet).ne'
  have hsq := Real.sq_sqrt hdet.le
  rw [← hsq, Real.sqrt_sq (Real.sqrt_nonneg _)]
  field_simp
  ring

/-- The second derivative of the square root of a determinant through the identity. -/
theorem hasDerivAt_deriv_sqrt_det_of_eq_one {A : ℝ → Matrix ι ι ℝ} {a : ℝ}
    (hA : ContDiffAt ℝ 2 A a) (hA_one : A a = 1) :
    HasDerivAt (deriv (fun t ↦ Real.sqrt (A t).det))
      ((1 / 2) * (deriv (deriv A) a).trace -
        (1 / 2) * (deriv A a * deriv A a).trace + (1 / 4) * (deriv A a).trace ^ 2) a := by
  simpa [hA_one] using! hasDerivAt_deriv_sqrt_det
    ((hA.eventually_differentiableAt one_le_two).mono fun _ ht ↦ ht.hasDerivAt)
    hA.differentiableAt_deriv_two.hasDerivAt (by simp [hA_one])

end Matrix
