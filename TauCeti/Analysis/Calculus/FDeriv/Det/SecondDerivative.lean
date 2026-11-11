/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Second derivative of determinants and volume densities

At the identity, the second derivative of a determinant along a `C²` matrix curve is
`tr A'' + (tr A')² - tr ((A')²)`. Taking the positive square root gives the second derivative
of a volume density in an orthonormal frame. This is the algebraic input to the second
variation of the volume of an immersion.
-/

public noncomputable section

open Filter
open scoped Topology ContDiff Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The second derivative of the determinant along a `C²` matrix curve through the identity. -/
theorem hasDerivAt_deriv_det_of_eq_one {A : ℝ → Matrix ι ι ℝ} {a : ℝ}
    (hA : ContDiffAt ℝ 2 A a) (hA_one : A a = 1) :
    HasDerivAt (deriv (fun t ↦ (A t).det))
      ((deriv (deriv A) a).trace + (deriv A a).trace ^ 2 -
        (deriv A a * deriv A a).trace) a := by
  have hdA := (hA.differentiableAt (by norm_num)).hasDerivAt
  have hdA' := (hA.derivWithin (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
    (by norm_num) |>.hasDerivAt
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ)
    (1 : (Matrix ι ι ℝ)ˣ)).comp_hasDerivAt_of_eq a hdA (by simpa using hA_one.symm)
  have hi' : HasDerivAt (fun t ↦ (A t)⁻¹) (-deriv A a) a := by
    simpa [nonsing_inv_eq_ringInverse, ContinuousLinearMap.mulLeftRight_apply] using! hi
  let tr := (traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have htr := tr.hasFDerivAt.comp_hasDerivAt a (hi'.mul hdA')
  have hd : HasDerivAt (fun t ↦ (A t).det) (deriv A a).trace a := by
    have h := (hasFDerivAt_det_one (n := ι) (𝕜 := ℝ)).comp_hasDerivAt_of_eq a hdA hA_one.symm
    simpa only [ContinuousLinearMap.coe_mk', traceLinearMap_apply] using! h
  change HasDerivAt (fun t ↦ ((A t)⁻¹ * deriv A t).trace)
    (-deriv A a * deriv A a + (A a)⁻¹ * deriv (deriv A) a).trace a at htr
  have hprod := hd.mul htr
  have heq : deriv (fun t ↦ (A t).det) =ᶠ[𝓝 a]
      fun t ↦ (A t).det * ((A t)⁻¹ * deriv A t).trace := by
    have hnear := hA.eventually (by norm_num)
    have hne : ∀ᶠ t in 𝓝 a, (A t).det ≠ 0 :=
      ((contDiff_det (r := 0)).continuous.continuousAt.comp hA.continuousAt).eventually_ne
        (by simp [hA_one])
    filter_upwards [hnear, hne] with t ht hdet
    exact ((hasFDerivAt_det hdet.isUnit).comp_hasDerivAt t
      (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hprod' : HasDerivAt
      (fun t ↦ (A t).det * ((A t)⁻¹ * deriv A t).trace)
      ((deriv (deriv A) a).trace + (deriv A a).trace ^ 2 -
        (deriv A a * deriv A a).trace) a := by
    convert hprod using 1
    simp only [hA_one, inv_one, one_mul, det_one, trace_add, neg_mul, trace_neg]
    ring
  exact hprod'.congr_of_eventuallyEq heq

/-- The second derivative of the square root of a determinant through the identity. -/
theorem hasDerivAt_deriv_sqrt_det_of_eq_one {A : ℝ → Matrix ι ι ℝ} {a : ℝ}
    (hA : ContDiffAt ℝ 2 A a) (hA_one : A a = 1) :
    HasDerivAt (deriv (fun t ↦ Real.sqrt (A t).det))
      ((1 / 2) * (deriv (deriv A) a).trace -
        (1 / 2) * (deriv A a * deriv A a).trace + (1 / 4) * (deriv A a).trace ^ 2) a := by
  have hd : HasDerivAt (fun t ↦ (A t).det) (deriv A a).trace a := by
    have h := (hasFDerivAt_det_one (n := ι) (𝕜 := ℝ)).comp_hasDerivAt_of_eq a
      (hA.differentiableAt (by norm_num)).hasDerivAt hA_one.symm
    simpa only [ContinuousLinearMap.coe_mk', traceLinearMap_apply] using! h
  have hs := hd.sqrt (by simp [hA_one])
  have hdd := hasDerivAt_deriv_det_of_eq_one hA hA_one
  have hq := hdd.div (hs.const_mul 2) (by simp [hA_one])
  have heq : deriv (fun t ↦ Real.sqrt (A t).det) =ᶠ[𝓝 a]
      fun t ↦ deriv (fun s ↦ (A s).det) t / (2 * Real.sqrt (A t).det) := by
    have hnear := hA.eventually (by norm_num)
    have hne : ∀ᶠ t in 𝓝 a, (A t).det ≠ 0 :=
      ((contDiff_det (r := 0)).continuous.continuousAt.comp hA.continuousAt).eventually_ne
        (by simp [hA_one])
    filter_upwards [hnear, hne] with t ht hdet
    exact (((contDiff_det.contDiffAt.comp t ht).differentiableAt
      (by norm_num)).hasDerivAt.sqrt hdet).deriv
  have hq' : HasDerivAt
      (fun t ↦ deriv (fun s ↦ (A s).det) t / (2 * Real.sqrt (A t).det))
      ((1 / 2) * (deriv (deriv A) a).trace -
        (1 / 2) * (deriv A a * deriv A a).trace + (1 / 4) * (deriv A a).trace ^ 2) a := by
    convert hq using 1
    rw [hd.deriv]
    simp only [hA_one, det_one, Real.sqrt_one]
    ring
  exact hq'.congr_of_eventuallyEq heq

end Matrix
