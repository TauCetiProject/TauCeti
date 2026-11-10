/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.Calculus.FDeriv.Det
import TauCeti.Analysis.Matrix.PosDef

/-!
# The log-determinant along a positive definite segment

`Matrix.log_det_sub_eq_integral_trace_of_posDef` integrates Jacobi's formula for the
log-determinant along the segment joining two real positive definite matrices. For Hessians at
two points, the integral supplies the coefficients in the Monge–Ampère difference equation.
This is the matrix identity in Gilbarg–Trudinger (2001), (17.56), as formalized in
[KLS](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix/LogDet/Segment.lean).
-/

public section

open Set
open scoped Matrix.Norms.Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The difference of log-determinants of positive definite matrices is the integral of the
trace of the inverse along the segment multiplied by its displacement. -/
theorem log_det_sub_eq_integral_trace_of_posDef {A B : Matrix ι ι ℝ} (hA : A.PosDef)
    (hB : B.PosDef) :
    Real.log B.det - Real.log A.det =
      ∫ t in (0 : ℝ)..1, trace ((A + t • (B - A))⁻¹ * (B - A)) := by
  have hdet (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A + t • (B - A)).det ≠ 0 := by
    have hseg : A + t • (B - A) = (1 - t) • A + t • B := by module
    rw [hseg]
    exact (TauCeti.convex_setOfPred_posDef hA hB (sub_nonneg.mpr ht.2) ht.1
      (sub_add_cancel 1 t)).det_pos.ne'
  have hpath (t : ℝ) : HasDerivAt (fun s : ℝ => A + s • (B - A)) (B - A) t :=
    HasDerivAt.const_add A
      (by simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const (B - A))
  have hlog (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => Real.log (A + s • (B - A)).det)
        (trace ((A + t • (B - A))⁻¹ * (B - A))) t := by
    have hd := hdet t ht
    have h := (differentiable_det (A + t • (B - A))).hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hJacobi := h.congr_deriv (fderiv_det_apply (isUnit_iff_ne_zero.mpr hd) (B - A))
    simpa only [Function.comp_apply, mul_div_cancel_left₀ _ hd] using hJacobi.log hd
  have hc : ContinuousOn (fun t : ℝ => trace ((A + t • (B - A))⁻¹ * (B - A))) (Icc 0 1) := by
    intro t ht
    have hinv : ContinuousAt (fun s : ℝ => (A + s • (B - A))⁻¹) t :=
      (continuousAt_matrix_inv (A + t • (B - A))
        (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hdet t ht))).comp
          (f := fun s : ℝ => A + s • (B - A)) (hpath t).continuousAt
    exact (continuous_id.matrix_trace.continuousAt.comp
      (hinv.mul continuousAt_const)).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hlog t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (hc.intervalIntegrable_of_Icc zero_le_one)
  simpa only [one_smul, zero_smul, add_zero, add_sub_cancel] using h.symm

end Matrix
