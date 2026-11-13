/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Matrix.Normed
import TauCeti.Analysis.Calculus.FDeriv.Adjugate
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiation of matrix curves

The trace commutes with differentiation, and the inverse has derivative `-A⁻¹ * A' * A⁻¹`
at an invertible matrix. These rules apply to finite matrix curves over a nontrivially normed
field. Matrices carry the operator norm, and no completeness assumption is needed.
-/

public section

open Filter
open scoped Topology Matrix.Norms.Operator

/-- The derivative of the trace of a matrix curve is the trace of its derivative. -/
theorem HasDerivAt.matrix_trace {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    {f : 𝕜 → Matrix ι ι 𝕜} {f' : Matrix ι ι 𝕜} {t : 𝕜} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s ↦ (f s).trace) f'.trace t := by
  let tr : Matrix ι ι 𝕜 →L[𝕜] 𝕜 :=
    ⟨Matrix.traceLinearMap ι 𝕜 𝕜, continuous_id.matrix_trace⟩
  have htr (A : Matrix ι ι 𝕜) : tr A = A.trace :=
    (congrFun (ContinuousLinearMap.coe_mk' (Matrix.traceLinearMap ι 𝕜 𝕜)
      continuous_id.matrix_trace) A).trans (Matrix.traceLinearMap_apply ι 𝕜 𝕜 A)
  have h := tr.hasFDerivAt.comp_hasDerivAt t hf
  exact (h.congr_deriv (htr f')).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s ↦ (htr (f s)).symm)

/-- The derivative of the inverse of a matrix curve at an invertible matrix is
`-(A⁻¹ * A' * A⁻¹)`. No scalar completeness assumption is needed. -/
theorem HasDerivAt.matrix_inv {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [DecidableEq ι] {A : 𝕜 → Matrix ι ι 𝕜} {A' : Matrix ι ι 𝕜} {a : 𝕜}
    (hA : HasDerivAt A A' a) (hdet : IsUnit (A a).det) :
    HasDerivAt (fun t ↦ (A t)⁻¹) (-((A a)⁻¹ * A' * (A a)⁻¹)) a := by
  have hd := hA.matrix_det hdet
  have hne := hd.continuousAt.eventually_ne hdet.ne_zero
  -- Entrywise adjugate calculus gives differentiability of the inverse without a Banach
  -- algebra assumption. Differentiating A * A⁻¹ = 1 then determines its derivative.
  have hAdj : DifferentiableAt 𝕜 (fun t ↦ (A t).adjugate) a := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact Matrix.differentiableAt_adjugate_apply A a
      (fun k l ↦ (differentiableAt_pi.mp (differentiableAt_pi.mp hA.differentiableAt k) l)) i j
  have hInv : DifferentiableAt 𝕜 (fun t ↦ (A t)⁻¹) a := by
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using!
      (hd.differentiableAt.inv hdet.ne_zero).fun_smul hAdj
  have hmul : (fun t ↦ A t * (A t)⁻¹) =ᶠ[𝓝 a] fun _ ↦ 1 := by
    filter_upwards [hne] with t ht
    exact Matrix.mul_nonsing_inv (A t) ht.isUnit
  have hzero := (hA.fun_mul hInv.hasDerivAt).congr_of_eventuallyEq hmul.symm
  apply hInv.hasDerivAt.congr_deriv
  have hz : A' * (A a)⁻¹ + A a * _root_.deriv (fun t ↦ (A t)⁻¹) a = 0 := by
    simpa using! hzero.unique (hasDerivAt_const a (1 : Matrix ι ι 𝕜))
  have hz' := congrArg (fun M ↦ (A a)⁻¹ * M) hz
  simpa [mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
    eq_neg_iff_add_eq_zero, add_comm] using! hz'
