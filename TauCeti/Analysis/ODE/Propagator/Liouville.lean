/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.LinearAlgebra.Trace.Basic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Liouville's formula for the propagator

For a finite-dimensional space `E` over `𝕜` and a coefficient `P : ℝ → E →L[𝕜] E` integrable on
`[a, b]`, the determinant of the propagator `N_P(t, s)` is
`det N_P(t, s) = exp (∫ u in s..t, trace (P u))` for `s, t ∈ [a, b]`
(`TauCeti.det_propagator`). For `E = Fin n → 𝕜` this is the matrix statement
`det N = exp (∫ tr P)` for the matrices in the standard basis (`TauCeti.det_toMatrix'_propagator`);
the formula is basis-free, so it holds equally on `EuclideanSpace 𝕜 (Fin n)`. No finiteness is
assumed: over an infinite-dimensional space Mathlib's conventions `det = 1` and `trace = 0` make
both sides `1`.

The proof differentiates `t ↦ det N_P(t, s)`. At an invertible `A` with inverse `B`, the
derivative of the determinant is `H ↦ det A * trace (B H)`
(`ContinuousLinearMap.hasFDerivAt_det_of_comp_eq_one`, Jacobi's formula). Along the propagator,
at almost every `t`, `H = P(t) N` with `N = N_P(t, s)` and `B = N⁻¹`, so the derivative is
`det N * trace P(t)`. The determinant of the absolutely continuous curve `N_P(·, s)` is absolutely
continuous, so it is the absolutely continuous solution of the scalar equation
`y' = trace P(t) y`, `y(s) = 1`, which is `exp (∫ trace P)` by uniqueness in the linear
Carathéodory theorem.

## Main results

* `TauCeti.ae_hasDerivAt_det_propagator_left`: `t ↦ det N_P(t, s)` has derivative
  `trace P(t) * det N_P(t, s)` at almost every `t`.
* `TauCeti.det_propagator`, `TauCeti.det_toMatrix'_propagator`: Liouville's formula, basis-free
  and for matrices.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

/-- **The derivative of the determinant of the propagator.** `t ↦ det N_P(t, s)` has derivative
`trace P(t) * det N_P(t, s)` at almost every `t ∈ (a, b)`. -/
theorem ae_hasDerivAt_det_propagator_left (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt (fun r ↦ LinearMap.det (propagator P r s : E →ₗ[𝕜] E))
      (LinearMap.trace 𝕜 E (P t) * LinearMap.det (propagator P t s : E →ₗ[𝕜] E)) t := by
  by_cases hE : FiniteDimensional 𝕜 E
  swap
  · refine Filter.Eventually.of_forall fun t _ ↦ ?_
    simpa [LinearMap.det_eq_one_of_not_module_finite hE,
      LinearMap.trace_eq_zero_of_not_finite hE] using hasDerivAt_const t (1 : 𝕜)
  have := FiniteDimensional.completeSpace 𝕜 E
  filter_upwards [ae_hasDerivAt_propagator_left hP hs] with t hd ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hJ := ContinuousLinearMap.hasFDerivAt_det_of_comp_eq_one
    (propagator_comp_propagator_swap hP ht' hs)
  refine ((hJ.restrictScalars ℝ).comp_hasDerivAt (f := fun r ↦ propagator P r s) t
    (hd ht)).congr_deriv ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  -- `trace (N(s, t) ∘ P(t) ∘ N(t, s)) = trace P(t)`, since `N(t, s) ∘ N(s, t) = 1`.
  rw [ContinuousLinearMap.traceCLM_comp_comp_of_comp_eq_id
    ((propagator_comp_propagator_swap hP ht' hs).trans ContinuousLinearMap.one_def),
    traceCLM_apply]

/-- **Liouville's formula.** For a coefficient `P` integrable on `[a, b]` and `s, t ∈ [a, b]`,
`det N_P(t, s) = exp (∫ u in s..t, trace (P u))`. -/
theorem det_propagator (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    LinearMap.det (propagator P t s : E →ₗ[𝕜] E) =
      NormedSpace.exp (∫ u in s..t, LinearMap.trace 𝕜 E (P u)) := by
  by_cases hE : FiniteDimensional 𝕜 E
  swap
  · simp [LinearMap.det_eq_one_of_not_module_finite hE, LinearMap.trace_eq_zero_of_not_finite hE]
  have := FiniteDimensional.completeSpace 𝕜 E
  have hab : a ≤ b := hs.1.trans hs.2
  have hs' : s ∈ uIcc a b := by rwa [uIcc_of_le hab]
  set g : ℝ → 𝕜 := fun u ↦ LinearMap.trace 𝕜 E (P u)
  have hg : IntegrableOn g (Icc a b) := by
    have h := (traceCLM 𝕜 E).integrable_comp hP
    simp only [traceCLM_apply] at h
    exact h
  have hgi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hg
  -- The scalar equation `y' = g y` as a real-linear Carathéodory equation on `𝕜`.
  let M : ℝ → 𝕜 →L[ℝ] 𝕜 := fun u ↦ ContinuousLinearMap.mul ℝ 𝕜 (g u)
  have hM : IntegrableOn M (Icc a b) := (ContinuousLinearMap.mul ℝ 𝕜).integrable_comp hg
  set y : ℝ → 𝕜 := fun r ↦ LinearMap.det (propagator P r s : E →ₗ[𝕜] E)
  set w : ℝ → 𝕜 := fun r ↦ NormedSpace.exp (∫ u in s..r, g u)
  have hexp : ∀ x : 𝕜, ContDiffAt ℝ 1 NormedSpace.exp x := fun x ↦
    (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hyac : AbsolutelyContinuousOnInterval y a b :=
    (absolutelyContinuousOnInterval_propagator_left hP hs).comp_of_contDiffAt fun _ _ ↦
      (ContinuousLinearMap.contDiff_det (𝕜 := 𝕜) (E := E)).contDiffAt.restrict_scalars ℝ
  have hwac : AbsolutelyContinuousOnInterval w a b :=
    (hgi.absolutelyContinuousOnInterval_intervalIntegral' hs').comp_of_contDiffAt
      fun x _ ↦ hexp x
  have hy := forall_mem_Icc_eq_picard_of_absolutelyContinuousOnInterval (x₀ := 1) hs hM
    integrableOn_zero hyac (by simp [y, propagator_self]) (by
      filter_upwards [ae_hasDerivAt_det_propagator_left hP hs] with r hr hr'
      simpa [M, g] using hr hr')
  have hw := forall_mem_Icc_eq_picard_of_absolutelyContinuousOnInterval (x₀ := 1) hs hM
    integrableOn_zero hwac (by simp [w]) (by
      filter_upwards [hgi.ae_hasDerivAt_integral] with r hr hr'
      have hd := ((hasFDerivAt_exp (𝕂 := ℝ)).comp_hasDerivAt r
        (hr (by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self hr') s hs'))
      convert hd using 1
      · simp only [w, Function.comp_def]
      · simp [M, w, mul_comm])
  have hyc : ContinuousOn y (Icc a b) := by simpa [uIcc_of_le hab] using hyac.continuousOn
  have hwc : ContinuousOn w (Icc a b) := by simpa [uIcc_of_le hab] using hwac.continuousOn
  exact eqOn_of_forall_mem_Icc_eq_picard hs hM integrableOn_zero hyc hwc hy hw ht

/-- **Liouville's formula for matrices.** For `E = Fin n → 𝕜`, the matrix of `N_P(t, s)` in the
standard basis has determinant `exp (∫ u in s..t, trace (matrix of P u))`. -/
theorem det_toMatrix'_propagator {n : ℕ} {P : ℝ → (Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)}
    (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (LinearMap.toMatrix' (propagator P t s : (Fin n → 𝕜) →ₗ[𝕜] Fin n → 𝕜)).det =
      NormedSpace.exp (∫ u in s..t,
        (LinearMap.toMatrix' (P u : (Fin n → 𝕜) →ₗ[𝕜] Fin n → 𝕜)).trace) := by
  rw [LinearMap.det_toMatrix', det_propagator hP hs ht]
  simp only [LinearMap.trace_eq_matrix_trace 𝕜 (Pi.basisFun 𝕜 (Fin n)),
    LinearMap.toMatrix_eq_toMatrix']

end TauCeti
