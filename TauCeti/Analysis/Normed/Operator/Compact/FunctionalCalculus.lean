/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Eigenvector
import TauCeti.Analysis.Normed.Operator.Compact.Spectrum
import TauCeti.Topology.Algebra.GroupWithZero.DifferenceQuotient

/-!
# The functional calculus of a compact self-adjoint operator on eigenvectors

The nonzero spectral values of a compact operator are isolated
(`IsCompactOperator.eventually_mem_spectrum_real_imp_eq`), so the difference quotient at such a
value of a function continuous on the spectrum is again continuous on the spectrum. Hence the
continuous functional calculus of a compact self-adjoint operator `T` on a complex Hilbert space
acts on an eigenvector for a nonzero eigenvalue `μ` as multiplication by `f μ`, for every real
function `f` continuous on the spectrum of `T`. Unlike the finite-dimensional statement
`ContinuousLinearMap.cfc_apply_of_apply_eq_smul`, this needs continuity of `f`.

## Main results

* `IsCompactOperator.cfc_apply_of_apply_eq_smul`: if `T x = μ x` with `μ ≠ 0`, then
  `f(T) x = f(μ) x`.
-/

public section

namespace IsCompactOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Eigenvector action of the functional calculus of a compact self-adjoint operator.** If
`T x = μ x` for a real `μ ≠ 0`, then `f(T) x = f(μ) x` for every real function `f` continuous on
the spectrum of `T`. -/
theorem cfc_apply_of_apply_eq_smul {T : H →L[ℂ] H} (hT : IsCompactOperator T) (f : ℝ → ℝ)
    {x : H} {μ : ℝ} (hμ : μ ≠ 0) (hx : T x = (μ : ℂ) • x)
    (hf : ContinuousOn f (spectrum ℝ T) := by cfc_cont_tac)
    (hT' : IsSelfAdjoint T := by cfc_tac) :
    cfc f T x = (f μ : ℂ) • x := by
  have halg (r : ℝ) : algebraMap ℝ (H →L[ℂ] H) r • x = (r : ℂ) • x := by
    rw [ContinuousLinearMap.smul_def, IsScalarTower.algebraMap_apply ℝ ℂ (H →L[ℂ] H),
      ContinuousLinearMap.algebraMap_apply, Complex.coe_algebraMap]
  rw [← ContinuousLinearMap.smul_def, ← halg] at hx ⊢
  exact TauCeti.cfc_smul_of_smul_eq_algebraMap_smul f hx
    (hf.sub_div_sub_of_eventually_imp_eq (hT.eventually_mem_spectrum_real_imp_eq hμ)) hT'

end IsCompactOperator
