/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing exponential damping of a half-line integral

Damping an integrand on a half-line `u ≥ a` by `exp (-u (sigma - 1))` leaves the integral of an
integrable function unchanged in the limit `sigma → 1⁺`: the damping factor is bounded on the
half-line uniformly in `sigma ∈ [1, 2]`, so dominated convergence applies.

This is the Abelian step of a Tauberian argument, where a Dirichlet series is tested on a vertical
line `Re s = sigma` inside its half-plane of convergence and the line is pushed to the boundary;
`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` uses it for the simple-pole
term of the Wiener--Ikehara identity.

## Main results

* `TauCeti.tendsto_setIntegral_exp_smul`: the damped integral converges to the undamped one as
  `sigma` decreases to `1`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} {f : ℝ → E}
  {a : ℝ}

/-- As `sigma` decreases to `1`, the one-sided Laplace transform
`∫ u in Ici a, exp (-u (sigma - 1)) • f u` of a function integrable on the half-line `u ≥ a`
converges to its undamped integral. -/
theorem tendsto_setIntegral_exp_smul (hf : IntegrableOn f (Ici a) μ) :
    Tendsto (fun sigma : ℝ ↦ ∫ u in Ici a, Real.exp (-u * (sigma - 1)) • f u ∂μ)
      (𝓝[≥] 1) (𝓝 (∫ u in Ici a, f u ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ Real.exp (max 0 (-a)) * ‖f u‖)
    (.of_forall fun sigma ↦ (Continuous.aestronglyMeasurable (by fun_prop)).smul hf.1) ?_
    (hf.norm.const_mul _) (.of_forall fun u ↦ ?_)
  · filter_upwards [Icc_mem_nhdsGE (by norm_num : (1 : ℝ) < 2)] with sigma ⟨h1, h2⟩
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u (hu : a ≤ u)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    gcongr
    rcases le_total 0 u with h | h <;> nlinarith [le_max_left 0 (-a), le_max_right 0 (-a)]
  · have hexp : Tendsto (fun sigma : ℝ ↦ Real.exp (-u * (sigma - 1))) (𝓝 1) (𝓝 1) :=
      (by fun_prop : Continuous fun sigma : ℝ ↦ Real.exp (-u * (sigma - 1))).tendsto' 1 1 (by simp)
    simpa using (hexp.mono_left nhdsWithin_le_nhds).smul_const (f u)

end TauCeti
