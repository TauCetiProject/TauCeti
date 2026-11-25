/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.Analysis.Calculus.LineDeriv.Basic

/-!
# Weak divergence on the real line

Weak divergence in dimension one is the ordinary weak derivative. A solenoidal field on the
whole real line is almost everywhere constant.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

/-- On the real line, weak divergence is the weak derivative in the direction `1`. -/
theorem hasWeakDivergenceOn_real_iff {μ : Measure ℝ} {Ω : Opens ℝ} {u g : ℝ → ℝ} :
    HasWeakDivergenceOn μ Ω u g ↔ HasWeakLineDerivOn μ Ω u g 1 := by
  rw [hasWeakDivergenceOn_iff, hasWeakLineDerivOn_iff_testFunction,
    iff_true_intro (inferInstance : CompleteSpace ℝ), true_and]
  simp only [gradient_eq_deriv', lineDeriv_one, smul_eq_mul, Real.inner_apply, mul_comm]

/-- A solenoidal field on the whole real line agrees almost everywhere with a constant. -/
theorem IsSolenoidalOn.exists_ae_eq_const {u : ℝ → ℝ} (hu : IsSolenoidalOn volume ⊤ u) :
    ∃ c : ℝ, u =ᵐ[volume] fun _ ↦ c := by
  have hd := hasWeakDivergenceOn_real_iff.mp (isSolenoidalOn_iff_hasWeakDivergenceOn.mp hu)
  simpa using hd.exists_ae_eq_add_intervalIntegral_top 0

end TauCeti
