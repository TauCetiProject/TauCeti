/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Weak derivatives and tempered distributions

For an `Lᵖ` function and an `L^q` candidate derivative, with `1 ≤ p, q ≤ ∞`, the weak
directional derivative identity on the whole space is equivalent to equality of their tempered
distributions after differentiation. The
weak derivative is tested against real compactly supported functions; the tempered derivative
is tested against complex Schwartz functions. Both notions therefore give the same derivative,
without a smoothness or compact-support assumption on the `Lᵖ` functions.

This is the derivative bridge between domain Sobolev spaces and the Fourier description of
whole-space Sobolev spaces. The measure may be any locally finite measure of temperate growth;
the forward implication only requires temperate growth.

## References

* L. C. Evans, *Partial Differential Equations*, Section 5.2 (weak derivatives).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.

The formalization uses Mathlib's `MeasureTheory.Lp.toTemperedDistribution` and the real-test
extensionality theorem `TauCeti.temperedDistribution_ext_real`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal SchwartzMap LineDeriv ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.HasTemperateGrowth] {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Differentiating an `Lᵖ` function as a tempered distribution gives its weak directional
derivative whenever that derivative is represented by an `L^q` function, `q ≥ 1`. -/
theorem HasWeakLineDerivOn.lineDerivOp_toTemperedDistribution_eq
    {u : Lp F p μ} {u' : Lp F q μ} {v : E} (h : HasWeakLineDerivOn μ ⊤ u u' v) :
    ∂_{v} (Lp.toTemperedDistribution u) = Lp.toTemperedDistribution u' := by
  apply temperedDistribution_ext_real
  intro φ hφ
  have hweak := (hasWeakLineDerivOn_iff h.locallyIntegrableOn
    h.locallyIntegrableOn_deriv).1 h φ (φ.smooth ⊤) hφ (by simp)
  have hderiv : ∀ x, ∂_{v} (φ.postcompCLM Complex.ofRealCLM) x =
      Complex.ofReal (lineDeriv ℝ (φ : E → ℝ) x v) := by
    intro x
    simp only [lineDerivOp_postcompCLM, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply, SchwartzMap.lineDerivOp_apply]
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, hderiv, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
    neg_smul, integral_neg, Complex.coe_smul]
  exact neg_eq_iff_eq_neg.mpr hweak

variable [IsLocallyFiniteMeasure μ]

omit [FiniteDimensional ℝ E] in
/-- If the tempered derivative of an `Lᵖ` function is represented by another `Lᵖ` function,
possibly with a different exponent, then the latter is its weak directional derivative on the
whole space. -/
theorem hasWeakLineDerivOn_of_lineDerivOp_toTemperedDistribution_eq
    {u : Lp F p μ} {u' : Lp F q μ} {v : E}
    (h : ∂_{v} (Lp.toTemperedDistribution u) = Lp.toTemperedDistribution u') :
    HasWeakLineDerivOn μ ⊤ u u' v := by
  have hu := (Lp.memLp u).locallyIntegrable Fact.out
  have hu' := (Lp.memLp u').locallyIntegrable Fact.out
  rw [hasWeakLineDerivOn_iff (hu.locallyIntegrableOn _) (hu'.locallyIntegrableOn _)]
  intro φ hφ hφc _
  let ψ : 𝓢(E, ℝ) := hφc.toSchwartzMap hφ
  have hderiv : ∀ x, ∂_{v} (ψ.postcompCLM Complex.ofRealCLM) x =
      Complex.ofReal (lineDeriv ℝ φ x v) := by
    intro x
    simp only [lineDerivOp_postcompCLM, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply, SchwartzMap.lineDerivOp_apply]
    -- `toSchwartzMap` bundles exactly `φ`, with no change to its values.
    rfl
  have heq := congrArg (fun T : 𝓢'(E, F) => T (ψ.postcompCLM Complex.ofRealCLM)) h
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, hderiv, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
    neg_smul, integral_neg, Complex.coe_smul] at heq
  exact neg_eq_iff_eq_neg.mp heq

/-- For an `Lᵖ` function and an `L^q` candidate derivative, `1 ≤ p, q ≤ ∞`, weak differentiation
on the whole space is exactly
differentiation of the associated tempered distributions. -/
theorem hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_eq
    (u : Lp F p μ) (u' : Lp F q μ) (v : E) :
    HasWeakLineDerivOn μ ⊤ u u' v ↔
      ∂_{v} (Lp.toTemperedDistribution u) = Lp.toTemperedDistribution u' :=
  ⟨HasWeakLineDerivOn.lineDerivOp_toTemperedDistribution_eq,
    hasWeakLineDerivOn_of_lineDerivOp_toTemperedDistribution_eq⟩

/-- A real-valued `Lᵖ` function has weak derivative `u'` exactly when the complexified
tempered distributions satisfy the derivative equation. This form applies to real Sobolev
functions using Mathlib's complex Fourier transform. -/
theorem hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq
    (u : Lp ℝ p μ) (u' : Lp ℝ q μ) (v : E) :
    HasWeakLineDerivOn μ ⊤ u u' v ↔
      ∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) =
        Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u') := by
  rw [← hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_eq]
  have hu : (Complex.ofRealCLM.compLp u : E → ℂ) =ᵐ[μ.restrict (⊤ : Opens E)]
      fun x => Complex.ofRealCLM (u x) := by
    rw [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u] with x hx
    exact hx
  have hu' : (Complex.ofRealCLM.compLp u' : E → ℂ) =ᵐ[μ.restrict (⊤ : Opens E)]
      fun x => Complex.ofRealCLM (u' x) := by
    rw [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u'] with x hx
    exact hx
  constructor
  · intro h
    exact ((h.clm_comp Complex.ofRealCLM).congr_ae (by simpa using hu.symm)).congr_ae_deriv
      (by simpa using hu'.symm)
  · intro h
    refine ((h.clm_comp Complex.reCLM).congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [hu] with x hx
      simp [hx]
    · filter_upwards [hu'] with x hx
      simp [hx]

end TauCeti
