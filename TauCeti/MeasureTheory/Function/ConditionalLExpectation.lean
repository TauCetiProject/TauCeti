/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Nonnegative conditional expectations and changes of measure

This file supplies the tower and measurable-multiplier laws for native `condLExp`, and
Bayes' formula for a measure given by a nonnegative density. The multiplication form does
not require the density to be strictly positive. The quotient form holds almost everywhere
for the new measure when it is finite. Observables may have infinite expectation.

The density-restriction identity identifies the conditional density on a sub-sigma-algebra.
It allows weighted integral identities to be used before any integrability or cancellation
argument, as needed for changes of probability measure.

The construction uses Mathlib's `condLExp`, `ae_eq_condLExp` and `Measure.withDensity`.
For the classical measure-change formula, see Karatzas and Shreve,
*Brownian Motion and Stochastic Calculus*, second edition, §3.5.
-/

public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace TauCeti.MeasureTheory

variable {Ω : Type*} {m₀ m m₁ : MeasurableSpace Ω} {P : Measure[m₀] Ω}
  {X Z G : Ω → ℝ≥0∞}

/-- Conditioning successively on a larger and then a smaller sigma-algebra is the same
as conditioning on the smaller one. Both trimmed measures must be sigma-finite. -/
theorem condLExp_condLExp_of_le (hm : m ≤ m₀) (hm₁ : m₁ ≤ m₀) (hle : m ≤ m₁)
    [SigmaFinite (P.trim hm)] [SigmaFinite (P.trim hm₁)] :
    P⁻[P⁻[X | m₁] | m] =ᵐ[P] P⁻[X | m] := by
  refine ae_eq_condLExp hm P X (measurable_condLExp _ _ _) ?_
  intro s hs
  rw [setLIntegral_condLExp hm P _ hs, setLIntegral_condLExp hm₁ P _ (hle s hs)]

/-- Restricting a measure with density to a sub-sigma-algebra replaces its density by
its conditional expectation. No measurability of the original density is needed here. -/
theorem trim_withDensity_eq_withDensity_condLExp (hm : m ≤ m₀)
    [SigmaFinite (P.trim hm)] :
    (P.withDensity Z).trim hm = (P.trim hm).withDensity P⁻[Z | m] := by
  ext s hs
  rw [trim_measurableSet_eq hm hs, withDensity_apply _ hs,
    setLIntegral_condLExp_trim hm P Z hs, withDensity_apply _ (hm s hs)]

/-- A measurable nonnegative weight can be tested against the conditional expectation
or the original function with the same result, including infinite integrals. -/
theorem lintegral_mul_condLExp (hm : m ≤ m₀) [SigmaFinite (P.trim hm)]
    (hZ : AEMeasurable[m₀] Z P) (hG : Measurable[m] G) :
    ∫⁻ ω, G ω * P⁻[Z | m] ω ∂P = ∫⁻ ω, G ω * Z ω ∂P := by
  calc
    _ = ∫⁻ ω, P⁻[Z | m] ω * G ω ∂P := by simp_rw [mul_comm]
    _ = ∫⁻ ω, P⁻[Z | m] ω * G ω ∂P.trim hm :=
      (lintegral_trim hm ((measurable_condLExp _ _ _).mul hG)).symm
    _ = ∫⁻ ω, G ω ∂(P.trim hm).withDensity P⁻[Z | m] :=
      (lintegral_withDensity_eq_lintegral_mul _ (measurable_condLExp _ _ _) hG).symm
    _ = ∫⁻ ω, G ω ∂(P.withDensity Z).trim hm := by
      rw [trim_withDensity_eq_withDensity_condLExp hm]
    _ = ∫⁻ ω, G ω ∂P.withDensity Z := lintegral_trim hm hG
    _ = ∫⁻ ω, Z ω * G ω ∂P :=
      lintegral_withDensity_eq_lintegral_mul₀ hZ (hG.mono hm le_rfl).aemeasurable
    _ = _ := by simp_rw [mul_comm]

/-- The weighted integral identity also holds on every set in the conditioning
sigma-algebra. -/
theorem setLIntegral_mul_condLExp (hm : m ≤ m₀) [SigmaFinite (P.trim hm)]
    (hZ : AEMeasurable[m₀] Z P) (hG : Measurable[m] G)
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    ∫⁻ ω in s, G ω * P⁻[Z | m] ω ∂P = ∫⁻ ω in s, G ω * Z ω ∂P := by
  simpa only [← Set.indicator_mul_left, lintegral_indicator (hm s hs)] using
    lintegral_mul_condLExp hm hZ (hG.indicator hs)

/-- Pull an arbitrary nonnegative measurable factor out of conditional expectation.
Neither boundedness nor integrability of the factor is required. -/
theorem condLExp_mul_of_measurable_left (hm : m ≤ m₀) [SigmaFinite (P.trim hm)]
    (hG : Measurable[m] G) (hX : AEMeasurable[m₀] X P) :
    P⁻[fun ω ↦ G ω * X ω | m] =ᵐ[P] fun ω ↦ G ω * P⁻[X | m] ω := by
  refine (ae_eq_condLExp hm P _ (hG.mul (measurable_condLExp _ _ _)) ?_).symm
  intro s hs
  exact setLIntegral_mul_condLExp hm hX hG hs

/-- Nonnegative Bayes' formula in multiplication form. It remains valid where the
conditional density vanishes, and allows observables of infinite expectation. -/
theorem condLExp_withDensity_mul (hm : m ≤ m₀) [SigmaFinite (P.trim hm)]
    [SigmaFinite ((P.withDensity Z).trim hm)]
    (hZ : AEMeasurable[m₀] Z P) (hX : AEMeasurable[m₀] X (P.withDensity Z)) :
    (fun ω ↦ P⁻[Z | m] ω * (P.withDensity Z)⁻[X | m] ω)
      =ᵐ[P] P⁻[fun ω ↦ Z ω * X ω | m] := by
  refine ae_eq_condLExp hm P _ ((measurable_condLExp _ _ _).mul
    (measurable_condLExp _ _ _)) ?_
  intro s hs
  calc
    _ = ∫⁻ ω in s, (P.withDensity Z)⁻[X | m] ω * Z ω ∂P := by
      simpa only [mul_comm] using
        setLIntegral_mul_condLExp hm hZ (measurable_condLExp m (P.withDensity Z) X) hs
    _ = ∫⁻ ω in s, (P.withDensity Z)⁻[X | m] ω ∂P.withDensity Z := by
      rw [setLIntegral_withDensity_eq_lintegral_mul₀ hZ
        (measurable_condLExp' _ _ _).aemeasurable (hm s hs)]
      simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ ω in s, X ω ∂P.withDensity Z := setLIntegral_condLExp hm _ _ hs
    _ = _ := setLIntegral_withDensity_eq_lintegral_mul₀' hZ hX (hm s hs)

/-- The conditional density is nonzero almost everywhere for the measure it defines.
It may vanish on a set of positive base measure when the two measures are not equivalent. -/
theorem condLExp_ne_zero_withDensity (hm : m ≤ m₀) [SigmaFinite (P.trim hm)] :
    ∀ᵐ ω ∂P.withDensity Z, P⁻[Z | m] ω ≠ 0 := by
  have h : ∀ᵐ ω ∂(P.trim hm).withDensity P⁻[Z | m], P⁻[Z | m] ω ≠ 0 :=
    (ae_withDensity_iff (measurable_condLExp _ _ _)).2 (Filter.Eventually.of_forall
      (fun _ h ↦ h))
  rw [← trim_withDensity_eq_withDensity_condLExp hm] at h
  exact ae_of_ae_trim hm h

/-- Nonnegative Bayes' formula for a finite measure obtained by a density change.
The quotient identity holds almost everywhere for the new measure, without assuming
strict positivity of the density. Under equivalence it therefore also holds almost
everywhere for the base measure. No integrability of the observable is required. -/
theorem condLExp_withDensity (hm : m ≤ m₀) [SigmaFinite (P.trim hm)]
    [IsFiniteMeasure (P.withDensity Z)]
    (hZ : AEMeasurable[m₀] Z P) (hX : AEMeasurable[m₀] X (P.withDensity Z)) :
    (P.withDensity Z)⁻[X | m]
      =ᵐ[P.withDensity Z] fun ω ↦ P⁻[fun ω ↦ Z ω * X ω | m] ω / P⁻[Z | m] ω := by
  have hfinite : ∫⁻ ω, Z ω ∂P ≠ ∞ := isFiniteMeasure_withDensity_iff.mp inferInstance
  filter_upwards [(withDensity_absolutelyContinuous P Z).ae_eq
    (condLExp_withDensity_mul hm hZ hX), condLExp_ne_zero_withDensity hm,
    (withDensity_absolutelyContinuous P Z).ae_le (condLExp_ne_top (mΩ := m) hfinite)]
    with ω hmul hzero htop
  exact (ENNReal.eq_div_iff hzero htop).2 hmul

end TauCeti.MeasureTheory
