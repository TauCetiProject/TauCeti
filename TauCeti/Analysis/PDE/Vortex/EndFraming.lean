/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reconstruction
import Mathlib.Analysis.Polynomial.Basic

/-!
# End framing of reconstructed polynomial vortices

For a monic polynomial `P` of degree `m`, the reconstructed section `exp(u) P` has the
prescribed phase framing `α(z) (z / ‖z‖)⁻ᵐ → 1` precisely when
`u(z) + m log ‖z‖ → 0`. Equivalently, its modulus tends to one. Thus solving the
regularized scalar equation with its scalar boundary condition supplies the phase condition
without any further choice of gauge. Repeated roots and degree zero are included.

All limits use the cocompact filter on the whole complex plane: they are uniform in the
angular variable, not merely limits along individual rays. No derivative decay, Sobolev tail,
finite energy, or existence of a scalar solution is asserted here.

The polynomial input is Mathlib's `Polynomial.isEquivalent_cobounded_leading_monomial`.
The reconstruction is `Vortex.amplitudeField`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology

-- Separate the positive radial amplitude from a correction tending to one. This factor
-- is used both for the complex framing and for the real modulus boundary condition.
private theorem exists_amplitudeField_end_factor
    {P : Polynomial ℂ} (hP : P.Monic) (u : ℂ → ℝ) :
    ∃ q : ℂ → ℂ, Tendsto q (cocompact ℂ) (𝓝 1) ∧
      (fun z ↦ sectionValue (amplitudeField u P.eval) z *
        ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) =ᶠ[cocompact ℂ]
      (fun z ↦ ((Real.exp (u z) * ‖z‖ ^ P.natDegree : ℝ) : ℂ) * q z) := by
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have hq : Tendsto (fun z ↦ P.eval z / z ^ P.natDegree) (cocompact ℂ) (𝓝 1) := by
    have he := Polynomial.isEquivalent_cobounded_leading_monomial (P := P)
    simp only [hP.leadingCoeff, one_mul, Metric.cobounded_eq_cocompact] at he
    exact (Asymptotics.isEquivalent_iff_tendsto_one
      (hz.mono fun z hz ↦ pow_ne_zero _ hz)).mp he
  -- The winding phase cancels the leading monomial, leaving a positive radial factor
  -- times the polynomial's quotient by that monomial.
  refine ⟨fun z ↦ P.eval z / z ^ P.natDegree, hq, ?_⟩
  filter_upwards [hz] with z hz
  simp only [sectionValue_amplitudeField, ofReal_mul, ofReal_pow, div_pow, inv_div]
  field_simp

/-- The end framing of a reconstructed monic polynomial section is equivalent to its
radial amplitude tending to one. No regularity or equation is needed for this equivalence. -/
theorem tendsto_sectionValue_amplitudeField_mul_inv_phase_iff
    {P : Polynomial ℂ} (hP : P.Monic) (u : ℂ → ℝ) :
    Tendsto (fun z ↦ sectionValue (amplitudeField u P.eval) z *
      ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) ↔
    Tendsto (fun z ↦ Real.exp (u z) * ‖z‖ ^ P.natDegree) (cocompact ℂ) (𝓝 1) := by
  obtain ⟨q, hq, hfactor⟩ := exists_amplitudeField_end_factor hP u
  rw [tendsto_congr' hfactor]
  constructor
  · intro h
    have hdiv := h.div hq one_ne_zero
    rw [div_one] at hdiv
    have hrad : Tendsto (fun z ↦ ((Real.exp (u z) * ‖z‖ ^ P.natDegree : ℝ) : ℂ))
        (cocompact ℂ) (𝓝 1) := by
      apply hdiv.congr'
      filter_upwards [hq.eventually_ne one_ne_zero] with z hz
      exact mul_div_cancel_right₀ _ hz
    simpa only [Function.comp_def, ofReal_re, one_re] using
      (continuous_re.tendsto 1).comp hrad
  · intro h
    have hc := (continuous_ofReal.tendsto 1).comp h
    simpa only [Function.comp_def, ofReal_one, one_mul] using hc.mul hq

/-- The scalar logarithmic boundary condition is exactly the degree-`m` phase framing
for the section reconstructed from a monic divisor polynomial. -/
theorem tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log
    {P : Polynomial ℂ} (hP : P.Monic) (u : ℂ → ℝ) :
    Tendsto (fun z ↦ sectionValue (amplitudeField u P.eval) z *
      ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) ↔
    Tendsto (fun z ↦ u z + P.natDegree * Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_sectionValue_amplitudeField_mul_inv_phase_iff hP]
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have he : (fun z ↦ Real.exp (u z + P.natDegree * Real.log ‖z‖)) =ᶠ[cocompact ℂ]
      (fun z ↦ Real.exp (u z) * ‖z‖ ^ P.natDegree) := by
    filter_upwards [hz] with z hz
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr hz)]
  constructor
  · intro h
    have hh := (Real.continuousAt_log one_ne_zero).tendsto.comp
      ((tendsto_congr' he).mpr h)
    simpa only [Function.comp_def, Real.log_exp, Real.log_one] using hh
  · intro h
    have hh := Real.continuous_exp.continuousAt.tendsto.comp h
    simpa only [Real.exp_zero] using (tendsto_congr' he).mp hh

/-- For a reconstructed monic polynomial section, unit modulus at infinity already fixes
its degree-`m` end phase. The scalar ansatz has no independent phase ambiguity. -/
theorem tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_norm
    {P : Polynomial ℂ} (hP : P.Monic) (u : ℂ → ℝ) :
    Tendsto (fun z ↦ sectionValue (amplitudeField u P.eval) z *
      ((z / (‖z‖ : ℂ)) ^ P.natDegree)⁻¹) (cocompact ℂ) (𝓝 1) ↔
    Tendsto (fun z ↦ ‖sectionValue (amplitudeField u P.eval) z‖)
      (cocompact ℂ) (𝓝 1) := by
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  constructor
  · intro h
    have hh := h.norm
    simp only [norm_one] at hh
    apply hh.congr'
    filter_upwards [hz] with z hz
    simp [norm_inv, norm_pow, norm_ne_zero_iff.mpr hz]
  · intro h
    rw [tendsto_sectionValue_amplitudeField_mul_inv_phase_iff hP]
    obtain ⟨q, hq, hfactor⟩ := exists_amplitudeField_end_factor hP u
    have hh := h.div hq.norm (by simp)
    simp only [norm_one, div_one] at hh
    apply hh.congr'
    filter_upwards [hz, hq.eventually_ne one_ne_zero, hfactor] with z hz hqz hfactor
    have hnorm : ‖sectionValue (amplitudeField u P.eval) z‖ =
        (Real.exp (u z) * ‖z‖ ^ P.natDegree) * ‖q z‖ := by
      have hn := congrArg norm hfactor
      simpa only [norm_mul, norm_inv, norm_pow, norm_div, norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_norm,
        div_self (norm_ne_zero_iff.mpr hz), one_pow, inv_one, mul_one] using hn
    simpa only [Pi.div_apply, hnorm] using
      mul_div_cancel_right₀ (Real.exp (u z) * ‖z‖ ^ P.natDegree) (norm_ne_zero_iff.mpr hqz)

end TauCeti.Vortex
