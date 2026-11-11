/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor
public import TauCeti.Analysis.PDE.Vortex.Minimizer
public import TauCeti.Analysis.PDE.Vortex.Smoothness
import TauCeti.Analysis.PDE.Vortex.EulerLagrange
import TauCeti.Analysis.PDE.Vortex.Reduced.Regularity
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Existence of framed plane vortices with prescribed zeros

This file proves Taubes's existence theorem: for every effective divisor `D` of degree `m` on the
plane, a point of `Sym ℂ m`, there is a smooth solution of the vortex equations
`∂bar_a α = 0`, `*iF_a = (1 - |α|²) / 8` whose section has zero divisor `D` and the degree-`m` end
framing `α(z) (z / |z|)⁻ᵐ → 1`. Together with Taubes's uniqueness theorem
(`TauCeti.Vortex.existsUnique_framedGaugeGroup_smul_eq`) this classifies the smooth framed
degree-`m` vortices up to smooth framed gauge by their zero divisors.

The construction assembles results proved elsewhere. Let `P` be a monic polynomial of degree
`m ≥ 1`, `u₀ = -log (1 + |P|²) / 2` the background amplitude
(`TauCeti.Vortex.backgroundAmplitude`) and `h = |P|² / (1 + |P|²)`
(`TauCeti.Vortex.backgroundWeight`).

1. Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P` attains its minimum at some
   `w ∈ H¹(ℂ)` (`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), and the minimizer is
   a weak solution of the reduced equation
   `Δw = (exp (2w) h - 1) / 8 + 2 |P'|² / (1 + |P|²)²`
   (`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`).
2. A weak solution lies in `H²(ℂ)`, so it has a continuous representative vanishing at infinity
   (`TauCeti.Vortex.exists_zeroAtInftyContinuousMap_ae_eq_of_forall_integral_reducedSource`).
   Integrating the gradient term by parts once more, this representative solves the reduced
   equation in the sense of distributions.
3. A continuous distributional solution is smooth and solves the reduced equation classically
   (`TauCeti.Vortex.contDiffOn_of_forall_integral_laplacian_mul_eq_reduced`).
4. The field reconstructed from the amplitude `u₀ + w` and the section `P` solves the vortex
   equations (`TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff`), its
   end framing is equivalent to `w → 0`
   (`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff`), and its
   section `exp (u₀ + w) P` has the zeros of `P`.

For `m = 0` the divisor is empty, `P = 1`, and the vortex is the vacuum: zero connection and
section `1`.

## Main results

* `TauCeti.Vortex.exists_contDiff_tendsto_zero_and_laplacian_eq`: for a polynomial `P` of positive
  degree the reduced equation has a smooth solution tending to zero at infinity.
* `TauCeti.Vortex.exists_contDiff_equation_amplitudeField_eq_zero`: for a monic polynomial `P`
  of degree `m` there is a smooth amplitude `u` with `u + m log |z| → 0` at infinity such that
  the field with section `exp (u) P` solves the vortex equations.
* `TauCeti.Vortex.exists_contDiff_equation_eq_zero_isZeroMultiplicity`: **existence** of a smooth
  framed degree-`m` vortex with prescribed zero divisor `D : Sym ℂ m`.
* `TauCeti.Vortex.exists_forall_existsUnique_existsUnique_framedGaugeGroup_smul_eq`:
  **classification**. There is a family `X D`, `D : Sym ℂ m`, of such vortices, and every smooth
  framed degree-`m` vortex is carried to `X D` by a smooth framed gauge transformation for exactly
  one `D`, and by exactly one such transformation.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Gradient Laplacian RealInnerProductSpace ZeroAtInfty

variable {P : Polynomial ℂ}

/-- **Existence of a decaying solution of the reduced vortex equation.** For a complex polynomial
`P` of positive degree there is a smooth `w` with `w → 0` at infinity solving

`Δw = (exp (2w) h - 1) / 8 + 2 |P'|² / (1 + |P|²)²`,    `h = |P|² / (1 + |P|²)`,

at every point. It is the continuous representative of a minimizer of Taubes's functional
`TauCeti.Vortex.sobolevReducedFunctional P` on `H¹(ℂ)`. -/
theorem exists_contDiff_tendsto_zero_and_laplacian_eq (hm : 0 < P.natDegree) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ Tendsto w (cocompact ℂ) (𝓝 0) ∧
      ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  obtain ⟨u, hu⟩ := exists_forall_sobolevReducedFunctional_le hm
  -- The minimizer is a weak solution, with the source written as `reducedSource P`.
  have hweak (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) + ∫ z, reducedSource P (W1p.value u) z * φ z = 0 := by
    rw [← integral_inner_gradient_add_integral_mul_eq_zero hm hu (hφ.of_le (by simp)) hφc]
    congr 2
    funext z
    rw [reducedSource_def, backgroundWeight_def, backgroundSource_def, backgroundWeight_def,
      Polynomial.deriv]
    ring
  obtain ⟨v, hv⟩ := exists_zeroAtInftyContinuousMap_ae_eq_of_forall_integral_reducedSource hm hweak
  -- Integrating by parts once more, `v` solves the reduced equation as a distribution.
  have hdist (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
      ∫ z, Δ (φ : ℂ → ℝ) z * v z = ∫ z, φ z *
        ((Real.exp (2 * v z) * backgroundWeight P.eval z - 1) / 8 +
          2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) := by
    have hibp := (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ
    simp only [Opens.coe_top, smul_eq_mul] at hibp
    have h := hweak φ φ.contDiff φ.hasCompactSupport
    have h1 : ∫ z, Δ (φ : ℂ → ℝ) z * v z = ∫ z, Δ (φ : ℂ → ℝ) z * W1p.value u z :=
      integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])
    have h2 : ∫ z, ⟪W1p.gradient u z, ∇ (φ : ℂ → ℝ) z⟫ =
        ∫ z, ⟪∇ (φ : ℂ → ℝ) z, W1p.gradient u z⟫ :=
      integral_congr_ae (Eventually.of_forall fun z ↦ real_inner_comm _ _)
    have h3 : ∫ z, reducedSource P (W1p.value u) z * φ z = ∫ z, φ z *
        ((Real.exp (2 * v z) * backgroundWeight P.eval z - 1) / 8 +
          2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) := by
      refine integral_congr_ae (hv.mono fun z hz ↦ ?_)
      simp only [reducedSource_def, backgroundSource_def, hz]
      ring
    rw [h1, hibp]
    linarith
  have hfa : AnalyticOnNhd ℂ P.eval (⊤ : Opens ℂ) := fun z _ ↦ P.differentiable.analyticAt z
  have hsmooth : ContDiff ℝ ∞ v := by
    rw [← contDiffOn_univ]
    simpa using contDiffOn_of_forall_integral_laplacian_mul_eq_reduced hfa v.continuous.continuousOn
      hdist
  refine ⟨v, hsmooth, zero_at_infty v, fun z ↦ ?_⟩
  have h' := (equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff (w := v)
    (P.differentiable.analyticAt z) (hsmooth.of_le (by simp)).contDiffAt).1
    (equation_amplitudeField_backgroundAmplitude_add_eq_zero_of_forall_integral_laplacian_mul_eq
      hfa v.continuous.continuousOn hdist (Set.mem_univ z))
  rwa [Polynomial.deriv] at h'

/-- **Existence for the scalar vortex equation.** For a monic polynomial `P` of degree `m` there
is a smooth amplitude `u` with `u + m log |z| → 0` at infinity such that the field with section
`exp (u) P` (`TauCeti.Vortex.amplitudeField`) solves the vortex equations. Equivalently `u`
solves `Δu = (exp (2u) |P|² - 1) / 8` (`TauCeti.Vortex.equation_amplitudeField_eq_zero_iff`). -/
theorem exists_contDiff_equation_amplitudeField_eq_zero (hP : P.Monic) :
    ∃ u : ℂ → ℝ, ContDiff ℝ ∞ u ∧ (∀ z, equation (amplitudeField u P.eval) z = 0) ∧
      Tendsto (fun z ↦ u z + P.natDegree * Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
  rcases Nat.eq_zero_or_pos P.natDegree with hm | hm
  · -- The vacuum: `P = 1` and `u = 0`.
    rw [hP.natDegree_eq_zero] at hm
    subst hm
    refine ⟨fun _ ↦ 0, contDiff_const, fun z ↦ ?_, by simp⟩
    rw [equation_amplitudeField_eq_zero_iff contDiffAt_const (by fun_prop)]
    simp
  · obtain ⟨w, hw, hw0, hΔ⟩ := exists_contDiff_tendsto_zero_and_laplacian_eq hm
    have hbg : ContDiff ℝ ∞ (backgroundAmplitude P.eval) :=
      contDiff_backgroundAmplitude (P.differentiable.contDiff.restrict_scalars ℝ)
    refine ⟨fun z ↦ backgroundAmplitude P.eval z + w z, hbg.add hw, fun z ↦ ?_, ?_⟩
    · rw [equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff
        (P.differentiable.analyticAt z) (hw.of_le (by simp)).contDiffAt, Polynomial.deriv]
      exact hΔ z
    · rw [← tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log hP,
        tendsto_sectionValue_amplitudeField_backgroundAmplitude_add_iff hP hm]
      exact hw0

/-- **Taubes's existence theorem for framed plane vortices.** For every effective divisor `D` of
degree `m` on the plane there is a smooth solution `x` of the vortex equations whose section has
the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` and zero divisor `D`: near each `z` it factors
as `(w - z) ^ D(z) v(w)` with `v` continuous and nonzero at `z`. -/
theorem exists_contDiff_equation_eq_zero_isZeroMultiplicity {m : ℕ} (D : Sym ℂ m) :
    ∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  set P : Polynomial ℂ := ((D : Multiset ℂ).map fun a ↦ Polynomial.X - Polynomial.C a).prod
  have hP : P.Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun a _ ↦ Polynomial.monic_X_sub_C a
  have hPm : P.natDegree = m := by
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Sym.card_coe]
  have hPeval : P.eval = fun w ↦ ((D : Multiset ℂ).map fun a ↦ w - a).prod := by
    funext w
    simp [P, Polynomial.eval_multiset_prod, Multiset.map_map]
  obtain ⟨u, hu, hsol, hlog⟩ := exists_contDiff_equation_amplitudeField_eq_zero hP
  refine ⟨amplitudeField u P.eval, contDiff_amplitudeField hu
    (P.differentiable.contDiff.restrict_scalars ℝ), hsol, ?_, ?_⟩
  · rw [← hPm]
    exact (tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log hP u).2 hlog
  · rw [hPeval]
    exact isZeroMultiplicity_sectionValue_amplitudeField_prod_sub hu.continuous _

/-- **Taubes's classification of framed plane vortices.** There is a family `X` of smooth framed
degree-`m` vortices indexed by `Sym ℂ m`, with `X D` having zero divisor `D`, such that every smooth
framed degree-`m` vortex `y` is carried to `X D` by a smooth framed gauge transformation for
exactly one divisor `D`, and by exactly one such gauge transformation. So the zero divisor
identifies the smooth framed gauge orbits of smooth framed degree-`m` vortices with `Sym ℂ m`. -/
theorem exists_forall_existsUnique_existsUnique_framedGaugeGroup_smul_eq (m : ℕ) :
    ∃ X : Sym ℂ m → ℂ → EuclideanSpace ℝ (Fin 4),
      (∀ D, ContDiff ℝ ∞ (X D) ∧ (∀ z, equation (X D) z = 0) ∧
        Tendsto (fun z ↦ sectionValue (X D) z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) ∧
        IsZeroMultiplicity (sectionValue (X D)) fun z ↦ (D : Multiset ℂ).count z) ∧
      ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y → (∀ z, equation y z = 0) →
        Tendsto (fun z ↦ sectionValue y z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
        ∃! D : Sym ℂ m, ∃! u : framedGaugeGroup, u • y = X D := by
  choose X hX hXsol hXfr hXD using exists_contDiff_equation_eq_zero_isZeroMultiplicity (m := m)
  refine ⟨X, fun D ↦ ⟨hX D, hXsol D, hXfr D, hXD D⟩, fun y hy hysol hyfr ↦ ?_⟩
  have hphase : Tendsto (fun z : ℂ ↦ ‖((z / (‖z‖ : ℂ)) ^ m)⁻¹‖) (cocompact ℂ) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
    have hz' : z ≠ 0 := hz
    simp [norm_inv, norm_pow, hz']
  -- The zero divisor `D` of `y`, a point of `Sym ℂ m` by the end framing.
  have hyi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ y w i := (contDiff_piLp 2).1 hy i
  obtain ⟨D, hD⟩ := exists_sym_sectionValue_eq_pow_count_mul (k := ⊤) le_top (hyi 0) (hyi 1)
    ((hyi 2).differentiable (by simp)) ((hyi 3).differentiable (by simp))
    (fun w ↦ by simp [hysol w]) hyfr
  have hyD : IsZeroMultiplicity (sectionValue y) fun z ↦ (D : Multiset ℂ).count z :=
    isZeroMultiplicity_iff.2 fun z ↦ by
      obtain ⟨v, hvc, hv₀, hvf⟩ := hD z
      exact ⟨v, hvc.continuousAt, hv₀, hvf⟩
  refine ⟨D, existsUnique_framedGaugeGroup_smul_eq (hX D) hy (hXsol D) hysol hphase (hXfr D) hyfr
    (isZeroMultiplicity_iff.1 (hXD D)) (isZeroMultiplicity_iff.1 hyD), fun D' ⟨u, hu, _⟩ ↦ ?_⟩
  -- Framed gauges preserve the divisor, so `X D'` has the divisor `D` of `y`.
  have h := isZeroMultiplicity_sectionValue_framedGaugeGroup_smul hyD u
  rw [hu] at h
  exact Sym.coe_injective (Multiset.ext.2 fun z ↦ congrFun ((hXD D').unique h) z)

end TauCeti.Vortex
