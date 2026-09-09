/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Integrable
public import TauCeti.MeasureTheory.Integral.ExpDamped
public import TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier

/-!
# The limiting Fourier identity for Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` tests a Dirichlet series against an
integrable function on a vertical line `Re s = sigma` strictly inside the half-plane of
convergence. This file lets `sigma` decrease to `1` and records the resulting identity on the
boundary line itself.

Each of the three terms of that identity has its own limit argument, and each is stated separately
so that a later step can reuse it: the Dirichlet series converges by the uniform convergence of a
summable Dirichlet series on a closed half-plane, while the two integrals converge by dominated
convergence, the pole term because the exponential damping `exp (-u (sigma - 1))` is bounded on
the half-line of integration, and the vertical integral because a test function with compact
support confines the integrand to a compact box on which `G` is continuous.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane
`Re s ≥ 1`; nothing is assumed about `LSeries a` there, where it is a total function with junk
values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier` and
  `TauCeti.LSeries.tendsto_integral_vertical` are two of the three one-sided limits; the third,
  for the pole term, is the general `TauCeti.tendsto_integral_exp_mul`.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` is the identity they
  combine into, and
  `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` is its form
  for a smooth test function, where the half-line integrability hypothesis is automatic by
  `TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport`.

## Provenance

The decomposition into three separate one-sided limits, and the shape of the identity they
combine into, follow `limiting_fourier_lim1`, `limiting_fourier_lim2`, `limiting_fourier_lim3`
and `limiting_fourier` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling file
`TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier`. The proofs here are written against
Mathlib's uniform- and dominated-convergence lemmas, and the hypotheses differ: the Chebyshev-type
bound of the source is replaced by the summability of the Fourier-weighted series at `s = 1`,
which is what the limit actually consumes.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

public section

namespace TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ} {x : ℝ}

/-! ### The Dirichlet series -/

/-- As `sigma` decreases to `1`, the Fourier-weighted Dirichlet series converges to its value on
the boundary line, provided the weighted series is summable there. -/
theorem tendsto_tsum_term_mul_fourier (hFsum : LSeriesSummable
    (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1) :
    Tendsto (fun sigma : ℝ ↦ ∑' n : ℕ,
        _root_.LSeries.term a sigma n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)))) := by
  have hterm (s : ℂ) (n : ℕ) :
      _root_.LSeries.term a s n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)) =
        _root_.LSeries.term
          (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) s n := by
    by_cases hn : n = 0
    · simp [_root_.LSeries.term, hn]
    · simp only [_root_.LSeries.term, hn, ite_false]
      ring
  have h := tendsto_LSeries_nhdsGT
    (a := fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) (σ := 1)
    (by simpa using hFsum)
  rw [Complex.ofReal_one] at h
  simp only [hterm]
  exact h

/-! ### The integral along the vertical line -/

/-- As `sigma` decreases to `1`, the integral of `G` along the vertical line `Re s = sigma`
against a compactly supported test function converges to the same integral along the boundary
line, because the integrand is confined to a compact box on which `G` is continuous. -/
theorem tendsto_integral_vertical (hx : 0 < x) (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hpsi : Integrable psi) (hsupp : HasCompactSupport psi) :
    Tendsto (fun sigma : ℝ ↦ ∫ t : ℝ, G (sigma + t * I) * psi t * (x : ℂ) ^ (t * I))
      (𝓝[>] 1) (𝓝 (∫ t : ℝ, G (1 + t * I) * psi t * (x : ℂ) ^ (t * I))) := by
  have hmem {sigma : ℝ} (hsigma : 1 ≤ sigma) (t : ℝ) :
      (sigma : ℂ) + t * I ∈ {z : ℂ | 1 ≤ z.re} := by simpa using hsigma
  have hcompact : IsCompact ((fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) '' (Icc 1 2 ×ˢ tsupport psi)) :=
    (isCompact_Icc.prod hsupp).image (by fun_prop)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn <| hG.mono <| by
    rintro _ ⟨⟨s, t⟩, ⟨hs, -⟩, rfl⟩
    exact hmem hs.1 t
  have hxnorm (t : ℝ) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hxpow : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  refine tendsto_integral_filter_of_dominated_convergence (fun t ↦ C * ‖psi t‖) ?_ ?_
    (hpsi.norm.const_mul C) (.of_forall fun t ↦ ?_)
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact ((hG.comp_continuous (by fun_prop) (hmem (le_of_lt hsigma))).aestronglyMeasurable.mul
      hpsi.aestronglyMeasurable).mul hxpow.aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with sigma hsigma
    filter_upwards with t
    by_cases ht : psi t = 0
    · simp [ht]
    · have hmemK : (sigma : ℂ) + t * I ∈
          (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) '' (Icc 1 2 ×ˢ tsupport psi) :=
        ⟨(sigma, t), ⟨⟨hsigma.1.le, hsigma.2⟩, subset_tsupport _ ht⟩, rfl⟩
      calc ‖G (sigma + t * I) * psi t * (x : ℂ) ^ (t * I)‖
          = ‖G (sigma + t * I)‖ * ‖psi t‖ := by
            rw [norm_mul, norm_mul, hxnorm t, mul_one]
        _ ≤ C * ‖psi t‖ := mul_le_mul_of_nonneg_right (hC _ hmemK) (norm_nonneg _)
  · have hmem1 : (1 : ℂ) + t * I ∈ {z : ℂ | 1 ≤ z.re} := by simp
    refine Filter.Tendsto.mul_const _ (Filter.Tendsto.mul_const _ ?_)
    refine Filter.Tendsto.comp (hG.continuousWithinAt hmem1) ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((by fun_prop : Continuous fun sigma : ℝ ↦ (sigma : ℂ) + t * I).tendsto' 1 _
        (by simp)).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact hmem (le_of_lt hsigma) t

/-! ### The identity on the boundary line -/

/-- The Fourier identity of `tsum_term_mul_fourier_sub_pole_eq_integral` on the boundary line
`Re s = 1`. The Dirichlet series is tested against an integrable, compactly supported `psi`, and
the pole term has lost its exponential damping.

The principal analytic inputs for the passage to the limit are that the Fourier-weighted series
is summable at `s = 1`, the Fourier transform of `psi` is integrable on the half-line, and the
pole-subtracted remainder `G` extends continuously to `Re s ≥ 1`. The additional hypotheses make
`x` positive, supply the interior identity through the formula for `G` and summability of the
original series, and give the integrability and compact support of the test function. -/
theorem tsum_term_mul_fourier_sub_pole_eq_integral_boundary (hx : 0 < x)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : Integrable psi) (hsupp : HasCompactSupport psi)
    (hFint : IntegrableOn (fun u : ℝ ↦ 𝓕 psi (u / (2 * π))) (Ici (-Real.log x)))
    (hFsum : LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1) :
    (∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) -
        A * ∫ u in Ici (-Real.log x), 𝓕 psi (u / (2 * π)) =
      ∫ t : ℝ, G (1 + t * I) * psi t * (x : ℂ) ^ (t * I) := by
  have key (sigma : ℝ) (hsigma : 1 < sigma) :
      (∑' n : ℕ, _root_.LSeries.term a sigma n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) -
          A * (((x ^ (1 - sigma) : ℝ) : ℂ) * ∫ u in Ici (-Real.log x),
            (Real.exp (-u * (sigma - 1)) : ℂ) * 𝓕 psi (u / (2 * π))) =
        ∫ t : ℝ, G (sigma + t * I) * psi t * (x : ℂ) ^ (t * I) := by
    rw [← mul_assoc]
    exact tsum_term_mul_fourier_sub_pole_eq_integral
      (fun t ↦ hG' _ (by simpa using hsigma)) hpsi hx hsigma (hsum sigma hsigma)
  refine tendsto_nhds_unique (l := 𝓝[>] (1 : ℝ)) (f := fun sigma : ℝ ↦
    (∑' n : ℕ, _root_.LSeries.term a sigma n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) -
      A * (((x ^ (1 - sigma) : ℝ) : ℂ) * ∫ u in Ici (-Real.log x),
        (Real.exp (-u * (sigma - 1)) : ℂ) * 𝓕 psi (u / (2 * π)))) ?_ ?_
  · exact (tendsto_tsum_term_mul_fourier hFsum).sub
      ((tendsto_integral_exp_mul hx hFint).const_mul A)
  · refine (tendsto_integral_vertical hx hG hpsi hsupp).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact (key sigma hsigma).symm

/-- The boundary Fourier identity for a smooth, compactly supported test function. Its regularity
supplies both its own integrability and the integrability of its Fourier transform, removing only
the explicit Fourier-integrability hypothesis from
`tsum_term_mul_fourier_sub_pole_eq_integral_boundary`. -/
theorem tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff (hx : 0 < x)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi)
    (hFsum : LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1) :
    (∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) -
        A * ∫ u in Ici (-Real.log x), 𝓕 psi (u / (2 * π)) =
      ∫ t : ℝ, G (1 + t * I) * psi t * (x : ℂ) ^ (t * I) :=
  tsum_term_mul_fourier_sub_pole_eq_integral_boundary hx hG hG' hsum
    (hpsi.continuous.integrable_of_hasCompactSupport hsupp) hsupp
    (((integrable_fourier_of_contDiff_of_hasCompactSupport hpsi hsupp).comp_div
      (by positivity)).integrableOn) hFsum

end TauCeti.LSeries
