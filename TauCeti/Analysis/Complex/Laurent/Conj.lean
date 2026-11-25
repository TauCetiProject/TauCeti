/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.Analysis.Complex.Laurent.MeromorphicGerm
public import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# Laurent coefficients under reflection

Conjugate reflection carries the Laurent expansion at `c` to the expansion with conjugate
coefficients at `conj c`. This holds for arbitrary meromorphic representatives, since the
coefficients depend only on the punctured germ. The circle calculation uses the periodic
change of angle as in Mathlib's `circleAverage_zero_one_congr_inv`.
-/

public section

open Complex Filter HahnSeries
open scoped ComplexConjugate Real Topology

namespace TauCeti

/-- Conjugate reflection conjugates the circle Laurent coefficients, with the reflected centre. -/
@[simp]
theorem circleLaurentCoeff_conj_conj (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (n : ℤ) :
    circleLaurentCoeff (conj ∘ f ∘ conj) c r n = conj (circleLaurentCoeff f (conj c) r n) := by
  let F : ℝ → ℂ := fun t ↦ circleMap 0 r t * I *
    ((circleMap (conj c) r t - conj c) ^ (-n - 1) * f (circleMap (conj c) r t))
  have hper : Function.Periodic F (2 * π) := fun t ↦ by
    simp only [F, periodic_circleMap _ _ t]
  have hreflect : (∫ t in 0..2 * π, F (-t)) = ∫ t in 0..2 * π, F t := by
    rw [intervalIntegral.integral_comp_neg, neg_zero]
    simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0
  -- Reflection reverses the contour orientation and conjugates the factor `1 / (2πi)`;
  -- the two signs cancel.
  rw [circleLaurentCoeff_def, circleLaurentCoeff_def]
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul, Function.comp_apply, map_mul, map_inv₀,
    map_ofNat, conj_I, conj_ofReal]
  rw [← intervalIntegral.intervalIntegral_conj]
  have hpoint (t : ℝ) : conj (F t) =
      -(circleMap 0 r (-t) * I *
        ((circleMap c r (-t) - c) ^ (-n - 1) * conj (f (conj (circleMap c r (-t)))))) := by
    simp [F, conj_circleMap]
  have hI : (∫ t in 0..2 * π, conj (F t)) = ∫ t in 0..2 * π, conj (F (-t)) := by
    rw [intervalIntegral.intervalIntegral_conj, intervalIntegral.intervalIntegral_conj, hreflect]
  rw [hI]
  simp only [hpoint, neg_neg, intervalIntegral.integral_neg, mul_neg, inv_neg, neg_mul]

/-- The Laurent coefficients of a reflected meromorphic germ are the conjugates of those at
its reflected centre. -/
theorem meromorphicGerms.coeff_laurentSeries_conj_conj {f : ℂ → ℂ} {c d : ℂ}
    (hcd : conj c = d) (hf : MeromorphicAt f d) (n : ℤ) :
    (laurentSeries c (mk (conj ∘ f ∘ conj)
      (meromorphicAt_conj_conj_iff.mpr (hcd.symm ▸ hf)))).coeff n =
      conj ((laurentSeries d (mk f hf)).coeff n) := by
  subst d
  have hR := meromorphicAt_conj_conj_iff.mpr hf
  obtain ⟨r, hr, hf'⟩ := ((eventually_coeff_laurentSeries_eq_circleLaurentCoeff (coe_mk _ hR)).and
    (eventually_coeff_laurentSeries_eq_circleLaurentCoeff (coe_mk _ hf))).exists
  rw [hr n, hf' n, circleLaurentCoeff_conj_conj]

/-- The leading Laurent coefficient is conjugated under reflection, including the totalized
zero coefficient for a zero germ or a nonmeromorphic function. -/
@[simp]
theorem meromorphicTrailingCoeffAt_conj_conj (f : ℂ → ℂ) (c : ℂ) :
    meromorphicTrailingCoeffAt (conj ∘ f ∘ conj) c =
      conj (meromorphicTrailingCoeffAt f (conj c)) := by
  by_cases hf : MeromorphicAt f (conj c)
  · by_cases h : meromorphicOrderAt f (conj c) = ⊤
    · simp [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top h,
        MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top
          (meromorphicOrderAt_conj_conj.trans h)]
    · obtain ⟨g, hg, hg₀, hfg⟩ := (meromorphicOrderAt_ne_top_iff hf).mp h
      have hconj : Tendsto conj (𝓝[≠] c) (𝓝[≠] (conj c)) :=
        continuous_conj.continuousAt.tendsto_nhdsNE (starRingEnd ℂ).injective
      have he : (conj ∘ f ∘ conj) =ᶠ[𝓝[≠] c] fun z ↦
          (z - c) ^ (meromorphicOrderAt f (conj c)).untop₀ • (conj ∘ g ∘ conj) z := by
        filter_upwards [hconj.eventually hfg] with z hz
        simp [hz]
      rw [hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hg₀ hfg]
      exact (analyticAt_conj_conj_iff.mpr hg).meromorphicTrailingCoeffAt_of_eq_nhdsNE
        (by simpa only [meromorphicOrderAt_conj_conj] using he)
  · simp [meromorphicTrailingCoeffAt_of_not_MeromorphicAt hf,
      meromorphicTrailingCoeffAt_of_not_MeromorphicAt (meromorphicAt_conj_conj_iff.not.mpr hf)]

end TauCeti
