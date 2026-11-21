/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.MeromorphicGerm
public import TauCeti.Analysis.Meromorphic.Derivation
import TauCeti.RingTheory.LaurentSeries.Multiplication

/-!
# Products and derivatives of meromorphic Laurent expansions

The circle-integral coefficients of a product of meromorphic functions are a finite
convolution. Clearing the poles gives bounds `N` and `M` and the explicit interval
`[-N, n + M]` for its coefficient of degree `n`. One sufficiently small circle computes these
formulas simultaneously for every integer degree; the values assigned at the centre do not matter.

Laurent expansion also intertwines differentiation of meromorphic germs with the native
formal Laurent derivative. We deduce this from the circle-integral differentiation formula,
rather than constructing another formal differentiation operation.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, Chapter 5, §1.3.
-/

public section

open Complex Filter HahnSeries Metric Topology

namespace TauCeti

/-- On sufficiently small circles, multiplication of meromorphic functions is finite
convolution of circle Laurent coefficients. There are bounds on the pole orders such that
the same radius bound works for every integer coefficient, including the negative ones. -/
theorem _root_.MeromorphicAt.exists_eventually_circleLaurentCoeff_mul
    {a : ℂ} {f g : ℂ → ℂ} (hf : MeromorphicAt f a) (hg : MeromorphicAt g a) :
    ∃ N M : ℕ, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ n : ℤ,
      circleLaurentCoeff (fun z ↦ f z * g z) a ρ n =
        ∑ i ∈ Finset.Icc (-(N : ℤ)) (n + M),
          circleLaurentCoeff f a ρ i * circleLaurentCoeff g a ρ (n - i) := by
  let φ := meromorphicGerms.mk f hf
  let ψ := meromorphicGerms.mk g hg
  have hφ : (φ : Germ (𝓝[≠] a) ℂ) = f := meromorphicGerms.coe_mk f hf
  have hψ : (ψ : Germ (𝓝[≠] a) ℂ) = g := meromorphicGerms.coe_mk g hg
  have hprod : ((φ * ψ : meromorphicGerms ℂ a) : Germ (𝓝[≠] a) ℂ) =
      (fun z ↦ f z * g z : ℂ → ℂ) := by
    rw [MulMemClass.coe_mul, hφ, hψ]
    exact (Germ.coe_mul f g).symm
  obtain ⟨N, hN⟩ := hf
  obtain ⟨M, hM⟩ := hg
  refine ⟨N, M, ?_⟩
  have hbound {u : ℂ → ℂ} {P : ℕ} {θ : meromorphicGerms ℂ a}
      (hu : AnalyticAt ℂ (fun z ↦ (z - a) ^ P * u z) a)
      (hθ : (θ : Germ (𝓝[≠] a) ℂ) = u) :
      (-(P : ℤ) : WithTop ℤ) ≤ (meromorphicGerms.laurentSeries a θ).orderTop := by
    apply meromorphicGerms.neg_le_orderTop_laurentSeries hu
    rw [hθ, Germ.coe_eq]
    filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ a)
    simp [inv_mul_cancel_left₀, pow_ne_zero _ (sub_ne_zero.mpr hz)]
  filter_upwards
    [meromorphicGerms.eventually_coeff_laurentSeries_eq_circleLaurentCoeff hφ,
      meromorphicGerms.eventually_coeff_laurentSeries_eq_circleLaurentCoeff hψ,
      meromorphicGerms.eventually_coeff_laurentSeries_eq_circleLaurentCoeff hprod]
    with ρ hfρ hgρ hprodρ n
  rw [← hprodρ n, map_mul,
    LaurentSeries.coeff_mul_eq_sum (hbound (by simpa only [smul_eq_mul] using hN) hφ)
      (hbound (by simpa only [smul_eq_mul] using hM) hψ), sub_neg_eq_add]
  simp_rw [hfρ, hgρ]

namespace meromorphicGerms

/-- A pole bound kills every circle Laurent coefficient below that bound, simultaneously
on all sufficiently small circles. The representation only concerns the punctured germ. -/
theorem eventually_circleLaurentCoeff_eq_zero_of_lt_neg
    {a : ℂ} {φ : meromorphicGerms ℂ a} {f h : ℂ → ℂ} {N : ℕ}
    (hh : AnalyticAt ℂ h a) (hf : (φ : Germ (𝓝[≠] a) ℂ) = f)
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : ℂ → ℂ)) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ n : ℤ, n < -(N : ℤ) →
      circleLaurentCoeff f a ρ n = 0 := by
  filter_upwards [eventually_coeff_laurentSeries_eq_circleLaurentCoeff hf] with ρ hρ n hn
  rw [← hρ]
  exact coeff_eq_zero_of_lt_orderTop
    ((WithTop.coe_lt_coe.mpr hn).trans_le (neg_le_orderTop_laurentSeries hh hφ))

/-- Laurent expansion intertwines analytic differentiation on the meromorphic germ field
with formal Laurent differentiation. This holds for arbitrary poles and for the zero germ. -/
@[simp]
theorem laurentSeries_derivation {a : ℂ} (φ : meromorphicGerms ℂ a) :
    laurentSeries a (derivation φ) = LaurentSeries.derivative ℂ (laurentSeries a φ) := by
  obtain ⟨f, hf, rfl⟩ := exists_mk φ
  obtain ⟨R, hR, han⟩ := EMetric.mem_nhdsWithin_iff.mp hf.eventually_analyticAt
  have hdiff : DifferentiableOn ℂ f (eball a R \ closedBall a 0) := by
    rw [closedBall_zero]
    intro z hz
    exact (han ⟨hz.1, hz.2⟩).differentiableAt.differentiableWithinAt
  obtain ⟨q, -, hq0, hqR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hR
  have hcoeff : ∀ᶠ _ in 𝓝[>] (0 : ℝ), ∀ n : ℤ,
      (laurentSeries a (derivation (mk f hf))).coeff n =
        ((n + 1 : ℤ) : ℂ) * (laurentSeries a (mk f hf)).coeff (n + 1) := by
    filter_upwards [eventually_coeff_laurentSeries_eq_circleLaurentCoeff
        (coe_derivation (coe_mk f hf)),
      eventually_coeff_laurentSeries_eq_circleLaurentCoeff (coe_mk f hf),
      Ioo_mem_nhdsGT (ENNReal.ofReal_pos.mp hq0)] with _ hdρ hfρ hρ n
    rw [hdρ, circleLaurentCoeff_deriv hdiff le_rfl hρ.1
      ((ENNReal.ofReal_le_ofReal hρ.2.le).trans_lt hqR), ← hfρ, smul_eq_mul]
  obtain ⟨_, hρ⟩ := hcoeff.exists
  ext n
  simpa only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Nat.cast_one, Ring.choose_one_right, zsmul_eq_mul] using hρ n

end meromorphicGerms

end TauCeti
