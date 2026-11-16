/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Basic
public import TauCeti.Analysis.Meromorphic.LaurentSeries

/-!
# Laurent expansions of meromorphic germs as circle integrals

Let `a : ℂ` and let `φ` be a meromorphic germ at `a`, represented by a function `f`. The
coefficients of its formal Laurent expansion `TauCeti.meromorphicGerms.laurentSeries a φ` are the
circle Laurent coefficients `TauCeti.circleLaurentCoeff f a ρ n`,
`(2πi)⁻¹ ∮_{|z - a| = ρ} (z - a) ^ (-n - 1) f(z) dz`, for every sufficiently small radius `ρ > 0`
and every `n : ℤ`. So the algebraic expansion, computed from Taylor coefficients, agrees with the
analytic one, computed by contour integration.

The representative `f` is any function whose germ on the punctured neighbourhood of `a` is `φ`;
its value at `a` plays no role. The radius bound is uniform in `n`: a single eventual statement in
`ρ → 0⁺` gives the equality for all integer orders at once, so one small circle computes every
Laurent coefficient of `φ`.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 5, §1.3.
-/

public section

open Complex Filter HahnSeries Metric Real Topology

namespace TauCeti.meromorphicGerms

variable {a : ℂ}

/-- **Laurent coefficients as circle integrals.** For every sufficiently small radius `ρ > 0`,
every coefficient of the Laurent expansion of a meromorphic germ `φ` at `a` is the circle Laurent
coefficient `(2πi)⁻¹ ∮_{|z - a| = ρ} (z - a) ^ (-n - 1) f(z) dz` of any representative `f`. -/
theorem eventually_coeff_laurentSeries_eq_circleLaurentCoeff {φ : meromorphicGerms ℂ a}
    {f : ℂ → ℂ} (hφ : (φ : Germ (𝓝[≠] a) ℂ) = f) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ n : ℤ, (laurentSeries a φ).coeff n = circleLaurentCoeff f a ρ n := by
  -- Write `f` as `(z - a)⁻ᴺ h z` with `h` analytic on a disc around `a`. On a circle inside that
  -- disc, the circle coefficient of order `n` of `f` is the circle coefficient of order `n + N` of
  -- `h`. For `n + N ≥ 0` it is a coefficient of the Cauchy power series of `h`, which is the power
  -- series of `h` at `a`; for `n + N < 0` the integrand is holomorphic on the closed disc and the
  -- integral vanishes by the Cauchy–Goursat theorem.
  obtain ⟨N, hN⟩ := coe_mem_meromorphicGerms.1 (hφ ▸ φ.2)
  set h : ℂ → ℂ := fun z ↦ (z - a) ^ N • f z
  have hfh : ∀ z ≠ a, f z = ((z - a) ^ N)⁻¹ * h z := fun z hz ↦ by
    simp only [h, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero N (sub_ne_zero.2 hz))]
  have hrep : (φ : Germ (𝓝[≠] a) ℂ) = (fun z ↦ ((z - a) ^ N)⁻¹ * h z : ℂ → ℂ) :=
    hφ.trans (Germ.coe_eq.2 (eventually_nhdsWithin_of_forall hfh))
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.1 hN.eventually_analyticAt
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ ⟨hρ, hρε⟩ n
  have hdiff : DifferentiableOn ℂ h (closedBall a ρ) := fun z hz ↦
    (hεh ((mem_closedBall.1 hz).trans_lt hρε)).differentiableAt.differentiableWithinAt
  have hcirc : circleLaurentCoeff f a ρ n = circleLaurentCoeff h a ρ (n + N) := by
    rw [← sub_neg_eq_add, ← circleLaurentCoeff_sub_zpow_smul_apply]
    refine circleLaurentCoeff_congr hρ.le (fun z hz ↦ ?_) n
    rw [hfh z (ne_of_mem_sphere hz hρ.ne'), zpow_neg, zpow_natCast, smul_eq_mul]
  rw [hcirc, laurentSeries_eq hN hrep, coeff_single_mul, one_mul, sub_neg_eq_add]
  rcases le_or_gt 0 (n + N) with hnN | hnN
  · lift n + N to ℕ using hnN with m
    have hρ' : ((ρ.toNNReal : NNReal) : ℝ) = ρ := Real.coe_toNNReal ρ hρ.le
    have hp := (hρ' ▸ hdiff).hasFPowerSeriesOnBall (Real.toNNReal_pos.2 hρ)
    rw [ofPowerSeries_apply_coeff, hp.hasFPowerSeriesAt.coeff_taylorSeries,
      circleLaurentCoeff_natCast, hρ']
  · rw [ofPowerSeries_apply, embDomain_of_notMem_range, circleLaurentCoeff_def]
    · -- The exponent `-(n + N) - 1` is a natural number `k`, so the integrand is holomorphic.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, -(n + N) - 1 = k := ⟨(-(n + N) - 1).toNat, by omega⟩
      simp_rw [hk, zpow_natCast, smul_eq_mul]
      rw [DiffContOnCl.circleIntegral_eq_zero hρ.le, mul_zero]
      exact ((differentiableOn_id.sub_const a).pow k |>.mul hdiff).diffContOnCl_ball subset_rfl
    · rintro ⟨m, hm⟩
      simp only [Nat.castOrderEmbedding_apply] at hm
      omega

end TauCeti.meromorphicGerms
