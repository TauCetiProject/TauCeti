/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.Meromorphic.PrincipalPart
import TauCeti.Analysis.Contour.Residue.Theorem

/-!
# Principal parts of meromorphic germs through residues and contour integrals

Let `a : ℂ` and let `φ` be a meromorphic germ at `a`, with principal part
`TauCeti.meromorphicGerms.principalPart φ : ℂ[X]`, so that the coefficient of `X ^ (k + 1)` is the
Laurent coefficient of `φ` of order `-(k + 1)`. This file computes these coefficients from any
representative `f` of `φ`: the coefficient of `X ^ (k + 1)` is the residue at `a` of
`(z - a)^k f(z)` (`coeff_principalPart_succ_eq_residue`), so the coefficient of `X` is the residue
of `f` (`coeff_principalPart_one_eq_residue`), and by the residue theorem it is
`(2πi)⁻¹ ∮_{|z - a| = ρ} (z - a)^k f(z) dz` for every sufficiently small `ρ > 0`
(`coeff_principalPart_succ_eq_circleIntegral`).

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 4, §§3.2–3.3 and
  Chapter 5, §1.3.
-/

public section

open Complex Filter Polynomial Real Topology

namespace TauCeti.meromorphicGerms

variable {a : ℂ}

/-- **Laurent coefficients as residues.** The coefficient of `X ^ (k + 1)` in the principal part
of a meromorphic germ, its Laurent coefficient of order `-(k + 1)`, is the residue at `a` of
`(z - a)^k f(z)` for any representative `f`. -/
theorem coeff_principalPart_succ_eq_residue {φ : meromorphicGerms ℂ a} {f : ℂ → ℂ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = f) (k : ℕ) :
    (principalPart φ).coeff (k + 1) = Contour.residue (fun z ↦ (z - a) ^ k * f z) a := by
  obtain ⟨N, hN⟩ := coe_mem_meromorphicGerms.1 (hφ ▸ φ.2)
  -- Write `f` as `h(z) / (z - a)^(N + k + 1)` with `h` analytic at `a`; both sides are then the
  -- Taylor coefficient of `h` of order `N`. The principal part is computed by
  -- `principalPart_eq_sum_coeff` and the residue by `Contour.residue_eq_of_eventuallyEq_zpow_smul`,
  -- and both equal the coefficient `iteratedDeriv N h a / N!` of the power series of `h` given by
  -- `AnalyticAt.hasFPowerSeriesAt`.
  have hh : AnalyticAt ℂ (fun z ↦ (z - a) ^ (k + 1) * ((z - a) ^ N • f z)) a :=
    ((analyticAt_id.sub analyticAt_const).pow _).mul hN
  have hφh : (φ : Germ (𝓝[≠] a) ℂ) = ↑(fun z ↦
      ((z - a) ^ (N + (k + 1)))⁻¹ * ((z - a) ^ (k + 1) * ((z - a) ^ N • f z))) := by
    rw [hφ, Germ.coe_eq]
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hza : z - a ≠ 0 := sub_ne_zero.2 hz
    rw [smul_eq_mul, pow_add]
    field_simp
  rw [principalPart_eq_sum_coeff hh.hasFPowerSeriesAt hφh, finsetSum_coeff, Finset.sum_eq_single N,
    coeff_C_mul_X_pow, Nat.add_sub_cancel_left, FormalMultilinearSeries.coeff_ofScalars,
    Contour.residue_eq_of_eventuallyEq_zpow_smul (n := -((N + 1 : ℕ) : ℤ)) (by omega) hh]
  · have hidx : (-1 - -((N + 1 : ℕ) : ℤ)).toNat = N := by omega
    simp only [↓reduceIte]
    rw [hidx, smul_eq_mul, inv_mul_eq_div]
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hza : z - a ≠ 0 := sub_ne_zero.2 hz
    rw [zpow_neg, zpow_natCast, smul_eq_mul, smul_eq_mul, pow_succ]
    field_simp
    ring
  · intro j _ hjN
    rw [coeff_C_mul_X_pow, ite_eq_right_iff]
    omega
  · intro hN
    exact absurd (Finset.mem_range.2 (by omega)) hN

/-- The coefficient of `X` in the principal part of a meromorphic germ is the residue at `a` of
any of its representatives. -/
theorem coeff_principalPart_one_eq_residue {φ : meromorphicGerms ℂ a} {f : ℂ → ℂ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = f) : (principalPart φ).coeff 1 = Contour.residue f a := by
  simpa using coeff_principalPart_succ_eq_residue hφ 0

/-- **Laurent coefficients as contour integrals.** For every sufficiently small radius `ρ > 0`,
the coefficient of `X ^ (k + 1)` in the principal part of a meromorphic germ, its Laurent
coefficient of order `-(k + 1)`, is `(2πi)⁻¹ ∮_{|z - a| = ρ} (z - a)^k f(z) dz` for any
representative `f`. -/
theorem coeff_principalPart_succ_eq_circleIntegral {φ : meromorphicGerms ℂ a} {f : ℂ → ℂ}
    (hφ : (φ : Germ (𝓝[≠] a) ℂ) = f) (k : ℕ) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (principalPart φ).coeff (k + 1) =
      (2 * π * I)⁻¹ * ∮ z in C(a, ρ), (z - a) ^ k * f z := by
  have hF : MeromorphicAt (fun z ↦ (z - a) ^ k * f z) a :=
    ((analyticAt_id.sub analyticAt_const).pow k).meromorphicAt.mul
      (coe_mem_meromorphicGerms.1 (hφ ▸ φ.2))
  obtain ⟨ε, hε, hεF⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hF.eventually_analyticAt)
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ ⟨hρ, hρε⟩
  have han {z : ℂ} (hz : z ∈ Metric.closedBall a ρ) (hza : z ≠ a) :
      AnalyticAt ℂ (fun z ↦ (z - a) ^ k * f z) z :=
    hεF ((Metric.mem_closedBall.1 hz).trans_lt hρε) hza
  rw [Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hρ {a} (fun z hz ↦ ?_)
    (by simpa using Metric.mem_ball_self (x := a) hρ) (fun z hz hneg ↦ ?_), Finset.sum_singleton,
    ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul,
    coeff_principalPart_succ_eq_residue hφ k]
  · rcases eq_or_ne z a with rfl | hza
    · exact hF
    · exact (han hz hza).meromorphicAt
  · by_contra hza
    exact (han hz (by simpa using hza)).meromorphicOrderAt_nonneg.not_gt hneg

end TauCeti.meromorphicGerms
