/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Potential
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
public import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Connected.Clopen

/-!
# The scalar similarity principle with smooth coefficient

A real-differentiable solution of `bar∂ f = a f`, for smooth `a` on the plane, becomes
holomorphic after multiplication by a nowhere-zero smooth integrating factor. Consequently
a nonzero solution has isolated zeros and factors near each point as a nonnegative integral
power of the complex coordinate times a nonvanishing smooth function. No curvature equation
or analyticity of the coefficient is needed.

The integrating factor comes from the planar Newtonian potential; the holomorphic zero
factorization is Mathlib's `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`.

## References

* I. N. Vekua, *Generalized Analytic Functions*, Chapter I.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
-/

public noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace TauCeti

/-- A smooth integrating factor makes a solution of `bar∂ f = a f` holomorphic locally. -/
theorem exists_contDiff_exp_mul_analyticAt {a f : ℂ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hf : Differentiable ℝ f)
    (heq : ∀ w, conjWirtingerDeriv f w 1 = a w * f w) (z : ℂ) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧
      AnalyticAt ℂ (fun w ↦ exp (-g w) * f w) z := by
  obtain ⟨g, hg, hgeq⟩ := exists_contDiff_conjWirtingerDeriv_eventuallyEq ha z
  refine ⟨g, hg, Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_⟩
  filter_upwards [hgeq] with w hw
  have hgd := hg.differentiable (by simp) w
  have hfd := hf w
  refine (differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
    ((hgd.neg.cexp).mul hfd)).mpr ?_
  have hG := congrArg (fun c : ℂ ↦ 2 * c) hw
  have hF := congrArg (fun c : ℂ ↦ 2 * c) (heq w)
  simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] at hG hF ⊢
  rw [hgd.hasFDerivAt.neg.cexp.mul hfd.hasFDerivAt |>.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply]
  linear_combination exp (-g w) / 2 * (hF - f w * hG)

/-- A nontrivial solution of a scalar Cauchy–Riemann equation with smooth coefficient
cannot vanish identically on any neighborhood. -/
theorem not_eventually_eq_zero_of_conjWirtingerDeriv_eq_mul {a f : ℂ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hf : Differentiable ℝ f)
    (heq : ∀ w, conjWirtingerDeriv f w 1 = a w * f w)
    (hne : ∃ w, f w ≠ 0) (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, f w = 0 := by
  let S := {z | ∀ᶠ w in 𝓝 z, f w = 0}
  have hS : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : IsOpen Sᶜ := by
    refine isOpen_iff_mem_nhds.mpr fun w hw ↦ ?_
    obtain ⟨g, _, hg⟩ := exists_contDiff_exp_mul_analyticAt ha hf heq w
    have hgn : ¬ ∀ᶠ y in 𝓝 w, exp (-g y) * f y = 0 := by
      have hnw : ¬ ∀ᶠ y in 𝓝 w, f y = 0 := hw
      simpa only [mul_eq_zero, exp_ne_zero, false_or] using hnw
    have hi := hg.eventually_eq_zero_or_eventually_ne_zero.resolve_left hgn
    rw [eventually_nhdsWithin_iff] at hi
    filter_upwards [hi] with y hy
    intro hyS
    by_cases hyw : y = w
    · exact hw (hyw ▸ hyS)
    · exact hy hyw (by simp [hyS.self_of_nhds])
  intro hz
  have hc : IsClopen S := ⟨by simpa using hSc.isClosed_compl, hS⟩
  have hu : S = univ := hc.eq_univ ⟨z, hz⟩
  obtain ⟨w, hw⟩ := hne
  have hwS : w ∈ S := by rw [hu]; trivial
  exact hw hwS.self_of_nhds

/-- Every zero of a nontrivial solution of `bar∂ f = a f` is isolated. -/
theorem eventually_ne_zero_of_conjWirtingerDeriv_eq_mul {a f : ℂ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hf : Differentiable ℝ f)
    (heq : ∀ w, conjWirtingerDeriv f w 1 = a w * f w)
    (hne : ∃ w, f w ≠ 0) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  obtain ⟨g, _, hg⟩ := exists_contDiff_exp_mul_analyticAt ha hf heq z
  have hn := not_eventually_eq_zero_of_conjWirtingerDeriv_eq_mul ha hf heq hne z
  have hgn : ¬ ∀ᶠ w in 𝓝 z, exp (-g w) * f w = 0 := by
    simpa only [mul_eq_zero, exp_ne_zero, false_or] using hn
  filter_upwards [hg.eventually_eq_zero_or_eventually_ne_zero.resolve_left hgn] with w hw
  exact fun h ↦ hw (by simp [h])

/-- Near each point, a nontrivial solution of `bar∂ f = a f` is an integral power of the
complex coordinate times a smooth factor nonzero at that point. -/
theorem exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_eq_mul {a f : ℂ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hf : Differentiable ℝ f)
    (heq : ∀ w, conjWirtingerDeriv f w 1 = a w * f w)
    (hne : ∃ w, f w ≠ 0) (z : ℂ) :
    ∃ (n : ℕ) (v : ℂ → ℂ), ContDiffAt ℝ ∞ v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n * v w := by
  obtain ⟨g, hg, hA⟩ := exists_contDiff_exp_mul_analyticAt ha hf heq z
  have hn := not_eventually_eq_zero_of_conjWirtingerDeriv_eq_mul ha hf heq hne z
  have hgn : ¬ ∀ᶠ w in 𝓝 z, exp (-g w) * f w = 0 := by
    simpa only [mul_eq_zero, exp_ne_zero, false_or] using hn
  obtain ⟨n, u, hu, hun, he⟩ := hA.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hgn
  refine ⟨n, fun w ↦ exp (g w) * u w,
    hg.contDiffAt.cexp.mul (hu.contDiffAt.restrict_scalars ℝ), mul_ne_zero (exp_ne_zero _) hun, ?_⟩
  filter_upwards [he] with w hw
  have := congrArg (fun c : ℂ ↦ exp (g w) * c) hw
  rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at this
  simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using this

end TauCeti
