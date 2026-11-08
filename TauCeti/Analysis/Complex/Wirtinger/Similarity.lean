/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Potential
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
public import Mathlib.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.ContinuousLog.ArgumentPrinciple
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The scalar similarity principle

A real-differentiable solution of `bar∂ f = a f`, for `Cᵏ` coefficient `a` on an open
domain (`k ≥ 1`), becomes holomorphic near each point after multiplication by a
nowhere-zero `Cᵏ` integrating factor depending on the point. On a preconnected domain,
a nonzero solution has isolated zeros and factors near each point as a nonnegative
integral power of the complex coordinate times a factor `Cᵏ` at the point and nonzero
there. For a solution on the plane that is nonzero outside a compact set, the zero set
is finite, by the general finiteness criterion for local power factorizations
`TauCeti.finite_setOfPred_eq_zero_of_eventually_eq_pow_mul`. No curvature equation or
analyticity of the coefficient is needed.

The integrating factor comes from the Cauchy transform; the holomorphic zero
factorization is Mathlib's `AnalyticAt.exists_eventuallyEq_pow_smul_ne_zero_iff`.

## References

* I. N. Vekua, *Generalized Analytic Functions*, Chapter I.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
-/

public noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {k : ℕ∞} {U : Set ℂ}

/-- A `Cᵏ` integrating factor makes a solution of `bar∂ f = a f` holomorphic locally. -/
theorem exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul {a f : ℂ → ℂ}
    (hn : 1 ≤ k) (hU : IsOpen U) (ha : ContDiffOn ℝ k a U)
    (hf : DifferentiableOn ℝ f U)
    (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w) {z : ℂ} (hz : z ∈ U) :
    ∃ g : ℂ → ℂ, ContDiff ℝ k g ∧
      AnalyticAt ℂ (fun w ↦ exp (-g w) * f w) z := by
  obtain ⟨g, hg, hgeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq hn hU ha hz
  refine ⟨g, hg, Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_⟩
  filter_upwards [hgeq, hU.mem_nhds hz] with w hw hwU
  have hgd := hg.differentiable (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))) w
  have hfd := (hf w hwU).differentiableAt (hU.mem_nhds hwU)
  refine (differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
    ((hgd.neg.cexp).mul hfd)).mpr ?_
  have hG := congrArg (fun c : ℂ ↦ 2 * c) hw
  have hF := congrArg (fun c : ℂ ↦ 2 * c) (heq w hwU)
  simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] at hG hF ⊢
  rw [hgd.hasFDerivAt.neg.cexp.mul hfd.hasFDerivAt |>.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply]
  linear_combination exp (-g w) / 2 * (hF - f w * hG)

private theorem exists_contDiff_analyticAt_exp_neg_mul_not_eventually_eq_zero
    {a f : ℂ → ℂ}
    (hn : 1 ≤ k) (hU : IsOpen U) (ha : ContDiffOn ℝ k a U)
    (hf : DifferentiableOn ℝ f U)
    (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w) {z : ℂ} (hz : z ∈ U)
    (hne : ¬ ∀ᶠ w in 𝓝 z, f w = 0) :
    ∃ g : ℂ → ℂ, ContDiff ℝ k g ∧ AnalyticAt ℂ (fun w ↦ exp (-g w) * f w) z ∧
      ¬ ∀ᶠ w in 𝓝 z, exp (-g w) * f w = 0 := by
  obtain ⟨g, hg, hA⟩ :=
    exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul hn hU ha hf heq hz
  exact ⟨g, hg, hA, by simpa only [mul_eq_zero, exp_ne_zero, false_or] using hne⟩

/-- On a preconnected open domain, a nontrivial solution of a scalar Cauchy–Riemann
equation with `Cᵏ` coefficient, `k ≥ 1`, cannot vanish on any neighborhood. -/
theorem not_eventually_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul {a f : ℂ → ℂ}
    (hn : 1 ≤ k) (hU : IsOpen U) (hconn : IsPreconnected U) (ha : ContDiffOn ℝ k a U)
    (hf : DifferentiableOn ℝ f U)
    (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w)
    (hne : ∃ w ∈ U, f w ≠ 0) {z : ℂ} (hz : z ∈ U) : ¬ ∀ᶠ w in 𝓝 z, f w = 0 := by
  let S := {z | ∀ᶠ w in 𝓝 z, f w = 0}
  have hS : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : IsOpen (U \ S) := by
    refine isOpen_iff_mem_nhds.mpr fun w hw ↦ ?_
    obtain ⟨g, _, hg, hgn⟩ :=
      exists_contDiff_analyticAt_exp_neg_mul_not_eventually_eq_zero
        hn hU ha hf heq hw.1 hw.2
    have hi := hg.eventually_eq_zero_or_eventually_ne_zero.resolve_left hgn
    rw [eventually_nhdsWithin_iff] at hi
    filter_upwards [hi, hU.mem_nhds hw.1] with y hy hyU
    refine ⟨hyU, ?_⟩
    intro hyS
    by_cases hyw : y = w
    · exact hw.2 (hyw ▸ hyS)
    · exact hy hyw (by simp [hyS.self_of_nhds])
  intro hzS
  have hsub : U ⊆ S := hconn.subset_left_of_subset_union hS hSc disjoint_sdiff_right
    (by intro w hw; by_cases hs : w ∈ S <;> simp [hw, hs]) ⟨z, hz, hzS⟩
  obtain ⟨w, hwU, hw⟩ := hne
  exact hw (hsub hwU).self_of_nhds

/-- A solution of `bar∂ f = a f` with `Cᵏ` coefficient, `k ≥ 1`, that does not vanish
on any neighborhood of a point is nonzero in a punctured neighborhood of that point. -/
theorem eventually_ne_zero_of_conjWirtingerDeriv_apply_one_eq_mul {a f : ℂ → ℂ}
    (hn : 1 ≤ k) (hU : IsOpen U) (ha : ContDiffOn ℝ k a U)
    (hf : DifferentiableOn ℝ f U)
    (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w) {z : ℂ} (hz : z ∈ U)
    (hne : ¬ ∀ᶠ w in 𝓝 z, f w = 0) : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  obtain ⟨g, _, hg, hgn⟩ :=
    exists_contDiff_analyticAt_exp_neg_mul_not_eventually_eq_zero
      hn hU ha hf heq hz hne
  filter_upwards [hg.eventually_eq_zero_or_eventually_ne_zero.resolve_left hgn] with w hw
  exact fun h ↦ hw (by simp [h])

/-- A solution of `bar∂ f = a f` with `Cᵏ` coefficient, `k ≥ 1`, whose germ is nonzero
factors as a nonnegative integral power of the coordinate times a `Cᵏ` factor nonzero
at the point. The exponent `n` may be zero. -/
theorem exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul {a f : ℂ → ℂ}
    (hn : 1 ≤ k) (hU : IsOpen U) (ha : ContDiffOn ℝ k a U)
    (hf : DifferentiableOn ℝ f U)
    (heq : ∀ w ∈ U, conjWirtingerDeriv f w 1 = a w * f w) {z : ℂ} (hz : z ∈ U)
    (hne : ¬ ∀ᶠ w in 𝓝 z, f w = 0) :
    ∃ (n : ℕ) (v : ℂ → ℂ), ContDiffAt ℝ k v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, f w = (w - z) ^ n * v w := by
  obtain ⟨g, hg, hA, hgn⟩ :=
    exists_contDiff_analyticAt_exp_neg_mul_not_eventually_eq_zero
      hn hU ha hf heq hz hne
  obtain ⟨n, u, hu, hun, he⟩ := hA.exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hgn
  refine ⟨n, fun w ↦ exp (g w) * u w,
    hg.contDiffAt.cexp.mul (hu.contDiffAt.restrict_scalars ℝ), mul_ne_zero (exp_ne_zero _) hun, ?_⟩
  filter_upwards [he] with w hw
  have := congrArg (fun c : ℂ ↦ exp (g w) * c) hw
  rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at this
  simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using this

/-- A solution of `bar∂ f = a f` with `Cᵏ` coefficient, `k ≥ 1`, that is nonzero outside a compact
set has finitely many zeros. -/
theorem finite_setOfPred_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul {a f : ℂ → ℂ}
    (hn : 1 ≤ k) (ha : ContDiff ℝ k a) (hf : Differentiable ℝ f)
    (heq : ∀ w, conjWirtingerDeriv f w 1 = a w * f w)
    (htail : ∀ᶠ w in cocompact ℂ, f w ≠ 0) : {w | f w = 0}.Finite := by
  have hne : ∃ w ∈ univ, f w ≠ 0 := by simpa using htail.exists
  choose n v hvc hv0 hvf using fun z ↦
    exists_contDiffAt_pow_mul_of_conjWirtingerDeriv_apply_one_eq_mul hn isOpen_univ
      ha.contDiffOn hf.differentiableOn (fun w _ ↦ heq w) (mem_univ z)
      (not_eventually_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul hn isOpen_univ
        isPreconnected_univ ha.contDiffOn hf.differentiableOn (fun w _ ↦ heq w) hne (mem_univ z))
  exact finite_setOfPred_eq_zero_of_eventually_eq_pow_mul
    (fun z ↦ ⟨v z, (hvc z).continuousAt, hv0 z, hvf z⟩) htail

end TauCeti
