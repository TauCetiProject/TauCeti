/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Analytic continuation of a moment-generating function

The moment-generating function of a real random variable `X` is the restriction to the real axis
of `ProbabilityTheory.complexMGF X μ`, which is analytic on the vertical strip over the interior
of the exponential-integrability domain.  A closed form for `mgf X μ` on a real interval therefore
determines `complexMGF X μ` on the whole strip above it, as soon as the proposed formula is itself
analytic there.  For an a.e.-measurable `X`, `complexMGF X μ` on the imaginary axis is the
characteristic function of the law of `X`, so this is the standard route from a moment-generating
function to a characteristic function.

`TauCeti.eqOn_complexMGF_of_eqOn_mgf` packages that continuation step.  The rest of the file
carries it out for the closed form

`mgf X μ t = ∏ j, (1 - 2 * t * lam j) ^ (-a j)`,

a product of real powers of a pencil of linear factors.  This is the shape taken by the trace
statistic of a Wishart matrix and, more generally, by any weighted sum of independent scaled
chi-squared variables with weights `lam j`.  On the imaginary axis the answer must be written as
an exponential of a *sum* of principal logarithms rather than as a single complex power of the
product: multiplying the factors before taking the logarithm can cross the branch cut.

## Main results

* `TauCeti.eqOn_complexMGF_of_eqOn_mgf`: an analytic function agreeing with `mgf X μ` on an open
  convex set of reals inside the exponential-integrability domain agrees with `complexMGF X μ` on
  the vertical strip above that set.
* `TauCeti.complexMGF_eq_exp_of_mgf_eq_prod_rpow`: the value of `complexMGF X μ` at any point of
  the strip on which the pencil `1 - 2 * z.re * lam j` is positive.
* `TauCeti.complexMGF_I_eq_exp_of_mgf_eq_prod_rpow`: its value at `Complex.I`, which for a
  measurable `X` is the characteristic function of the law of `X` at `1`.

## References

* E. Mayerhofer, *Reforming the Wishart characteristic function*,
  [arXiv:1901.09347](https://arxiv.org/abs/1901.09347), for the branch analysis that forces the
  sum-of-logarithms form.
* The identity-theorem argument follows `ProbabilityTheory.eqOn_complexMGF_of_mgf'` in
  `Mathlib/Probability/Moments/ComplexMGF.lean`.
-/

public section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-! ### Continuation from a real interval to a vertical strip -/

/-- **Analytic continuation of a moment-generating function.**  If `g` is analytic on the vertical
strip over an open convex set `s` of reals on which the exponential moments of `X` are finite, and
`g` agrees with `mgf X μ` on `s`, then `g` agrees with `complexMGF X μ` on the whole strip. -/
theorem eqOn_complexMGF_of_eqOn_mgf {s : Set ℝ} {g : ℂ → ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    (hsub : s ⊆ integrableExpSet X μ) (hg : AnalyticOnNhd ℂ g {z : ℂ | z.re ∈ s})
    (hmgf : ∀ t ∈ s, g t = mgf X μ t) :
    EqOn (complexMGF X μ) g {z : ℂ | z.re ∈ s} := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  have hX : AnalyticOnNhd ℂ (complexMGF X μ) {z : ℂ | z.re ∈ s} :=
    analyticOnNhd_complexMGF.mono fun _ hz ↦ interior_maximal hsub hs hz
  have hconn : IsPreconnected {z : ℂ | z.re ∈ s} :=
    (hconv.linear_preimage Complex.reLm).isPreconnected
  refine hX.eqOn_of_preconnected_of_frequently_eq hg hconn (z₀ := (t₀ : ℂ)) (by simpa using ht₀) ?_
  have hreal : ∀ᶠ x : ℝ in 𝓝[≠] t₀, complexMGF X μ x = g x := by
    filter_upwards [nhdsWithin_le_nhds (hs.mem_nhds ht₀)] with x hx
    rw [complexMGF_ofReal, hmgf x hx]
  exact (Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    fun _ hx ↦ by simpa using hx).frequently hreal.frequently

/-! ### A product of real powers of a linear pencil -/

/-- The set of reals at which every factor of the pencil `1 - 2 * t * lam j` is positive is
open. -/
private theorem isOpen_setOf_forall_pencil_pos {ι : Type*} [Finite ι] (lam : ι → ℝ) :
    IsOpen {t : ℝ | ∀ j, 0 < 1 - 2 * t * lam j} := by
  have : {t : ℝ | ∀ j, 0 < 1 - 2 * t * lam j}
      = ⋂ j, (fun t : ℝ ↦ 1 - 2 * t * lam j) ⁻¹' Ioi 0 := by
    ext t; simp
  rw [this]
  exact isOpen_iInter_of_finite fun j ↦ isOpen_Ioi.preimage (by fun_prop)

private theorem convex_setOf_forall_pencil_pos {ι : Type*} (lam : ι → ℝ) :
    Convex ℝ {t : ℝ | ∀ j, 0 < 1 - 2 * t * lam j} := by
  have : {t : ℝ | ∀ j, 0 < 1 - 2 * t * lam j} = ⋂ j, {t : ℝ | 2 * lam j * t < 1} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_congr' fun j ↦ by constructor <;> intro h <;> nlinarith
  rw [this]
  exact convex_iInter fun j ↦
    convex_halfSpace_lt ⟨fun _ _ ↦ by ring, fun _ _ ↦ by simp only [smul_eq_mul]; ring⟩ 1

variable {ι : Type*} [Fintype ι]

/-- On the positivity region of the pencil, the exponential of minus the sum of the principal
logarithms is the real product of powers. -/
private theorem exp_neg_sum_mul_log_eq (lam a : ι → ℝ) {t : ℝ}
    (ht : ∀ j, 0 < 1 - 2 * t * lam j) :
    cexp (-∑ j, (a j : ℂ) * Complex.log (1 - 2 * (t : ℂ) * (lam j : ℂ)))
      = ((∏ j, (1 - 2 * t * lam j) ^ (-a j) : ℝ) : ℂ) := by
  have hprod : Real.exp (-∑ j, a j * Real.log (1 - 2 * t * lam j))
      = ∏ j, (1 - 2 * t * lam j) ^ (-a j) := by
    rw [neg_eq_neg_one_mul, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Real.rpow_def_of_pos (ht j)]
    congr 1
    ring
  rw [← hprod, Complex.ofReal_exp]
  congr 1
  push_cast
  refine congrArg Neg.neg (Finset.sum_congr rfl fun j _ ↦ ?_)
  congr 1
  rw [Complex.ofReal_log (ht j).le]
  congr 1
  push_cast
  ring

private theorem analyticOnNhd_exp_neg_sum_mul_log (lam a : ι → ℝ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ cexp (-∑ j, (a j : ℂ) * Complex.log (1 - 2 * z * (lam j : ℂ))))
      {z : ℂ | z.re ∈ {t : ℝ | ∀ j, 0 < 1 - 2 * t * lam j}} := by
  refine AnalyticOnNhd.cexp (AnalyticOnNhd.neg (Finset.analyticOnNhd_fun_sum _ fun j _ ↦ ?_))
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.log (1 - 2 * z * (lam j : ℂ)))
      {z : ℂ | z.re ∈ {t : ℝ | ∀ j, 0 < 1 - 2 * t * lam j}} := by
    refine AnalyticOnNhd.clog (by fun_prop) fun z hz ↦ ?_
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    have hre : (1 - 2 * z * (lam j : ℂ)).re = 1 - 2 * z.re * lam j := by simp
    rw [hre]
    exact hz j
  exact (analyticOnNhd_const (v := (a j : ℂ))).mul hlog

/-- **Continuation of a product-of-powers moment-generating function.**  If the
moment-generating function of `X` is the product `∏ j, (1 - 2 * t * lam j) ^ (-a j)` wherever
every factor of the pencil is positive, then `complexMGF X μ` is given at every point of the
corresponding vertical strip by the exponential of minus the sum of the principal logarithms.

The value is *not* a principal complex power of `∏ j, (1 - 2 * z * lam j)`: collecting the factors
before taking the logarithm can cross the branch cut. -/
theorem complexMGF_eq_exp_of_mgf_eq_prod_rpow (lam a : ι → ℝ)
    (hmgf : ∀ t : ℝ, (∀ j, 0 < 1 - 2 * t * lam j) →
      mgf X μ t = ∏ j, (1 - 2 * t * lam j) ^ (-a j))
    {z : ℂ} (hz : ∀ j, 0 < 1 - 2 * z.re * lam j) :
    complexMGF X μ z = cexp (-∑ j, (a j : ℂ) * Complex.log (1 - 2 * z * (lam j : ℂ))) := by
  refine eqOn_complexMGF_of_eqOn_mgf (isOpen_setOf_forall_pencil_pos lam)
    (convex_setOf_forall_pencil_pos lam) (fun t ht ↦ ?_)
    (analyticOnNhd_exp_neg_sum_mul_log lam a) (fun t ht ↦ ?_) hz
  · -- A nonzero moment-generating function forces the exponential moment to be finite.
    by_contra hcon
    have hpos : 0 < ∏ j, (1 - 2 * t * lam j) ^ (-a j) :=
      Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (ht j) _
    rw [← hmgf t ht, mgf_undef hcon] at hpos
    exact hpos.false
  · rw [exp_neg_sum_mul_log_eq lam a ht, hmgf t ht]

/-- The value of `complexMGF X μ` at `Complex.I`, for a moment-generating function that is a
product of real powers of a linear pencil.  Every factor `1 - 2 * I * lam j` has real part `1`, so
the principal logarithms are unambiguous.

For a measurable `X` this is the characteristic function of the law of `X` at `1`, by
`ProbabilityTheory.complexMGF_mul_I`. -/
theorem complexMGF_I_eq_exp_of_mgf_eq_prod_rpow (lam a : ι → ℝ)
    (hmgf : ∀ t : ℝ, (∀ j, 0 < 1 - 2 * t * lam j) →
      mgf X μ t = ∏ j, (1 - 2 * t * lam j) ^ (-a j)) :
    complexMGF X μ Complex.I =
      cexp (-∑ j, (a j : ℂ) * Complex.log (1 - 2 * Complex.I * (lam j : ℂ))) :=
  complexMGF_eq_exp_of_mgf_eq_prod_rpow lam a hmgf fun j ↦ by simp

end TauCeti
