/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Variance

/-!
# The first two moments of a pencil transform

This file reads the mean and the variance off the moment-generating function of a real random
variable `X` whose transform is a product `∏ j, (1 - 2 * t * lam j) ^ (-a j)` wherever every
factor is positive. The spectral decomposition of a quadratic form produces transforms of this
shape, the factors being the eigenvalues of a matrix pencil `1 - 2 * t * B`; they occur for the
Gaussian quadratic forms, the chi-squared laws and the Wishart trace statistics, and only the
exponents differ between those.

The set where every factor is positive is open and contains the origin, so where the transform
is finite there the cumulant-generating function is `∑ j, -a j * log (1 - 2 * t * lam j)` on a
neighbourhood of the origin, and its first two derivatives there are the mean and the
variance.

## Main results

* `TauCeti.zero_mem_interior_integrableExpSet_of_forall_mul_lt_one` — exponential integrability
  on the domain of the product puts the origin in the interior of the
  exponential-integrability domain, which is what makes the transform differentiable there;
* `TauCeti.hasDerivAt_sum_log` and `TauCeti.hasDerivAt_sum_div` — the first two derivatives of
  the sum of logarithms that the cumulant-generating function equals there;
* `TauCeti.integral_eq_of_mgf_eq_prod_rpow` — the mean is `2 * ∑ j, a j * lam j`;
* `TauCeti.variance_eq_of_mgf_eq_prod_rpow` — the variance is `4 * ∑ j, a j * lam j ^ 2`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace TauCeti

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {lam a : ι → ℝ}

/-! ### The domain of the product -/

/-- The set of real `t` at which every factor `1 - 2 * t * lam j` of a pencil product is
positive is open. -/
theorem isOpen_setOf_forall_mul_lt_one [Finite ι] (lam : ι → ℝ) :
    IsOpen {t : ℝ | ∀ j, 2 * t * lam j < 1} := by
  have hinter : {t : ℝ | ∀ j, 2 * t * lam j < 1} = ⋂ j, {t : ℝ | 2 * t * lam j < 1} := by
    ext t
    simp
  rw [hinter]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

/-- The origin lies in the domain of a pencil product: there every factor equals one. -/
theorem zero_mem_setOf_forall_mul_lt_one (lam : ι → ℝ) :
    (0 : ℝ) ∈ {t : ℝ | ∀ j, 2 * t * lam j < 1} := fun j => by norm_num

/-- The domain of a pencil product is a neighbourhood of the origin, being open and containing
it. -/
theorem setOf_forall_mul_lt_one_mem_nhds_zero [Finite ι] (lam : ι → ℝ) :
    {t : ℝ | ∀ j, 2 * t * lam j < 1} ∈ 𝓝 (0 : ℝ) :=
  (isOpen_setOf_forall_mul_lt_one lam).mem_nhds (zero_mem_setOf_forall_mul_lt_one lam)

/-- A random variable whose exponential moments are finite on the domain of a pencil product has
the origin interior to its exponential-integrability domain, hence finite moments of every order
and an analytic transform at the origin. -/
theorem zero_mem_interior_integrableExpSet_of_forall_mul_lt_one [Finite ι] (lam : ι → ℝ)
    (h : ∀ t : ℝ, (∀ j, 2 * t * lam j < 1) → Integrable (fun ω => Real.exp (t * X ω)) μ) :
    0 ∈ interior (integrableExpSet X μ) :=
  interior_maximal (fun t ht => h t ht) (isOpen_setOf_forall_mul_lt_one lam)
    (zero_mem_setOf_forall_mul_lt_one lam)

/-! ### Differentiating the cumulant-generating function -/

variable [Fintype ι]

/-- On the domain of the product, the cumulant-generating function of a pencil transform is
`∑ j, -a j * log (1 - 2 * t * lam j)`. -/
private theorem cgf_eventuallyEq_sum_log
    (hmgf : ∀ t : ℝ, (∀ j, 2 * t * lam j < 1) →
      mgf X μ t = ∏ j, (1 - 2 * t * lam j) ^ (-a j)) :
    cgf X μ =ᶠ[𝓝 0] fun t => ∑ j, -a j * Real.log (1 - 2 * t * lam j) := by
  filter_upwards [setOf_forall_mul_lt_one_mem_nhds_zero lam] with t ht
  have hpos : ∀ j, 0 < 1 - 2 * t * lam j := fun j => sub_pos.2 (ht j)
  rw [cgf, hmgf t ht, Real.log_prod fun j _ => (Real.rpow_pos_of_pos (hpos j) _).ne']
  exact Finset.sum_congr rfl fun j _ => Real.log_rpow (hpos j) _

/-- The derivative of `fun s => ∑ j, -a j * log (1 - 2 * s * lam j)`, the sum of logarithms that
a pencil cumulant-generating function equals on the domain of its product. -/
theorem hasDerivAt_sum_log {t : ℝ} (ht : ∀ j, 2 * t * lam j < 1) :
    HasDerivAt (fun s : ℝ => ∑ j, -a j * Real.log (1 - 2 * s * lam j))
      (∑ j, -a j * (-(2 * lam j) / (1 - 2 * t * lam j))) t := by
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.const_mul _ ?_
  have hlin : HasDerivAt (fun s : ℝ => 1 - 2 * s * lam j) (-(2 * lam j)) t := by
    simpa using (((hasDerivAt_id t).const_mul (2 : ℝ)).mul_const (lam j)).const_sub 1
  exact hlin.log (sub_pos.2 (ht j)).ne'

/-- The derivative at the origin of `fun s => ∑ j, -a j * (-(2 * lam j) / (1 - 2 * s * lam j))`,
the derivative of the sum of logarithms above. Every factor of the product equals one at the
origin, which is why the value is a polynomial in the data. -/
theorem hasDerivAt_sum_div (lam a : ι → ℝ) :
    HasDerivAt (fun s : ℝ => ∑ j, -a j * (-(2 * lam j) / (1 - 2 * s * lam j)))
      (∑ j, -a j * -(4 * lam j ^ 2)) 0 := by
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.const_mul _ ?_
  have hlin : HasDerivAt (fun s : ℝ => 1 - 2 * s * lam j) (-(2 * lam j)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).mul_const (lam j)).const_sub 1
  have hne : (1 : ℝ) - 2 * 0 * lam j ≠ 0 := by norm_num
  simp only [div_eq_mul_inv]
  exact ((hlin.inv hne).const_mul (-(2 * lam j))).congr_deriv (by norm_num; ring)

/-! ### The mean and the variance -/

variable [IsProbabilityMeasure μ]

/-- **The mean of a pencil transform.** A random variable whose moment-generating function is
`∏ j, (1 - 2 * t * lam j) ^ (-a j)` wherever every factor is positive has mean
`2 * ∑ j, a j * lam j`. -/
theorem integral_eq_of_mgf_eq_prod_rpow (hX : 0 ∈ interior (integrableExpSet X μ))
    (hmgf : ∀ t : ℝ, (∀ j, 2 * t * lam j < 1) →
      mgf X μ t = ∏ j, (1 - 2 * t * lam j) ^ (-a j)) :
    μ[X] = 2 * ∑ j, a j * lam j := by
  have hderiv : deriv (cgf X μ) 0 = μ[X] := by
    rw [deriv_cgf_zero hX]
    simp
  rw [← hderiv, (cgf_eventuallyEq_sum_log hmgf).deriv_eq,
    (hasDerivAt_sum_log (a := a) (zero_mem_setOf_forall_mul_lt_one lam)).deriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_zero, zero_mul, sub_zero, div_one]
  ring

/-- **The variance of a pencil transform.** A random variable whose moment-generating function is
`∏ j, (1 - 2 * t * lam j) ^ (-a j)` wherever every factor is positive has variance
`4 * ∑ j, a j * lam j ^ 2`. -/
theorem variance_eq_of_mgf_eq_prod_rpow (hX : 0 ∈ interior (integrableExpSet X μ))
    (hmgf : ∀ t : ℝ, (∀ j, 2 * t * lam j < 1) →
      mgf X μ t = ∏ j, (1 - 2 * t * lam j) ^ (-a j)) :
    Var[X; μ] = 4 * ∑ j, a j * lam j ^ 2 := by
  have hvar : iteratedDeriv 2 (cgf X μ) 0 = Var[X; μ] := by
    rw [iteratedDeriv_two_cgf hX, deriv_cgf_zero hX, mgf_zero',
      variance_eq_sub (memLp_of_mem_interior_integrableExpSet hX 2)]
    simp
  have hsecond : deriv (deriv (cgf X μ)) 0 = ∑ j, -a j * -(4 * lam j ^ 2) := by
    have hdderiv : deriv (cgf X μ) =ᶠ[𝓝 0]
        fun s : ℝ => ∑ j, -a j * (-(2 * lam j) / (1 - 2 * s * lam j)) := by
      filter_upwards [(cgf_eventuallyEq_sum_log hmgf).eventually_nhds,
        setOf_forall_mul_lt_one_mem_nhds_zero lam] with s hs hst
      rw [Filter.EventuallyEq.deriv_eq hs, (hasDerivAt_sum_log (a := a) hst).deriv]
    rw [hdderiv.deriv_eq, (hasDerivAt_sum_div lam a).deriv]
  rw [← hvar, iteratedDeriv_succ, iteratedDeriv_one, hsecond, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end TauCeti
