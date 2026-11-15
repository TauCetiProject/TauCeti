/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Cokernel

/-!
# The nonzero Fourier modes of a cylinder operator

Let `c : ℝ → ℝ` be a coefficient. The real Cauchy–Riemann operator `∂ₛ + i ∂ₜ - c(s)` on the
cylinder `ℝ × ℝ/ℤ` preserves the Fourier decomposition in the circle variable: since
`i ∂ₜ e^{2πikt} = -2πk e^{2πikt}`, on `u(s, t) = v(s) e^{2πikt}` it acts by

`(∂ₛ + i ∂ₜ - c(s)) u = (v' - (c(s) + 2πk) v) e^{2πikt}`.

So its `k`-th Fourier mode is the operator `d/ds - (c(s) + 2πk)`, with coefficient
`TauCeti.fourierModeCoeff c k`. In the convention `D_A u = u' + A u` of
`TauCeti.WeakDerivStep.trajectoryOperator`, it is the trajectory operator of
`A(s) = -(c(s) + 2πk) • id`, acting on `W^{1,2}(ℝ, E)` for a finite-dimensional real inner
product space `E`, such as `E = ℂⁿ` for maps into `ℂⁿ`.

If `c` is `C¹` with `|c| ≤ 1` and `|c'| ≤ 1`, every nonzero mode has a uniform spectral gap:
`|c(s) + 2πk| ≥ 2π |k| - 1 ≥ 2π - 1` for `k ≠ 0`, while the derivative of the coefficient stays
at most `1`. The coercive estimate for such families then shows that the `k`-th mode operator is
a linear isomorphism from `W^{1,2}(ℝ, E)` onto `L²(ℝ, E)` with

`‖u‖_{W^{1,2}} ≤ ‖u' - (c + 2πk) u‖_{L²}`,

a bound independent of `k ≠ 0` and of `c`. The nonzero modes therefore contribute neither kernel
nor cokernel, and any kernel, cokernel or blow-up of the inverse of the cylinder operator is
carried by its zero mode `d/ds - c(s)`. The hypotheses hold for the coefficients `±tanh s` of the
operators `∂ₛ + i ∂ₜ ± tanh s`, and for the coefficient `a_R` of the operator obtained by gluing
them along a neck of length `2R` (`TauCeti.neckCoeff`, for `R ≥ 0`). There the zero mode is
invertible but its inverse has norm at least `exp (2 R) / 2`
(`TauCeti.WeakDerivStep.exp_div_two_le_of_forall_norm_le_mul_norm_trajectoryOperator_neckCoeff`),
while by this file the inverses of all the other modes are bounded by `1`.

## Main declarations

* `TauCeti.fourierModeCoeff`: the coefficient `c(s) + 2πk` of the `k`-th Fourier mode.
* `TauCeti.WeakDerivStep.norm_le_norm_trajectoryOperator_neg_fourierModeCoeff_smul_id`: for
  `k ≠ 0`, `‖u‖ ≤ ‖u' - (c + 2πk) u‖` on `W^{1,2}(ℝ, E)`.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_neg_fourierModeCoeff_smul_id` and
  `TauCeti.WeakDerivStep.range_trajectoryOperator_neg_fourierModeCoeff_smul_id`: for `k ≠ 0`, the
  `k`-th mode operator has zero kernel and is onto.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Chapter 10 (linear gluing of Cauchy–Riemann operators on
  cylindrical ends, with asymptotic operators `-i ∂ₜ` and their Fourier decomposition).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33 (the operator `d/ds + A(s)` and its spectral decomposition).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Real
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-! ### The coefficient of a Fourier mode -/

/-- The coefficient `c(s) + 2πk` of the `k`-th Fourier mode `d/ds - (c(s) + 2πk)` of the cylinder
operator `∂ₛ + i ∂ₜ - c(s)` on `ℝ × ℝ/ℤ`. -/
def fourierModeCoeff (c : ℝ → ℝ) (k : ℤ) (s : ℝ) : ℝ := c s + 2 * π * k

theorem fourierModeCoeff_def (c : ℝ → ℝ) (k : ℤ) (s : ℝ) :
    fourierModeCoeff c k s = c s + 2 * π * k := (rfl)

/-- The zero mode of `∂ₛ + i ∂ₜ - c(s)` is `d/ds - c(s)`. -/
@[simp]
theorem fourierModeCoeff_zero (c : ℝ → ℝ) : fourierModeCoeff c 0 = c := by
  funext s
  simp [fourierModeCoeff_def]

theorem hasDerivAt_fourierModeCoeff {c : ℝ → ℝ} {c' s : ℝ} (h : HasDerivAt c c' s) (k : ℤ) :
    HasDerivAt (fourierModeCoeff c k) c' s :=
  h.add_const _

@[simp]
theorem deriv_fourierModeCoeff (c : ℝ → ℝ) (k : ℤ) (s : ℝ) :
    deriv (fourierModeCoeff c k) s = deriv c s :=
  deriv_add_const _

theorem contDiff_fourierModeCoeff {c : ℝ → ℝ} {n : WithTop ℕ∞} (hc : ContDiff ℝ n c) (k : ℤ) :
    ContDiff ℝ n (fourierModeCoeff c k) :=
  hc.add contDiff_const

/-- **Nonzero modes have a spectral gap.** If `|c(s)| ≤ 1`, the coefficient of the `k`-th mode
satisfies `|c(s) + 2πk| ≥ 2π |k| - 1`. -/
theorem two_mul_pi_mul_abs_sub_one_le_abs_fourierModeCoeff {c : ℝ → ℝ} {s : ℝ}
    (hc : |c s| ≤ 1) (k : ℤ) : 2 * π * |(k : ℝ)| - 1 ≤ |fourierModeCoeff c k s| := by
  have h := abs_sub_abs_le_abs_sub (2 * π * (k : ℝ)) (-c s)
  rw [abs_mul, abs_of_pos two_pi_pos, abs_neg, sub_neg_eq_add, add_comm] at h
  rw [fourierModeCoeff_def]
  linarith

end TauCeti

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {c : ℝ → ℝ} {k : ℤ}

/-- The gap `2π - 1` of the nonzero modes leaves room for a derivative bound `1` with a margin of
at least `1`: `(2π - 1)² - 1 ≥ 1`. -/
private theorem one_le_two_mul_pi_sub_one_sq_sub_one : 1 ≤ (2 * π - 1) ^ 2 - 1 := by
  nlinarith [two_le_pi]

omit [FiniteDimensional ℝ E] in
/-- The family `A(s) = -(c(s) + 2πk) • id` of a nonzero mode is `C¹` and symmetric, has the
uniform gap `2π - 1`, and its derivative `-c'(s) • id` has quadratic form at most `‖v‖²` in
absolute value. These are the hypotheses of the coercive trajectory estimate. -/
private theorem fourierMode_bounds (hc : ContDiff ℝ 1 c) (hc1 : ∀ s, |c s| ≤ 1)
    (hdc : ∀ s, |deriv c s| ≤ 1) (hk : k ≠ 0) :
    ContDiff ℝ 1 (fun s ↦ -fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E) ∧
      (∀ s, (-fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E).toLinearMap.IsSymmetric) ∧
      (∀ s (v : E), (2 * π - 1) * ‖v‖ ≤
        ‖(-fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E) v‖) ∧
      ∀ s (v : E), |⟪v, deriv (fun s ↦ -fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E) s v⟫_ℝ|
        ≤ 1 * ‖v‖ ^ 2 := by
  refine ⟨(contDiff_fourierModeCoeff hc k).neg.smul contDiff_const,
    fun s x y ↦ by simp [inner_smul_left, inner_smul_right], fun s v ↦ ?_, fun s v ↦ ?_⟩
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hgap := two_mul_pi_mul_abs_sub_one_le_abs_fourierModeCoeff (hc1 s) k
    rw [smul_apply, ContinuousLinearMap.id_apply, norm_smul, norm_neg,
      Real.norm_eq_abs]
    gcongr
    nlinarith [two_pi_pos]
  · have hd : deriv (fun s ↦ -fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E) s =
        -deriv c s • ContinuousLinearMap.id ℝ E :=
      ((hasDerivAt_fourierModeCoeff ((hc.differentiable one_ne_zero s).hasDerivAt) k).neg.smul_const
        (ContinuousLinearMap.id ℝ E)).deriv
    rw [hd, smul_apply, ContinuousLinearMap.id_apply, inner_smul_right,
      real_inner_self_eq_norm_sq, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ‖v‖)]
    exact mul_le_mul_of_nonneg_right (hdc s) (sq_nonneg _)

/-- **Nonzero Fourier modes have uniformly bounded inverses.** Let `c` be a `C¹` coefficient with
`|c| ≤ 1` and `|c'| ≤ 1`, and `k ≠ 0`. Then the `k`-th Fourier mode `D u = u' - (c + 2πk) u` of the
cylinder operator `∂ₛ + i ∂ₜ - c(s)` satisfies `‖u‖ ≤ ‖D u‖` for every `u ∈ W^{1,2}(ℝ, E)`. The
coefficient of the operator is any `L∞` class `AL` of `-(c + 2πk) • id`. -/
theorem norm_le_norm_trajectoryOperator_neg_fourierModeCoeff_smul_id (hc : ContDiff ℝ 1 c)
    (hc1 : ∀ s, |c s| ≤ 1) (hdc : ∀ s, |deriv c s| ≤ 1) (hk : k ≠ 0)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E)
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖u‖ ≤ ‖trajectoryOperator AL u‖ := by
  obtain ⟨hA, hsym, hgap, hsmall⟩ := fourierMode_bounds (E := E) hc hc1 hdc hk
  have h := min_one_mul_norm_le_norm_trajectoryOperator hA hsym
    (by linarith [two_le_pi]) hgap (fun s v ↦ (le_abs_self _).trans (hsmall s v)) AL hAL u
  rwa [min_eq_left one_le_two_mul_pi_sub_one_sq_sub_one, one_mul] at h

/-- **Nonzero Fourier modes have no kernel.** For a `C¹` coefficient `c` with `|c| ≤ 1` and
`|c'| ≤ 1`, and `k ≠ 0`, the `k`-th Fourier mode `u' - (c + 2πk) u` of the cylinder operator
`∂ₛ + i ∂ₜ - c(s)` has zero kernel on `W^{1,2}(ℝ, E)`. -/
theorem ker_trajectoryOperator_neg_fourierModeCoeff_smul_id (hc : ContDiff ℝ 1 c)
    (hc1 : ∀ s, |c s| ≤ 1) (hdc : ∀ s, |deriv c s| ≤ 1) (hk : k ≠ 0)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).ker = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun u hu ↦ norm_le_zero_iff.1 <|
    (norm_le_norm_trajectoryOperator_neg_fourierModeCoeff_smul_id hc hc1 hdc hk AL hAL u).trans
      (by simp only [ContinuousLinearMap.coe_coe] at hu; simp [hu])

/-- **Nonzero Fourier modes have no cokernel.** For a `C¹` coefficient `c` with `|c| ≤ 1` and
`|c'| ≤ 1`, and `k ≠ 0`, the `k`-th Fourier mode `u' - (c + 2πk) u` of the cylinder operator
`∂ₛ + i ∂ₜ - c(s)` maps `W^{1,2}(ℝ, E)` onto `L²(ℝ, E)`. -/
theorem range_trajectoryOperator_neg_fourierModeCoeff_smul_id (hc : ContDiff ℝ 1 c)
    (hc1 : ∀ s, |c s| ≤ 1) (hdc : ∀ s, |deriv c s| ≤ 1) (hk : k ≠ 0)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -fourierModeCoeff c k s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).range = ⊤ := by
  obtain ⟨hA, hsym, hgap, hsmall⟩ := fourierMode_bounds (E := E) hc hc1 hdc hk
  exact LinearMap.range_eq_top.2 <| surjective_trajectoryOperator hA hsym
    (by linarith [two_le_pi]) hgap hsmall
    (by linarith [one_le_two_mul_pi_sub_one_sq_sub_one]) AL hAL

end TauCeti.WeakDerivStep
