/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.MeasureTheory.Integral.Dilation
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The estimate `‖D²u‖₁ ≤ C ‖Δu‖₁` fails

For `1 < p < ∞` the second derivatives of a Schwartz function on `ℝⁿ` are controlled by its
Laplacian, `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`
(`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`). This file proves that the
estimate fails at the endpoint `p = 1` in every dimension `n ≥ 2`: for every `C` there is a smooth
compactly supported real function `u` with `C ‖Δu‖_{L¹} < ‖D²u‖_{L¹}`
(`TauCeti.exists_contDiff_hasCompactSupport_mul_eLpNorm_laplacian_lt_eLpNorm_iteratedFDeriv_two`),
so no constant works for all real Schwartz functions
(`TauCeti.not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_one`). In dimension one the
estimate holds with `C = 1`, since there `D²u` and `Δu = u''` have the same pointwise norm. The
failure matches the endpoint behaviour of Calderón–Zygmund operators, which are not bounded on
`L¹`: on Schwartz functions `∂ᵢ∂ⱼ = -Rᵢ Rⱼ Δ` with the Riesz transforms `Rᵢ`.

## The construction

The second derivatives of the fundamental solution `Φ` of the Laplacian are homogeneous of degree
`-n`, so they are not integrable near the origin, while `ΔΦ = 0` away from it. The test functions
are smoothed and cut-off versions of `Φ`. Write `σ = ‖x‖²` and, for `ε > 0`, `s = σ + ε²`. Let
`ψ` be a smooth cutoff equal to `1` for `σ ≤ 1/4` and to `0` for `σ ≥ 1`, and let `u_ε` be the
radial function `x ↦ F(‖x‖²)` whose profile `F` has `F(σ) = 0` for `σ ≥ 1` and

`F'(σ) = k(σ) = s^(-n/2) ψ(σ)`.

So `u_ε` is smooth and supported in the closed unit ball. Its derivatives are those of a radial
function: `D²u_ε(x)(h, h) = 4 k'(σ) ⟪x, h⟫² + 2 k(σ) ‖h‖²` and `Δu_ε(x) = 4 σ k'(σ) + 2 n k(σ)`,
that is

`Δu_ε(x) = 2 n ε² s^(-n/2 - 1) ψ(σ) + 4 σ s^(-n/2) ψ'(σ)`.

* **The Laplacian stays bounded in `L¹`.** The first term is `2 n ε^(-n) G(x / ε)` up to the
  factor `ψ ≤ 1`, with `G(y) = (1 + ‖y‖²)^(-(n + 2)/2)` integrable, so its integral is at most
  `2 n ∫ G`, whatever `ε`. The second term vanishes unless `1/4 ≤ σ ≤ 1`, where it is bounded
  independently of `ε`.
* **The Hessian does not.** For `‖x‖ < 1/2` and a unit vector `h` orthogonal to `x`, which exists
  since `n ≥ 2`, `D²u_ε(x)(h, h) = 2 s^(-n/2)`. As `ε → 0` these functions increase to
  `2 ‖x‖^(-n)`, whose integral over the ball of radius `1/2` is infinite
  (`TauCeti.setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior`), so by monotone convergence
  `‖D²u_ε‖_{L¹} → ∞`.

## Main declarations

* `TauCeti.exists_contDiff_hasCompactSupport_mul_eLpNorm_laplacian_lt_eLpNorm_iteratedFDeriv_two`:
  for every `C` a smooth compactly supported real function with `C ‖Δu‖₁ < ‖D²u‖₁`.
* `TauCeti.not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_one`: no constant gives
  `‖D²u‖₁ ≤ C ‖Δu‖₁` for all real Schwartz functions.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  University Press, 1970, Chapter III, §1 (the second derivatives of the Newtonian potential as
  compositions of Riesz transforms).
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Metric Module Set Topology
open scoped ENNReal NNReal ContDiff SchwartzMap

/-! ### The radial profile -/

/-- The cutoff `ψ`, equal to `1` on `(-∞, 1/4]` and to `0` on `[1, ∞)`. -/
private def cutoff (σ : ℝ) : ℝ :=
  Real.smoothTransition (4 * (1 - σ) / 3)

private theorem cutoff_eq_one {σ : ℝ} (h : σ ≤ 1 / 4) : cutoff σ = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

private theorem cutoff_eq_zero {σ : ℝ} (h : 1 ≤ σ) : cutoff σ = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

private theorem cutoff_nonneg (σ : ℝ) : 0 ≤ cutoff σ :=
  Real.smoothTransition.nonneg _

private theorem cutoff_le_one (σ : ℝ) : cutoff σ ≤ 1 :=
  Real.smoothTransition.le_one _

private theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private theorem deriv_cutoff_eq_zero {σ : ℝ} (h : σ < 1 / 4 ∨ 1 < σ) : deriv cutoff σ = 0 := by
  rcases h with h | h
  · have : cutoff =ᶠ[𝓝 σ] fun _ => 1 :=
      Filter.eventually_of_mem (Iio_mem_nhds h) fun τ hτ => cutoff_eq_one (le_of_lt hτ)
    rw [this.deriv_eq, deriv_const]
  · have : cutoff =ᶠ[𝓝 σ] fun _ => 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds h) fun τ hτ => cutoff_eq_zero (le_of_lt hτ)
    rw [this.deriv_eq, deriv_const]

/-- The derivative of the cutoff is bounded. -/
private theorem exists_abs_deriv_cutoff_le : ∃ K : ℝ, ∀ σ, |deriv cutoff σ| ≤ K := by
  have hsupp : HasCompactSupport (deriv cutoff) :=
    HasCompactSupport.intro (isCompact_Icc (a := 1 / 4) (b := 1)) fun σ hσ =>
      deriv_cutoff_eq_zero (by
        simp only [mem_Icc, not_and_or, not_le] at hσ
        exact hσ)
  obtain ⟨K, hK⟩ := (contDiff_cutoff.continuous_deriv (by simp)).bounded_above_of_compact_support
    hsupp
  exact ⟨K, fun σ => by simpa [Real.norm_eq_abs] using hK σ⟩

variable {n : ℕ} {ε : ℝ}

/-- The derivative `k(σ) = (σ + ε²)^(-n/2) ψ(σ)` of the radial profile. -/
private def kernel (n : ℕ) (ε σ : ℝ) : ℝ :=
  (σ + ε ^ 2) ^ (-(n : ℝ) / 2) * cutoff σ

/-- The radial profile `F(σ) = ∫_1^σ k`. -/
private def profile (n : ℕ) (ε σ : ℝ) : ℝ :=
  ∫ τ in (1 : ℝ)..σ, kernel n ε τ

private theorem contDiffAt_kernel {σ : ℝ} (hσ : -ε ^ 2 < σ) :
    ContDiffAt ℝ ∞ (kernel n ε) σ :=
  ((contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (by simp; linarith)).mul
    contDiff_cutoff.contDiffAt

private theorem hasDerivAt_kernel {σ : ℝ} (hσ : -ε ^ 2 < σ) :
    HasDerivAt (kernel n ε)
      (-(n : ℝ) / 2 * (σ + ε ^ 2) ^ (-(n : ℝ) / 2 - 1) * cutoff σ +
        (σ + ε ^ 2) ^ (-(n : ℝ) / 2) * deriv cutoff σ) σ := by
  have h₁ : HasDerivAt (fun τ : ℝ => (τ + ε ^ 2) ^ (-(n : ℝ) / 2))
      (1 * (-(n : ℝ) / 2) * (σ + ε ^ 2) ^ (-(n : ℝ) / 2 - 1)) σ :=
    ((hasDerivAt_id σ).add_const (ε ^ 2)).rpow_const (Or.inl (by simp; linarith))
  have h₂ : HasDerivAt cutoff (deriv cutoff σ) σ :=
    ((contDiff_cutoff.differentiable (by simp)) σ).hasDerivAt
  exact (h₁.mul h₂).congr_deriv (by ring)

private theorem hasDerivAt_profile {σ : ℝ} (hσ : -ε ^ 2 < σ) :
    HasDerivAt (profile n ε) (kernel n ε σ) σ := by
  have hcont : ContinuousOn (kernel n ε) (Ioi (-ε ^ 2)) := fun τ hτ =>
    (contDiffAt_kernel (n := n) hτ).continuousAt.continuousWithinAt
  have h1 : -ε ^ 2 < 1 := by nlinarith [sq_nonneg ε]
  refine intervalIntegral.integral_hasDerivAt_right ?_
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi σ hσ)
    (contDiffAt_kernel (n := n) hσ).continuousAt
  refine (hcont.mono fun τ (hτ : τ ∈ uIcc (1 : ℝ) σ) => ?_).intervalIntegrable
  rw [mem_uIcc] at hτ
  rcases hτ with hτ | hτ
  · exact lt_of_lt_of_le h1 hτ.1
  · exact lt_of_lt_of_le hσ hτ.1

private theorem contDiffAt_profile {σ : ℝ} (hσ : -ε ^ 2 < σ) :
    ContDiffAt ℝ ∞ (profile n ε) σ := by
  have hU : IsOpen (Ioi (-ε ^ 2)) := isOpen_Ioi
  have hon : ContDiffOn ℝ ∞ (profile n ε) (Ioi (-ε ^ 2)) :=
    (contDiffOn_infty_iff_deriv_of_isOpen hU).2
      ⟨fun τ hτ => (hasDerivAt_profile hτ).differentiableAt.differentiableWithinAt,
        ContDiffOn.congr (f := kernel n ε)
          (fun τ hτ => (contDiffAt_kernel (n := n) hτ).contDiffWithinAt)
          fun τ hτ => (hasDerivAt_profile hτ).deriv⟩
  exact hon.contDiffAt (hU.mem_nhds (mem_Ioi.2 hσ))

private theorem deriv_deriv_profile {σ : ℝ} (hσ : -ε ^ 2 < σ) :
    deriv (deriv (profile n ε)) σ = deriv (kernel n ε) σ :=
  Filter.EventuallyEq.deriv_eq <|
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (mem_Ioi.2 hσ)) fun _ hτ =>
      (hasDerivAt_profile hτ).deriv

private theorem profile_eq_zero {σ : ℝ} (h : 1 ≤ σ) : profile n ε σ = 0 := by
  rw [profile, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
    intervalIntegral.integral_zero]
  intro τ hτ
  rw [uIcc_of_le h] at hτ
  simp [kernel, cutoff_eq_zero hτ.1]

/-! ### The test functions -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The test function `u_ε(x) = F(‖x‖²)`. -/
private def testFunction (n : ℕ) (ε : ℝ) (x : V) : ℝ :=
  profile n ε (‖x‖ ^ 2)

omit [InnerProductSpace ℝ V] in
private theorem neg_sq_lt_norm_sq (hε : 0 < ε) (x : V) : -ε ^ 2 < ‖x‖ ^ 2 :=
  lt_of_lt_of_le (neg_neg_of_pos (pow_pos hε 2)) (sq_nonneg _)

omit [InnerProductSpace ℝ V] in
private theorem contDiffAt_profile_norm_sq (hε : 0 < ε) (x : V) :
    ContDiffAt ℝ ∞ (profile n ε) (‖x‖ ^ 2) :=
  contDiffAt_profile (neg_sq_lt_norm_sq hε x)

private theorem contDiff_testFunction (hε : 0 < ε) : ContDiff ℝ ∞ (testFunction (V := V) n ε) :=
  contDiff_iff_contDiffAt.2 fun x =>
    (contDiffAt_profile_norm_sq hε x).comp x (contDiff_norm_sq ℝ).contDiffAt

/-- The second derivative of the test function on the diagonal. -/
private theorem iteratedFDeriv_two_testFunction_apply (hε : 0 < ε) (x h : V) :
    iteratedFDeriv ℝ 2 (testFunction n ε) x ![h, h] =
      4 * deriv (kernel n ε) (‖x‖ ^ 2) * ⟪x, h⟫_ℝ ^ 2 + 2 * kernel n ε (‖x‖ ^ 2) * ‖h‖ ^ 2 := by
  have hφ : ContDiffAt ℝ 2 (profile n ε) (‖x‖ ^ 2) :=
    (contDiffAt_profile_norm_sq hε x).of_le (by simp)
  have h2 : iteratedDeriv 2 (profile n ε) = deriv (deriv (profile n ε)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- By definition, the test function is the profile composed with the squared norm.
  have hcomp : testFunction (V := V) n ε = profile n ε ∘ fun y : V => ‖y‖ ^ 2 := rfl
  have hd2 : fderiv ℝ (fderiv ℝ fun y : V => ‖y‖ ^ 2) x = (2 • innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) := by
    rw [fderiv_norm_sq]
    exact (2 • innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).fderiv
  rw [iteratedFDeriv_two_apply, hcomp,
    fderiv_fderiv_scalar_comp_apply (f := fun y : V => ‖y‖ ^ 2) (x := x) hφ
      (contDiff_norm_sq ℝ).contDiffAt, h2,
    deriv_deriv_profile (neg_sq_lt_norm_sq hε x),
    (hasDerivAt_profile (neg_sq_lt_norm_sq hε x)).deriv, hd2, fderiv_norm_sq_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_apply, innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul]
  rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  push_cast
  ring

variable [FiniteDimensional ℝ V]

private theorem hasCompactSupport_testFunction : HasCompactSupport (testFunction (V := V) n ε) :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun x hx => by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact profile_eq_zero (one_le_pow₀ hx.le)

/-- The Laplacian of the test function. -/
private theorem laplacian_testFunction (hε : 0 < ε) (x : V) :
    Δ (testFunction (V := V) (finrank ℝ V) ε) x =
      2 * finrank ℝ V * ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(finrank ℝ V : ℝ) / 2 - 1) *
          cutoff (‖x‖ ^ 2) +
        4 * ‖x‖ ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(finrank ℝ V : ℝ) / 2) * deriv cutoff (‖x‖ ^ 2) := by
  set b := stdOrthonormalBasis ℝ V
  set n := finrank ℝ V
  have hs : ‖x‖ ^ 2 + ε ^ 2 ≠ 0 := by positivity
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x]
  simp_rw [iteratedFDeriv_two_testFunction_apply hε, b.orthonormal.norm_eq_one, one_pow,
    mul_one, Finset.sum_add_distrib, ← Finset.mul_sum, b.sum_sq_inner_left x,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    (hasDerivAt_kernel (n := n) (neg_sq_lt_norm_sq hε x)).deriv, kernel]
  have hsplit : (‖x‖ ^ 2 + ε ^ 2) ^ (-(n : ℝ) / 2) =
      (‖x‖ ^ 2 + ε ^ 2) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(n : ℝ) / 2 - 1) := by
    rw [Real.rpow_sub_one hs, mul_div_cancel₀ _ hs]
  rw [hsplit]
  ring

/-- **A pointwise bound for the Laplacian of the test function**, by its main term and a cutoff
term that is bounded independently of `ε` and supported in the closed unit ball. -/
private theorem abs_laplacian_testFunction_le (hε : 0 < ε) {K : ℝ}
    (hK : ∀ σ, |deriv cutoff σ| ≤ K) (x : V) :
    |Δ (testFunction (V := V) (finrank ℝ V) ε) x| ≤
      2 * finrank ℝ V * (ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-((finrank ℝ V : ℝ) + 2) / 2)) +
        (closedBall (0 : V) 1).indicator
          (fun _ => 4 * (1 / 4 : ℝ) ^ (-(finrank ℝ V : ℝ) / 2) * K) x := by
  set n := finrank ℝ V
  set σ := ‖x‖ ^ 2
  set s := σ + ε ^ 2
  have hσ0 : 0 ≤ σ := sq_nonneg _
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  -- The main term: the cutoff lies in `[0, 1]`.
  have hmain : |2 * n * ε ^ 2 * s ^ (-(n : ℝ) / 2 - 1) * cutoff σ| ≤
      2 * n * (ε ^ 2 * s ^ (-((n : ℝ) + 2) / 2)) := by
    rw [show -((n : ℝ) + 2) / 2 = -(n : ℝ) / 2 - 1 by ring,
      abs_of_nonneg (mul_nonneg (by positivity) (cutoff_nonneg σ))]
    calc 2 * n * ε ^ 2 * s ^ (-(n : ℝ) / 2 - 1) * cutoff σ
        ≤ 2 * n * ε ^ 2 * s ^ (-(n : ℝ) / 2 - 1) * 1 := by
          gcongr
          exact cutoff_le_one σ
      _ = _ := by ring
  -- The cutoff term: `ψ'` vanishes unless `1/4 ≤ σ ≤ 1`, where `s ≥ 1/4`.
  have hcut : |4 * σ * s ^ (-(n : ℝ) / 2) * deriv cutoff σ| ≤
      (closedBall (0 : V) 1).indicator (fun _ => 4 * (1 / 4 : ℝ) ^ (-(n : ℝ) / 2) * K) x := by
    by_cases hmid : 1 / 4 ≤ σ ∧ σ ≤ 1
    · have hx : x ∈ closedBall (0 : V) 1 := by
        rw [mem_closedBall, dist_zero_right]
        exact (pow_le_one_iff_of_nonneg (norm_nonneg x) two_ne_zero).1 hmid.2
      rw [indicator_of_mem hx, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg hσ0, abs_of_nonneg (by positivity : 0 ≤ s ^ (-(n : ℝ) / 2))]
      have hspow : s ^ (-(n : ℝ) / 2) ≤ (1 / 4 : ℝ) ^ (-(n : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith [sq_nonneg ε])
          (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
      calc 4 * σ * s ^ (-(n : ℝ) / 2) * |deriv cutoff σ|
          ≤ 4 * 1 * (1 / 4 : ℝ) ^ (-(n : ℝ) / 2) * K := by
            gcongr
            · exact hmid.2
            · exact hK σ
        _ = _ := by ring
    · have hzero : deriv cutoff σ = 0 :=
        deriv_cutoff_eq_zero (by
          rw [not_and_or, not_le, not_le] at hmid
          exact hmid)
      rw [hzero, mul_zero, abs_zero]
      exact indicator_nonneg (fun _ _ => by positivity) x
  rw [laplacian_testFunction hε]
  exact (abs_add_le _ _).trans (add_le_add hmain hcut)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- At every `x ≠ 0`, the regularised kernels `(‖x‖² + (m + 1)⁻²)^(-n/2)` tend to `‖x‖^(-n)` as
`m → ∞`, so their supremum is at least `‖x‖^(-n)`. -/
private theorem enorm_rpow_le_iSup_ofReal_rpow {x : V} (hx : x ≠ 0) (n : ℕ) :
    ‖x‖ₑ ^ (-(n : ℝ)) ≤
      ⨆ m : ℕ, ENNReal.ofReal ((‖x‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) ^ (-(n : ℝ) / 2)) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hident : (‖x‖ ^ 2) ^ (-(n : ℝ) / 2) = ‖x‖ ^ (-(n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos hx0, ← hident]
  have hc : ContinuousAt (fun t : ℝ => (‖x‖ ^ 2 + t ^ 2) ^ (-(n : ℝ) / 2)) 0 :=
    ((continuous_const.add (continuous_pow 2)).continuousAt).rpow_const (Or.inl (by simp [hx]))
  have htend := ENNReal.tendsto_ofReal (hc.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at htend
  exact le_of_tendsto' htend fun m => le_iSup
    (fun m : ℕ => ENNReal.ofReal ((‖x‖ ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) ^ (-(n : ℝ) / 2))) m

/-! ### The two integral bounds -/

variable [MeasurableSpace V] [BorelSpace V]

/-- Up to the factor `2 n`, the main term `ε² (‖x‖² + ε²)^(-(n + 2)/2)` of the Laplacian has the
integral of `G(y) = (1 + ‖y‖²)^(-(n + 2)/2)`, whatever `ε > 0`, by the dilation `x ↦ ε⁻¹ x`. -/
private theorem lintegral_mul_rpow_eq (hε : 0 < ε) :
    ∫⁻ x : V, ENNReal.ofReal (ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-((finrank ℝ V : ℝ) + 2) / 2)) =
      ∫⁻ y : V, ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ (-((finrank ℝ V : ℝ) + 2) / 2)) := by
  set n := finrank ℝ V
  set G : V → ℝ≥0∞ := fun y => ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ (-((n : ℝ) + 2) / 2))
  have hpt : ∀ x : V, ENNReal.ofReal (ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-((n : ℝ) + 2) / 2)) =
      ENNReal.ofReal ((ε ^ n)⁻¹) * G (ε⁻¹ • x) := by
    intro x
    have hε2 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
    have hsum : ‖x‖ ^ 2 + ε ^ 2 = ε ^ 2 * (1 + ‖ε⁻¹ • x‖ ^ 2) := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hε.le, mul_pow, inv_pow]
      field_simp
      ring
    have hpow : ε ^ 2 * (ε ^ 2) ^ (-((n : ℝ) + 2) / 2) = (ε ^ n)⁻¹ := by
      rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le, ← Real.rpow_natCast ε n,
        ← Real.rpow_neg hε.le, ← Real.rpow_add hε]
      congr 1
      push_cast
      ring
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hε.le n)), hsum,
      Real.mul_rpow hε2 (by positivity), ← mul_assoc, hpow]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    Measure.lintegral_comp_inv_smul volume G hε.ne', abs_of_pos (pow_pos hε n), ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hε.le n)),
    inv_mul_cancel₀ (pow_pos hε n).ne', ENNReal.ofReal_one, one_mul]

/-- **The Laplacians of the test functions are bounded in `L¹`.** -/
private theorem exists_eLpNorm_laplacian_testFunction_le :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ ε : ℝ, 0 < ε →
      eLpNorm (Δ (testFunction (V := V) (finrank ℝ V) ε)) 1 volume ≤ A := by
  set n := finrank ℝ V
  obtain ⟨K, hK⟩ := exists_abs_deriv_cutoff_le
  set M : ℝ := 4 * (1 / 4 : ℝ) ^ (-(n : ℝ) / 2) * K
  set J : ℝ≥0∞ := ∫⁻ y : V, ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ (-((n : ℝ) + 2) / 2))
  have hJ : J < ⊤ :=
    (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure V))
      (by linarith : (n : ℝ) < n + 2)).lintegral_lt_top
  refine ⟨ENNReal.ofReal (2 * n) * J + ENNReal.ofReal M * volume (closedBall (0 : V) 1),
    ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top⟩, fun ε hε => ?_⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hpt : ∀ x : V, ‖Δ (testFunction (V := V) n ε) x‖ₑ ≤
      ENNReal.ofReal (2 * n) *
          ENNReal.ofReal (ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-((n : ℝ) + 2) / 2)) +
        (closedBall (0 : V) 1).indicator (fun _ => ENNReal.ofReal M) x := by
    intro x
    rw [← ofReal_norm, Real.norm_eq_abs]
    refine (ENNReal.ofReal_le_ofReal (abs_laplacian_testFunction_le hε hK x)).trans_eq ?_
    rw [ENNReal.ofReal_add (by positivity) (indicator_nonneg (fun _ _ => by positivity) x),
      ENNReal.ofReal_mul (by positivity)]
    congr 1
    by_cases hx : x ∈ closedBall (0 : V) 1
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  rw [eLpNorm_one_eq_lintegral_eNorm
    ((contDiff_testFunction hε).of_le (by simp)).continuous_laplacian.aestronglyMeasurable]
  refine (lintegral_mono hpt).trans_eq ?_
  rw [lintegral_add_left (by fun_prop), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_mul_rpow_eq hε, lintegral_indicator_const measurableSet_closedBall]

/-- **The Hessians of the test functions dominate the regularised kernel.** On the ball of
radius `1/2`, `‖D²u_ε(x)‖ ≥ (‖x‖² + ε²)^(-n/2)`. -/
private theorem setLIntegral_le_eLpNorm_iteratedFDeriv_two_testFunction
    (hV : 2 ≤ finrank ℝ V) (hε : 0 < ε) :
    ∫⁻ x in ball (0 : V) (1 / 2), ENNReal.ofReal ((‖x‖ ^ 2 + ε ^ 2) ^ (-(finrank ℝ V : ℝ) / 2)) ≤
      eLpNorm (iteratedFDeriv ℝ 2 (testFunction (finrank ℝ V) ε)) 1 (volume : Measure V) := by
  rw [eLpNorm_one_eq_lintegral_eNorm ((contDiff_testFunction hε).continuous_iteratedFDeriv
    (by simp)).aestronglyMeasurable]
  refine (setLIntegral_mono' measurableSet_ball fun x hx => ?_).trans
    (setLIntegral_le_lintegral _ _)
  -- A unit vector `h` orthogonal to `x`: the line through `x` is not all of `V`.
  obtain ⟨h, hh, hxh⟩ : ∃ h : V, ‖h‖ = 1 ∧ ⟪x, h⟫_ℝ = 0 := by
    have hpos : 0 < finrank ℝ (ℝ ∙ x)ᗮ := by
      have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ x)
      have : finrank ℝ (ℝ ∙ x) ≤ 1 := by
        simpa using finrank_span_le_card (R := ℝ) ({x} : Set V)
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp hpos)
    exact ⟨‖w‖⁻¹ • w, norm_smul_inv_norm hw0, by
      rw [inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hw, mul_zero]⟩
  have hσ : ‖x‖ ^ 2 ≤ 1 / 4 := by
    rw [mem_ball, dist_zero_right] at hx
    nlinarith [norm_nonneg x]
  have hval := iteratedFDeriv_two_testFunction_apply (n := finrank ℝ V) hε x h
  rw [hxh, hh, kernel, cutoff_eq_one hσ] at hval
  norm_num at hval
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle := (iteratedFDeriv ℝ 2 (testFunction (finrank ℝ V) ε) x).le_opNorm ![h, h]
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hh, mul_one, hval, Real.norm_eq_abs] at hle
  have hpos : 0 ≤ (‖x‖ ^ 2 + ε ^ 2) ^ (-(finrank ℝ V : ℝ) / 2) := by positivity
  rw [abs_of_nonneg (by positivity)] at hle
  linarith

/-- **The regularised kernel has unbounded integral near the origin.** -/
private theorem exists_lt_setLIntegral_rpow (hV : 2 ≤ finrank ℝ V) {B : ℝ≥0∞} (hB : B < ⊤) :
    ∃ ε : ℝ, 0 < ε ∧ B < ∫⁻ x in ball (0 : V) (1 / 2),
      ENNReal.ofReal ((‖x‖ ^ 2 + ε ^ 2) ^ (-(finrank ℝ V : ℝ) / 2)) := by
  set n := finrank ℝ V
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hp : -(n : ℝ) / 2 ≤ 0 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  set ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hεpos : ∀ m, 0 < ε m := fun m => by positivity
  set f : ℕ → V → ℝ≥0∞ := fun m x =>
    ENNReal.ofReal ((‖x‖ ^ 2 + ε m ^ 2) ^ (-(n : ℝ) / 2))
  have hmeas : ∀ m, Measurable (f m) := fun m => by fun_prop
  have hmono : Monotone f := by
    intro m m' hmm' x
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hp)
    have hle : ε m' ≤ ε m := one_div_le_one_div_of_le (by positivity) (by
      have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
      linarith)
    have := hεpos m'
    gcongr
  -- The limit is the non-integrable kernel `‖x‖^(-n)`.
  have hlim : ∀ x : V, x ≠ 0 → ‖(0 : V) - x‖ₑ ^ (-(n : ℝ)) ≤ ⨆ m, f m x := fun x hx => by
    rw [zero_sub, eNorm_neg]
    exact enorm_rpow_le_iSup_ofReal_rpow hx n
  have htop : ∫⁻ x in ball (0 : V) (1 / 2), ‖(0 : V) - x‖ₑ ^ (-(n : ℝ)) = ⊤ :=
    setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior le_rfl
      (by rw [isOpen_ball.interior_eq]; exact mem_ball_self (by norm_num))
  have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : V) (1 / 2))),
      ‖(0 : V) - x‖ₑ ^ (-(n : ℝ)) ≤ ⨆ m, f m x := by
    refine ae_restrict_of_ae ?_
    have hnull : ∀ᵐ x ∂(volume : Measure V), x ≠ 0 := by
      rw [ae_iff]
      simp
    exact hnull.mono hlim
  have hsup : ⨆ m, ∫⁻ x in ball (0 : V) (1 / 2), f m x = ⊤ := by
    rw [← lintegral_iSup hmeas hmono]
    exact top_le_iff.1 (htop ▸ lintegral_mono_ae hae)
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 (hsup.symm ▸ hB)
  exact ⟨ε m, hεpos m, hm⟩

/-! ### The failure of the estimate -/

/-- **The estimate `‖D²u‖₁ ≤ C ‖Δu‖₁` fails.** Let `V` be a real inner product space of finite
dimension at least two, with its volume measure. For every constant `C` there is a smooth compactly
supported real function `u` on `V` with `C ‖Δu‖_{L¹} < ‖D²u‖_{L¹}`. -/
theorem exists_contDiff_hasCompactSupport_mul_eLpNorm_laplacian_lt_eLpNorm_iteratedFDeriv_two
    (hV : 2 ≤ finrank ℝ V) (C : ℝ≥0) :
    ∃ u : V → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      C * eLpNorm (Δ u) 1 volume < eLpNorm (iteratedFDeriv ℝ 2 u) 1 volume := by
  obtain ⟨A, hA, hlap⟩ := exists_eLpNorm_laplacian_testFunction_le (V := V)
  obtain ⟨ε, hε, hlt⟩ := exists_lt_setLIntegral_rpow hV
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hA : (C : ℝ≥0∞) * A < ⊤)
  refine ⟨testFunction (finrank ℝ V) ε, contDiff_testFunction hε,
    hasCompactSupport_testFunction, ?_⟩
  calc (C : ℝ≥0∞) * eLpNorm (Δ (testFunction (finrank ℝ V) ε)) 1 volume
      ≤ C * A := by gcongr; exact hlap ε hε
    _ < _ := hlt
    _ ≤ _ := setLIntegral_le_eLpNorm_iteratedFDeriv_two_testFunction hV hε

/-- **The Calderón–Zygmund estimate fails at `p = 1`.** Let `V` be a real inner product space of
finite dimension at least two, with its volume measure. No constant `C` gives
`‖D²u‖_{L¹} ≤ C ‖Δu‖_{L¹}` for every real Schwartz function `u` on `V`. This is the negation at
`p = 1` of `TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real`. -/
theorem not_exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_one
    (hV : 2 ≤ finrank ℝ V) :
    ¬ ∃ C : ℝ≥0, ∀ u : 𝓢(V, ℝ), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) 1 volume ≤
      C * eLpNorm (⇑(Δ u : 𝓢(V, ℝ))) 1 volume := by
  rintro ⟨C, hC⟩
  obtain ⟨u, hu, hc, hlt⟩ :=
    exists_contDiff_hasCompactSupport_mul_eLpNorm_laplacian_lt_eLpNorm_iteratedFDeriv_two hV C
  set ψ : 𝓢(V, ℝ) := hc.toSchwartzMap hu
  have hψ : ⇑ψ = u := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hΔ : ⇑(Δ ψ : 𝓢(V, ℝ)) = Δ u := funext fun x => by
    rw [SchwartzMap.laplacian_apply, hψ]
  have := hC ψ
  rw [hψ, hΔ] at this
  exact (not_le.2 hlt) this

end TauCeti
