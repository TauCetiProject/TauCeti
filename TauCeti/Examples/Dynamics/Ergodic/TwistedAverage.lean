/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Atoms
public import TauCeti.Examples.Dynamics.Ergodic.Koopman
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Checks: twisted averages of the translation flow on the circle

Checks for the continuous-time mean ergodic projection
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.exists_tendsto_twistedAverage`) on the
Koopman group `U` of the translation flow `t +ᵥ x = t + x` on `AddCircle 1` with its normalised
Haar measure, acting on the modes `e_n = fourierLp 2 n`, for which `U_t e_n = exp(2πint) e_n`
(`TauCeti.Examples.KoopmanChecks.koopmanGroup_fourierLp`). Write
`A_T^a v = T⁻¹ ∫₀ᵀ exp(−2πiat) U_t v dt` and `P_a` for the orthogonal projection onto the common
eigenspace `{u | ∀ t, U_t u = exp(2πiat) u}`.

* `twistedAverage_fourierLp`: `A_T^a e_n = (T⁻¹ ∫₀ᵀ exp(2πi(n − a)t) dt) e_n`.
* `twistedAverage_fourierLp_self`: at `a = n`, `A_T^n e_n = e_n` for every `T ≠ 0`.
* `tendsto_twistedAverage_fourierLp_of_ne`: at `a ≠ n`, `A_T^a e_n → 0`.
* `starProjection_fourierLp_self` and `starProjection_fourierLp_of_ne`: `P_n e_n = e_n`, and
  `P_a e_n = 0` for `a ≠ n`.
* `twistedAverage_fourierLp_natCast_eq_zero`: for integers `m ≠ n`, `A_N^m e_n = 0` at every
  natural `N`.
* `inner_mode_circleFlow_mode`: the correlation `⟪e_n, U_t e_n⟫ = exp(2πint)`.
* `inner_koopmanGroup_fourierLp_eq_charFun`: the spectral measure of `e_n` is `δ_{2πn}`.

For the unit mode `e₁`: `U₁ e₁ = e₁`, so the discrete time-one averages of `e₁` are `e₁`, but
`A_N^0 e₁ = 0` at every positive integer `N` and `P₀ e₁ = 0`, the spectral mass of `e₁` at `0`
being `0`; `A_T^1 e₁ = e₁` for every `T > 0`, `‖P₁ e₁‖² = 1 = δ_{2π}({2π})` and
`⟪e₁, U_{1/4} e₁⟫ = i`; the opposite twist `a = −1` gives averages tending to `0`.
-/

public section

noncomputable section

open Filter MeasureTheory Complex TauCeti.Semigroups StronglyContinuousGroup
open scoped Real ENNReal InnerProductSpace Topology

namespace TauCeti.Examples.TwistedAverageCircleChecks

open TauCeti.Examples.KoopmanChecks

/-- The Koopman group of the translation flow on `AddCircle 1` on complex `L²` of the normalised
Haar measure, with the real structure of `L²` restricted from its complex one, the structure seen
by the eigenspaces and projections of a unitary group. -/
abbrev circleFlow :
    @StronglyContinuousGroup (Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) _
      NormedSpace.complexToReal :=
  koopmanGroup (AddCircle.haarAddCircle (T := 1)) ℂ 2 ENNReal.ofNat_ne_top

/-- The Koopman group of the translation flow on `AddCircle 1` is unitary. -/
theorem circleFlow_isUnitary : circleFlow.IsUnitary :=
  koopmanGroup_isUnitary _ ℂ

/-- The mode `e_n(x) = exp(2πinx)` in complex `L²` of the normalised Haar measure on
`AddCircle 1`. -/
abbrev mode (n : ℤ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
  fourierLp 2 n

/-- The modes are eigenvectors: `U_t e_n = exp(2πint) e_n`. -/
theorem circleFlow_mode (n : ℤ) (t : ℝ) :
    circleFlow t (mode n) = exp (2 * π * I * n * t) • mode n :=
  koopmanGroup_fourierLp n t

/-- The time-one Koopman operator fixes every mode: `U₁ e_n = e_n`. -/
theorem circleFlow_one_mode (n : ℤ) : circleFlow 1 (mode n) = mode n := by
  rw [circleFlow_mode, ofReal_one, mul_one,
    show 2 * π * I * n = (n : ℂ) * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I, one_smul]

/-- The mode `e_n` lies in the common eigenspace of angular frequency `2πn`. -/
theorem mode_mem_eigenspace (n : ℤ) :
    mode n ∈ circleFlow.eigenspace circleFlow_isUnitary.isComplexLinear (2 * π * n) := by
  rw [mem_eigenspace_iff]
  intro t
  rw [circleFlow_mode]
  congr 2
  push_cast
  ring

/-- **The twisted average of a mode**: `A_T^a e_n = (T⁻¹ ∫₀ᵀ exp(2πi(n − a)t) dt) e_n`. -/
theorem twistedAverage_fourierLp (n : ℤ) (a T : ℝ) :
    (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • circleFlow t (mode n) =
      ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (↑(t * (2 * π * (n - a))) * I)) • mode n := by
  have hfun : (fun t : ℝ => exp (-(2 * π * a * t * I)) • circleFlow t (mode n)) =
      fun t : ℝ => exp (↑(t * (2 * π * (n - a))) * I) • mode n := by
    funext t
    rw [circleFlow_mode, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfun, intervalIntegral.integral_smul_const, smul_smul]

/-- At the matching frequency the twisted averages of a mode are constant: `A_T^n e_n = e_n` for
every `T ≠ 0`. -/
theorem twistedAverage_fourierLp_self (n : ℤ) {T : ℝ} (hT : T ≠ 0) :
    (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * (n : ℝ) * t * I)) • circleFlow t (mode n) =
      mode n := by
  rw [twistedAverage_fourierLp]
  simp [hT]

/-- **Away from the matching frequency the twisted averages of a mode tend to `0`**: for `a ≠ n`,
`A_T^a e_n → 0`. -/
theorem tendsto_twistedAverage_fourierLp_of_ne {n : ℤ} {a : ℝ} (ha : a ≠ n) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
        ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • circleFlow t (mode n))
      atTop (𝓝 0) := by
  have hc : 2 * π * (n - a) ≠ 0 :=
    mul_ne_zero (by positivity) (sub_ne_zero.2 (Ne.symm ha))
  simp_rw [twistedAverage_fourierLp]
  have h := (tendsto_average_integral_cexp (2 * π * (n - a))).smul_const (mode n)
  rwa [Set.indicator_of_notMem (by simpa using hc), zero_smul] at h

/-- The projection of a mode onto the eigenspace of its own frequency: `P_n e_n = e_n`. -/
theorem starProjection_fourierLp_self (n : ℤ) :
    (circleFlow.eigenspace circleFlow_isUnitary.isComplexLinear (2 * π * n)).starProjection
      (mode n) = mode n :=
  Submodule.starProjection_eq_self_iff.2 (mode_mem_eigenspace n)

/-- The projection of a mode onto the eigenspace of another frequency vanishes: `P_a e_n = 0` for
`a ≠ n`. -/
theorem starProjection_fourierLp_of_ne {n : ℤ} {a : ℝ} (ha : a ≠ n) :
    (circleFlow.eigenspace circleFlow_isUnitary.isComplexLinear (2 * π * a)).starProjection
      (mode n) = 0 := by
  refine tendsto_nhds_unique
    (circleFlow_isUnitary.tendsto_twistedAverage_starProjection (2 * π * a) (mode n)) ?_
  refine (tendsto_twistedAverage_fourierLp_of_ne ha).congr fun T => ?_
  rw [← ofReal_inv, ← Complex.coe_smul]
  congr 2
  funext t
  rw [ofReal_mul, ofReal_mul, ofReal_ofNat]

/-- At natural times the twisted averages of a mode at another integer frequency vanish: for
integers `m ≠ n`, `A_N^m e_n = 0` at every natural `N`, since `∫₀ᴺ exp(2πi(n − m)t) dt = 0`. -/
theorem twistedAverage_fourierLp_natCast_eq_zero {n m : ℤ} (h : m ≠ n) (N : ℕ) :
    ((N : ℝ) : ℂ)⁻¹ •
        ∫ t in (0 : ℝ)..N, exp (-(2 * π * (m : ℝ) * t * I)) • circleFlow t (mode n) = 0 := by
  have hc : 2 * π * ((n - m : ℤ) : ℂ) * I ≠ 0 := by
    simp [Real.pi_ne_zero, sub_eq_zero, Ne.symm h]
  rw [twistedAverage_fourierLp]
  simp_rw [show ∀ t : ℝ, (↑(t * (2 * π * ((n : ℝ) - m))) : ℂ) * I =
    2 * π * ((n - m : ℤ) : ℂ) * I * t from fun t => by push_cast; ring]
  rw [integral_exp_mul_complex hc, show 2 * π * ((n - m : ℤ) : ℂ) * I * ((N : ℝ) : ℂ) =
    ((n - m) * N : ℤ) * (2 * π * I) by push_cast; ring, exp_int_mul_two_pi_mul_I]
  simp

/-- The correlation of a mode: `⟪e_n, U_t e_n⟫ = exp(2πint)`. -/
theorem inner_mode_circleFlow_mode (n : ℤ) (t : ℝ) :
    ⟪mode n, circleFlow t (mode n)⟫_ℂ = exp (2 * π * I * n * t) := by
  rw [circleFlow_mode, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (orthonormal_fourier (T := 1)).1 n]
  simp

/-- **The spectral measure of a mode** is `δ_{2πn}`:
`⟪e_n, U_t e_n⟫ = exp(2πint) = charFun δ_{2πn} t`. -/
theorem inner_koopmanGroup_fourierLp_eq_charFun (n : ℤ) (t : ℝ) :
    ⟪mode n, circleFlow t (mode n)⟫_ℂ = charFun (Measure.dirac (2 * π * n : ℝ)) t := by
  rw [inner_mode_circleFlow_mode, charFun_apply_real, integral_dirac]
  push_cast
  ring_nf

/-! ### The unit mode -/

/-- The discrete time-one averages of `e₁` are `e₁`: `U₁ e₁ = e₁`. -/
example : circleFlow 1 (mode 1) = mode 1 :=
  circleFlow_one_mode 1

/-- At every positive integer time `N`, the untwisted average vanishes: `A_N^0 e₁ = 0`. -/
example (N : ℕ) :
    (((N : ℝ) : ℂ)⁻¹) •
        ∫ t in (0 : ℝ)..N, exp (-(2 * π * (0 : ℝ) * t * I)) • circleFlow t (mode 1) = 0 := by
  exact_mod_cast twistedAverage_fourierLp_natCast_eq_zero (n := 1) (m := 0) zero_ne_one N

/-- The projection onto the fixed vectors kills `e₁`: `P₀ e₁ = 0`. -/
example :
    (circleFlow.fixedSubmodule circleFlow_isUnitary.isComplexLinear).starProjection (mode 1) =
      0 := by
  have h := starProjection_fourierLp_of_ne (n := 1) (a := 0) (by norm_num)
  rw [mul_zero] at h
  simpa using h

/-- The spectral mass of `e₁` at `0` is `0`: `‖P₀ e₁‖² = 0 = δ_{2π}({0})`. -/
example :
    ‖(circleFlow.eigenspace circleFlow_isUnitary.isComplexLinear 0).starProjection (mode 1)‖ ^ 2 =
        0 ∧
      (Measure.dirac (2 * π * (1 : ℤ) : ℝ)).real {0} = 0 := by
  have h := starProjection_fourierLp_of_ne (n := 1) (a := 0) (by norm_num)
  rw [mul_zero] at h
  refine ⟨by rw [h, norm_zero]; norm_num, ?_⟩
  simp [measureReal_def, Measure.dirac_apply', Real.pi_ne_zero]

/-- At the matching twist the averages are constant: `A_T^1 e₁ = e₁` for every `T > 0`. -/
example {T : ℝ} (hT : 0 < T) :
    (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * ((1 : ℤ) : ℝ) * t * I)) • circleFlow t (mode 1) =
      mode 1 :=
  twistedAverage_fourierLp_self 1 hT.ne'

/-- **The atomic-mass identity** for `e₁` at its own frequency:
`‖P₁ e₁‖² = 1 = δ_{2π}({2π})`. -/
example :
    ‖(circleFlow.eigenspace circleFlow_isUnitary.isComplexLinear (2 * π * (1 : ℤ))).starProjection
        (mode 1)‖ ^ 2 = 1 ∧
      ‖(circleFlow.eigenspace circleFlow_isUnitary.isComplexLinear (2 * π * (1 : ℤ))).starProjection
        (mode 1)‖ ^ 2 = (Measure.dirac (2 * π * (1 : ℤ) : ℝ)).real {2 * π * (1 : ℤ)} := by
  refine ⟨?_, circleFlow_isUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton _ _
    (inner_koopmanGroup_fourierLp_eq_charFun 1)⟩
  rw [starProjection_fourierLp_self, (orthonormal_fourier (T := 1)).1 1, one_pow]

/-- The correlation of `e₁` at time `1/4` is `i`: `⟪e₁, U_{1/4} e₁⟫ = i`. -/
example : ⟪mode 1, circleFlow (1 / 4) (mode 1)⟫_ℂ = I := by
  rw [inner_mode_circleFlow_mode,
    show 2 * π * I * ((1 : ℤ) : ℂ) * ((1 / 4 : ℝ) : ℂ) = π / 2 * I by push_cast; ring,
    exp_pi_div_two_mul_I]

/-- The opposite twist `a = −1` has limit `0`: `A_T^{−1} e₁ → 0`. -/
example :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
        ∫ t in (0 : ℝ)..T, exp (-(2 * π * (-1 : ℝ) * t * I)) • circleFlow t (mode 1))
      atTop (𝓝 0) :=
  tendsto_twistedAverage_fourierLp_of_ne (by norm_num)

end TauCeti.Examples.TwistedAverageCircleChecks
