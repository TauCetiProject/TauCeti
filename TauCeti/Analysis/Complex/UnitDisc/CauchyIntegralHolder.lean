/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Holder.MeanValue

/-!
# The Cauchy integral of Hölder boundary data on the unit circle

For a function `φ` on the unit circle, the **Cauchy integral**

`F z = (2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw`

is holomorphic on the open unit disc, with Taylor coefficients the Fourier coefficients of `φ` of
nonnegative index. This file proves the theorem of Privalov that the Cauchy integral preserves
Hölder continuity: if `φ` is `α`-Hölder on the circle with constant `K`, for `0 < α < 1`, then `F`
is `α`-Hölder on the open disc, with constant `C(α) K`
(`TauCeti.holderOnWith_ball_circleIntegral_sub_inv_smul`). Being uniformly continuous, `F` then
extends continuously to the closed disc; that extension is not constructed here.

This is the existence half of the Hölder theory of the Riemann–Hilbert problem on the disc: a
holomorphic function with prescribed Hölder boundary data modulo the boundary condition is built
from Cauchy integrals, and the theorem of Privalov and of Hardy and Littlewood in
`TauCeti.Analysis.Complex.BoundaryHolder` then controls such a function on the closed disc from its
boundary values.

The exponent `1` is excluded: the Cauchy integral of a Lipschitz function on the circle need not be
Lipschitz, and the constant `C(α)` blows up like `1 / (1 - α)`.

## The proof

The proof estimates the derivative and then integrates it.

* **The derivative grows like `(1 - |z|)^(α - 1)`**
  (`TauCeti.norm_deriv_circleIntegral_sub_inv_smul_le`). The derivative of `F` is the Cauchy
  integral of `φ` against the kernel `(w - z)⁻²`, whose own integral vanishes, so `φ(w)` may be
  replaced by `φ(w) - φ(w₀)` for the point `w₀ = e^{i arg z}` of the circle nearest to `z`. With
  `ε = 1 - |z|` and `w = w₀ e^{is}` for `|s| ≤ π`, the distance `|w - z|` is at least `ε`, and at
  least `(|s| + ε) / 6`, since `|w - w₀| = 2 |sin (s / 2)| ≥ |s| / 2`, while
  `|φ(w) - φ(w₀)| ≤ K |w - w₀|^α ≤ K (2 |w - z|)^α`. So the integrand is at most
  `72 K (|s| + ε)^(α - 2)`, whose integral over `[-π, π]` is at most `144 K ε^(α - 1) / (1 - α)`.
* **Integrating the derivative** is the lemma of Hardy and Littlewood,
  `TauCeti.holderOnWith_ball_of_norm_fderiv_le_mul_rpow`.

## Main results

* `TauCeti.norm_deriv_circleIntegral_sub_inv_smul_le`: the derivative of the Cauchy integral of an
  `α`-Hölder function on the circle is at most `144 K (1 - |z|)^(α - 1) / (1 - α)`.
* `TauCeti.holderOnWith_ball_circleIntegral_sub_inv_smul`: **Privalov's theorem.** The Cauchy
  integral of an `α`-Hölder function on the circle, `0 < α < 1`, is `α`-Hölder on the open disc.

## References

* I. I. Privalov, *Sur les fonctions conjuguées*, Bull. Soc. Math. France **44** (1916), 100–103.
* G. H. Hardy and J. E. Littlewood, *Some properties of fractional integrals. II*, Math. Z. **34**
  (1932), 403–439.
* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press, 1970, Chapter 5 (Hölder continuity from the
  growth of the derivative, and the conjugate function of a Hölder function).
-/

public section

noncomputable section

open Complex Metric Set MeasureTheory intervalIntegral
open scoped Real NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The integral of `(|s| + ε)^(α - 2)` over `[-π, π]`, for `ε > 0` and `α < 1`, is at most
`2 ε^(α - 1) / (1 - α)`. -/
private theorem integral_abs_add_rpow_le {ε α : ℝ} (hε : 0 < ε) (hα : α < 1) :
    ∫ s in -π..π, (|s| + ε) ^ (α - 2) ≤ 2 * (ε ^ (α - 1) / (1 - α)) := by
  have hcont : Continuous fun s : ℝ ↦ (|s| + ε) ^ (α - 2) :=
    (continuous_abs.add continuous_const).rpow_const fun s ↦
      Or.inl (add_pos_of_nonneg_of_pos (abs_nonneg s) hε).ne'
  -- The integral over `[0, π]`, by the power rule after translating by `ε`.
  have hright : ∫ s in (0 : ℝ)..π, (|s| + ε) ^ (α - 2) ≤ ε ^ (α - 1) / (1 - α) := by
    rw [intervalIntegral.integral_congr (g := fun s ↦ (s + ε) ^ (α - 2)) fun s hs ↦ by
      rw [uIcc_of_le Real.pi_pos.le] at hs; simp only [abs_of_nonneg hs.1]]
    rw [intervalIntegral.integral_comp_add_right (fun x ↦ x ^ (α - 2)), zero_add,
      integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le (by linarith [Real.pi_pos])]; exact fun h ↦ by linarith [h.1]⟩)]
    have h2 : 0 ≤ (π + ε) ^ (α - 1) := Real.rpow_nonneg (by positivity) _
    rw [show α - 2 + 1 = α - 1 by ring, ← neg_div_neg_eq, neg_sub, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  -- The integral over `[-π, 0]` is the same, by the reflection `s ↦ -s`.
  have hleft : ∫ s in -π..0, (|s| + ε) ^ (α - 2) = ∫ s in (0 : ℝ)..π, (|s| + ε) ^ (α - 2) := by
    simpa using (intervalIntegral.integral_comp_neg (a := 0) (b := π)
      (fun s ↦ (|s| + ε) ^ (α - 2))).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hleft]
  linarith

/-- The pointwise bound on the kernel: if `ε ≤ a`, `b ≤ a + ε` and `t / 2 ≤ b`, for `ε > 0`,
`t ≥ 0` and `0 ≤ α ≤ 1`, then `b^α / a² ≤ 72 (t + ε)^(α - 2)`. Here `a = |w - z|`,
`b = |w - w₀|`, `t = |s|` and `ε = 1 - |z|`. -/
private theorem rpow_div_sq_le {a b t ε α : ℝ} (hε : 0 < ε) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (ht : 0 ≤ t) (hεa : ε ≤ a) (hba : b ≤ a + ε) (htb : t / 2 ≤ b) :
    b ^ α / a ^ 2 ≤ 72 * (t + ε) ^ (α - 2) := by
  have ha : 0 < a := hε.trans_le hεa
  have hlow : (t + ε) / 6 ≤ a := by linarith
  have h6 : (6 : ℝ) ^ (2 - α) ≤ 36 := by
    calc (6 : ℝ) ^ (2 - α) ≤ 6 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 36 := by norm_num
  calc b ^ α / a ^ 2 ≤ (2 * a) ^ α / a ^ 2 := by
        gcongr
        · linarith
        · linarith
    _ = 2 ^ α * a ^ (α - 2) := by
        rw [Real.mul_rpow (by norm_num) ha.le, Real.rpow_sub ha, Real.rpow_two]
        ring
    _ ≤ 2 * ((t + ε) / 6) ^ (α - 2) :=
        mul_le_mul (by simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hα1)
          (Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith))
          (Real.rpow_nonneg ha.le _) (by norm_num)
    _ = 2 * 6 ^ (2 - α) * (t + ε) ^ (α - 2) := by
        rw [Real.div_rpow (by positivity) (by norm_num), show 2 - α = -(α - 2) by ring,
          Real.rpow_neg (by norm_num)]
        ring
    _ ≤ 72 * (t + ε) ^ (α - 2) := by
        have : 0 ≤ (t + ε) ^ (α - 2) := Real.rpow_nonneg (by positivity) _
        nlinarith

/-- The geometry of the circle near `z`: for `z` in the open unit disc, its nearest point
`w₀ = e^{i arg z}` on the circle, and `w = e^{i (arg z + s)}` with `|s| ≤ π`, the distances satisfy
`1 - |z| ≤ |w - z|`, `|w - w₀| ≤ |w - z| + (1 - |z|)` and `|s| / 2 ≤ |w - w₀|`. -/
private theorem norm_circleMap_sub_le {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs : |s| ≤ π) :
    1 - ‖z‖ ≤ ‖circleMap 0 1 (arg z + s) - z‖ ∧
      ‖circleMap 0 1 (arg z + s) - circleMap 0 1 (arg z)‖ ≤
        ‖circleMap 0 1 (arg z + s) - z‖ + (1 - ‖z‖) ∧
      |s| / 2 ≤ ‖circleMap 0 1 (arg z + s) - circleMap 0 1 (arg z)‖ := by
  have hw : ‖circleMap 0 1 (arg z + s)‖ = 1 := by simp [norm_circleMap_zero]
  have hw₀ : ‖z - circleMap 0 1 (arg z)‖ = 1 - ‖z‖ := by
    have hpolar : z - circleMap 0 1 (arg z) = ((‖z‖ - 1 : ℝ) : ℂ) * exp (arg z * I) := by
      rw [circleMap_zero]
      nth_rewrite 1 [← norm_mul_exp_arg_mul_I z]
      push_cast
      ring
    rw [hpolar, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
      Real.norm_of_nonpos (by linarith)]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simpa [hw] using norm_sub_norm_le (circleMap 0 1 (arg z + s)) z
  · simpa [hw₀] using norm_sub_le_norm_sub_add_norm_sub (circleMap 0 1 (arg z + s)) z
      (circleMap 0 1 (arg z))
  · -- The chord `|e^{is} - 1| = 2 |sin (s / 2)|` is at least `|s| / 2` for `|s| ≤ π`.
    have hchord : ‖circleMap 0 1 (arg z + s) - circleMap 0 1 (arg z)‖ = ‖2 * Real.sin (s / 2)‖ := by
      rw [← norm_exp_I_mul_ofReal_sub_one s, circleMap_zero, circleMap_zero, ofReal_one, one_mul,
        one_mul, ofReal_add, add_mul, Complex.exp_add, ← mul_sub_one, norm_mul,
        norm_exp_ofReal_mul_I, one_mul, mul_comm I]
    have hsin : 2 / π * (|s| / 2) ≤ |Real.sin (s / 2)| := by
      rcases abs_cases s with ⟨h, h0⟩ | ⟨h, h0⟩
      · rw [h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
        exact Real.mul_le_sin (by linarith) (by linarith)
      · rw [h, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)),
          ← Real.sin_neg, show -s / 2 = -(s / 2) by ring]
        exact Real.mul_le_sin (by linarith) (by linarith)
    rw [hchord, norm_mul, Real.norm_two, Real.norm_eq_abs]
    have : |s| / 2 / 2 ≤ 2 / π * (|s| / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_le_four, abs_nonneg s]
    linarith

/-- The pointwise bound on the integrand of the derivative of the Cauchy integral: for `φ`
`α`-Hölder on the circle with constant `K`, `z` in the open disc, `w₀ = e^{i arg z}` and
`w = e^{i (arg z + s)}` with `|s| ≤ π`, the kernel term `(w - z)⁻² (φ(w) - φ(w₀))` has norm at most
`72 K (|s| + (1 - |z|))^(α - 2)`. -/
private theorem norm_zpow_smul_sub_le {φ : ℂ → E} {K α : ℝ≥0} (hα1 : α ≤ 1)
    (hφ : HolderOnWith K α φ (sphere 0 1)) {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs : |s| ≤ π) :
    ‖(circleMap 0 1 (arg z + s) - z) ^ (-2 : ℤ) •
        (φ (circleMap 0 1 (arg z + s)) - φ (circleMap 0 1 (arg z)))‖ ≤
      72 * K * (|s| + (1 - ‖z‖)) ^ ((α : ℝ) - 2) := by
  obtain ⟨h₁, h₂, h₃⟩ := norm_circleMap_sub_le hz hs
  set w := circleMap 0 1 (arg z + s)
  set w₀ := circleMap 0 1 (arg z)
  have hφw : ‖φ w - φ w₀‖ ≤ K * ‖w - w₀‖ ^ (α : ℝ) := by
    simpa [dist_eq_norm] using hφ.dist_le (circleMap_mem_sphere 0 zero_le_one _)
      (circleMap_mem_sphere 0 zero_le_one _)
  have hker := rpow_div_sq_le (by linarith) α.coe_nonneg (by exact_mod_cast hα1) (abs_nonneg s)
    h₁ h₂ h₃
  rw [norm_smul, norm_zpow]
  calc ‖w - z‖ ^ (-2 : ℤ) * ‖φ w - φ w₀‖ ≤ ‖w - z‖ ^ (-2 : ℤ) * (K * ‖w - w₀‖ ^ (α : ℝ)) := by
        gcongr
    _ = K * (‖w - w₀‖ ^ (α : ℝ) / ‖w - z‖ ^ 2) := by
        rw [zpow_neg, zpow_two, ← pow_two]
        ring
    _ ≤ K * (72 * (|s| + (1 - ‖z‖)) ^ ((α : ℝ) - 2)) := by gcongr
    _ = 72 * K * (|s| + (1 - ‖z‖)) ^ ((α : ℝ) - 2) := by ring

/-- **The derivative of the Cauchy integral of Hölder data.** If `φ` is `α`-Hölder on the unit
circle with constant `K`, for `0 < α < 1`, then the derivative of its Cauchy integral
`z ↦ ∮_{|w| = 1} φ(w) / (w - z) dw` at a point `z` of the open unit disc is at most
`144 K (1 - |z|)^(α - 1) / (1 - α)`. -/
theorem norm_deriv_circleIntegral_sub_inv_smul_le [CompleteSpace E] {φ : ℂ → E} {K α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) (hφ : HolderOnWith K α φ (sphere 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv (fun z ↦ ∮ w in C(0, 1), (w - z)⁻¹ • φ w) z‖ ≤
      144 / (1 - α) * K * (1 - ‖z‖) ^ ((α : ℝ) - 1) := by
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hε : 0 < 1 - ‖z‖ := by linarith
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have hint : CircleIntegrable φ 0 1 := (hφ.continuousOn hα0).circleIntegrable zero_le_one
  have hz' : z ∉ sphere (0 : ℂ) |1| := by
    rw [abs_one, mem_sphere_zero_iff_norm]
    exact hzn.ne
  set w₀ := circleMap 0 1 (arg z)
  set g : ℂ → E := fun w ↦ (w - z) ^ (-2 : ℤ) • (φ w - φ w₀)
  -- The kernel `(w - z)⁻²` integrates to zero, so `φ(w)` may be replaced by `φ(w) - φ(w₀)`.
  have hderiv : deriv (fun z ↦ ∮ w in C(0, 1), (w - z)⁻¹ • φ w) z = ∮ w in C(0, 1), g w := by
    rw [(hasDerivAt_circleIntegral_sub_inv_smul hint hz').deriv]
    simp only [g, smul_sub]
    rw [circleIntegral.integral_sub (hint.sub_zpow_smul _ hz')
      ((continuousOn_const.circleIntegrable zero_le_one).sub_zpow_smul _ hz'),
      circleIntegral.integral_smul_const, circleIntegral.integral_sub_zpow_of_ne (by norm_num),
      zero_smul, sub_zero]
  -- Write the circle integral over the period `[arg z - π, arg z + π]`, centred at `arg z`.
  set H : ℝ → E := fun θ ↦ deriv (circleMap 0 1) θ • g (circleMap 0 1 θ)
  have hH : Function.Periodic H (2 * π) := fun θ ↦ by
    simp only [H, deriv_circleMap, periodic_circleMap 0 1 θ]
  have hshift : (∮ w in C(0, 1), g w) = ∫ s in -π..π, H (arg z + s) := by
    rw [circleIntegral, intervalIntegral.integral_comp_add_left H (arg z),
      ← zero_add (2 * π), hH.intervalIntegral_add_eq 0 (arg z + -π)]
    congr 1
    ring
  rw [hderiv, hshift]
  have hcont : Continuous fun s : ℝ ↦ (|s| + (1 - ‖z‖)) ^ ((α : ℝ) - 2) :=
    (continuous_abs.add continuous_const).rpow_const fun s ↦
      Or.inl (add_pos_of_nonneg_of_pos (abs_nonneg s) hε).ne'
  refine (norm_integral_le_of_norm_le (g := fun s ↦ 72 * K * (|s| + (1 - ‖z‖)) ^ ((α : ℝ) - 2))
    (by linarith [Real.pi_pos]) (Filter.Eventually.of_forall fun s hs ↦ ?_)
    ((hcont.const_smul (72 * (K : ℝ))).intervalIntegrable _ _)).trans ?_
  · simpa only [H, g, deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_one, norm_I,
      mul_one, one_mul] using
      norm_zpow_smul_sub_le hα1'.le hφ hzn (abs_le.2 ⟨hs.1.le, hs.2⟩)
  · -- The integral of the bound.
    rw [intervalIntegral.integral_const_mul]
    have := integral_abs_add_rpow_le hε hα1'
    calc 72 * (K : ℝ) * ∫ s in -π..π, (|s| + (1 - ‖z‖)) ^ ((α : ℝ) - 2)
        ≤ 72 * K * (2 * ((1 - ‖z‖) ^ ((α : ℝ) - 1) / (1 - α))) := by gcongr
      _ = 144 / (1 - α) * K * (1 - ‖z‖) ^ ((α : ℝ) - 1) := by ring

/-- **Privalov's theorem.** If `φ` is `α`-Hölder on the unit circle with constant `K`, for
`0 < α < 1`, then its Cauchy integral `z ↦ (2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw` is `α`-Hölder
on the open unit disc, with constant `(3 + 2 / α) · 36 K / (1 - α)`. -/
theorem holderOnWith_ball_circleIntegral_sub_inv_smul [CompleteSpace E] {φ : ℂ → E}
    {K α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) (hφ : HolderOnWith K α φ (sphere 0 1)) :
    HolderOnWith ((3 + 2 / α) * (36 / (1 - α) * K)) α
      (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) (ball 0 1) := by
  have hint : CircleIntegrable φ 0 1 := (hφ.continuousOn hα0).circleIntegrable zero_le_one
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have hderiv (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasDerivAt (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w)
        ((2 * π * I)⁻¹ • deriv (fun z ↦ ∮ w in C(0, 1), (w - z)⁻¹ • φ w) z) z := by
    have hz' : z ∉ sphere (0 : ℂ) |1| := by
      rw [abs_one, mem_sphere_zero_iff_norm]
      exact (mem_ball_zero_iff.1 hz).ne
    exact (hasDerivAt_circleIntegral_sub_inv_smul hint hz').differentiableAt.hasDerivAt.const_smul _
  refine holderOnWith_ball_of_norm_fderiv_le_mul_rpow hα0 hα1.le
    (fun z hz ↦ ((hderiv z hz).differentiableAt.restrictScalars ℝ).differentiableWithinAt)
    fun z hz ↦ ?_
  rw [((hderiv z hz).hasFDerivAt.restrictScalars ℝ).fderiv,
    ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_toSpanSingleton, norm_smul,
    dist_zero_right]
  have hbound := norm_deriv_circleIntegral_sub_inv_smul_le hα0 hα1 hφ hz
  have hnorm : ‖(2 * π * I)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_two, norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  have hpow : 0 ≤ (1 - ‖z‖) ^ ((α : ℝ) - 1) := Real.rpow_nonneg (by
    linarith [mem_ball_zero_iff.1 hz]) _
  have hconst : (2 * π)⁻¹ * (144 / (1 - α)) ≤ 36 / (1 - α) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by linarith), inv_mul_le_iff₀ (by positivity)]
    nlinarith [Real.two_le_pi]
  rw [hnorm]
  push_cast [NNReal.coe_sub hα1.le]
  calc (2 * π)⁻¹ * ‖deriv (fun z ↦ ∮ w in C(0, 1), (w - z)⁻¹ • φ w) z‖
      ≤ (2 * π)⁻¹ * (144 / (1 - α) * K * (1 - ‖z‖) ^ ((α : ℝ) - 1)) := by gcongr
    _ = (2 * π)⁻¹ * (144 / (1 - α)) * (K * (1 - ‖z‖) ^ ((α : ℝ) - 1)) := by ring
    _ ≤ 36 / (1 - α) * (K * (1 - ‖z‖) ^ ((α : ℝ) - 1)) := by gcongr
    _ = 36 / (1 - α) * K * (1 - ‖z‖) ^ ((α : ℝ) - 1) := by ring

end TauCeti
