/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Complex.Circle.Rotation
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Topology.Circle.Metric
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Cauchy integral of Hölder boundary data on the unit circle

For a function `φ` on the unit circle, the **Cauchy integral**

`F z = (2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw`

is holomorphic on the open unit disc, with Taylor coefficients the Fourier coefficients of `φ` of
nonnegative index. This file proves the theorem of Privalov that the Cauchy integral preserves
Hölder continuity: if `φ` is `α`-Hölder on the circle with constant `K`, for `0 < α < 1`, then `F`
is `α`-Hölder on the open disc, with constant `C(α) K`
(`TauCeti.holderOnWith_ball_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`).

**Boundary values.** Being Hölder, `F` extends to an `α`-Hölder function `G` on the closed disc,
with the same constant
(`TauCeti.exists_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_holderOnWith_closedBall`). For
any function `φ` integrable on the circle and any extension `G` of `F` continuous on the closed
disc, the Fourier coefficients of `θ ↦ G(e^{iθ})` are those of `θ ↦ φ(e^{iθ})` at the indices
`n ≥ 0` and vanish at the indices `n < 0`
(`TauCeti.fourierCoeffOn_circleMap_eq_of_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`):
on the circle, `G` is the part of `φ` of nonnegative frequency. The Taylor coefficients of `F` are
these Fourier coefficients, and a holomorphic function continuous up to the boundary has its
Taylor coefficients as nonnegative Fourier coefficients of its boundary values.

**Derivatives.** Suppose that at every point `w` of the circle `t ↦ φ (e^{it} w)` has a derivative
`v w` at `t = 0`, with `v` continuous on the circle. Then `φ` is Lipschitz on the circle
(`TauCeti.lipschitzOnWith_sphere_of_hasDerivAt_exp_I_mul_mul` in
`TauCeti.Analysis.Complex.Circle.Rotation`), and integrating by parts along the circle shows that
the tangential derivative `(i z) F'(z)` is the Cauchy integral of `v`
(`TauCeti.I_mul_smul_deriv_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`). Passing to the limit
from the circles of radius `r < 1`, the boundary values of the extension `G` of `F` have the
derivative along the rotations given by the extension of the Cauchy integral of `v`
(`TauCeti.hasDerivAt_comp_exp_I_mul_mul_of_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`).
These are the inputs that Privalov's theorem for the derivative
(`DiffContOnCl.exists_holderOnWith_closedBall_deriv` in `TauCeti.Analysis.Complex.BoundaryHolder`)
needs; the Riemann–Hilbert problem with `C^{1,α}` data
(`TauCeti.exists_holderOnWith_closedBall_deriv_sub_zpow_mul_conj_eq_of_fourierCoeffOn_eq_zero` in
`TauCeti.Analysis.Complex.UnitDisc.RiemannHilbert`) combines them.

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
* `TauCeti.holderOnWith_ball_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`: **Privalov's
  theorem.** The Cauchy integral of an `α`-Hölder function on the circle, `0 < α < 1`, is
  `α`-Hölder on the open disc.
* `TauCeti.exists_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_holderOnWith_closedBall`: it
  extends to an `α`-Hölder function on the closed disc.
* `TauCeti.fourierCoeffOn_circleMap_eq_of_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`: the
  boundary values of a continuous extension of the Cauchy integral are the part of `φ` of
  nonnegative frequency.
* `TauCeti.I_mul_smul_deriv_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`: the tangential
  derivative of the Cauchy integral of `φ` is the Cauchy integral of the derivative of `φ` along
  the rotations.
* `TauCeti.hasDerivAt_comp_exp_I_mul_mul_of_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul`: the
  same holds for the boundary values of the extensions to the closed disc.

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

/-- A point of the open unit disc is off the unit circle, in the form that
`hasDerivAt_circleIntegral_sub_inv_smul` asks for. -/
private theorem notMem_sphere_abs_one_of_mem_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    z ∉ sphere (0 : ℂ) |1| := by
  rw [abs_one, mem_sphere_zero_iff_norm]
  exact (mem_ball_zero_iff.1 hz).ne

/-- The kernel bound `s ↦ (|s| + ε)^p` is continuous for `ε > 0`. -/
private theorem continuous_abs_add_rpow {ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    Continuous fun s : ℝ ↦ (|s| + ε) ^ p :=
  (continuous_abs.add continuous_const).rpow_const fun s ↦
    Or.inl (add_pos_of_nonneg_of_pos (abs_nonneg s) hε).ne'

/-- The integral of `(|s| + ε)^(α - 2)` over `[-π, π]`, for `ε > 0` and `α < 1`, is at most
`2 ε^(α - 1) / (1 - α)`. -/
private theorem integral_abs_add_rpow_le {ε α : ℝ} (hε : 0 < ε) (hα : α < 1) :
    ∫ s in -π..π, (|s| + ε) ^ (α - 2) ≤ 2 * (ε ^ (α - 1) / (1 - α)) := by
  have hcont := continuous_abs_add_rpow hε (α - 2)
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
  · -- The chord `|e^{is} - 1| = 2 sin (|s| / 2)` is at least `|s| / 2` for `|s| ≤ π`.
    rw [← dist_eq_norm, dist_circleMap_eq_two_mul_sin_abs 0 1
      (by rw [add_sub_cancel_left]; linarith [Real.pi_pos]), add_sub_cancel_left, abs_one, mul_one]
    have hsin : 2 / π * (|s| / 2) ≤ Real.sin (|s| / 2) :=
      Real.mul_le_sin (by positivity) (by linarith)
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
  have hz' := notMem_sphere_abs_one_of_mem_ball hz
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
  have hcont := continuous_abs_add_rpow hε ((α : ℝ) - 2)
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
theorem holderOnWith_ball_two_pi_I_inv_smul_circleIntegral_sub_inv_smul [CompleteSpace E]
    {φ : ℂ → E} {K α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) (hφ : HolderOnWith K α φ (sphere 0 1)) :
    HolderOnWith ((3 + 2 / α) * (36 / (1 - α) * K)) α
      (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) (ball 0 1) := by
  have hint : CircleIntegrable φ 0 1 := (hφ.continuousOn hα0).circleIntegrable zero_le_one
  have hα1' : (α : ℝ) < 1 := by exact_mod_cast hα1
  have hderiv (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasDerivAt (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w)
        ((2 * π * I)⁻¹ • deriv (fun z ↦ ∮ w in C(0, 1), (w - z)⁻¹ • φ w) z) z := by
    exact (hasDerivAt_circleIntegral_sub_inv_smul hint
      (notMem_sphere_abs_one_of_mem_ball hz)).differentiableAt.hasDerivAt.const_smul _
  refine holderOnWith_ball_of_norm_fderiv_le_mul_rpow hα0 hα1.le
    (fun z hz ↦ ((hderiv z hz).differentiableAt.restrictScalars ℝ).differentiableWithinAt)
    fun z hz ↦ ?_
  rw [((hderiv z hz).hasFDerivAt.restrictScalars ℝ).fderiv,
    ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_toSpanSingleton, norm_smul,
    dist_zero_right]
  have hbound := norm_deriv_circleIntegral_sub_inv_smul_le hα0 hα1 hφ hz
  have hnorm : ‖(2 * π * I)⁻¹‖ = (2 * π)⁻¹ := by simp [abs_of_pos Real.pi_pos]
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


/-! ### Boundary values -/

/-- The Cauchy integral `z ↦ (2 π i)⁻¹ ∮_{|w - c| = R} φ(w) / (w - z) dw` of a function integrable
on the circle `C(c, R)` is holomorphic on the open disc `ball c R`. -/
theorem differentiableOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul {φ : ℂ → E} {c : ℂ}
    {R : ℝ} (hφ : CircleIntegrable φ c R) :
    DifferentiableOn ℂ (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(c, R), (w - z)⁻¹ • φ w) (ball c R) :=
  fun _ hz ↦ ((hasDerivAt_circleIntegral_sub_inv_smul hφ
    ((mem_ball.1 hz).trans_le (le_abs_self R)).ne).differentiableAt.const_smul _
    ).differentiableWithinAt

/-- **The Cauchy integral of Hölder data extends to the closed disc.** If `φ` is `α`-Hölder on the
unit circle with constant `K`, for `0 < α < 1`, then its Cauchy integral
`z ↦ (2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw` agrees on the open unit disc with a function `G`
which is `α`-Hölder on the closed disc, with the constant of Privalov's theorem, and hence is
holomorphic on the open disc and continuous on the closed disc. -/
theorem exists_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_holderOnWith_closedBall
    [CompleteSpace E] {φ : ℂ → E} {K α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (hφ : HolderOnWith K α φ (sphere 0 1)) :
    ∃ G : ℂ → E, EqOn G (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) (ball 0 1) ∧
      HolderOnWith ((3 + 2 / α) * (36 / (1 - α) * K)) α G (closedBall 0 1) ∧
      DiffContOnCl ℂ G (ball 0 1) := by
  obtain ⟨G, hGF, hG⟩ := (holderOnWith_ball_two_pi_I_inv_smul_circleIntegral_sub_inv_smul hα0
    hα1 hφ).exists_eqOn_holderOnWith_closure hα0
  rw [closure_ball (0 : ℂ) one_ne_zero] at hG
  refine ⟨G, hGF, hG, ⟨(differentiableOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul
    ((hφ.continuousOn hα0).circleIntegrable zero_le_one)).congr hGF, ?_⟩⟩
  rw [closure_ball (0 : ℂ) one_ne_zero]
  exact hG.continuousOn hα0

/-- **The boundary values of the Cauchy integral.** Let `φ` be integrable on the unit circle, and
let `G` be continuous on the closed unit disc and equal on the open disc to the Cauchy integral
`z ↦ (2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw`. Then the Fourier coefficients of
`θ ↦ G(e^{iθ})` on `[0, 2π]` are those of `θ ↦ φ(e^{iθ})` at the indices `n ≥ 0`, and vanish at
the indices `n < 0`: on the circle, `G` is the part of `φ` of nonnegative frequency. -/
theorem fourierCoeffOn_circleMap_eq_of_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul
    [CompleteSpace E] {φ G : ℂ → E} (hφ : CircleIntegrable φ 0 1)
    (hG : ContinuousOn G (closedBall 0 1))
    (hGF : EqOn G (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) (ball 0 1))
    (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ ↦ G (circleMap 0 1 θ)) n =
      if 0 ≤ n then fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n else 0 := by
  have hGd : DiffContOnCl ℂ G (ball 0 1) :=
    ⟨(differentiableOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul hφ).congr hGF, by
      rwa [closure_ball (0 : ℂ) one_ne_zero]⟩
  split_ifs with hn
  · lift n to ℕ using hn
    refine hGd.fourierCoeffOn_circleMap_eq_of_hasSum
      (a := fun n : ℕ ↦ fourierCoeffOn Real.two_pi_pos (fun θ ↦ φ (circleMap 0 1 θ)) n)
      (fun z hz ↦ ?_) n
    rw [hGF hz]
    exact hasSum_pow_smul_fourierCoeffOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul hφ hz
  · rw [← fourierCoeff_comp_toCircle]
    exact hGd.fourierCoeff_comp_toCircle_eq_zero (not_le.1 hn)


/-! ### The derivative of the Cauchy integral -/

/-- The kernel `θ ↦ i e^{iθ} / (e^{iθ} - z)` of the Cauchy integral, written in the angle, has
derivative `z e^{iθ} / (e^{iθ} - z)²`. -/
private theorem hasDerivAt_circleMap_mul_I_div_sub {z : ℂ} {θ : ℝ} (hne : circleMap 0 1 θ - z ≠ 0) :
    HasDerivAt (fun θ ↦ circleMap 0 1 θ * I / (circleMap 0 1 θ - z))
      (z * circleMap 0 1 θ / (circleMap 0 1 θ - z) ^ 2) θ := by
  have he := hasDerivAt_circleMap 0 1 θ
  convert (he.mul_const I).div (he.sub_const z) hne using 1
  field_simp
  linear_combination z * I_sq

/-- **The tangential derivative of the Cauchy integral.** Let `φ` have at every point `w` of the
unit circle a derivative `v w` along the rotations, that is of `t ↦ φ (e^{it} w)` at `t = 0`, with
`v` continuous on the circle. Then the tangential derivative `(i z) F'(z)` of the Cauchy integral
`F z = (2 π i)⁻¹ ∮_{|w| = 1} φ(w) / (w - z) dw` is the Cauchy integral of `v`, at every point `z`
of the open unit disc. This is an integration by parts along the circle. -/
theorem I_mul_smul_deriv_two_pi_I_inv_smul_circleIntegral_sub_inv_smul [CompleteSpace E]
    {φ v : ℂ → E}
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ φ (exp (I * t) * w)) (v w) 0)
    (hvc : ContinuousOn v (sphere 0 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (I * z) • deriv (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) z =
      (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • v w := by
  have hφe := continuous_comp_circleMap_of_hasDerivAt hv
  have hve : Continuous fun θ ↦ v (circleMap 0 1 θ) :=
    hvc.comp_continuous (continuous_circleMap 0 1) fun θ ↦ by simp
  have hd : HasDerivAt (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w)
      ((2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z) ^ (-2 : ℤ) • φ w) z :=
    (hasDerivAt_circleIntegral_sub_inv_smul (hφe.intervalIntegrable _ _)
      (notMem_sphere_abs_one_of_mem_ball hz)).const_smul (2 * π * I)⁻¹
  rw [hd.deriv, smul_comm]
  congr 1
  simp only [circleIntegral, deriv_circleMap]
  have hne (θ : ℝ) : circleMap 0 1 θ - z ≠ 0 := sub_ne_zero.2 fun h ↦ by
    have := mem_ball_zero_iff.1 hz
    rw [← h] at this
    simp at this
  -- Integrate by parts against `u θ = i e^{iθ} / (e^{iθ} - z)`, whose derivative is
  -- `u' θ = z e^{iθ} / (e^{iθ} - z)²`; the boundary terms cancel by periodicity.
  set u' : ℝ → ℂ := fun θ ↦ z * circleMap 0 1 θ / (circleMap 0 1 θ - z) ^ 2
  have hu'c : Continuous u' :=
    (continuous_const.mul (continuous_circleMap 0 1)).div
      (((continuous_circleMap 0 1).sub continuous_const).pow 2) fun θ ↦ pow_ne_zero 2 (hne θ)
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := 0) (b := 2 * π)
    (fun θ _ ↦ hasDerivAt_circleMap_mul_I_div_sub (hne θ))
    (fun θ _ ↦ hasDerivAt_comp_circleMap hv θ) (hu'c.intervalIntegrable _ _)
    (hve.intervalIntegrable _ _)
  have hper : circleMap (0 : ℂ) 1 (2 * π) = circleMap 0 1 0 := by
    simpa using periodic_circleMap (0 : ℂ) 1 0
  simp only [hper, sub_self, zero_sub] at hibp
  rw [← intervalIntegral.integral_smul]
  calc ∫ θ in 0..2 * π,
        (I * z) • (circleMap 0 1 θ * I) • (circleMap 0 1 θ - z) ^ (-2 : ℤ) • φ (circleMap 0 1 θ)
      = -∫ θ in 0..2 * π, u' θ • φ (circleMap 0 1 θ) := by
        rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun θ _ ↦ ?_
        simp only [smul_smul, ← neg_smul, u', zpow_neg, zpow_ofNat]
        congr 1
        field_simp
        linear_combination z / (circleMap 0 1 θ - z) ^ 2 * I_sq
    _ = ∫ θ in 0..2 * π, (circleMap 0 1 θ * I / (circleMap 0 1 θ - z)) • v (circleMap 0 1 θ) :=
        hibp.symm
    _ = ∫ θ in 0..2 * π, (circleMap 0 1 θ * I) • (circleMap 0 1 θ - z)⁻¹ • v (circleMap 0 1 θ) := by
        refine intervalIntegral.integral_congr fun θ _ ↦ ?_
        rw [smul_smul, div_eq_mul_inv]

/-- Inside the disc, the rotations of a point carry the extension `G` of the Cauchy integral of `φ`
with derivative the extension `G'` of the Cauchy integral of `v`. -/
private theorem hasDerivAt_comp_exp_I_mul_mul_of_mem_ball [CompleteSpace E] {φ v G G' : ℂ → E}
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ φ (exp (I * t) * w)) (v w) 0)
    (hvc : ContinuousOn v (sphere 0 1))
    (hGF : EqOn G (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) (ball 0 1))
    (hG'F : EqOn G' (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • v w) (ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ G (exp (I * t) * z)) (G' (exp (I * t) * z)) t := by
  have hφi : CircleIntegrable φ 0 1 :=
    (continuous_comp_circleMap_of_hasDerivAt hv).intervalIntegrable _ _
  have hξ : exp (I * t) * z ∈ ball (0 : ℂ) 1 := exp_I_mul_mul_mem_ball_iff.2 hz
  have hF : HasDerivAt G (deriv (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w)
      (exp (I * t) * z)) (exp (I * t) * z) :=
    (((differentiableOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul hφi).differentiableAt
      (isOpen_ball.mem_nhds hξ)).hasDerivAt).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds hξ) hGF)
  convert hF.scomp t (hasDerivAt_exp_I_mul_mul z t) using 1
  · rfl
  · rw [hG'F hξ, I_mul_smul_deriv_two_pi_I_inv_smul_circleIntegral_sub_inv_smul hv hvc hξ]

/-- If `t ↦ G (e^{it} z)` has derivative `G' (e^{it} z)` for every `z` in the open disc, with `G`
and `G'` continuous on the closed disc, then `G (e^{it} w) - G w = ∫_0^t G' (e^{is} w) ds` also on
the circle: let the radius `r` of `z = r w` tend to `1`. -/
private theorem sub_eq_integral_of_mem_sphere [CompleteSpace E] {G G' : ℂ → E}
    (hG : ContinuousOn G (closedBall 0 1)) (hG' : ContinuousOn G' (closedBall 0 1))
    (hderiv : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ,
      HasDerivAt (fun t : ℝ ↦ G (exp (I * t) * z)) (G' (exp (I * t) * z)) t)
    {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) (t : ℝ) :
    G (exp (I * t) * w) - G w = ∫ s in 0..t, G' (exp (I * s) * w) := by
  have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 hw
  have hrot {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (s : ℝ) : exp (I * s) * z ∈ closedBall 0 1 :=
    exp_I_mul_mul_mem_closedBall_iff.2 hz
  set P : ℝ → ℂ := fun r ↦ ((projIcc (0 : ℝ) 1 zero_le_one r : ℝ) : ℂ) * w
  have hP (r : ℝ) : P r ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_mul, hw1, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (projIcc (0 : ℝ) 1 zero_le_one r).property.1]
    exact (projIcc (0 : ℝ) 1 zero_le_one r).property.2
  set Ψ : ℝ → E := fun r ↦
    G (exp (I * t) * P r) - G (P r) - ∫ s in 0..t, G' (exp (I * s) * P r)
  have hΨ : Continuous Ψ := by
    refine ((hG.comp_continuous (by fun_prop) fun r ↦ hrot (hP r) t).sub
      (hG.comp_continuous (by fun_prop) hP)).sub ?_
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 t
    exact hG'.comp_continuous (by fun_prop) fun q ↦ hrot (hP q.1) q.2
  -- `Ψ` vanishes on the radii `0 < r < 1` by the fundamental theorem of calculus.
  have hΨ0 : ∀ᶠ r in nhdsWithin (1 : ℝ) (Iio 1), Ψ r = 0 := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
    have hPr : P r = r * w := by simp [P, projIcc_of_mem _ ⟨hr.1.le, hr.2.le⟩]
    have hrw : P r ∈ ball (0 : ℂ) 1 := by
      rw [hPr, mem_ball_zero_iff, norm_mul, hw1, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1]
      exact hr.2
    simp only [Ψ, sub_eq_zero]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv _ hrw s)
      ((hG'.comp_continuous (by fun_prop) (hrot (ball_subset_closedBall hrw))).intervalIntegrable
        _ _)]
    simp
  have h1 : Ψ 1 = 0 := tendsto_nhds_unique (hΨ.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds) (tendsto_const_nhds.congr' (hΨ0.mono fun r hr ↦ hr.symm))
  have hP1 : P 1 = w := by simp [P]
  simpa only [Ψ, hP1, sub_eq_zero] using h1

/-- **The tangential derivative of the boundary values of the Cauchy integral.** Let `φ` have at
every point `w` of the unit circle a derivative `v w` along the rotations, that is of
`t ↦ φ (e^{it} w)` at `t = 0`, with `v` continuous on the circle, and let `G` and `G'` be
continuous on the closed unit disc and equal on the open disc to the Cauchy integrals of `φ` and of
`v`. Then at every point `w` of the unit circle, `t ↦ G (e^{it} w)` has derivative `G' w` at
`t = 0`: the boundary values of `G` have the derivative `G'` along the rotations. -/
theorem hasDerivAt_comp_exp_I_mul_mul_of_eqOn_two_pi_I_inv_smul_circleIntegral_sub_inv_smul
    [CompleteSpace E] {φ v G G' : ℂ → E}
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ φ (exp (I * t) * w)) (v w) 0)
    (hvc : ContinuousOn v (sphere 0 1)) (hG : ContinuousOn G (closedBall 0 1))
    (hGF : EqOn G (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • φ w) (ball 0 1))
    (hG' : ContinuousOn G' (closedBall 0 1))
    (hG'F : EqOn G' (fun z ↦ (2 * π * I)⁻¹ • ∮ w in C(0, 1), (w - z)⁻¹ • v w) (ball 0 1))
    {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    HasDerivAt (fun t : ℝ ↦ G (exp (I * t) * w)) (G' w) 0 := by
  have hint := sub_eq_integral_of_mem_sphere hG hG'
    (fun z hz t ↦ hasDerivAt_comp_exp_I_mul_mul_of_mem_ball hv hvc hGF hG'F hz t) hw
  have hcont : Continuous fun s : ℝ ↦ G' (exp (I * s) * w) :=
    hG'.comp_continuous (by fun_prop) fun s ↦
      sphere_subset_closedBall (exp_I_mul_mul_mem_sphere_iff.2 hw)
  have hd := (hcont.integral_hasStrictDerivAt 0 0).hasDerivAt.const_add (G w)
  simp only [ofReal_zero, mul_zero, exp_zero, one_mul] at hd
  convert hd using 1
  funext t
  rw [← hint t, add_sub_cancel]

end TauCeti
