/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Background
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral

/-!
# Taubes's variational functional for the prescribed-zero vortex equation

For a holomorphic function `f`, the background amplitude `u₀ = -log (1 + ‖f‖²) / 2`
(`TauCeti.Vortex.backgroundAmplitude`) turns the vortex equation for the field reconstructed from
the amplitude `u₀ + w` and the section `f` into the reduced equation
`Δw = (exp (2w) h - 1) / 8 + 2 ‖f'‖² / (1 + ‖f‖²)²`, where `h = ‖f‖² / (1 + ‖f‖²)`
(`TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff`). Following Taubes,
this file exhibits the reduced equation as the Euler–Lagrange equation of a convex functional.

Write `φ(t) = (exp (2t) - 1 - 2t) / 16` (`TauCeti.Vortex.taubesPotential`). It is nonnegative,
vanishes only at `0`, and `φ'(t) = (exp (2t) - 1) / 8`. For coefficient functions `h` and `k` on
a finite-dimensional real inner product space, **Taubes's functional** is

`𝒜(w) = ∫ (‖∇w‖² / 2 + h φ(w) + k w)`     (`TauCeti.Vortex.taubesFunctional`),

with Euler–Lagrange equation `Δw = h (exp (2w) - 1) / 8 + k`. The reduced vortex equation is the
case `h = ‖f‖² / (1 + ‖f‖²)` (`TauCeti.Vortex.backgroundWeight`) and
`k = (h - 1) / 8 + 2 ‖f'‖² / (1 + ‖f‖²)²` (`TauCeti.Vortex.backgroundSource`). The coefficient `k`
need not be integrable (for `f z = z`, `h - 1 = -(1 + ‖z‖²)⁻¹`), so `𝒜` is the integral of the
whole density, not a sum of separately finite terms. For continuous `h` and `k`, the density is
integrable, for instance, whenever `w` is a compactly supported `C¹` function
(`TauCeti.Vortex.integrable_taubesDensity_of_hasCompactSupport`).

The expansion `φ(t + s) = φ(t) + φ'(t) s + exp (2t) φ(s)` gives the exact second-order expansion
of `𝒜` along a compactly supported perturbation `v`:

`𝒜(w + v) = 𝒜(w) + ∫ (⟪∇w, ∇v⟫ + (h φ'(w) + k) v) + ∫ (‖∇v‖² / 2 + h exp (2w) φ(v))`.

The middle term is the first variation, and Green's identity turns it into
`∫ v (-Δw + h φ'(w) + k)`. Hence a `C²` function with integrable density is a critical point of
`𝒜` along all compactly supported directions exactly when it solves the Euler–Lagrange equation.
For `h ≥ 0` the last term is nonnegative, so `𝒜` lies above its tangent lines, and on a nonzero
space a solution is the strict minimizer of `𝒜` among its compactly supported perturbations. For
the background coefficients of an entire function `f` and a `C²` function `w` with integrable
density, this says that the field reconstructed from `u₀ + w` and `f` is a vortex exactly when
`w` is a critical point of `𝒜`, and that `w` is then the strict minimizer of `𝒜` among its
compactly supported perturbations.

Existence of a minimizer is not treated here: it needs the extension of `𝒜` to a Sobolev space, a
coercivity estimate, and the regularity and decay of the minimizer.

## Main definitions

* `TauCeti.Vortex.taubesPotential`: the potential `φ(t) = (exp (2t) - 1 - 2t) / 16`.
* `TauCeti.Vortex.taubesDensity`, `TauCeti.Vortex.taubesFunctional`: the density
  `‖∇w‖² / 2 + h φ(w) + k w` and its integral `𝒜(w)`.
* `TauCeti.Vortex.backgroundSource`: the coefficient `k` of the reduced vortex equation, whose
  coefficient `h` is `TauCeti.Vortex.backgroundWeight` from `Vortex/Background.lean`.

## Main results

* `TauCeti.Vortex.taubesFunctional_add`: the exact second-order expansion of `𝒜`.
* `TauCeti.Vortex.hasDerivAt_taubesFunctional_add_smul`: the first variation of `𝒜`.
* `TauCeti.Vortex.forall_hasDerivAt_taubesFunctional_add_smul_iff`: the critical points of `𝒜`
  are the solutions of `Δw = h (exp (2w) - 1) / 8 + k`.
* `TauCeti.Vortex.taubesFunctional_add_integral_le`: the convexity inequality for `𝒜`.
* `TauCeti.Vortex.taubesFunctional_lt_add`: a solution strictly minimizes `𝒜` among its
  compactly supported perturbations.
* `TauCeti.Vortex.forall_hasDerivAt_taubesFunctional_add_smul_iff_equation_amplitudeField`: for
  the background coefficients, the critical points of `𝒜` are the vortex amplitudes, and
  `TauCeti.Vortex.taubesFunctional_lt_add_of_equation_amplitudeField`: a vortex amplitude strictly
  minimizes `𝒜` among its compactly supported perturbations.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Filter InnerProductSpace MeasureTheory Set Topology
open scoped Gradient Laplacian

/-! ### The potential -/

/-- **Taubes's potential** `φ(t) = (exp (2t) - 1 - 2t) / 16`. It is nonnegative, vanishes only at
`0`, and its derivative `(exp (2t) - 1) / 8` is the nonlinearity of the reduced vortex
equation. -/
def taubesPotential (t : ℝ) : ℝ :=
  (Real.exp (2 * t) - 1 - 2 * t) / 16

/-- The defining formula of `TauCeti.Vortex.taubesPotential`. -/
theorem taubesPotential_def (t : ℝ) :
    taubesPotential t = (Real.exp (2 * t) - 1 - 2 * t) / 16 := (rfl)

@[simp]
theorem taubesPotential_zero : taubesPotential 0 = 0 := by
  simp [taubesPotential_def]

theorem taubesPotential_nonneg (t : ℝ) : 0 ≤ taubesPotential t := by
  rw [taubesPotential_def]
  linarith [Real.add_one_le_exp (2 * t)]

theorem taubesPotential_pos {t : ℝ} (ht : t ≠ 0) : 0 < taubesPotential t := by
  rw [taubesPotential_def]
  linarith [Real.add_one_lt_exp (mul_ne_zero two_ne_zero ht)]

@[simp]
theorem taubesPotential_eq_zero_iff {t : ℝ} : taubesPotential t = 0 ↔ t = 0 :=
  ⟨fun h ↦ by_contra fun ht ↦ (taubesPotential_pos ht).ne' h, fun h ↦ h ▸ taubesPotential_zero⟩

/-- The derivative of Taubes's potential is the nonlinearity `(exp (2t) - 1) / 8`. -/
theorem hasDerivAt_taubesPotential (t : ℝ) :
    HasDerivAt taubesPotential ((Real.exp (2 * t) - 1) / 8) t := by
  have h2 : HasDerivAt (fun s : ℝ ↦ 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hφ : taubesPotential = fun s ↦ (Real.exp (2 * s) - 1 - 2 * s) / 16 :=
    funext taubesPotential_def
  rw [hφ]
  convert ((h2.exp.sub_const 1).sub h2).div_const 16 using 1
  ring

@[fun_prop]
theorem contDiff_taubesPotential {n : WithTop ℕ∞} : ContDiff ℝ n taubesPotential := by
  have hφ : taubesPotential = fun s ↦ (Real.exp (2 * s) - 1 - 2 * s) / 16 :=
    funext taubesPotential_def
  rw [hφ]
  fun_prop

@[fun_prop]
theorem continuous_taubesPotential : Continuous taubesPotential :=
  contDiff_taubesPotential (n := 0).continuous

/-- **Expansion of Taubes's potential**:
`φ(t + s) = φ(t) + φ'(t) s + exp (2t) φ(s)`, with `φ'(t) = (exp (2t) - 1) / 8`. The remainder is
nonnegative. -/
theorem taubesPotential_add (t s : ℝ) :
    taubesPotential (t + s) = taubesPotential t + (Real.exp (2 * t) - 1) / 8 * s +
      Real.exp (2 * t) * taubesPotential s := by
  simp only [taubesPotential_def, mul_add, Real.exp_add]
  ring

/-- Near `0`, Taubes's potential is at most quadratic: `φ(s) ≤ s² / 4` for `|s| ≤ 1 / 2`. -/
theorem taubesPotential_le_sq {s : ℝ} (hs : |s| ≤ 1 / 2) : taubesPotential s ≤ s ^ 2 / 4 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := 2 * s) (by rw [abs_mul, abs_two]; linarith)
  calc taubesPotential s ≤ (2 * s) ^ 2 / 16 := by
        rw [taubesPotential_def]
        gcongr
        exact (abs_le.mp h).2
    _ = s ^ 2 / 4 := by ring

/-! ### The functional -/

section Functional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h k w v : E → ℝ}

/-- The density `‖∇w‖² / 2 + h φ(w) + k w` of Taubes's functional, for coefficient functions `h`
and `k`. -/
def taubesDensity (h k w : E → ℝ) (x : E) : ℝ :=
  ‖∇ w x‖ ^ 2 / 2 + h x * taubesPotential (w x) + k x * w x

/-- The defining formula of `TauCeti.Vortex.taubesDensity`. -/
theorem taubesDensity_def (h k w : E → ℝ) (x : E) :
    taubesDensity h k w x = ‖∇ w x‖ ^ 2 / 2 + h x * taubesPotential (w x) + k x * w x := (rfl)

@[simp]
theorem taubesDensity_zero : taubesDensity h k 0 = 0 := by
  funext x
  simp [taubesDensity_def, Pi.zero_def]

/-- **Pointwise expansion of the density** along a perturbation `v`: the first-order term is
`⟪∇w, ∇v⟫ + (h φ'(w) + k) v`, and the remainder `‖∇v‖² / 2 + h exp (2w) φ(v)` is exact. -/
theorem taubesDensity_add {x : E} (hw : DifferentiableAt ℝ w x) (hv : DifferentiableAt ℝ v x) :
    taubesDensity h k (w + v) x = taubesDensity h k w x +
      (⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x) +
      (‖∇ v x‖ ^ 2 / 2 + h x * Real.exp (2 * w x) * taubesPotential (v x)) := by
  rw [taubesDensity_def, taubesDensity_def, TauCeti.gradient_add hw hv, norm_add_sq_real,
    Pi.add_apply, taubesPotential_add]
  ring

variable [MeasurableSpace E] {μ : Measure E}

variable (μ) in
/-- **Taubes's functional** `𝒜(w) = ∫ (‖∇w‖² / 2 + h φ(w) + k w)`, with
`φ(t) = (exp (2t) - 1 - 2t) / 16`. Its Euler–Lagrange equation is
`Δw = h (exp (2w) - 1) / 8 + k`. As a Bochner integral it is `0` when the density is not
integrable, so statements about it carry the integrability of the density as a hypothesis. -/
def taubesFunctional (h k w : E → ℝ) : ℝ :=
  ∫ x, taubesDensity h k w x ∂μ

/-- The defining formula of `TauCeti.Vortex.taubesFunctional`. -/
theorem taubesFunctional_def (h k w : E → ℝ) :
    taubesFunctional μ h k w = ∫ x, taubesDensity h k w x ∂μ := (rfl)

@[simp]
theorem taubesFunctional_zero : taubesFunctional μ h k 0 = 0 := by
  simp [taubesFunctional_def]

variable [BorelSpace E]

/-- The first-order term of the expansion is integrable. -/
private theorem integrable_firstVariation [IsFiniteMeasureOnCompacts μ] (hh : Continuous h)
    (hk : Continuous k) (hw : ContDiff ℝ 1 w) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    Integrable (fun x ↦ ⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x)
      μ := by
  have := hw.continuous_gradient one_ne_zero
  have := hv.continuous_gradient one_ne_zero
  have := hw.continuous
  have := hv.continuous
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact hvc.mono_of_forall_gradient fun x hx hgx ↦ by simp [hx, hgx]

/-- The remainder of the expansion is integrable. -/
private theorem integrable_secondVariation [IsFiniteMeasureOnCompacts μ] (hh : Continuous h)
    (hw : Continuous w) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    Integrable (fun x ↦ ‖∇ v x‖ ^ 2 / 2 + h x * Real.exp (2 * w x) * taubesPotential (v x))
      μ := by
  have := hv.continuous_gradient one_ne_zero
  have := hv.continuous
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact hvc.mono_of_forall_gradient fun x hx hgx ↦ by simp [hx, hgx]

/-- **The exact second-order expansion of Taubes's functional.** For continuous coefficients, a
`C¹` function `w` with integrable density and a compactly supported `C¹` perturbation `v`,
`𝒜(w + v) = 𝒜(w) + ∫ (⟪∇w, ∇v⟫ + (h φ'(w) + k) v) + ∫ (‖∇v‖² / 2 + h exp (2w) φ(v))`. -/
theorem taubesFunctional_add [IsFiniteMeasureOnCompacts μ] (hh : Continuous h) (hk : Continuous k)
    (hw : ContDiff ℝ 1 w) (hwi : Integrable (taubesDensity h k w) μ) (hv : ContDiff ℝ 1 v)
    (hvc : HasCompactSupport v) :
    taubesFunctional μ h k (w + v) = taubesFunctional μ h k w +
      ∫ x, (⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x) ∂μ +
      ∫ x, (‖∇ v x‖ ^ 2 / 2 + h x * Real.exp (2 * w x) * taubesPotential (v x)) ∂μ := by
  have h1 := integrable_firstVariation (μ := μ) hh hk hw hv hvc
  have h2 := integrable_secondVariation (μ := μ) hh hw.continuous hv hvc
  rw [taubesFunctional_def, taubesFunctional_def, ← integral_add hwi h1,
    ← integral_add (f := fun x ↦ taubesDensity h k w x +
      (⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x)) (hwi.add h1) h2]
  exact integral_congr_ae (ae_of_all _ fun x ↦
    taubesDensity_add (hw.differentiable one_ne_zero x) (hv.differentiable one_ne_zero x))

/-- A compactly supported perturbation preserves the integrability of the density. -/
theorem integrable_taubesDensity_add [IsFiniteMeasureOnCompacts μ] (hh : Continuous h)
    (hk : Continuous k) (hw : ContDiff ℝ 1 w) (hwi : Integrable (taubesDensity h k w) μ)
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) : Integrable (taubesDensity h k (w + v)) μ :=
  ((hwi.add (integrable_firstVariation hh hk hw hv hvc)).add
    (integrable_secondVariation hh hw.continuous hv hvc)).congr
      (ae_of_all _ fun x ↦ (taubesDensity_add (hw.differentiable one_ne_zero x)
        (hv.differentiable one_ne_zero x)).symm)

/-- For continuous coefficients, the density of a compactly supported `C¹` function is
integrable, so Taubes's functional is finite on such functions. -/
theorem integrable_taubesDensity_of_hasCompactSupport [IsFiniteMeasureOnCompacts μ]
    (hh : Continuous h) (hk : Continuous k) (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) :
    Integrable (taubesDensity h k w) μ := by
  simpa using integrable_taubesDensity_add (μ := μ) (w := 0) hh hk contDiff_zero_fun
    (by simp) hw hwc

/-- Along a compactly supported `C¹` direction `v`, the remainder
`∫ (t² ‖∇v‖² / 2 + h exp (2w) φ(t v))` of the expansion of `𝒜(w + t v)` is `O(t²)` as `t → 0`:
near `t = 0`, `φ(t v) ≤ t² v² / 4`. -/
private theorem isBigO_remainder_taubesFunctional [IsFiniteMeasureOnCompacts μ] (hh : Continuous h)
    (hw : Continuous w) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    (fun t : ℝ ↦ ∫ x, (t ^ 2 * (‖∇ v x‖ ^ 2 / 2) +
      h x * Real.exp (2 * w x) * taubesPotential (t * v x)) ∂μ) =O[𝓝 0] fun t ↦ t ^ 2 := by
  obtain ⟨M, hM⟩ := hv.continuous.bounded_above_of_compact_support hvc
  set B : E → ℝ := fun x ↦ ‖∇ v x‖ ^ 2 / 2 + |h x| * Real.exp (2 * w x) * (v x ^ 2 / 4)
  have hB : Integrable B μ := by
    have := hv.continuous_gradient one_ne_zero
    have := hv.continuous
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hvc.mono_of_forall_gradient fun x hx hgx ↦ by simp [B, hx, hgx]
  refine IsBigO.of_bound (∫ x, B x ∂μ) ?_
  have hr : (0 : ℝ) < 1 / (2 * (|M| + 1)) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
  rw [Metric.mem_ball, Real.dist_0_eq_abs] at ht
  have hpt (x : E) : ‖t ^ 2 * (‖∇ v x‖ ^ 2 / 2) +
      h x * Real.exp (2 * w x) * taubesPotential (t * v x)‖ ≤ t ^ 2 * B x := by
    have htv : |t * v x| ≤ 1 / 2 := by
      rw [abs_mul]
      calc |t| * |v x| ≤ 1 / (2 * (|M| + 1)) * (|M| + 1) := by
            gcongr
            exact ((Real.norm_eq_abs _).symm.trans_le (hM x)).trans (by linarith [le_abs_self M])
        _ = 1 / 2 := by field_simp
    have hφ := taubesPotential_le_sq htv
    have hφ0 := taubesPotential_nonneg (t * v x)
    have he := Real.exp_pos (2 * w x)
    calc ‖t ^ 2 * (‖∇ v x‖ ^ 2 / 2) + h x * Real.exp (2 * w x) * taubesPotential (t * v x)‖
        ≤ |t ^ 2 * (‖∇ v x‖ ^ 2 / 2)| +
            |h x * Real.exp (2 * w x) * taubesPotential (t * v x)| := by
          rw [Real.norm_eq_abs]
          exact abs_add_le _ _
      _ ≤ t ^ 2 * (‖∇ v x‖ ^ 2 / 2) + |h x| * Real.exp (2 * w x) * ((t * v x) ^ 2 / 4) := by
          rw [abs_of_nonneg (by positivity), abs_mul, abs_mul, abs_of_pos he,
            abs_of_nonneg hφ0]
          gcongr
      _ = t ^ 2 * B x := by
          simp only [B]
          ring
  calc _ ≤ ∫ x, t ^ 2 * B x ∂μ :=
        norm_integral_le_of_norm_le (hB.const_mul _) (ae_of_all _ hpt)
    _ = (∫ x, B x ∂μ) * ‖t ^ 2‖ := by
        rw [integral_const_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]

/-- **The first variation of Taubes's functional.** For continuous coefficients, a `C¹` function
`w` with integrable density and a compactly supported `C¹` direction `v`, the function
`t ↦ 𝒜(w + t v)` has derivative `∫ (⟪∇w, ∇v⟫ + (h (exp (2w) - 1) / 8 + k) v)` at `t = 0`. -/
theorem hasDerivAt_taubesFunctional_add_smul [IsFiniteMeasureOnCompacts μ] (hh : Continuous h)
    (hk : Continuous k) (hw : ContDiff ℝ 1 w) (hwi : Integrable (taubesDensity h k w) μ)
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    HasDerivAt (fun t : ℝ ↦ taubesFunctional μ h k (w + t • v))
      (∫ x, (⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x) ∂μ) 0 := by
  set D := ∫ x, (⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x) ∂μ
    with hD
  -- The remainder along the line `w + t v`.
  set R : ℝ → ℝ := fun t ↦ ∫ x, (t ^ 2 * (‖∇ v x‖ ^ 2 / 2) +
    h x * Real.exp (2 * w x) * taubesPotential (t * v x)) ∂μ with hR_def
  have hexp (t : ℝ) :
      taubesFunctional μ h k (w + t • v) = taubesFunctional μ h k w + t * D + R t := by
    have hgrad (x : E) : ∇ (t • v) x = t • ∇ v x := by
      simp [TauCeti.gradient_const_smul]
    have h1 : ∫ x, (⟪∇ w x, ∇ (t • v) x⟫_ℝ +
        (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * (t • v) x) ∂μ = t * D := by
      rw [hD, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only [hgrad, Pi.smul_apply, smul_eq_mul, inner_smul_right]
      ring
    have h2 : ∫ x, (‖∇ (t • v) x‖ ^ 2 / 2 +
        h x * Real.exp (2 * w x) * taubesPotential ((t • v) x)) ∂μ = R t := by
      rw [hR_def]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only [hgrad, Pi.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hcd : ContDiff ℝ 1 (t • v) := hv.const_smul t
    rw [taubesFunctional_add hh hk hw hwi hcd
      (hvc.mono (Function.support_const_smul_subset t v)), h1, h2]
  have hRO : R =O[𝓝 0] fun t ↦ t ^ 2 :=
    isBigO_remainder_taubesFunctional hh hw.continuous hv hvc
  have hRd : HasDerivAt R 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hR0 : R 0 = 0 := by simp [R]
    simpa [hR0] using hRO.trans_isLittleO (isLittleO_pow_id one_lt_two)
  convert (((hasDerivAt_id (0 : ℝ)).const_mul D).const_add (taubesFunctional μ h k w)).add hRd
    using 1
  · funext t
    simp only [hexp, Pi.add_apply, id]
    ring
  · simp

/-- Green's identity turns the first variation into `∫ v (-Δw + h (exp (2w) - 1) / 8 + k)` for a
`C²` function `w`. -/
private theorem integral_firstVariation_eq [μ.IsAddHaarMeasure] (hh : Continuous h)
    (hk : Continuous k) (hw : ContDiff ℝ 2 w) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
    ∫ x, (⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x) ∂μ =
      ∫ x, v x * (-Δ w x + h x * (Real.exp (2 * w x) - 1) / 8 + k x) ∂μ := by
  have := hw.continuous_gradient two_ne_zero
  have := hv.continuous_gradient one_ne_zero
  have := hw.continuous
  have := hv.continuous
  have := hw.continuous_laplacian
  have hI1 : Integrable (fun x ↦ ⟪∇ w x, ∇ v x⟫_ℝ) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hvc.mono_of_forall_gradient fun x _ hgx ↦ by simp [hgx])
  have hI2 : Integrable (fun x ↦ (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hvc.mul_left
  have hI3 : Integrable (fun x ↦ v x * Δ w x) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hvc.mul_right
  rw [integral_add hI1 hI2, integral_inner_gradient_eq_neg_integral_mul_laplacian hw hv hvc,
    ← integral_neg, ← integral_add (f := fun x ↦ -(v x * Δ w x)) hI3.neg hI2]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)

/-- **The Euler–Lagrange equation of Taubes's functional.** For continuous coefficients and a
`C²` function `w` with integrable density, `w` is a critical point of `𝒜` along every compactly
supported `C¹` direction exactly when it solves `Δw = h (exp (2w) - 1) / 8 + k`. -/
theorem forall_hasDerivAt_taubesFunctional_add_smul_iff [μ.IsAddHaarMeasure] (hh : Continuous h)
    (hk : Continuous k) (hw : ContDiff ℝ 2 w) (hwi : Integrable (taubesDensity h k w) μ) :
    (∀ v : E → ℝ, ContDiff ℝ 1 v → HasCompactSupport v →
        HasDerivAt (fun t : ℝ ↦ taubesFunctional μ h k (w + t • v)) 0 0) ↔
      ∀ x, Δ w x = h x * (Real.exp (2 * w x) - 1) / 8 + k x := by
  set F : E → ℝ := fun x ↦ -Δ w x + h x * (Real.exp (2 * w x) - 1) / 8 + k x
  have hF : Continuous F := by
    have := hw.continuous
    have := hw.continuous_laplacian
    fun_prop
  have hderiv (v : E → ℝ) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) :
      HasDerivAt (fun t : ℝ ↦ taubesFunctional μ h k (w + t • v)) (∫ x, v x * F x ∂μ) 0 := by
    rw [← integral_firstVariation_eq hh hk hw hv hvc]
    exact hasDerivAt_taubesFunctional_add_smul hh hk (hw.of_le one_le_two) hwi hv hvc
  constructor
  · intro hcrit
    have hae : ∀ᵐ x ∂μ, F x = 0 :=
      ae_eq_zero_of_integral_contDiff_smul_eq_zero hF.locallyIntegrable fun g hg hgc ↦ by
        have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
        simpa only [smul_eq_mul] using (hderiv g hg1 hgc).unique (hcrit g hg1 hgc)
    have hF0 : F = 0 := (hF.ae_eq_iff_eq μ continuous_const).1 hae
    intro x
    have := congr_fun hF0 x
    simp only [F, Pi.zero_apply] at this
    linarith
  · intro heq v hv hvc
    have h0 : ∫ x, v x * F x ∂μ = 0 :=
      integral_eq_zero_of_ae (ae_of_all _ fun x ↦ by simp only [F, heq x, Pi.zero_apply]; ring)
    simpa only [h0] using hderiv v hv hvc

/-- **Convexity of Taubes's functional.** For continuous coefficients with `h ≥ 0`, `𝒜` lies above
its tangent line at a `C¹` function `w` with integrable density, in every compactly supported `C¹`
direction `v`. -/
theorem taubesFunctional_add_integral_le [IsFiniteMeasureOnCompacts μ] (hh₀ : ∀ x, 0 ≤ h x)
    (hh : Continuous h) (hk : Continuous k) (hw : ContDiff ℝ 1 w)
    (hwi : Integrable (taubesDensity h k w) μ) (hv : ContDiff ℝ 1 v)
    (hvc : HasCompactSupport v) :
    taubesFunctional μ h k w +
        ∫ x, (⟪∇ w x, ∇ v x⟫_ℝ + (h x * (Real.exp (2 * w x) - 1) / 8 + k x) * v x) ∂μ ≤
      taubesFunctional μ h k (w + v) := by
  rw [taubesFunctional_add hh hk hw hwi hv hvc, le_add_iff_nonneg_right]
  exact integral_nonneg fun x ↦ add_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (hh₀ x) (Real.exp_pos _).le) (taubesPotential_nonneg _))

/-- **A solution strictly minimizes Taubes's functional among its compactly supported
perturbations.** On a nonzero space, let the coefficients be continuous with `h ≥ 0`, and let `w`
be a `C²` solution of `Δw = h (exp (2w) - 1) / 8 + k` with integrable density. Then
`𝒜(w) < 𝒜(w + v)` for every nonzero compactly supported `C¹` function `v`. -/
theorem taubesFunctional_lt_add [Nontrivial E] [μ.IsAddHaarMeasure] (hh₀ : ∀ x, 0 ≤ h x)
    (hh : Continuous h) (hk : Continuous k) (hw : ContDiff ℝ 2 w)
    (hwi : Integrable (taubesDensity h k w) μ)
    (heq : ∀ x, Δ w x = h x * (Real.exp (2 * w x) - 1) / 8 + k x) (hv : ContDiff ℝ 1 v)
    (hvc : HasCompactSupport v) (hv₀ : v ≠ 0) :
    taubesFunctional μ h k w < taubesFunctional μ h k (w + v) := by
  rw [taubesFunctional_add hh hk (hw.of_le one_le_two) hwi hv hvc,
    integral_firstVariation_eq hh hk hw hv hvc,
    integral_eq_zero_of_ae (ae_of_all _ fun x ↦ by simp only [heq x, Pi.zero_apply]; ring),
    add_zero, lt_add_iff_pos_right]
  set g : E → ℝ := fun x ↦ ‖∇ v x‖ ^ 2 / 2 + h x * Real.exp (2 * w x) * taubesPotential (v x)
  have hrem (x : E) : 0 ≤ h x * Real.exp (2 * w x) * taubesPotential (v x) :=
    mul_nonneg (mul_nonneg (hh₀ x) (Real.exp_pos _).le) (taubesPotential_nonneg _)
  have hg₀ : 0 ≤ g := fun x ↦ add_nonneg (by positivity) (hrem x)
  have hgc : Continuous g := by
    have := hv.continuous_gradient one_ne_zero
    have := hv.continuous
    have := hw.continuous
    fun_prop
  -- `g` is not identically zero: otherwise `∇v = 0`, so `v` is constant, hence zero.
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
    by_contra! hzero
    apply hv₀
    have hd (x : E) : fderiv ℝ v x = 0 := by
      have hgx : ‖∇ v x‖ ^ 2 / 2 + h x * Real.exp (2 * w x) * taubesPotential (v x) = 0 :=
        hzero x
      have hsq : ‖∇ v x‖ ^ 2 = 0 := by linarith [hrem x, sq_nonneg ‖∇ v x‖]
      rw [← norm_eq_zero, ← TauCeti.norm_gradient_eq_norm_fderiv]
      exact pow_eq_zero_iff two_ne_zero |>.mp hsq
    obtain ⟨y, hy⟩ := ne_univ_iff_exists_notMem _ |>.mp hvc.isCompact.ne_univ
    funext x
    rw [is_const_of_fderiv_eq_zero (hv.differentiable one_ne_zero) hd x y,
      image_eq_zero_of_notMem_tsupport hy, Pi.zero_apply]
  exact hgc.integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (hvc.mono_of_forall_gradient fun x hx hgx ↦ by simp [g, hx, hgx]) hg₀ hx

end Functional

/-! ### The reduced vortex equation -/

section Vortex

variable {f : ℂ → ℂ} {w : ℂ → ℝ}

/-- The source `k = (h - 1) / 8 + 2 ‖f'‖² / (1 + ‖f‖²)²` of the reduced vortex equation, written
as an Euler–Lagrange equation of Taubes's functional. When `f` is holomorphic,
`2 ‖f'‖² / (1 + ‖f‖²)² = -Δu₀` for the background amplitude `u₀`
(`TauCeti.Vortex.laplacian_backgroundAmplitude`). -/
def backgroundSource (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (backgroundWeight f z - 1) / 8 + 2 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2

/-- The defining formula of `TauCeti.Vortex.backgroundSource`. -/
theorem backgroundSource_def (f : ℂ → ℂ) (z : ℂ) :
    backgroundSource f z =
      (backgroundWeight f z - 1) / 8 + 2 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2 := (rfl)

theorem continuous_backgroundSource (hf : Differentiable ℂ f) :
    Continuous (backgroundSource f) := by
  have hf' : Continuous (deriv f) := hf.contDiff.continuous_deriv le_top
  have hw := continuous_backgroundWeight hf.continuous
  have hk : backgroundSource f = fun z ↦
      (backgroundWeight f z - 1) / 8 + 2 * ‖deriv f z‖ ^ 2 / (1 + ‖f z‖ ^ 2) ^ 2 :=
    funext (backgroundSource_def f)
  rw [hk]
  exact ((hw.sub continuous_const).div_const 8).add
    ((continuous_const.mul (hf'.norm.pow 2)).div
      ((continuous_const.add (hf.continuous.norm.pow 2)).pow 2) fun z ↦ by positivity)

/-- **The Euler–Lagrange equation for the background coefficients is the vortex equation.** For a
holomorphic `f`, the function `w` solves `Δw = h (exp (2w) - 1) / 8 + k` at `z`, with the
background coefficients `h` and `k`, exactly when the field reconstructed from the amplitude
`u₀ + w` and the section `f` solves the vortex equation at `z`. -/
theorem laplacian_eq_iff_equation_amplitudeField_backgroundAmplitude_add_eq_zero {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hw : ContDiffAt ℝ 2 w z) :
    Δ w z = backgroundWeight f z * (Real.exp (2 * w z) - 1) / 8 + backgroundSource f z ↔
      equation (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) z = 0 := by
  rw [equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff hf hw, backgroundSource_def]
  constructor <;> intro H <;> rw [H] <;> ring

/-- **Vortex amplitudes are the critical points of Taubes's functional.** For an entire function
`f` and a `C²` function `w` whose density for the background coefficients is integrable, `w` is a
critical point of `𝒜` along every compactly supported `C¹` direction exactly when the field
reconstructed from the amplitude `u₀ + w` and the section `f` solves the vortex equation. -/
theorem forall_hasDerivAt_taubesFunctional_add_smul_iff_equation_amplitudeField
    (hf : Differentiable ℂ f) (hw : ContDiff ℝ 2 w)
    (hwi : Integrable (taubesDensity (backgroundWeight f) (backgroundSource f) w)) :
    (∀ v : ℂ → ℝ, ContDiff ℝ 1 v → HasCompactSupport v →
        HasDerivAt (fun t : ℝ ↦
          taubesFunctional volume (backgroundWeight f) (backgroundSource f) (w + t • v)) 0 0) ↔
      ∀ z, equation (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) z = 0 := by
  rw [forall_hasDerivAt_taubesFunctional_add_smul_iff (continuous_backgroundWeight hf.continuous)
    (continuous_backgroundSource hf) hw hwi]
  exact forall_congr' fun z ↦
    laplacian_eq_iff_equation_amplitudeField_backgroundAmplitude_add_eq_zero (hf.analyticAt z)
      hw.contDiffAt

/-- **A vortex amplitude strictly minimizes Taubes's functional among its compactly supported
perturbations.** For an entire function `f` and a `C²` function `w` with integrable density for
the background coefficients, if the field reconstructed from the amplitude `u₀ + w` and the
section `f` solves the vortex equation, then `𝒜(w) < 𝒜(w + v)` for every nonzero compactly
supported `C¹` function `v`. -/
theorem taubesFunctional_lt_add_of_equation_amplitudeField (hf : Differentiable ℂ f)
    (hw : ContDiff ℝ 2 w)
    (hwi : Integrable (taubesDensity (backgroundWeight f) (backgroundSource f) w))
    (hsol : ∀ z, equation (amplitudeField (fun z ↦ backgroundAmplitude f z + w z) f) z = 0)
    {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (hv₀ : v ≠ 0) :
    taubesFunctional volume (backgroundWeight f) (backgroundSource f) w <
      taubesFunctional volume (backgroundWeight f) (backgroundSource f) (w + v) :=
  taubesFunctional_lt_add (backgroundWeight_nonneg f) (continuous_backgroundWeight hf.continuous)
    (continuous_backgroundSource hf) hw hwi
    (fun z ↦ (laplacian_eq_iff_equation_amplitudeField_backgroundAmplitude_add_eq_zero
      (hf.analyticAt z) hw.contDiffAt).2 (hsol z)) hv hvc hv₀

end Vortex

end TauCeti.Vortex
