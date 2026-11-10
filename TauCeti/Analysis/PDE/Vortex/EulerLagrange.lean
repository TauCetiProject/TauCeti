/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ReducedFunctional
public import TauCeti.Analysis.PDE.Vortex.Variational
public import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.PDE.Vortex.Minimizer
import TauCeti.Analysis.SpecialFunctions.Exp.Modular

/-!
# The weak Euler–Lagrange equation of Taubes's functional

Let `P` be a complex polynomial of degree `m ≥ 1`, and let `h = ‖P‖² / (1 + ‖P‖²)`
(`TauCeti.Vortex.backgroundWeight`) and `k = (h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`
(`TauCeti.Vortex.backgroundSource`) be the coefficients of the reduced vortex equation

`Δw = h (exp (2w) - 1) / 8 + k`.

Taubes's functional `I` on `H¹(ℂ) = W^{1,2}(ℂ)` (`TauCeti.Vortex.sobolevReducedFunctional`) has a
minimizer (`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`). This file shows that a
minimizer is a weak solution of the reduced equation.

Write `w` for the value of `u ∈ H¹(ℂ)`. When `I(u)` is finite, `h exp (2w)` is integrable against
`ψ²` for every bounded `ψ ∈ L²(ℂ)`: since `exp (2w) = (exp (2w) - 1 - 2w) + 1 + 2w` and
`0 ≤ h ≤ 1`, it is bounded by the potential, `ψ²` and `|w| |ψ|`. Along an essentially bounded
direction `v ∈ H¹(ℂ)` with value `ψ`, the expansion
`φ(a + s) = φ(a) + φ'(a) s + exp (2a) φ(s)` of Taubes's potential
`φ(t) = (exp (2t) - 1 - 2t) / 16` (`TauCeti.Vortex.taubesPotential_add`) then gives, for small
`t`, the exact expansion

`I(u + t v) = I(u) + t D + t² ‖∇v‖₂² / 2 + ∫ h exp (2w) φ(t ψ)`,

with `D = ⟪∇u, ∇v⟫ + ∫ (h (exp (2w) - 1) / 8 + k) ψ`. The last term is `O(t²)` because
`φ(s) ≤ s² / 4` for `|s| ≤ 1 / 2`. This is the `H¹` counterpart of
`TauCeti.Vortex.hasDerivAt_taubesFunctional_add_smul`, which treats `C¹` functions.

## Main results

* `TauCeti.Vortex.eventually_sobolevReducedFunctional_add_smul_ne_top`: a finite value of `I`
  stays finite along an essentially bounded direction for small steps.
* `TauCeti.Vortex.hasDerivAt_toReal_sobolevReducedFunctional_add_smul`: the first variation of
  `I` at `u` in an essentially bounded direction `v` is `D`.
* `TauCeti.Vortex.inner_gradient_add_integral_eq_zero_of_isLocalMin`: at a local minimizer with
  finite value, `D = 0` for every essentially bounded direction.
* `TauCeti.Vortex.locallyIntegrable_backgroundWeight_mul_add_backgroundSource`: when `I(u)` is
  finite, the right-hand side `h (exp (2w) - 1) / 8 + k` is locally integrable.
* `TauCeti.Vortex.exists_forall_integral_inner_gradient_add_integral_eq_zero`: the reduced
  equation has a weak solution in `H¹(ℂ)`: some minimizer `u` of `I` satisfies
  `∫ ⟪∇u, ∇φ⟫ + ∫ (h (exp (2w) - 1) / 8 + k) φ = 0` for every compactly supported `C¹`
  function `φ`.

The regularity of the weak solution is not treated here. A `C²` solution of the reduced equation
gives a vortex with zero divisor `P` by
`TauCeti.Vortex.laplacian_eq_iff_equation_amplitudeField_backgroundAmplitude_add_eq_zero`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal Gradient

variable {P : Polynomial ℂ}

/-! ### Pointwise identities and integrability -/

/-- The coefficient of the linear term of Taubes's functional on `H¹(ℂ)` is the source
`TauCeti.Vortex.backgroundSource` of the reduced equation. -/
private theorem two_mul_norm_derivative_eval_sq_div_sub_eq_backgroundSource (z : ℂ) :
    2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8 =
      backgroundSource P.eval z := by
  have h1 : (1 + ‖P.eval z‖ ^ 2) ≠ 0 := by positivity
  rw [backgroundSource_def, backgroundWeight_def, Polynomial.deriv]
  field_simp
  ring

private theorem continuous_backgroundWeight_eval : Continuous (backgroundWeight P.eval) :=
  continuous_backgroundWeight P.continuous

private theorem continuous_backgroundSource_eval : Continuous (backgroundSource P.eval) :=
  continuous_backgroundSource P.differentiable

/-- If the potential `h (exp (2w) - 1 - 2w)` is integrable and `w ∈ L²(ℂ)`, then `h exp (2w) ψ²` is
integrable for every essentially bounded `ψ ∈ L²(ℂ)`. -/
private theorem integrable_backgroundWeight_mul_exp_mul_sq {w ψ : ℂ → ℝ} (hw : MemLp w 2)
    (hψ : MemLp ψ 2) {M : ℝ} (hψM : ∀ᵐ z, |ψ z| ≤ M)
    (hpot : Integrable fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z)) :
    Integrable fun z ↦ backgroundWeight P.eval z * Real.exp (2 * w z) * ψ z ^ 2 := by
  have hbound : Integrable fun z ↦ M ^ 2 * (backgroundWeight P.eval z *
      (Real.exp (2 * w z) - 1 - 2 * w z)) + ψ z ^ 2 + 2 * M * (|w z| * |ψ z|) :=
    ((hpot.const_mul _).add hψ.integrable_sq).add
      ((hw.abs.integrable_mul hψ.abs).const_mul _)
  refine hbound.mono' ((continuous_backgroundWeight_eval.aestronglyMeasurable.mul
    (Real.continuous_exp.comp_aestronglyMeasurable (hw.aestronglyMeasurable.const_mul 2))).mul
      (hψ.aestronglyMeasurable.pow 2)) ?_
  filter_upwards [hψM] with z hz
  have hh0 := backgroundWeight_nonneg P.eval z
  have hh1 := backgroundWeight_le_one P.eval z
  have hp := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (w z)
  have hψ2 : ψ z ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have hψ2' : ψ z ^ 2 ≤ M * |ψ z| := by
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have hwψ : backgroundWeight P.eval z * w z * ψ z ^ 2 ≤ M * (|w z| * |ψ z|) := by
    calc backgroundWeight P.eval z * w z * ψ z ^ 2 ≤ |w z| * ψ z ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact (mul_le_mul_of_nonneg_left (le_abs_self _) hh0).trans
            (mul_le_of_le_one_left (abs_nonneg _) hh1)
      _ ≤ |w z| * (M * |ψ z|) := mul_le_mul_of_nonneg_left hψ2' (abs_nonneg _)
      _ = M * (|w z| * |ψ z|) := by ring
  rw [Real.norm_of_nonneg (by positivity)]
  have hpψ : backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z) * ψ z ^ 2 ≤
      M ^ 2 * (backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z)) := by
    rw [mul_comm (M ^ 2)]
    exact mul_le_mul_of_nonneg_left hψ2 (mul_nonneg hh0 hp)
  have hhψ : backgroundWeight P.eval z * ψ z ^ 2 ≤ ψ z ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) hh1
  nlinarith

/-- If the potential `h (exp (2w) - 1 - 2w)` is integrable and `w ∈ L²(ℂ)`, then
`h (exp (2w) - 1) ψ` is integrable for every essentially bounded `ψ ∈ L²(ℂ)`. -/
private theorem integrable_backgroundWeight_mul_exp_sub_one_mul {w ψ : ℂ → ℝ} (hw : MemLp w 2)
    (hψ : MemLp ψ 2) {M : ℝ} (hψM : ∀ᵐ z, |ψ z| ≤ M)
    (hpot : Integrable fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z)) :
    Integrable fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * w z) - 1) * ψ z := by
  have hbound : Integrable fun z ↦ M * (backgroundWeight P.eval z *
      (Real.exp (2 * w z) - 1 - 2 * w z)) + 2 * (|w z| * |ψ z|) :=
    (hpot.const_mul _).add ((hw.abs.integrable_mul hψ.abs).const_mul _)
  refine hbound.mono' ((continuous_backgroundWeight_eval.aestronglyMeasurable.mul
    ((Real.continuous_exp.comp_aestronglyMeasurable (hw.aestronglyMeasurable.const_mul 2)).sub
      aestronglyMeasurable_const)).mul hψ.aestronglyMeasurable) ?_
  filter_upwards [hψM] with z hz
  have hh0 := backgroundWeight_nonneg P.eval z
  have hh1 := backgroundWeight_le_one P.eval z
  have hp := Real.exp_two_mul_sub_one_sub_two_mul_nonneg (w z)
  have hsplit : backgroundWeight P.eval z * (Real.exp (2 * w z) - 1) * ψ z =
      backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z) * ψ z +
        2 * (backgroundWeight P.eval z * (w z * ψ z)) := by ring
  rw [hsplit, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (mul_nonneg hh0 hp), mul_comm M]
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg hh0 hp)
  · rw [abs_mul, abs_two, abs_mul, abs_of_nonneg hh0, ← abs_mul]
    gcongr
    exact mul_le_of_le_one_left (abs_nonneg _) hh1

/-- For `|s| ≤ 1 / 2`, `0 ≤ h exp (2a) φ(s) ≤ s² / 4 · h exp (2a)`, with `φ` Taubes's potential. -/
private theorem norm_backgroundWeight_mul_exp_mul_taubesPotential_le (z : ℂ) (a : ℝ) {t b : ℝ}
    (hs : |t * b| ≤ 1 / 2) :
    ‖backgroundWeight P.eval z * Real.exp (2 * a) * taubesPotential (t * b)‖ ≤
      t ^ 2 / 4 * (backgroundWeight P.eval z * Real.exp (2 * a) * b ^ 2) := by
  have he : 0 ≤ backgroundWeight P.eval z * Real.exp (2 * a) :=
    mul_nonneg (backgroundWeight_nonneg _ _) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg (mul_nonneg he (taubesPotential_nonneg _))]
  calc backgroundWeight P.eval z * Real.exp (2 * a) * taubesPotential (t * b)
      ≤ backgroundWeight P.eval z * Real.exp (2 * a) * ((t * b) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (taubesPotential_le_sq hs) he
    _ = t ^ 2 / 4 * (backgroundWeight P.eval z * Real.exp (2 * a) * b ^ 2) := by ring

/-- If the potential `h (exp (2w) - 1 - 2w)` is integrable, `w ∈ L²(ℂ)`, and `|t ψ| ≤ 1 / 2`
almost everywhere for some essentially bounded `ψ ∈ L²(ℂ)`, then `h exp (2w) φ(t ψ)` is
integrable. -/
private theorem integrable_backgroundWeight_mul_exp_mul_taubesPotential {w ψ : ℂ → ℝ}
    (hw : MemLp w 2) (hψ : MemLp ψ 2) {M : ℝ} (hψM : ∀ᵐ z, |ψ z| ≤ M)
    (hpot : Integrable fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z))
    {t : ℝ} (htψ : ∀ᵐ z, |t * ψ z| ≤ 1 / 2) :
    Integrable fun z ↦
      backgroundWeight P.eval z * Real.exp (2 * w z) * taubesPotential (t * ψ z) := by
  refine ((integrable_backgroundWeight_mul_exp_mul_sq hw hψ hψM hpot).const_mul (t ^ 2 / 4)).mono'
    ((continuous_backgroundWeight_eval.aestronglyMeasurable.mul
      (Real.continuous_exp.comp_aestronglyMeasurable (hw.aestronglyMeasurable.const_mul 2))).mul
        (continuous_taubesPotential.comp_aestronglyMeasurable
          (hψ.aestronglyMeasurable.const_mul t))) ?_
  filter_upwards [htψ] with z hz
  exact norm_backgroundWeight_mul_exp_mul_taubesPotential_le z (w z) hz

/-- The pointwise expansion of the potential: with `φ` Taubes's potential,
`h (exp (2(a + s)) - 1 - 2(a + s)) = h (exp (2a) - 1 - 2a) + 2 h (exp (2a) - 1) s
+ 16 h exp (2a) φ(s)`. -/
private theorem mul_exp_sub_one_sub_add_eq (h a s : ℝ) :
    h * (Real.exp (2 * (a + s)) - 1 - 2 * (a + s)) =
      h * (Real.exp (2 * a) - 1 - 2 * a) + 2 * (h * (Real.exp (2 * a) - 1) * s) +
        16 * (h * Real.exp (2 * a) * taubesPotential s) := by
  have := taubesPotential_add a s
  simp only [taubesPotential_def] at this ⊢
  linear_combination 16 * h * this

/-- **The potential along an essentially bounded direction.** If the potential of `w ∈ L²(ℂ)` is
integrable and `|t| M ≤ 1 / 2`, where `|ψ| ≤ M` almost everywhere for `ψ ∈ L²(ℂ)`, then the
potential of `w + t ψ` is integrable, with integral
`∫ h (exp (2w) - 1 - 2w) + t ∫ 2 h (exp (2w) - 1) ψ + 16 ∫ h exp (2w) φ(t ψ)`. -/
private theorem integrable_potential_add_smul_and_integral_eq {w ψ : ℂ → ℝ} (hw : MemLp w 2)
    (hψ : MemLp ψ 2) {M : ℝ} (hψM : ∀ᵐ z, |ψ z| ≤ M)
    (hpot : Integrable fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z))
    {t : ℝ} (ht : |t| * M ≤ 1 / 2) :
    (Integrable fun z ↦ backgroundWeight P.eval z *
      (Real.exp (2 * (w z + t * ψ z)) - 1 - 2 * (w z + t * ψ z))) ∧
    ∫ z, backgroundWeight P.eval z * (Real.exp (2 * (w z + t * ψ z)) - 1 - 2 * (w z + t * ψ z)) =
      (∫ z, backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z)) +
        t * (2 * ∫ z, backgroundWeight P.eval z * (Real.exp (2 * w z) - 1) * ψ z) +
        16 * ∫ z, backgroundWeight P.eval z * Real.exp (2 * w z) * taubesPotential (t * ψ z) := by
  have htψ : ∀ᵐ z, |t * ψ z| ≤ 1 / 2 := by
    filter_upwards [hψM] with z hz
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hz (abs_nonneg t)).trans ht
  have hC := ((integrable_backgroundWeight_mul_exp_sub_one_mul hw hψ hψM hpot).const_mul
    2).const_mul t
  have hA : Integrable fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z) +
      t * (2 * (backgroundWeight P.eval z * (Real.exp (2 * w z) - 1) * ψ z)) :=
    hpot.add hC
  have hB : Integrable fun z ↦
      16 * (backgroundWeight P.eval z * Real.exp (2 * w z) * taubesPotential (t * ψ z)) :=
    (integrable_backgroundWeight_mul_exp_mul_taubesPotential hw hψ hψM hpot htψ).const_mul 16
  have hexp (z : ℂ) : backgroundWeight P.eval z *
      (Real.exp (2 * (w z + t * ψ z)) - 1 - 2 * (w z + t * ψ z)) =
      (backgroundWeight P.eval z * (Real.exp (2 * w z) - 1 - 2 * w z) +
        t * (2 * (backgroundWeight P.eval z * (Real.exp (2 * w z) - 1) * ψ z))) +
        16 * (backgroundWeight P.eval z * Real.exp (2 * w z) * taubesPotential (t * ψ z)) := by
    rw [mul_exp_sub_one_sub_add_eq]
    ring
  simp only [hexp]
  refine ⟨hA.add hB, ?_⟩
  rw [integral_add hA hB, integral_add hpot hC, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-! ### The expansion along a bounded direction -/

/-- The value of an element of `H¹(ℂ)` is square integrable for Lebesgue measure. -/
private theorem memLp_value_volume (u : W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (W1p.value u : ℂ → ℝ) 2 := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.value u)

/-- For small `t`, `|t| M < 1 / 2`. -/
private theorem eventually_abs_mul_lt_one_half (M : ℝ) : ∀ᶠ t : ℝ in 𝓝 0, |t| * M < 1 / 2 := by
  have : Tendsto (fun t : ℝ ↦ |t| * M) (𝓝 0) (𝓝 (|0| * M)) :=
    (continuous_abs.mul continuous_const).tendsto 0
  rw [abs_zero, zero_mul] at this
  exact this.eventually_lt_const (by norm_num)

/-- The value of `u + t v` is almost everywhere `w + t ψ`. -/
private theorem value_add_smul_ae (u v : W1p (volume : Measure ℂ) ⊤ 2) (t : ℝ) :
    ∀ᵐ z, W1p.value (u + t • v) z = W1p.value u z + t * W1p.value v z := by
  have hadd := W1p.value_add_ae u (t • v)
  have hsmul := W1p.value_smul_ae t v
  simp only [Opens.coe_top, Measure.restrict_univ] at hadd hsmul
  filter_upwards [hadd, hsmul] with z h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]

/-- The remainder `t² ‖∇v‖₂² / 2 + ∫ h exp (2w) φ(t ψ)` of the expansion of Taubes's functional at
`u` along `v`. -/
private def remainder (P : Polynomial ℂ) (u v : W1p (volume : Measure ℂ) ⊤ 2) (t : ℝ) : ℝ :=
  t ^ 2 * ‖W1p.gradient v‖ ^ 2 / 2 + ∫ z, backgroundWeight P.eval z *
    Real.exp (2 * W1p.value u z) * taubesPotential (t * W1p.value v z)

/-- The first variation `⟪∇u, ∇v⟫ + ∫ (h (exp (2w) - 1) / 8 + k) ψ`. -/
private def firstVariation (P : Polynomial ℂ) (u v : W1p (volume : Measure ℂ) ⊤ 2) : ℝ :=
  inner ℝ (W1p.gradient u) (W1p.gradient v) + ∫ z, (backgroundWeight P.eval z *
    (Real.exp (2 * W1p.value u z) - 1) / 8 + backgroundSource P.eval z) * W1p.value v z

/-- The potential of a function, written with `TauCeti.Vortex.backgroundWeight`. -/
private theorem integrable_norm_eval_sq_div_mul_iff (f : ℂ → ℝ) :
    (Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * f z) ↔
      Integrable fun z ↦ backgroundWeight P.eval z * f z := by
  simp only [backgroundWeight_def]

/-- The integral of the potential of a function, written with
`TauCeti.Vortex.backgroundWeight`. -/
private theorem integral_norm_eval_sq_div_mul_eq (f : ℂ → ℝ) :
    ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * f z = ∫ z, backgroundWeight P.eval z * f z := by
  simp only [backgroundWeight_def]

/-- A finite value of Taubes's functional has an integrable potential. -/
private theorem integrable_potential_of_ne_top {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : sobolevReducedFunctional P u ≠ ⊤) :
    Integrable fun z ↦ backgroundWeight P.eval z *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
  (integrable_norm_eval_sq_div_mul_iff _).1
    (not_not.1 fun h ↦ hu (sobolevReducedFunctional_eq_top h))

/-- The potential of `u + t v` is almost everywhere the potential of `w + t ψ`. -/
private theorem potential_add_smul_ae (u v : W1p (volume : Measure ℂ) ⊤ 2) (t : ℝ) :
    (fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * W1p.value (u + t • v) z) - 1 -
      2 * W1p.value (u + t • v) z)) =ᵐ[volume] fun z ↦ backgroundWeight P.eval z *
        (Real.exp (2 * (W1p.value u z + t * W1p.value v z)) - 1 -
          2 * (W1p.value u z + t * W1p.value v z)) := by
  filter_upwards [value_add_smul_ae u v t] with z hz
  rw [hz]

/-- **A finite value of Taubes's functional stays finite along a bounded direction.** If
`I(u) ≠ ⊤`, the value of `v ∈ H¹(ℂ)` is bounded by `M` almost everywhere and `|t| M ≤ 1 / 2`,
then `I(u + t v) ≠ ⊤`. -/
private theorem sobolevReducedFunctional_add_smul_ne_top {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : sobolevReducedFunctional P u ≠ ⊤) {M : ℝ} (hv : ∀ᵐ z, |W1p.value v z| ≤ M) {t : ℝ}
    (ht : |t| * M ≤ 1 / 2) :
    sobolevReducedFunctional P (u + t • v) ≠ ⊤ := by
  rw [sobolevReducedFunctional_eq_coe ((integrable_norm_eval_sq_div_mul_iff _).2
    ((integrable_congr (potential_add_smul_ae u v t)).2
      (integrable_potential_add_smul_and_integral_eq (memLp_value_volume u)
        (memLp_value_volume v) hv (integrable_potential_of_ne_top hu) ht).1))]
  exact EReal.coe_ne_top _

/-- **The exact expansion of Taubes's functional along an essentially bounded direction.** If
`I(u)` is finite, `|ψ| ≤ M` almost everywhere for the value `ψ` of `v`, and `|t| M ≤ 1 / 2`, then
`I(u + t v)` is the real number `I(u) + t D + R(t)`. -/
private theorem sobolevReducedFunctional_add_smul_eq (hm : 0 < P.natDegree)
    {u v : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤) {M : ℝ}
    (hv : ∀ᵐ z, |W1p.value v z| ≤ M) {t : ℝ} (ht : |t| * M ≤ 1 / 2) :
    sobolevReducedFunctional P (u + t • v) =
      (((sobolevReducedFunctional P u).toReal + t * firstVariation P u v +
        remainder P u v t : ℝ) : EReal) := by
  have hw := memLp_value_volume u
  have hψ := memLp_value_volume v
  have hpot := integrable_potential_of_ne_top hu
  obtain ⟨hpotI, hpotE⟩ := integrable_potential_add_smul_and_integral_eq hw hψ hv hpot ht
  have hc : MemLp (backgroundSource P.eval) 2 := by
    refine (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm).congr_norm
      continuous_backgroundSource_eval.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    rw [two_mul_norm_derivative_eval_sq_div_sub_eq_backgroundSource]
  have hcw : Integrable fun z ↦ backgroundSource P.eval z * W1p.value u z := hc.integrable_mul hw
  have hcψ : Integrable fun z ↦ backgroundSource P.eval z * W1p.value v z := hc.integrable_mul hψ
  -- The linear term.
  have hlin (f : ℂ → ℝ) : ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * f z = ∫ z, backgroundSource P.eval z * f z := by
    simp only [two_mul_norm_derivative_eval_sq_div_sub_eq_backgroundSource]
  have hlinE : ∫ z, backgroundSource P.eval z * W1p.value (u + t • v) z =
      (∫ z, backgroundSource P.eval z * W1p.value u z) +
        t * ∫ z, backgroundSource P.eval z * W1p.value v z := by
    rw [← integral_const_mul, ← integral_add hcw (hcψ.const_mul t)]
    refine integral_congr_ae ?_
    filter_upwards [value_add_smul_ae u v t] with z hz
    rw [hz]
    ring
  -- The gradient term.
  have hnorm : ‖W1p.gradient (u + t • v)‖ ^ 2 = ‖W1p.gradient u‖ ^ 2 +
      2 * t * inner ℝ (W1p.gradient u) (W1p.gradient v) + t ^ 2 * ‖W1p.gradient v‖ ^ 2 := by
    have hgrad : W1p.gradient (u + t • v) = W1p.gradient u + t • W1p.gradient v := by
      simp only [← W1p.gradientL_apply, map_add, map_smul]
    rw [hgrad, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  -- The first variation splits into the potential and linear contributions.
  have hD : ∫ z, (backgroundWeight P.eval z * (Real.exp (2 * W1p.value u z) - 1) / 8 +
      backgroundSource P.eval z) * W1p.value v z =
      (∫ z, backgroundWeight P.eval z * (Real.exp (2 * W1p.value u z) - 1) * W1p.value v z) / 8 +
        ∫ z, backgroundSource P.eval z * W1p.value v z := by
    have hsum := integral_add
      ((integrable_backgroundWeight_mul_exp_sub_one_mul hw hψ hv hpot).div_const 8) hcψ
    rw [integral_div] at hsum
    rw [← hsum]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)
  rw [sobolevReducedFunctional_eq_coe ((integrable_norm_eval_sq_div_mul_iff _).2
    ((integrable_congr (potential_add_smul_ae u v t)).2 hpotI)),
    sobolevReducedFunctional_eq_coe ((integrable_norm_eval_sq_div_mul_iff _).2 hpot),
    EReal.toReal_coe]
  congr 1
  rw [integral_norm_eval_sq_div_mul_eq, integral_norm_eval_sq_div_mul_eq,
    integral_congr_ae (potential_add_smul_ae u v t), hpotE, hlin, hlin, hlinE, hnorm,
    firstVariation, remainder, hD]
  ring

/-- The remainder is `O(t²)` as `t → 0`. -/
private theorem isBigO_remainder {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : sobolevReducedFunctional P u ≠ ⊤) {M : ℝ} (hv : ∀ᵐ z, |W1p.value v z| ≤ M) :
    remainder P u v =O[𝓝 0] fun t ↦ t ^ 2 := by
  have hI2 := integrable_backgroundWeight_mul_exp_mul_sq (memLp_value_volume u)
    (memLp_value_volume v) hv (integrable_potential_of_ne_top hu)
  set B := ‖W1p.gradient v‖ ^ 2 / 2 + (∫ z, backgroundWeight P.eval z *
    Real.exp (2 * W1p.value u z) * W1p.value v z ^ 2) / 4
  have hsmall := eventually_abs_mul_lt_one_half M
  refine IsBigO.of_bound B ?_
  filter_upwards [hsmall] with t ht
  have hpt : ∀ᵐ z, ‖backgroundWeight P.eval z * Real.exp (2 * W1p.value u z) *
      taubesPotential (t * W1p.value v z)‖ ≤
      t ^ 2 / 4 * (backgroundWeight P.eval z * Real.exp (2 * W1p.value u z) *
        W1p.value v z ^ 2) := by
    filter_upwards [hv] with z hz
    have htz : |t * W1p.value v z| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hz (abs_nonneg t)).trans ht.le
    exact norm_backgroundWeight_mul_exp_mul_taubesPotential_le z _ htz
  have hint := norm_integral_le_of_norm_le (hI2.const_mul (t ^ 2 / 4)) hpt
  rw [integral_const_mul] at hint
  rw [remainder, Real.norm_of_nonneg (sq_nonneg t)]
  calc ‖t ^ 2 * ‖W1p.gradient v‖ ^ 2 / 2 + ∫ z, backgroundWeight P.eval z *
        Real.exp (2 * W1p.value u z) * taubesPotential (t * W1p.value v z)‖
      ≤ ‖t ^ 2 * ‖W1p.gradient v‖ ^ 2 / 2‖ + ‖∫ z, backgroundWeight P.eval z *
          Real.exp (2 * W1p.value u z) * taubesPotential (t * W1p.value v z)‖ := norm_add_le _ _
    _ ≤ t ^ 2 * ‖W1p.gradient v‖ ^ 2 / 2 + t ^ 2 / 4 * ∫ z, backgroundWeight P.eval z *
          Real.exp (2 * W1p.value u z) * W1p.value v z ^ 2 := by
        rw [Real.norm_of_nonneg (by positivity)]
        linarith [hint]
    _ = B * t ^ 2 := by ring

/-! ### The first variation -/

/-- **A finite value of Taubes's functional stays finite along a bounded direction.** If
`I(u) ≠ ⊤` and the value of `v ∈ H¹(ℂ)` is essentially bounded, then `I(u + t v) ≠ ⊤` for all
`t` near `0`. -/
theorem eventually_sobolevReducedFunctional_add_smul_ne_top
    {u v : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤) {M : ℝ}
    (hv : ∀ᵐ z, |W1p.value v z| ≤ M) :
    ∀ᶠ t : ℝ in 𝓝 0, sobolevReducedFunctional P (u + t • v) ≠ ⊤ := by
  have hsmall := eventually_abs_mul_lt_one_half M
  filter_upwards [hsmall] with t ht
  exact sobolevReducedFunctional_add_smul_ne_top hu hv ht.le

/-- **The first variation of Taubes's functional on `H¹(ℂ)`.** Let `P` have degree at least one,
let `I(u)` be finite, and let the value `ψ` of `v ∈ H¹(ℂ)` be essentially bounded. Then
`t ↦ I(u + t v)` (finite near `0` by
`TauCeti.Vortex.eventually_sobolevReducedFunctional_add_smul_ne_top`) has derivative
`⟪∇u, ∇v⟫ + ∫ (h (exp (2w) - 1) / 8 + k) ψ` at `t = 0`, where `w` is the value of `u`,
`h = TauCeti.Vortex.backgroundWeight P.eval` and `k = TauCeti.Vortex.backgroundSource P.eval`. -/
theorem hasDerivAt_toReal_sobolevReducedFunctional_add_smul (hm : 0 < P.natDegree)
    {u v : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤) {M : ℝ}
    (hv : ∀ᵐ z, |W1p.value v z| ≤ M) :
    HasDerivAt (fun t : ℝ ↦ (sobolevReducedFunctional P (u + t • v)).toReal)
      (inner ℝ (W1p.gradient u) (W1p.gradient v) + ∫ z, (backgroundWeight P.eval z *
        (Real.exp (2 * W1p.value u z) - 1) / 8 + backgroundSource P.eval z) * W1p.value v z) 0 := by
  have hsmall := eventually_abs_mul_lt_one_half M
  have hR : HasDerivAt (remainder P u v) 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hR0 : remainder P u v 0 = 0 := by simp [remainder, taubesPotential_zero]
    simpa [hR0] using (isBigO_remainder hu hv).trans_isLittleO (isLittleO_pow_id one_lt_two)
  have hF : HasDerivAt (fun t ↦ (sobolevReducedFunctional P u).toReal +
      t * firstVariation P u v + remainder P u v t) (1 * firstVariation P u v + 0) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (firstVariation P u v)).const_add
      (sobolevReducedFunctional P u).toReal).add hR
  rw [one_mul, add_zero] at hF
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [hsmall] with t ht
  rw [sobolevReducedFunctional_add_smul_eq hm hu hv ht.le, EReal.toReal_coe]

/-- **The Euler–Lagrange equation of Taubes's functional at a local minimizer.** Let `P` have
degree at least one and let `u` be a local minimizer of `I` on `H¹(ℂ)` with `I(u)` finite. Then
for every `v ∈ H¹(ℂ)` with essentially bounded value `ψ`,
`⟪∇u, ∇v⟫ + ∫ (h (exp (2w) - 1) / 8 + k) ψ = 0`, where `w` is the value of `u`. -/
theorem inner_gradient_add_integral_eq_zero_of_isLocalMin (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hmin : IsLocalMin (sobolevReducedFunctional P) u)
    (hu : sobolevReducedFunctional P u ≠ ⊤) {v : W1p (volume : Measure ℂ) ⊤ 2} {M : ℝ}
    (hv : ∀ᵐ z, |W1p.value v z| ≤ M) :
    inner ℝ (W1p.gradient u) (W1p.gradient v) + ∫ z, (backgroundWeight P.eval z *
      (Real.exp (2 * W1p.value u z) - 1) / 8 + backgroundSource P.eval z) * W1p.value v z = 0 := by
  refine IsLocalMin.hasDerivAt_eq_zero ?_
    (hasDerivAt_toReal_sobolevReducedFunctional_add_smul hm hu hv)
  have hline : IsLocalMin (fun t : ℝ ↦ sobolevReducedFunctional P (u + t • v)) 0 := by
    have hcont : ContinuousAt (fun t : ℝ ↦ u + t • v) 0 := by fun_prop
    have h0 : u + (0 : ℝ) • v = u := by simp
    exact IsLocalMin.comp_continuous (g := fun t : ℝ ↦ u + t • v) (by rwa [h0]) hcont
  filter_upwards [hline, eventually_sobolevReducedFunctional_add_smul_ne_top hu hv] with t ht hne
  exact EReal.toReal_le_toReal ht (sobolevReducedFunctional_ne_bot _) hne

/-! ### Weak solutions of the reduced equation -/

/-- **Local integrability of the right-hand side.** If `I(u)` is finite, then the right-hand side
`h (exp (2w) - 1) / 8 + k` of the reduced equation, with `w` the value of `u`, is locally
integrable. -/
theorem locallyIntegrable_backgroundWeight_mul_add_backgroundSource
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤) :
    LocallyIntegrable fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * W1p.value u z) - 1) / 8 +
      backgroundSource P.eval z := by
  have hw := memLp_value_volume u
  have hpot := integrable_potential_of_ne_top hu
  have hhw : MemLp (fun z ↦ backgroundWeight P.eval z * W1p.value u z) 2 := by
    refine hw.of_le (continuous_backgroundWeight_eval.aestronglyMeasurable.mul
      hw.aestronglyMeasurable) (ae_of_all _ fun z ↦ ?_)
    rw [norm_mul, Real.norm_of_nonneg (backgroundWeight_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (backgroundWeight_le_one _ z)
  have hfun : (fun z ↦ backgroundWeight P.eval z * (Real.exp (2 * W1p.value u z) - 1) / 8 +
      backgroundSource P.eval z) = fun z ↦ (1 / 8 * (backgroundWeight P.eval z *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) +
        1 / 4 * (backgroundWeight P.eval z * W1p.value u z)) + backgroundSource P.eval z :=
    funext fun z ↦ by ring
  rw [hfun]
  exact ((hpot.const_mul _).locallyIntegrable.add
    ((hhw.const_mul _).locallyIntegrable (by norm_num))).add
      continuous_backgroundSource_eval.locallyIntegrable

/-- **The reduced vortex equation has a weak solution in `H¹(ℂ)`.** For a complex polynomial `P`
of degree at least one there is a minimizer `u ∈ H¹(ℂ)` of Taubes's functional, with value `w`,
such that the right-hand side `h (exp (2w) - 1) / 8 + k` of `Δw = h (exp (2w) - 1) / 8 + k` is
locally integrable and `∫ ⟪∇u, ∇φ⟫ + ∫ (h (exp (2w) - 1) / 8 + k) φ = 0` for every compactly
supported `C¹` function `φ`. Here `h = TauCeti.Vortex.backgroundWeight P.eval` and
`k = TauCeti.Vortex.backgroundSource P.eval`. -/
theorem exists_forall_integral_inner_gradient_add_integral_eq_zero (hm : 0 < P.natDegree) :
    ∃ u : W1p (volume : Measure ℂ) ⊤ 2,
      (∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) ∧
      (LocallyIntegrable fun z ↦ backgroundWeight P.eval z *
        (Real.exp (2 * W1p.value u z) - 1) / 8 + backgroundSource P.eval z) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ z, inner ℝ (W1p.gradient u z) (∇ φ z)) + ∫ z, (backgroundWeight P.eval z *
          (Real.exp (2 * W1p.value u z) - 1) / 8 + backgroundSource P.eval z) * φ z = 0 := by
  obtain ⟨u, hmin⟩ := exists_forall_sobolevReducedFunctional_le hm
  have hu : sobolevReducedFunctional P u ≠ ⊤ :=
    ((hmin 0).trans_eq sobolevReducedFunctional_zero).trans_lt EReal.zero_lt_top |>.ne
  refine ⟨u, hmin, locallyIntegrable_backgroundWeight_mul_add_backgroundSource hu,
    fun φ hφ hφc ↦ ?_⟩
  obtain ⟨v, hval, hgrad, -, -⟩ :=
    W1p.exists_value_gradient_ae_eq_of_hasCompactSupport (mu := (volume : Measure ℂ)) (p := 2) hφ
      hφc
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hv : ∀ᵐ z, |W1p.value v z| ≤ C := by
    filter_upwards [hval] with z hz
    rw [hz, ← Real.norm_eq_abs]
    exact hC z
  have h := inner_gradient_add_integral_eq_zero_of_isLocalMin hm
    (Eventually.of_forall hmin) hu hv
  rw [L2.inner_def] at h
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  have e1 : ∫ z, inner ℝ (W1p.gradient u z) (W1p.gradient v z) =
      ∫ z, inner ℝ (W1p.gradient u z) (∇ φ z) :=
    integral_congr_ae (by filter_upwards [hgrad] with z hz; rw [hz])
  have e2 : ∫ z, (backgroundWeight P.eval z * (Real.exp (2 * W1p.value u z) - 1) / 8 +
      backgroundSource P.eval z) * W1p.value v z = ∫ z, (backgroundWeight P.eval z *
        (Real.exp (2 * W1p.value u z) - 1) / 8 + backgroundSource P.eval z) * φ z :=
    integral_congr_ae (by filter_upwards [hval] with z hz; rw [hz])
  rwa [e1, e2] at h

end TauCeti.Vortex
