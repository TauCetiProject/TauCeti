/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.WeakDeriv
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball

/-!
# Mollification oscillation bounds for locally integrable and weakly differentiable functions

Let `E` be a proper normed additive group with an additive Haar measure `μ`, and let `ρ : E → ℝ`
be a nonnegative kernel of integral `1`, supported in `ball 0 r` and bounded by
`C / μ.real (ball 0 r)`. For any Banach-valued function `f : E → F` integrable on `ball x r`, the
mollified value `(ρ ⋆ f) x` stays within `C` times the mean oscillation of `f` from the ball
average `⨍_{B(x, r)} f`:

`‖(ρ ⋆ f) x - ⨍_{B(x, r)} f‖ₑ ≤ C * ⨍⁻ z in B(x, r), ‖f z - ⨍_{B(x, r)} f‖ₑ`,

and consequently the average distance from `f` to the constant `(ρ ⋆ f) x` on `B(x, r)` is at most
`(1 + C)` times the mean oscillation of `f` on `B(x, r)`.

For a normalized smooth bump `φ.normed μ` on a finite-dimensional real normed space `E` of
dimension `n`, `C` may be taken to be `(φ.rOut / φ.rIn) ^ n`. Combining this with the Banach-valued
Poincaré–Wirtinger inequality on balls
(`TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le_mul_rpow`) yields the Sobolev
mollification oscillation bound: for `u : E → F` with weak Fréchet derivative `Du` on `Ω`,
`ball x φ.rOut ⊆ Ω`, and `1 ≤ p ≤ ∞`,

`⨍⁻ z in B(x, φ.rOut), ‖u z - (φ.normed μ ⋆ u) x‖ₑ`
`  ≤ (1 + (φ.rOut / φ.rIn) ^ n) * 2 ^ (n + 1) * ω ^ (-1 / p) * φ.rOut ^ (1 - n / p) * ‖Du‖_{Lᵖ(B)}`.

At the borderline exponent `p = n` (in positive dimension `n ≥ 1`), the radius cancels completely;
for any family of bumps with bounded aspect ratio `φᵢ.rOut / φᵢ.rIn ≤ κ` and `φᵢ.rOut → 0`, the
oscillation `⨍⁻ z in B(x, φᵢ.rOut), ‖u z - (φᵢ.normed μ ⋆ u) x‖ₑ` vanishes uniformly over compact
subsets (and globally when `Du ∈ Lⁿ(μ)`), by absolute continuity of the integral. This is the
quantitative VMO estimate used to keep mollifications of `W^{1,n}` maps close to a target
submanifold in Schoen–Uhlenbeck approximation.

## Main declarations

* `TauCeti.enorm_convolution_sub_setAverage_ball_le` and
  `TauCeti.setLAverage_enorm_sub_convolution_le`: kernel oscillation bounds on a ball.
* `ContDiffBump.enorm_normed_convolution_sub_setAverage_ball_le` and
  `ContDiffBump.setLAverage_enorm_sub_normed_convolution_le`: specializations to
  `ContDiffBump.normed`.
* `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le` and
  `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le_of_finrank`: Sobolev
  mollification oscillation bounds for all `1 ≤ p ≤ ∞` and at the scale-invariant exponent `p = n`.
* `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_indicator_le` and
  `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_indicator_le_of_finrank`: the
  same estimates for the zero-extended interior mollification `φ.normed μ ⋆ V.indicator u`.
* `TauCeti.HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution_indicator` and
  `TauCeti.HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution`: uniform
  vanishing of the mollification oscillation at `p = n` on compact subsets and globally.

## References

* P. Hajłasz, *Sobolev mappings between manifolds and metric spaces*, in *Sobolev Spaces in
  Mathematics I*, Int. Math. Ser. (N.Y.) **8**, Springer (2009), 185–222, inequality (2.1).
* R. Schoen, K. Uhlenbeck, *Boundary regularity and the Dirichlet problem for harmonic maps*,
  J. Differential Geom. **18** (1983), 253–268, §4.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped Convolution ENNReal Topology

/-! ### General kernel oscillation bounds on balls -/

section Kernel

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [BorelSpace E] [ProperSpace E] [μ.IsAddHaarMeasure] in
/-- If a kernel `ρ` has integral `1` and support inside `ball 0 r`, then `0 < r`. -/
private theorem pos_of_integral_eq_one_of_support_subset_ball {ρ : E → ℝ} {r : ℝ}
    (hρ1 : ∫ y, ρ y ∂μ = 1) (hρs : Function.support ρ ⊆ ball 0 r) : 0 < r := by
  by_contra hr
  have h0 : ρ = 0 := by
    ext y
    exact Function.notMem_support.1 fun hy => by
      have := hρs hy
      rw [ball_eq_empty.2 (not_lt.1 hr)] at this
      exact this
  simp [h0] at hρ1

/-- **Distance from a mollification to the ball average.** Let `ρ ≥ 0` have integral `1`, support
in `ball 0 r`, and upper bound `C / μ.real (ball 0 r)`. For any `f` integrable on `ball x r`,
`‖(ρ ⋆ f) x - ⨍_{B(x, r)} f‖ₑ` is at most `C` times the mean oscillation of `f` on `ball x r`. -/
theorem enorm_convolution_sub_setAverage_ball_le {ρ : E → ℝ} {f : E → F} {x : E} {r C : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) (hρs : Function.support ρ ⊆ ball 0 r)
    (hρM : ∀ y, ρ y ≤ C / μ.real (ball 0 r)) (hf : IntegrableOn f (ball x r) μ) :
    ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - ⨍ z in ball x r, f z ∂μ‖ₑ ≤
      ENNReal.ofReal C * ⨍⁻ z in ball x r, ‖f z - ⨍ w in ball x r, f w ∂μ‖ₑ ∂μ := by
  have hr : 0 < r := pos_of_integral_eq_one_of_support_subset_ball hρ1 hρs
  have hBtop : μ (ball (0 : E) r) ≠ ∞ := measure_ball_lt_top.ne
  have hBreal_pos : 0 < μ.real (ball (0 : E) r) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' hBtop
  set m : F := ⨍ z in ball x r, f z ∂μ
  have hρi : Integrable ρ μ := Integrable.of_integral_ne_zero (by simp [hρ1])
  have hfi : Integrable ((ball x r).indicator f) μ := hf.integrable_indicator measurableSet_ball
  have hmem (t : E) : t ∈ ball (0 : E) r ↔ x - t ∈ ball x r := by simp [mem_ball, dist_eq_norm]
  -- Replace `f` by its indicator on `ball x r`, which does not change the convolution at `x`.
  have hconv_eq : (ρ ⋆[lsmul ℝ ℝ, μ] f) x = (ρ ⋆[lsmul ℝ ℝ, μ] (ball x r).indicator f) x :=
    (convolution_indicator_eq_of_forall_sub_mem (lsmul ℝ ℝ) fun t ht => (hmem t).1 (hρs ht)).symm
  have hconv_ex : Integrable (fun t => lsmul ℝ ℝ (ρ t) ((ball x r).indicator f (x - t))) μ :=
    convolutionExists_of_ae_norm_le_of_integrable (lsmul ℝ ℝ) hρi.aestronglyMeasurable
      (.of_forall fun t => by rw [Real.norm_of_nonneg (hρ0 t)]; exact hρM t) hfi x
  have hdiff : (ρ ⋆[lsmul ℝ ℝ, μ] f) x - m =
      ∫ t, ρ t • ((ball x r).indicator f (x - t) - m) ∂μ := by
    rw [hconv_eq, convolution_def]
    conv_lhs => rhs; rw [← one_smul ℝ m, ← hρ1, ← integral_smul_const]
    rw [← integral_sub hconv_ex (hρi.smul_const m)]
    simp only [lsmul_apply, smul_sub]
  -- Change of variables `z = x - t` identifies the `ball 0 r` and `ball x r` integrals.
  have hchg : ∫⁻ t in ball (0 : E) r, ‖f (x - t) - m‖ₑ ∂μ = ∫⁻ z in ball x r, ‖f z - m‖ₑ ∂μ := by
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
      ← lintegral_sub_left_eq_self (fun z => (ball x r).indicator (fun w => ‖f w - m‖ₑ) z) x]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ ball (0 : E) r <;> simp [ht, (hmem t).1, mt (hmem t).2]
  calc ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ
      ≤ ∫⁻ t, ‖ρ t • ((ball x r).indicator f (x - t) - m)‖ₑ ∂μ :=
        hdiff ▸ eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ENNReal.ofReal (C / μ.real (ball 0 r)) *
          (ball (0 : E) r).indicator (fun t => ‖f (x - t) - m‖ₑ) t ∂μ := by
        refine lintegral_mono fun t => ?_
        rw [eNorm_smul]
        by_cases ht : t ∈ ball (0 : E) r
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ((hmem t).1 ht), ← ofReal_norm,
            Real.norm_of_nonneg (hρ0 t)]
          gcongr; exact hρM t
        · simp [Function.notMem_support.1 fun h => ht (hρs h)]
    _ = ENNReal.ofReal (C / μ.real (ball 0 r)) * ∫⁻ z in ball x r, ‖f z - m‖ₑ ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_ball,
          hchg]
    _ = ENNReal.ofReal C * ⨍⁻ z in ball x r, ‖f z - m‖ₑ ∂μ := by
        rw [ENNReal.ofReal_div_of_pos hBreal_pos, measureReal_def,
          ENNReal.ofReal_toReal hBtop, ← Measure.addHaar_ball_center μ x r,
          setLAverage_eq, div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- **Mean deviation from a mollified value.** Under the hypotheses of
`TauCeti.enorm_convolution_sub_setAverage_ball_le`, the average distance on `ball x r` between `f`
and the constant `(ρ ⋆ f) x` is at most `1 + C` times the mean oscillation of `f` on `ball x r`. -/
theorem setLAverage_enorm_sub_convolution_le {ρ : E → ℝ} {f : E → F} {x : E} {r C : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) (hρs : Function.support ρ ⊆ ball 0 r)
    (hρM : ∀ y, ρ y ≤ C / μ.real (ball 0 r)) (hf : IntegrableOn f (ball x r) μ) :
    ⨍⁻ z in ball x r, ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ ≤
      ENNReal.ofReal (1 + C) * ⨍⁻ z in ball x r, ‖f z - ⨍ w in ball x r, f w ∂μ‖ₑ ∂μ := by
  have hr : 0 < r := pos_of_integral_eq_one_of_support_subset_ball hρ1 hρs
  have hB0 : μ (ball x r) ≠ 0 := (measure_ball_pos μ x hr).ne'
  have hBtop : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  have hC0 : 0 ≤ C := by
    by_contra hC
    have hneg : C / μ.real (ball (0 : E) r) < 0 :=
      div_neg_of_neg_of_pos (not_le.1 hC)
        (ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne)
    have h0 := (hρ0 0).trans (hρM 0)
    linarith
  set m : F := ⨍ w in ball x r, f w ∂μ
  set osc : ℝ≥0∞ := ⨍⁻ z in ball x r, ‖f z - m‖ₑ ∂μ
  have hpt (z : E) :
      ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ≤ ‖f z - m‖ₑ + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ := by
    calc ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ
        = ‖(f z - m) - ((ρ ⋆[lsmul ℝ ℝ, μ] f) x - m)‖ₑ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖f z - m‖ₑ + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ := eNorm_sub_le
  have htri : ⨍⁻ z in ball x r, ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ ≤
      osc + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ := by
    rw [setLAverage_eq]
    calc (∫⁻ z in ball x r, ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ) / μ (ball x r)
        ≤ (∫⁻ z in ball x r, (‖f z - m‖ₑ + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ) ∂μ) / μ (ball x r) :=
          ENNReal.div_le_div_right (lintegral_mono hpt) _
      _ = ((∫⁻ z in ball x r, ‖f z - m‖ₑ ∂μ) +
            ∫⁻ _ in ball x r, ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ ∂μ) / μ (ball x r) := by
          rw [lintegral_add_right _ measurable_const]
      _ = osc + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ := by
          dsimp only [osc]
          rw [ENNReal.add_div, setLAverage_eq, setLIntegral_const,
            ENNReal.mul_div_cancel_right hB0 hBtop]
  calc ⨍⁻ z in ball x r, ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ
      ≤ osc + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ := htri
    _ ≤ osc + ENNReal.ofReal C * osc :=
        add_le_add_right (enorm_convolution_sub_setAverage_ball_le hρ0 hρ1 hρs hρM hf) _
    _ = (1 + ENNReal.ofReal C) * osc := by rw [add_mul, one_mul]
    _ = ENNReal.ofReal (1 + C) * osc := by
        rw [ENNReal.ofReal_add zero_le_one hC0, ENNReal.ofReal_one]

end Kernel

/-! ### Normalized smooth bumps and Sobolev oscillation bounds -/

section Bump

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Upper bound on `φ.normed μ` in terms of the open ball `ball 0 φ.rOut` and aspect ratio
`φ.rOut / φ.rIn`. -/
private theorem normed_le_div_measure_ball_rOut (φ : ContDiffBump (0 : E)) (y : E) :
    φ.normed μ y ≤ (φ.rOut / φ.rIn) ^ finrank ℝ E / μ.real (ball 0 φ.rOut) := by
  have hbound := φ.normed_le_div_measure_closedBall_rOut μ (φ.rOut / φ.rIn)
    (by rw [div_mul_cancel₀ _ φ.rIn_pos.ne']) y
  refine hbound.trans (div_le_div_of_nonneg_left (by positivity [φ.rOut_pos.le, φ.rIn_pos.le])
    (ENNReal.toReal_pos (measure_ball_pos μ 0 φ.rOut_pos).ne' measure_ball_lt_top.ne) ?_)
  exact measureReal_mono ball_subset_closedBall measure_closedBall_lt_top.ne

/-- **Distance from a normalized-bump mollification to the ball average.** -/
theorem _root_.ContDiffBump.enorm_normed_convolution_sub_setAverage_ball_le [CompleteSpace F]
    (φ : ContDiffBump (0 : E)) {f : E → F} {x : E} (hf : IntegrableOn f (ball x φ.rOut) μ) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x - ⨍ z in ball x φ.rOut, f z ∂μ‖ₑ ≤
      ENNReal.ofReal ((φ.rOut / φ.rIn) ^ finrank ℝ E) *
        ⨍⁻ z in ball x φ.rOut, ‖f z - ⨍ w in ball x φ.rOut, f w ∂μ‖ₑ ∂μ :=
  enorm_convolution_sub_setAverage_ball_le φ.nonneg_normed φ.integral_normed
    φ.support_normed_eq.subset (normed_le_div_measure_ball_rOut φ) hf

/-- **Mean deviation from a normalized-bump mollification.** -/
theorem _root_.ContDiffBump.setLAverage_enorm_sub_normed_convolution_le [CompleteSpace F]
    (φ : ContDiffBump (0 : E)) {f : E → F} {x : E} (hf : IntegrableOn f (ball x φ.rOut) μ) :
    ⨍⁻ z in ball x φ.rOut, ‖f z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ ≤
      ENNReal.ofReal (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) *
        ⨍⁻ z in ball x φ.rOut, ‖f z - ⨍ w in ball x φ.rOut, f w ∂μ‖ₑ ∂μ :=
  setLAverage_enorm_sub_convolution_le φ.nonneg_normed φ.integral_normed
    φ.support_normed_eq.subset (normed_le_div_measure_ball_rOut φ) hf

variable {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F}

/-- **Sobolev mollification oscillation bound.** For a weakly differentiable function `u : E → F`
on `Ω`, a normalized bump `φ`, a point `x` with `ball x φ.rOut ⊆ Ω`, and any exponent `1 ≤ p ≤ ∞`,

`⨍⁻ z in B(x, φ.rOut), ‖u z - (φ.normed μ ⋆ u) x‖ₑ`
`  ≤ (1 + (φ.rOut / φ.rIn) ^ n) * 2 ^ (n + 1) * ω ^ (-1 / p) * φ.rOut ^ (1 - n / p) * ‖Du‖_{Lᵖ(B)}`.

No a priori integrability assumption on `u` or `Du` is required. -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le
    (hu : HasWeakFDerivOn μ Ω u Du) (φ : ContDiffBump (0 : E)) {x : E}
    (hball : ball x φ.rOut ⊆ Ω) {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    ⨍⁻ z in ball x φ.rOut, ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ ≤
      ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
          μ.real (ball 0 1) ^ (-p.toReal⁻¹) * φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
        eLpNorm Du p (μ.restrict (ball x φ.rOut)) := by
  have : CompleteSpace F := hu.completeSpace
  have hK1 : 0 < 1 + (φ.rOut / φ.rIn) ^ finrank ℝ E := by
    have : 0 ≤ (φ.rOut / φ.rIn) ^ finrank ℝ E := by positivity [φ.rOut_pos.le, φ.rIn_pos.le]
    linarith
  have hωpos : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have hK2 : 0 < 2 ^ (finrank ℝ E + 1) * μ.real (ball (0 : E) 1) ^ (-p.toReal⁻¹) *
      φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal) :=
    mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hωpos _))
      (Real.rpow_pos_of_pos φ.rOut_pos _)
  by_cases hDu_top : eLpNorm Du p (μ.restrict (ball x φ.rOut)) = ∞
  · have hCpos : 0 < (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
        μ.real (ball (0 : E) 1) ^ (-p.toReal⁻¹) * φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal) := by
      simpa only [mul_assoc] using mul_pos hK1 hK2
    rw [hDu_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top
  · -- Finite `Lᵖ` seminorm of `Du` on the ball forces `u` to be integrable on the ball.
    have : IsFiniteMeasure (μ.restrict (ball x φ.rOut)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hDup : MemLp Du p (μ.restrict (ball x φ.rOut)) := lt_top_iff_ne_top.2 hDu_top
    have hDu1 : MemLp Du 1 (μ.restrict (ball x φ.rOut)) := hDup.mono_exponent hp1
    let B : Opens E := ⟨ball x φ.rOut, isOpen_ball⟩
    have hB : HasWeakFDerivOn μ B u Du := hu.mono hball
    have hu1 : IntegrableOn u (ball x φ.rOut) μ :=
      memLp_one_iff_integrable.1 <|
        hB.memLp_of_convex (convex_ball x φ.rOut) isBounded_ball le_rfl ENNReal.one_ne_top hDu1
    calc ⨍⁻ z in ball x φ.rOut, ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ
        ≤ ENNReal.ofReal (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) *
            ⨍⁻ z in ball x φ.rOut, ‖u z - ⨍ w in ball x φ.rOut, u w ∂μ‖ₑ ∂μ :=
          φ.setLAverage_enorm_sub_normed_convolution_le hu1
      _ ≤ ENNReal.ofReal (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) *
            (ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-p.toReal⁻¹) *
                φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
              eLpNorm Du p (μ.restrict (ball x φ.rOut))) :=
          mul_le_mul_right
            (hu.setLAverage_enorm_sub_setAverage_ball_le_mul_rpow φ.rOut_pos hball hp1) _
      _ = ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
            μ.real (ball 0 1) ^ (-p.toReal⁻¹) * φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
          eLpNorm Du p (μ.restrict (ball x φ.rOut)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK1.le]
          congr 2
          ring

/-- **Scale-invariant Sobolev mollification oscillation bound at the borderline exponent `p = n`.**
In positive dimension `n = finrank ℝ E ≥ 1`, for `ball x φ.rOut ⊆ Ω`,

`⨍⁻ z in B(x, φ.rOut), ‖u z - (φ.normed μ ⋆ u) x‖ₑ`
`  ≤ (1 + (φ.rOut / φ.rIn) ^ n) * 2 ^ (n + 1) * ω ^ (-1 / n) * ‖Du‖_{Lⁿ(B(x, φ.rOut))}`.

The radius cancels completely; only the aspect ratio `φ.rOut / φ.rIn` enters the constant. -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le_of_finrank [Nontrivial E]
    (hu : HasWeakFDerivOn μ Ω u Du) (φ : ContDiffBump (0 : E)) {x : E}
    (hball : ball x φ.rOut ⊆ Ω) :
    ⨍⁻ z in ball x φ.rOut, ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ ≤
      ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
          μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        eLpNorm Du (finrank ℝ E) (μ.restrict (ball x φ.rOut)) := by
  have hn : 1 ≤ (finrank ℝ E : ℝ≥0∞) := by exact_mod_cast finrank_pos
  have hn0 : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have h := hu.setLAverage_enorm_sub_normed_convolution_le φ hball hn
  simpa only [ENNReal.toReal_natCast, div_self hn0, sub_self, Real.rpow_zero, mul_one] using h

/-- **Sobolev mollification oscillation bound for the zero-extended interior mollification.** -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_indicator_le
    (hu : HasWeakFDerivOn μ Ω u Du) {V : Opens E} (hVΩ : V ≤ Ω) (φ : ContDiffBump (0 : E))
    {x : E} (hball : ball x φ.rOut ⊆ V) {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    ⨍⁻ z in ball x φ.rOut,
        ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) x‖ₑ ∂μ ≤
      ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
          μ.real (ball 0 1) ^ (-p.toReal⁻¹) * φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
        eLpNorm Du p (μ.restrict (ball x φ.rOut)) := by
  rw [φ.normed_convolution_indicator_eq_of_ball_subset hball]
  exact hu.setLAverage_enorm_sub_normed_convolution_le φ
    (hball.trans (SetLike.coe_subset_coe.2 hVΩ)) hp1

/-- **Scale-invariant oscillation bound for the zero-extended interior mollification at `p = n`.**
-/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_indicator_le_of_finrank
    [Nontrivial E] (hu : HasWeakFDerivOn μ Ω u Du) {V : Opens E} (hVΩ : V ≤ Ω)
    (φ : ContDiffBump (0 : E)) {x : E} (hball : ball x φ.rOut ⊆ V) :
    ⨍⁻ z in ball x φ.rOut,
        ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) x‖ₑ ∂μ ≤
      ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
          μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        eLpNorm Du (finrank ℝ E) (μ.restrict (ball x φ.rOut)) := by
  rw [φ.normed_convolution_indicator_eq_of_ball_subset hball]
  exact hu.setLAverage_enorm_sub_normed_convolution_le_of_finrank φ
    (hball.trans (SetLike.coe_subset_coe.2 hVΩ))

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Monotonicity of the scale-invariant `p = n` oscillation constant in the aspect ratio bound. -/
private theorem oscillationConst_le (φ : ContDiffBump (0 : E)) {κ : ℝ}
    (hκ : φ.rOut ≤ κ * φ.rIn) :
    (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
        μ.real (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹) ≤
      (1 + (max κ 0) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
        μ.real (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹) := by
  have hratio : φ.rOut / φ.rIn ≤ max κ 0 :=
    ((div_le_iff₀ φ.rIn_pos).2 hκ).trans (le_max_left κ 0)
  have hr0 : 0 ≤ φ.rOut / φ.rIn := div_nonneg φ.rOut_pos.le φ.rIn_pos.le
  gcongr

/-- **Uniform vanishing of the mollification oscillation on compact subsets at `p = n`.** Let
`u : E → F` have weak Fréchet derivative `Du` on `Ω` in positive dimension `n`, let `K ⊆ V` be a
compact subset of an open set `V ≤ Ω` with `eLpNorm Du n (μ.restrict V) ≠ ∞`, and let `φ i` be
bumps with `(φ i).rOut → 0` and uniformly bounded aspect ratio `(φ i).rOut ≤ κ * (φ i).rIn`. Then
the mean deviation of `u` from its interior mollification `φ i ⋆ V.indicator u` over
`B(x, (φ i).rOut)` tends to `0` uniformly over `x ∈ K`. -/
theorem HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution_indicator
    [Nontrivial E] (hu : HasWeakFDerivOn μ Ω u Du) {V : Opens E} (hVΩ : V ≤ Ω)
    {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    (hDu : eLpNorm Du (finrank ℝ E) (μ.restrict V) ≠ ∞)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {κ : ℝ} (hκ : ∀ᶠ i in l, (φ i).rOut ≤ κ * (φ i).rIn) :
    Tendsto (fun i => ⨆ x ∈ K, ⨍⁻ z in ball x (φ i).rOut,
        ‖u z - ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) x‖ₑ ∂μ)
      l (𝓝 0) := by
  have hn0 : (finrank ℝ E : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have hntop : (finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hDext : eLpNorm ((V : Set E).indicator Du) (finrank ℝ E) μ ≠ ∞ := by
    rwa [eLpNorm_indicator_eq_eLpNorm_restrict (f := Du) V.isOpen.measurableSet.nullMeasurableSet]
  have hsup : Tendsto (fun i =>
        ⨆ c : E, eLpNorm ((V : Set E).indicator Du) (finrank ℝ E) (μ.restrict (ball c (φ i).rOut)))
      l (𝓝 0) :=
    tendsto_iSup_eLpNorm_restrict_ball_zero hn0 hntop hDext hφ
  set C : ℝ := (1 + (max κ 0) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
    μ.real (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹)
  have hrhs := ENNReal.Tendsto.const_mul hsup (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  rw [mul_zero] at hrhs
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open V.isOpen hKV
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrhs
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [hφ.eventually (gt_mem_nhds hδ), hκ] with i hi hκi
  refine iSup₂_le fun x hx => ?_
  have hball : ball x (φ i).rOut ⊆ V := fun y hy =>
    hδV (mem_cthickening_of_dist_le y x δ K hx ((mem_ball.1 hy).trans hi).le)
  have hDu_eq : eLpNorm Du (finrank ℝ E) (μ.restrict (ball x (φ i).rOut)) =
      eLpNorm ((V : Set E).indicator Du) (finrank ℝ E) (μ.restrict (ball x (φ i).rOut)) :=
    eLpNorm_congr_ae <| ae_restrict_of_forall_mem isOpen_ball.measurableSet fun y hy =>
      (Set.indicator_of_mem (hball hy) Du).symm
  refine (hu.setLAverage_enorm_sub_normed_convolution_indicator_le_of_finrank hVΩ (φ i)
    hball).trans ?_
  rw [hDu_eq]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (oscillationConst_le (φ i) hκi))
    (le_iSup (fun c => eLpNorm ((V : Set E).indicator Du) (finrank ℝ E)
      (μ.restrict (ball c (φ i).rOut))) x)

/-- **Global uniform vanishing of the mollification oscillation at `p = n`.** For a globally weakly
differentiable function `u : E → F` in positive dimension `n` with `eLpNorm Du n μ ≠ ∞` and bumps
`φ i` with `(φ i).rOut → 0` and uniformly bounded aspect ratio `(φ i).rOut ≤ κ * (φ i).rIn`, the
mean deviation of `u` from `(φ i).normed μ ⋆ u` over `B(x, (φ i).rOut)` tends to `0` uniformly over
all `x : E`. -/
theorem HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution
    [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du) (hDu : eLpNorm Du (finrank ℝ E) μ ≠ ∞)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {κ : ℝ} (hκ : ∀ᶠ i in l, (φ i).rOut ≤ κ * (φ i).rIn) :
    Tendsto (fun i => ⨆ x : E, ⨍⁻ z in ball x (φ i).rOut,
        ‖u z - ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ)
      l (𝓝 0) := by
  have hn0 : (finrank ℝ E : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have hntop : (finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsup : Tendsto (fun i => ⨆ c : E, eLpNorm Du (finrank ℝ E) (μ.restrict (ball c (φ i).rOut)))
      l (𝓝 0) :=
    tendsto_iSup_eLpNorm_restrict_ball_zero hn0 hntop hDu hφ
  set C : ℝ := (1 + (max κ 0) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
    μ.real (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹)
  have hrhs := ENNReal.Tendsto.const_mul hsup (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  rw [mul_zero] at hrhs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrhs
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [hκ] with i hκi
  refine iSup_le fun x => ?_
  refine (hu.setLAverage_enorm_sub_normed_convolution_le_of_finrank (φ i) (subset_univ _)).trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (oscillationConst_le (φ i) hκi))
    (le_iSup (fun c => eLpNorm Du (finrank ℝ E) (μ.restrict (ball c (φ i).rOut))) x)

end Bump

end TauCeti
