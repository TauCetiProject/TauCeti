/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.BoundedVariation.SmoothApproximation
import TauCeti.Analysis.Calculus.ContDiff.LevelSet
import TauCeti.Analysis.Calculus.FDeriv.Clamp
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic
import TauCeti.Topology.Order.Sublevel

/-!
# The sharp isoperimetric inequality for sets of finite volume

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 1` with its volume,
and write `ω_n = volume (ball 0 1)` and `P(s)` for the perimeter of `s` in the whole space. Every
null-measurable set `s` of finite positive volume satisfies the sharp isoperimetric inequality

`P(s)^n ≥ n^n ω_n |s|^(n-1)`

(`MeasureTheory.NullMeasurableSet.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`),
with no boundedness, connectedness or regularity hypothesis on `s`, and with `P(s)` finite or
infinite. Equivalently `n ω_n^(1/n) |s|^(1 - 1/n) ≤ P(s)`
(`MeasureTheory.NullMeasurableSet.ofReal_mul_volume_real_rpow_mul_le_perimeter`), which is also
stated in real numbers when the perimeter is finite
(`MeasureTheory.NullMeasurableSet.mul_volume_real_rpow_mul_le_perimeter_toReal`).
Balls attain equality (`TauCeti.perimeter_ball_pow`), so the constant is sharp. Finite volume
cannot be dropped: the complement of a ball has finite perimeter.

## Strategy

Every set of finite volume is a limit, in measure and in perimeter, of regular superlevel sets
`{u > t}` of compactly supported smooth functions
(`MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`), so it suffices to treat
such sets. For these, `w = (u - t) / √(‖∇u‖² + (u - t)²)` is a smooth defining function of
`F = {u > t}` whose gradient has norm one on the boundary `{u = t}`
(`ContDiff.exists_contDiff_setOf_pos_eq_setOf_lt`). Near the boundary
`‖∇w‖` lies within `ε` of one, and for small `η > 0`:

* the `η / (1 + ε)`-neighbourhood of `G = {w ≥ η}` lies in `F`, so the Brunn–Minkowski inequality
  bounds the volume of the shell `S = {0 < w < η} = F \ G` from below by
  `n |G|^(1 - 1/n) ω_n^(1/n) η / (1 + ε)`;
* for a test vector field `ψ` equal to `-∇w / ‖∇w‖` near the boundary, integration by parts against
  the clamped function `max 0 (min w η)` gives the calibration estimate
  `(1 - ε) |S| ≤ ∫_S ‖∇w‖ ≤ η (∫_F div ψ + ∫_S |div ψ|)`.

Dividing by `η`, letting `η → 0` and then `ε → 0` gives `n ω_n^(1/n) |F|^(1 - 1/n) ≤ ∫_F div ψ`,
and the right-hand side is at most `P(F)` by the definition of the perimeter. No identification of
the perimeter with surface measure or Minkowski content is used.

## Main results

* `MeasureTheory.NullMeasurableSet.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`:
  the sharp isoperimetric inequality `n^n ω_n |s|^(n-1) ≤ P(s)^n` in `ℝ≥0∞`.
* `MeasureTheory.NullMeasurableSet.ofReal_mul_volume_real_rpow_mul_le_perimeter`: the equivalent
  form `n ω_n^(1/n) |s|^(1 - 1/n) ≤ P(s)` in `ℝ≥0∞`, with no hypothesis on the perimeter.
* `MeasureTheory.NullMeasurableSet.mul_volume_real_rpow_mul_le_perimeter_toReal`: its real form
  for sets of finite perimeter.
* `ContDiff.ofReal_mul_volume_real_rpow_mul_le_perimeter_setOf_lt`: the smooth case, for a
  regular superlevel set `{u > t}` of a compactly supported smooth function `u` with `t > 0`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapters 13 and 14, for the approximation by smooth sets and the isoperimetric
  inequality.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002), 355–405,
  Section 5.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set Filter TopologicalSpace TestFunction InnerProductSpace
open scoped ENNReal Topology ContDiff Distributions Gradient Pointwise symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth function `w` whose derivative does not vanish on its zero level, with `{w ≥ -δ}`
compact, admits an admissible test vector field equal to `-∇w / ‖∇w‖` near the zero level. Its
derivative pairing with `w` there is `-‖Dw‖`. -/
private theorem exists_testFunction_fderiv_apply_eq_neg_norm {w : E → ℝ} (hw : ContDiff ℝ ∞ w)
    {δ : ℝ} (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x})
    (hreg : ∀ x, w x = 0 → fderiv ℝ w x ≠ 0) :
    ∃ η > 0, ∃ ψ : 𝓓(⊤, E), (∀ x, ‖ψ x‖ ≤ 1) ∧
      ∀ x, |w x| ≤ η → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖ := by
  obtain ⟨η, hη, hηδ, hηC⟩ := exists_forall_abs_le_notMem hw.continuous hδ hK
    (isClosed_eq (hw.continuous_fderiv (by simp)) continuous_const) fun x hx h0 => hreg x h0 hx
  -- `G` is the gradient of `w`, and `ρ ∘ w` cuts off to `{|w| < η}`.
  let G : E → E := ∇ w
  have hG : ContDiff ℝ ∞ G := hw.gradient_right le_rfl
  have hGnorm (x : E) : ‖G x‖ = ‖fderiv ℝ w x‖ := norm_gradient_eq_norm_fderiv w x
  have hGapp (x : E) : fderiv ℝ w x (G x) = ‖G x‖ ^ 2 := by
    rw [← toDual_gradient, toDual_apply_apply, real_inner_self_eq_norm_sq]
  have hG0 {x : E} (hx : |w x| ≤ η) : G x ≠ 0 := by
    rw [← norm_ne_zero_iff, hGnorm, norm_ne_zero_iff]
    exact hηC x hx
  let ρ : ContDiffBump (0 : ℝ) := ⟨η / 2, η, half_pos hη, half_lt_self hη⟩
  have hρ0 {x : E} (hx : η ≤ |w x|) : ρ (w x) = 0 := by
    rw [← Function.notMem_support, ρ.support_eq, mem_ball_zero_iff, Real.norm_eq_abs]
    exact hx.not_gt
  have hρ1 {x : E} (hx : |w x| ≤ η / 2) : ρ (w x) = 1 :=
    ρ.one_of_mem_closedBall (by rwa [mem_closedBall_zero_iff, Real.norm_eq_abs])
  let ψ : E → E := fun x => -((ρ (w x) * ‖G x‖⁻¹) • G x)
  have hψs : ContDiff ℝ ∞ ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hGx : G x = 0
    · -- Where the gradient vanishes, `|w| > η`, so `ψ` vanishes nearby.
      have hx : η < |w x| := lt_of_not_ge fun h => hG0 h hGx
      refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [(hw.continuous.abs.isOpen_preimage _ isOpen_Ioi).mem_nhds hx] with y hy
      simp [ψ, hρ0 (le_of_lt hy)]
    · exact (((ρ.contDiff.comp hw).contDiffAt.mul
        ((hG.contDiffAt.norm ℝ hGx).inv (norm_ne_zero_iff.2 hGx))).smul hG.contDiffAt).neg
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro hK fun x hx => by
    have hx : w x < -δ := not_le.1 hx
    have : η ≤ |w x| := hηδ.trans (le_abs.2 (Or.inr (by linarith)))
    simp [ψ, hρ0 this]
  refine ⟨η / 2, half_pos hη, ⟨ψ, hψs, hψc, by simp⟩, fun x => ?_, fun x hx => ?_⟩
  · simp only [coe_mk, ψ]
    by_cases hGx : G x = 0
    · simp [hGx]
    rw [norm_neg, norm_smul,
      Real.norm_of_nonneg (mul_nonneg ρ.nonneg (inv_nonneg.2 (norm_nonneg _))), mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hGx), mul_one]
    exact ρ.le_one
  · have hGx := hG0 (hx.trans (half_le_self hη.le))
    simp only [coe_mk, ψ, map_neg, map_smul, smul_eq_mul, hGapp, hρ1 hx, one_mul, ← hGnorm]
    field_simp [norm_ne_zero_iff.2 hGx]

/-- **The calibration estimate.** If a test vector field `ψ` satisfies `Dw (ψ) = -‖Dw‖` on the
shell `S = {0 < w < η}`, as `-∇w / ‖∇w‖` does, then
`∫_S ‖Dw‖ ≤ η (∫_{w > 0} div ψ + ∫_S |div ψ|)`. -/
private theorem setIntegral_norm_fderiv_le {w : E → ℝ} (hw : ContDiff ℝ 1 w) {η : ℝ} (hη : 0 < η)
    (ψ : 𝓓(⊤, E)) (hψ : ∀ x, w x ∈ Ioo 0 η → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖) :
    ∫ x in w ⁻¹' Ioo 0 η, ‖fderiv ℝ w x‖ ≤
      η * ((∫ x, divergenceCLM ψ x * {x | 0 < w x}.indicator 1 x) +
        ∫ x in w ⁻¹' Ioo 0 η, |divergenceCLM ψ x|) := by
  set S := w ⁻¹' Ioo 0 η
  set F := {x | 0 < w x}
  let v : E → ℝ := fun y => max 0 (min (w y) η)
  let D : E → ℝ := divergenceCLM ψ
  have hS : MeasurableSet S := hw.continuous.measurable measurableSet_Ioo
  have hF : MeasurableSet F := measurableSet_lt measurable_const hw.continuous.measurable
  have hD : Integrable D :=
    (divergenceCLM ψ).continuous.integrable_of_hasCompactSupport (divergenceCLM ψ).hasCompactSupport
  have hv : LocallyLipschitz v := (hw.locallyLipschitz.min_const η).const_max 0
  -- Integration by parts against the clamped function `v` gives `∫ D v = ∫_S ‖Dw‖`.
  have hibp : ∫ x, D x * v x = ∫ x in S, ‖fderiv ℝ w x‖ := by
    have := (hv.locallyLipschitzOn (s := ((⊤ : Opens E) : Set E))).hasWeakFDerivOn_fderiv
      (μ := volume) |>.integral_divergenceCLM_smul_eq_neg_integral ψ
    simp only [smul_eq_mul] at this
    rw [this, ← integral_indicator hS, ← integral_neg]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [v]
    rw [fderiv_max_min_eq_indicator hw.continuous hη x]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem (s := w ⁻¹' Ioo 0 η) hx, indicator_of_mem hx, hψ x hx, neg_neg]
    · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) hx, indicator_of_notMem hx]
      simp
  -- The clamped function agrees with `η 1_F` off `S`, and differs from it by at most `η` on `S`.
  have hpt (x : E) : ‖D x * (η * F.indicator 1 x - v x)‖ ≤ η * S.indicator (fun x => |D x|) x := by
    have hcl := abs_mul_indicator_sub_max_min_le (w := w) hη.le x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem (s := w ⁻¹' Ioo 0 η) hxS] at hcl
      rw [indicator_of_mem hxS, mul_comm η (|D x|)]
      exact mul_le_mul_of_nonneg_left hcl (abs_nonneg _)
    · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) hxS] at hcl
      rw [indicator_of_notMem hxS, mul_zero]
      exact (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hcl)
  have hbdd (f : E → ℝ) (hf : Measurable f) (c : ℝ) (hfc : ∀ x, ‖f x‖ ≤ c) :
      Integrable fun x => D x * f x :=
    hD.mul_bdd hf.aestronglyMeasurable (.of_forall hfc)
  have hFm : Measurable (F.indicator (1 : E → ℝ)) := measurable_const.indicator hF
  have hvm : Measurable v := hv.continuous.measurable
  have hFb (x : E) : ‖F.indicator (1 : E → ℝ) x‖ ≤ 1 := by
    by_cases hx : x ∈ F <;> simp [hx]
  have hvb (x : E) : ‖v x‖ ≤ η := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [le_max_left 0 (min (w x) η)], max_le hη.le (min_le_right _ _)⟩
  have hdiff : ∫ x, D x * (η * F.indicator 1 x - v x) =
      η * (∫ x, D x * F.indicator 1 x) - ∫ x, D x * v x := by
    rw [← integral_const_mul, ← integral_sub ((hbdd _ hFm 1 hFb).const_mul η) (hbdd _ hvm η hvb)]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  have hrem : ‖∫ x, D x * (η * F.indicator 1 x - v x)‖ ≤ η * ∫ x in S, |D x| := by
    rw [← integral_indicator hS, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (((hD.abs.indicator hS)).const_mul η) (.of_forall hpt)
  rw [Real.norm_eq_abs] at hrem
  rw [← hibp, mul_add]
  linarith [neg_abs_le (∫ x, D x * (η * F.indicator 1 x - v x))]

/-- **One step of the smooth isoperimetric argument.** Suppose that `‖Dw‖` lies within `ε < 1`
of `1` on `{0 ≤ w ≤ η}` and that a test vector field `ψ` satisfies `Dw (ψ) = -‖Dw‖` on
`S = {0 < w < η}`. Then, with `F = {w > 0}` of finite volume and `G = {w ≥ η}` nonempty,
`(1 - ε) / (1 + ε) n ω_n ^ (1 / n) (volume G ^ (1 / n)) ^ (n - 1) ≤ ∫_F div ψ + ∫_S |div ψ|`. -/
private theorem div_mul_le_integral_add_setIntegral {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hn : finrank ℝ E ≠ 0) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hF : volume {x | 0 < w x} ≠ ⊤) (hG : {x | η ≤ w x}.Nonempty)
    (hgrad : ∀ x, 0 ≤ w x → w x ≤ η → |‖fderiv ℝ w x‖ - 1| < ε)
    (hint : IntegrableOn (fun x => ‖fderiv ℝ w x‖) (w ⁻¹' Ioo 0 η)) (ψ : 𝓓(⊤, E))
    (hψ : ∀ x, w x ∈ Ioo 0 η → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖) :
    (1 - ε) / (1 + ε) * (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        (volume.real {x | η ≤ w x} ^ (finrank ℝ E : ℝ)⁻¹) ^ (finrank ℝ E - 1)) ≤
      (∫ x, divergenceCLM ψ x * {x | 0 < w x}.indicator 1 x) +
        ∫ x in w ⁻¹' Ioo 0 η, |divergenceCLM ψ x| := by
  set n := finrank ℝ E
  set F := {x | 0 < w x}
  set G := {x | η ≤ w x}
  set S := w ⁻¹' Ioo 0 η
  have hGm : MeasurableSet G := measurableSet_le measurable_const hw.continuous.measurable
  have hGF : G ⊆ F := fun x hx => hη.trans_le hx
  have hSFG : S = F \ G := by
    ext x
    simp [S, F, G, not_le]
  have hSm : MeasurableSet S := hw.continuous.measurable measurableSet_Ioo
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hF (measure_mono (hSFG ▸ sdiff_subset))
  -- The `η / (1 + ε)`-neighbourhood of `G` stays in `F`, so Brunn–Minkowski bounds `|S|` below.
  have hsub : G + ball (0 : E) (η / (1 + ε)) ⊆ F := by
    rintro _ ⟨x, hx, z, hz, rfl⟩
    refine lt_apply_add_of_norm_fderiv_le (hw.differentiable one_ne_zero) (L := 1 + ε) (by linarith)
      (fun y hy1 hy2 => ?_) hx ?_
    · linarith [(abs_lt.1 (hgrad y hy1 hy2)).2]
    · rw [mem_ball_zero_iff, lt_div_iff₀ (by linarith)] at hz
      linarith
  have hshell := finrank_mul_rpow_pow_mul_le_volume_real_sub hn hGm.nullMeasurableSet hG hF
    (div_pos hη (by linarith)) hsub
  rw [← measureReal_sdiff hGF hGm hF, ← hSFG] at hshell
  -- On `S` the gradient has norm at least `1 - ε`, and the calibration bounds its integral.
  have hlow : (1 - ε) * volume.real S ≤ ∫ x in S, ‖fderiv ℝ w x‖ :=
    setIntegral_ge_of_const_le_real hSm hSfin
      (fun x hx => by linarith [(abs_lt.1 (hgrad x hx.1.le hx.2.le)).1]) hint
  have hcal := setIntegral_norm_fderiv_le hw hη ψ hψ
  refine le_of_mul_le_mul_left ?_ hη
  calc η * ((1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
          (volume.real G ^ (n : ℝ)⁻¹) ^ (n - 1)))
      = (1 - ε) * (n * (volume.real G ^ (n : ℝ)⁻¹) ^ (n - 1) *
          (η / (1 + ε) * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹)) := by
        field_simp
    _ ≤ (1 - ε) * volume.real S := mul_le_mul_of_nonneg_left hshell (by linarith)
    _ ≤ _ := hlow.trans hcal

/-- **The limit over shrinking shells.** Let `w` be smooth with `{w ≥ -δ}` compact and
`‖Dw‖ = 1` on its zero level, let `F = {w > 0}` have positive volume, and let the test vector
field `ψ` satisfy `Dw (ψ) = -‖Dw‖` on `{|w| ≤ η₀}`. Then for every `0 < ε < 1`,
`(1 - ε) / (1 + ε) n ω_n ^ (1 / n) (|F| ^ (1 / n)) ^ (n - 1) ≤ ∫_F div ψ`. -/
private theorem div_mul_le_integral_mul_indicator {w : E → ℝ} (hw : ContDiff ℝ ∞ w) {δ : ℝ}
    (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x}) (hnorm : ∀ x, w x = 0 → ‖fderiv ℝ w x‖ = 1)
    (hn : finrank ℝ E ≠ 0) (hV : volume {x | 0 < w x} ≠ 0) (ψ : 𝓓(⊤, E)) {η₀ : ℝ}
    (hη₀ : 0 < η₀) (hψ : ∀ x, |w x| ≤ η₀ → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) / (1 + ε) * (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        (volume.real {x | 0 < w x} ^ (finrank ℝ E : ℝ)⁻¹) ^ (finrank ℝ E - 1)) ≤
      ∫ x, divergenceCLM ψ x * {x | 0 < w x}.indicator 1 x := by
  set n := finrank ℝ E
  set F := {x | 0 < w x}
  have hF : volume F ≠ ⊤ := ne_top_of_le_ne_top hK.measure_lt_top.ne
    (measure_mono fun x hx => ((neg_lt_zero.2 hδ).trans hx).le)
  have hfd : Continuous fun x => ‖fderiv ℝ w x‖ := (hw.continuous_fderiv (by simp)).norm
  -- Near the zero level, `‖Dw‖` lies within `ε` of `1`.
  obtain ⟨η₁, hη₁, -, hη₁C⟩ := exists_forall_abs_le_notMem hw.continuous hδ hK
    (C := {x | ε ≤ |‖fderiv ℝ w x‖ - 1|})
    (isClosed_le continuous_const (hfd.sub continuous_const).abs) fun x hx h0 => by
      have hx : ε ≤ |‖fderiv ℝ w x‖ - 1| := hx
      rw [hnorm x h0, sub_self, abs_zero] at hx
      linarith
  -- Along `η k = min η₀ η₁ / (k + 1)`, apply the one-step estimate and let `k → ∞`.
  set m := min η₀ η₁
  have hm : 0 < m := lt_min hη₀ hη₁
  let η : ℕ → ℝ := fun k => m / (k + 1)
  have hηpos (k : ℕ) : 0 < η k := by positivity
  have hηm (k : ℕ) : η k ≤ m := div_le_self hm.le (by linarith [k.cast_nonneg (α := ℝ)])
  have hηanti : Antitone η := fun i j hij =>
    div_le_div_of_nonneg_left hm.le (by positivity) (by gcongr)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul m
    rw [mul_zero] at this
    exact this.congr fun k => by simp only [η]; ring
  let G : ℕ → Set E := fun k => {x | η k ≤ w x}
  let S : ℕ → Set E := fun k => w ⁻¹' Ioo 0 (η k)
  -- The superlevel sets `G k` exhaust `F`, and the shells `S k` shrink to the empty set.
  have hGlim : Tendsto (fun k => volume (G k)) atTop (𝓝 (volume F)) := by
    have hU : (⋃ k, G k) = F := by
      ext x
      simp only [mem_iUnion]
      refine ⟨fun ⟨k, hk⟩ => (hηpos k).trans_le hk, fun hx => ?_⟩
      exact ((hηlim.eventually (gt_mem_nhds hx)).exists).imp fun k hk => hk.le
    have hmono : Monotone G := fun i j hij x (hx : η i ≤ w x) => (hηanti hij).trans hx
    have := tendsto_measure_iUnion_atTop (μ := volume) hmono
    rwa [hU] at this
  have hSlim : Tendsto (fun k => ∫ x in S k, |divergenceCLM ψ x|) atTop (𝓝 0) := by
    have hI : (⋂ k, S k) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      simp only [mem_iInter] at hx
      obtain ⟨k, hk⟩ := (hηlim.eventually (gt_mem_nhds (hx 0).1)).exists
      exact (hx k).2.not_gt hk
    have hanti : Antitone S := fun i j hij x (hx : w x ∈ Ioo 0 (η j)) =>
      ⟨hx.1, hx.2.trans_le (hηanti hij)⟩
    have hDint : Integrable fun x => |divergenceCLM ψ x| :=
      ((divergenceCLM ψ).continuous.integrable_of_hasCompactSupport
        (divergenceCLM ψ).hasCompactSupport).abs
    have := tendsto_setIntegral_of_antitone (μ := volume)
      (fun k => hw.continuous.measurable measurableSet_Ioo) hanti ⟨0, hDint.integrableOn⟩
    rwa [hI, setIntegral_empty] at this
  have hlhs : Tendsto (fun k => (1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
      (volume.real (G k) ^ (n : ℝ)⁻¹) ^ (n - 1))) atTop
      (𝓝 ((1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
        (volume.real F ^ (n : ℝ)⁻¹) ^ (n - 1)))) := by
    have hreal := (ENNReal.tendsto_toReal hF).comp hGlim
    exact (((Real.continuous_rpow_const (by positivity)).tendsto _).comp hreal).pow _
      |>.const_mul _ |>.const_mul _
  refine le_of_tendsto_of_tendsto hlhs
    (by simpa only [add_zero] using hSlim.const_add (∫ x, divergenceCLM ψ x * F.indicator 1 x)) ?_
  filter_upwards [hGlim.eventually_ne hV] with k hk
  refine div_mul_le_integral_add_setIntegral (hw.of_le (by simp)) hn (hηpos k) hε hε1 hF
    (nonempty_of_measure_ne_zero hk) (fun x hx0 hxη => ?_)
    ((hfd.continuousOn.integrableOn_compact hK).mono_set fun x hx => ?_) ψ fun x hx => ?_
  · exact lt_of_not_ge (hη₁C x (abs_le.2 ⟨by linarith [hηpos k], hxη.trans
      ((hηm k).trans (min_le_right _ _))⟩))
  · exact ((neg_lt_zero.2 hδ).trans (hx : w x ∈ Ioo 0 (η k)).1).le
  · exact hψ x (abs_le.2 ⟨by linarith [hx.1], hx.2.le.trans ((hηm k).trans (min_le_left _ _))⟩)

/-- **The sharp isoperimetric inequality for a normalized smooth defining function.** Let `w` be
smooth with `{w ≥ -δ}` compact for some `δ > 0` and `‖Dw‖ = 1` on its zero level. In dimension
`n ≥ 1`, if `F = {w > 0}` has positive volume, then `n ω_n ^ (1 / n) |F| ^ (1 - 1 / n) ≤ P(F)`. -/
private theorem ofReal_le_perimeter_setOf_pos {w : E → ℝ} (hw : ContDiff ℝ ∞ w) {δ : ℝ}
    (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x}) (hnorm : ∀ x, w x = 0 → ‖fderiv ℝ w x‖ = 1)
    (hn : finrank ℝ E ≠ 0) (hV : volume {x | 0 < w x} ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real {x | 0 < w x} ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤
      perimeter volume ⊤ {x | 0 < w x} := by
  set n := finrank ℝ E
  obtain ⟨η₀, hη₀, ψ, hψ1, hψ⟩ := exists_testFunction_fderiv_apply_eq_neg_norm hw hδ hK
    fun x hx h0 => by
      have := hnorm x hx
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  -- It suffices to bound `∫_F div ψ`, which is at most the perimeter of `F`.
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    ((ofReal_integral_le_totalVariationOn ψ hψ1).trans_eq perimeter_def.symm)
  have hpow : volume.real {x | 0 < w x} ^ (1 - (n : ℝ)⁻¹) =
      (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1) := by
    rw [← Real.rpow_mul_natCast measureReal_nonneg, Nat.cast_pred (Nat.pos_of_ne_zero hn),
      mul_sub, mul_one, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn)]
  rw [hpow]
  -- Let the gradient tolerance `ε` tend to zero.
  have hlim : Tendsto (fun ε : ℝ => (1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^
      (n : ℝ)⁻¹ * (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1))) (𝓝[>] 0)
      (𝓝 (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
        (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1))) := by
    have : ContinuousAt (fun ε : ℝ => (1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^
        (n : ℝ)⁻¹ * (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1))) 0 := by
      fun_prop (disch := norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε using
      div_mul_le_integral_mul_indicator hw hδ hK hnorm hn hV ψ hη₀ hψ hε.1 hε.2)

end TauCeti

section ContDiff

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The sharp isoperimetric inequality for regular superlevel sets.** Let `u` be smooth and
compactly supported, and let `t > 0` be a regular value of `u`. In dimension `n ≥ 1`, if
`F = {u > t}` has positive volume, then `n ω_n ^ (1 / n) |F| ^ (1 - 1 / n) ≤ P(F)`. -/
theorem ContDiff.ofReal_mul_volume_real_rpow_mul_le_perimeter_setOf_lt {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) {t : ℝ} (ht : 0 < t)
    (hreg : ∀ x, u x = t → fderiv ℝ u x ≠ 0) (hn : finrank ℝ E ≠ 0)
    (hV : volume {x | t < u x} ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real {x | t < u x} ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤
      perimeter volume ⊤ {x | t < u x} := by
  obtain ⟨w, hw, hK, hnorm, hset⟩ := hu.exists_contDiff_setOf_pos_eq_setOf_lt huc ht hreg
  rw [← hset] at hV ⊢
  exact ofReal_le_perimeter_setOf_pos hw (by norm_num) hK hnorm hn hV

end ContDiff

namespace MeasureTheory.NullMeasurableSet

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The sharp isoperimetric inequality, extended-real form.** In a Euclidean space of dimension
`n ≥ 1`, every null-measurable set `s` of finite positive volume satisfies
`n ω_n ^ (1 / n) |s| ^ (1 - 1 / n) ≤ P(s)`, where `ω_n = volume (ball 0 1)` and `P(s)` is the
perimeter of `s` in the whole space, finite or infinite. No boundedness or regularity is
assumed. -/
theorem ofReal_mul_volume_real_rpow_mul_le_perimeter
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hn : finrank ℝ E ≠ 0)
    (hs0 : volume s ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤ perimeter volume ⊤ s := by
  obtain ⟨u, t, hprop, hsymm, hP⟩ := hs.exists_smooth_perimeter_approximation hμs
  set F : ℕ → Set E := fun k => {x | t k < u k x}
  have hFm (k : ℕ) : NullMeasurableSet (F k) volume := by
    obtain ⟨hu, -⟩ := hprop k
    exact (measurableSet_lt measurable_const hu.continuous.measurable).nullMeasurableSet
  have hFfin (k : ℕ) : volume (F k) ≠ ⊤ := by
    obtain ⟨-, -, -, -, hcl, -⟩ := hprop k
    exact ne_top_of_le_ne_top hcl.measure_lt_top.ne (measure_mono subset_closure)
  -- The volumes of the approximations converge to the volume of `s`.
  have hV : Tendsto (fun k => volume.real (F k)) atTop (𝓝 (volume.real s)) := by
    have h0 : Tendsto (fun k => volume.real (F k ∆ s)) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsymm
      rwa [ENNReal.toReal_zero] at this
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) h0)
    rw [Real.dist_eq]
    exact abs_measureReal_sub_le_measureReal_symmDiff' (hFm k) hs (hFfin k) hμs
  have hpos : 0 < volume.real s := ENNReal.toReal_pos hs0 hμs
  refine le_of_tendsto_of_tendsto (ENNReal.tendsto_ofReal ((((Real.continuous_rpow_const
    (sub_nonneg.2 (inv_le_one_of_one_le₀ (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn))))).tendsto
      _).comp hV).const_mul _)) hP ?_
  filter_upwards [hV.eventually (lt_mem_nhds hpos)] with k hk
  obtain ⟨hu, huc, htk, hreg, -⟩ := hprop k
  refine hu.ofReal_mul_volume_real_rpow_mul_le_perimeter_setOf_lt huc htk.1
    (fun x hx h0 => ?_) hn ?_
  · obtain ⟨v, hv⟩ := hreg x hx 1
    simp [h0] at hv
  · intro h
    rw [measureReal_def, (h : volume (F k) = 0), ENNReal.toReal_zero] at hk
    exact hk.false

/-- **The sharp isoperimetric inequality, real-valued form.** In a Euclidean space of dimension
`n ≥ 1`, every null-measurable set `s` of finite positive volume and finite perimeter satisfies
`n ω_n ^ (1 / n) |s| ^ (1 - 1 / n) ≤ P(s)`, where `ω_n = volume (ball 0 1)` and `P(s)` is the
perimeter of `s` in the whole space. No boundedness or regularity is assumed. -/
theorem mul_volume_real_rpow_mul_le_perimeter_toReal
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hn : finrank ℝ E ≠ 0)
    (hs0 : volume s ≠ 0) (hP : perimeter volume ⊤ s ≠ ⊤) :
    finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤ (perimeter volume ⊤ s).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hP).1
    (hs.ofReal_mul_volume_real_rpow_mul_le_perimeter hμs hn hs0)

/-- **The sharp isoperimetric inequality.** In a Euclidean space of dimension `n ≥ 1`, every
null-measurable set `s` of finite positive volume satisfies `P(s)^n ≥ n^n ω_n |s|^(n-1)`, where
`ω_n = volume (ball 0 1)` and `P(s)` is the perimeter of `s` in the whole space, finite or
infinite. No boundedness or regularity is assumed. Balls attain equality
(`TauCeti.perimeter_ball_pow`). -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hn : finrank ℝ E ≠ 0)
    (hs0 : volume s ≠ 0) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) * volume s ^ (finrank ℝ E - 1) ≤
      perimeter volume ⊤ s ^ finrank ℝ E := by
  rw [finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hμs hn,
    ENNReal.ofReal_pow (by positivity)]
  exact pow_le_pow_left₀ zero_le (hs.ofReal_mul_volume_real_rpow_mul_le_perimeter hμs hn hs0) _

end MeasureTheory.NullMeasurableSet
