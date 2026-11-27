/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
public import TauCeti.Analysis.Fourier.Continuous
public import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# The Fourier integral on `L¹ ∩ L²`

On a finite-dimensional real inner product space `E`, Mathlib has two Fourier transforms: the
Fourier integral `𝓕 f ξ = ∫ 𝐞(-⟪x, ξ⟫) • f x` of a function, and the Fourier transform on
`L²(E, F)` (`MeasureTheory.Lp.fourierTransformₗᵢ`), obtained by extending the Fourier transform of
Schwartz functions by continuity. This file proves **Plancherel's theorem on `L¹ ∩ L²`**: if `f`
is integrable and square integrable, then `𝓕 f` is square integrable with `‖𝓕 f‖₂ = ‖f‖₂`, and
the Fourier integral preserves the `L²` inner product of two such functions (Parseval's identity).

It rests on the fact that the two transforms agree on `L¹ ∩ L²`: the `L²` Fourier
transform of the class of such an `f` is almost everywhere the Fourier integral of `f`. Both are
the Fourier transform of `f` as a tempered distribution
(`MeasureTheory.Lp.fourier_toTemperedDistribution_eq`,
`MeasureTheory.Lp.fourier_toTemperedDistribution_apply`), and an `L²` function is determined
almost everywhere by its pairings with Schwartz functions.

Together with the `L¹ → L^∞` bound `‖𝓕 f‖_∞ ≤ ‖f‖₁` (`TauCeti.eLpNorm_fourier_top_le`), these are
the two endpoint estimates which the Riesz–Thorin theorem interpolates to the Hausdorff–Young
inequality, in `TauCeti.Analysis.Fourier.HausdorffYoung`.

The file also records the Fourier transform of an `L²` derivative: if the tempered distribution
`f` has a Fourier transform `v ∈ L^q`, `1 ≤ q`, and the derivative `∂_m f` is an `L²` function
`d`, then `𝓕 d(ξ) = 2πi⟪ξ, m⟫ v(ξ)` almost everywhere, and the Fourier transform of an `L²`
dilation: the `L²` Fourier transform turns the normalized dilation `D_r` into `D_{r⁻¹}`.

## Main declarations

* `MeasureTheory.Integrable.coeFn_fourier_toLp`: on `L¹ ∩ L²` the `L²` Fourier transform is the
  Fourier integral.
* `MeasureTheory.Integrable.eLpNorm_fourier_two_eq`: Plancherel's theorem on `L¹ ∩ L²`.
* `MeasureTheory.Integrable.memLp_fourier_two`: the Fourier integral of a function in `L¹ ∩ L²`
  lies in `L²`.
* `MeasureTheory.Integrable.integral_inner_fourier_fourier`: Parseval's identity on `L¹ ∩ L²`.
* `MeasureTheory.Lp.fourier_ae_eq_of_lineDerivOp_eq`: the Fourier transform of an `L²` derivative
  `∂_m f` is `2πi⟪ξ, m⟫ 𝓕f`.
* `MeasureTheory.Lp.fourier_dilateLp`: the `L²` Fourier transform turns the normalized dilation
  `D_r` of `L²` into `D_{r⁻¹}`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 2.2.4.
* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter I,
  Theorem 2.1.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace MeasureTheory.Integrable

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {f : E → F}

/-- On `L¹ ∩ L²` the Fourier transform on `L²` is the Fourier integral: for `f` integrable and
square integrable, the `L²` Fourier transform of the class of `f` is almost everywhere `𝓕 f`. -/
theorem coeFn_fourier_toLp (hf : Integrable f) (hf₂ : MemLp f 2) :
    ⇑(𝓕 (hf₂.toLp f) : Lp F 2 (volume : Measure E)) =ᵐ[volume] 𝓕 f := by
  refine Lp.ae_eq_of_toTemperedDistribution_apply_eq _ hf.continuous_fourier.locallyIntegrable
    fun φ => ?_
  rw [← Lp.fourier_toTemperedDistribution_eq]
  exact Lp.fourier_toTemperedDistribution_apply _ hf hf₂.coeFn_toLp φ

/-- **Plancherel's theorem on `L¹ ∩ L²`.** The Fourier integral of an integrable, square
integrable function has the same `L²` norm as the function. -/
theorem eLpNorm_fourier_two_eq (hf : Integrable f) (hf₂ : MemLp f 2) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  rw [← eLpNorm_congr_ae (hf.coeFn_fourier_toLp hf₂), ← eLpNorm_congr_ae hf₂.coeFn_toLp,
    ← ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ← Lp.norm_def,
    ← Lp.norm_def, Lp.norm_fourier_eq]

/-- The Fourier integral of an integrable, square integrable function is square integrable. -/
theorem memLp_fourier_two (hf : Integrable f) (hf₂ : MemLp f 2) : MemLp (𝓕 f) 2 :=
  memLp_iff.2 ((hf.eLpNorm_fourier_two_eq hf₂).trans_lt hf₂.eLpNorm_lt_top)

open scoped ComplexInnerProductSpace in
/-- **Parseval's identity on `L¹ ∩ L²`.** The Fourier integrals of two integrable, square
integrable functions have the same `L²` inner product as the functions. -/
theorem integral_inner_fourier_fourier (hf : Integrable f) (hf₂ : MemLp f 2) {g : E → F}
    (hg : Integrable g) (hg₂ : MemLp g 2) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x, ⟪f x, g x⟫ := by
  have h := Lp.inner_fourier_eq (hf₂.toLp f) (hg₂.toLp g)
  rw [L2.inner_def, L2.inner_def] at h
  calc ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫
      = ∫ ξ, ⟪(𝓕 (hf₂.toLp f) : Lp F 2 (volume : Measure E)) ξ,
          (𝓕 (hg₂.toLp g) : Lp F 2 (volume : Measure E)) ξ⟫ := by
        refine integral_congr_ae ?_
        filter_upwards [hf.coeFn_fourier_toLp hf₂, hg.coeFn_fourier_toLp hg₂] with ξ h₁ h₂
        rw [h₁, h₂]
    _ = ∫ x, ⟪f x, g x⟫ := by
        rw [h]
        refine integral_congr_ae ?_
        filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x h₁ h₂
        rw [h₁, h₂]

end MeasureTheory.Integrable

namespace MeasureTheory.Lp

open TemperedDistribution
open scoped LineDeriv SchwartzMap Real

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Fourier transform of a derivative.** If a tempered distribution `f` has the `L^q`
Fourier transform `v` and its derivative in the direction `m` is an `L²` function `d`, then
`𝓕 d(ξ) = 2πi⟪ξ, m⟫ v(ξ)` almost everywhere. -/
theorem fourier_ae_eq_of_lineDerivOp_eq {f : 𝓢'(E, F)} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {v : Lp F q (volume : Measure E)} {d : Lp F 2 (volume : Measure E)} (hv : 𝓕 f = v) {m : E}
    (hd : ∂_{m} f = d) :
    𝓕 d =ᵐ[volume] fun ξ ↦ (2 * π * Complex.I * inner ℝ ξ m) • v ξ := by
  rw [← toTemperedDistribution_eq_smulLeftCLM_iff (by fun_prop),
    ← fourier_toTemperedDistribution_eq, ← hd, fourier_lineDerivOp_eq, hv]
  exact (DFunLike.congr_fun (smulLeftCLM_smul (F := F) (g := fun ξ : E ↦ (inner ℝ ξ m : ℂ))
    (by fun_prop) (2 * π * Complex.I)) _).symm

/-! ### Dilations -/

section Dilation

open Measure Module

/-- `MeasureTheory.Lp.fourier_dilateLp` for the class of a Schwartz function. -/
private theorem fourier_dilateLp_toLp {r : ℝ} (hr : 0 < r) (φ : 𝓢(E, F)) :
    𝓕 (dilateLp volume ℝ 2 r hr (φ.toLp 2)) =
      dilateLp volume ℝ 2 r⁻¹ (inv_pos.2 hr) (𝓕 (φ.toLp 2)) := by
  set g : E → F := fun x ↦ r ^ (-((finrank ℝ E : ℝ) / 2)) • φ (r⁻¹ • x)
  -- The dilated class is represented by the dilated Schwartz function `g`.
  have hg : ⇑(dilateLp volume ℝ 2 r hr (φ.toLp 2)) =ᵐ[volume] g := by
    simpa only [ENNReal.toReal_ofNat] using coeFn_dilateLp_of_ae_eq (𝕜 := ℝ) hr (φ.coeFn_toLp 2)
  have hg₂ : MemLp g 2 volume := (Lp.memLp _).ae_eq hg
  have hg₁ : Integrable g volume := (φ.integrable.comp_smul (inv_ne_zero hr.ne')).smul _
  have hD : dilateLp volume ℝ 2 r hr (φ.toLp 2) = hg₂.toLp g :=
    Lp.ext (hg.trans hg₂.coeFn_toLp.symm)
  rw [hD]
  refine Lp.ext ?_
  rw [SchwartzMap.toLp_fourier_eq]
  filter_upwards [hg₁.coeFn_fourier_toLp hg₂,
    coeFn_dilateLp_of_ae_eq (𝕜 := ℝ) (inv_pos.2 hr) ((𝓕 φ).coeFn_toLp 2)] with ξ h₁ h₂
  rw [h₁, h₂, ENNReal.toReal_ofNat]
  have hc : 𝓕 g ξ = r ^ (-((finrank ℝ E : ℝ) / 2)) • 𝓕 (fun x ↦ φ (r⁻¹ • x)) ξ := by
    simp only [g, Real.fourier_eq, smul_comm _ (r ^ (-((finrank ℝ E : ℝ) / 2))), integral_smul]
  rw [hc, TauCeti.fourier_comp_smul, inv_inv, smul_smul]
  congr 1
  rw [abs_of_pos (by positivity), inv_pow, inv_inv, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le,
    ← Real.rpow_add_natCast hr.ne']
  ring_nf

/-- **The `L²` Fourier transform of a dilation.** The Fourier transform on `L²` turns the normalized
dilation by `r > 0` into the normalized dilation by `r⁻¹`: replacing `f` by
`r ^ (-n/2) • f (r⁻¹ • ·)` replaces `𝓕 f` by `r ^ (n/2) • 𝓕 f (r • ·)`. -/
theorem fourier_dilateLp {r : ℝ} (hr : 0 < r) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (dilateLp volume ℝ 2 r hr f) = dilateLp volume ℝ 2 r⁻¹ (inv_pos.2 hr) (𝓕 f) := by
  have hc₁ : Continuous fun f : Lp F 2 (volume : Measure E) ↦ 𝓕 (dilateLp volume ℝ 2 r hr f) :=
    FourierTransform.continuous_fourier.comp (dilateLp volume ℝ 2 r hr).continuous
  have hc₂ : Continuous fun f : Lp F 2 (volume : Measure E) ↦
      dilateLp volume ℝ 2 r⁻¹ (inv_pos.2 hr) (𝓕 f) :=
    (dilateLp volume ℝ 2 r⁻¹ (inv_pos.2 hr)).continuous.comp FourierTransform.continuous_fourier
  exact congrFun ((SchwartzMap.denseRange_toLpCLM (F := F) (E := E) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top).equalizer hc₁ hc₂ (funext fun φ ↦ fourier_dilateLp_toLp hr φ)) f

end Dilation

end MeasureTheory.Lp
