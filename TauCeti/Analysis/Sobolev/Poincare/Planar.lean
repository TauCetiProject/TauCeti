/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# An `L²` bound for planar functions from the gradient and a linear-growth modular

Let `E` be a real normed space of dimension two with an additive Haar measure `μ`. For a
compactly supported `C¹` function `w : E → ℝ` and a measurable set `s` of finite measure,

`∫ w² ≤ 2 k ∫_{sᶜ} (√(1 + w²) - 1) + k² μ(s)`,    `k = 2 + C (∫ ‖Dw‖²) ^ (1/2)`,

with a constant `C` depending only on `μ`
(`TauCeti.exists_integral_sq_le_of_finrank_eq_two`). The modular `√(1 + t²) - 1` is
comparable to `t²` for small `t` but grows only linearly for large `t`. So `w` is controlled in
`L²` by its Dirichlet energy, by a quantity of linear growth in `|w|` outside `s`, and by the
measure of `s`, where nothing is known about `w` beyond its energy. The bound is linear in the
modular, and the gradient enters only through `k`, which grows like the square root of the
energy. This is what makes it useful for coercivity of convex functionals whose nonlinear part
grows only linearly in one direction, such as the functional of Taubes for planar vortices,
whose potential `exp (2w) - 1 - 2w` is linear for negative `w`.

The proof applies the Gagliardo–Nirenberg–Sobolev inequality `‖f‖₂ ≤ G ‖Df‖₁`, valid in
dimension two (`MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv`), to `f = r(w)³`, where
`r(t) = t / √(1 + √(1 + t²))` is the smooth square root of `g(t) = √(1 + t²) - 1`. Since
`|(r³)'| ≤ (3/2) |r|`, the Cauchy–Schwarz inequality bounds `∫ g(w)³` by `∫ g(w) · ∫ ‖Dw‖²`, and
`∫ g(w)²` by the geometric mean of `∫ g(w)` and `∫ g(w)³`. As `w² = g(w)² + 2 g(w)`, this
gives `∫ w² ≤ k ∫ g(w)`. Finally `g(t) ≤ |t|` bounds the part of `∫ g(w)` over `s` by
`(μ(s) ∫ w²) ^ (1/2)`, which is absorbed.

## Main results

* `TauCeti.integral_sq_le_mul_sq_integral_norm_fderiv`: the Gagliardo–Nirenberg–Sobolev
  inequality `∫ f² ≤ G (∫ ‖Df‖)²` in dimension two, for Bochner integrals.
* `TauCeti.exists_integral_sq_le_of_finrank_eq_two`: the `L²` bound above.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
* L. Nirenberg, *On elliptic partial differential equations*, Ann. Scuola Norm. Sup. Pisa (3) 13
  (1959), 115–162.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Module Set
open scoped ENNReal

/-! ### The smooth square root of the modular -/

/-- The smooth function `r(t) = t / √(1 + √(1 + t²))`, whose square is `√(1 + t²) - 1`. -/
private def modularRoot (t : ℝ) : ℝ := t / √(1 + √(1 + t ^ 2))

private theorem modularRoot_sq (t : ℝ) : modularRoot t ^ 2 = √(1 + t ^ 2) - 1 := by
  have h1 := Real.one_le_sqrt_one_add_sq t
  have hs : √(1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  rw [modularRoot, div_pow, Real.sq_sqrt (by linarith), div_eq_iff (by linarith)]
  nlinarith

private theorem contDiff_modularRoot : ContDiff ℝ ⊤ modularRoot := by
  have h1 : ContDiff ℝ ⊤ fun t : ℝ ↦ √(1 + t ^ 2) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt fun t ↦ by positivity
  have h2 : ContDiff ℝ ⊤ fun t : ℝ ↦ √(1 + √(1 + t ^ 2)) :=
    (contDiff_const.add h1).sqrt fun t ↦ by positivity
  exact contDiff_id.div h2 fun t ↦ by positivity

/-- The derivative of `r³` is `(3/2) r(t) t / √(1 + t²)`; its absolute value is at most
`(3/2) |r(t)|`. -/
private theorem hasDerivAt_modularRoot_pow_three (t : ℝ) :
    HasDerivAt (fun t ↦ modularRoot t ^ 3) (3 / 2 * modularRoot t * (t / √(1 + t ^ 2))) t := by
  have hd : HasDerivAt modularRoot (deriv modularRoot t) t :=
    ((contDiff_modularRoot.differentiable (by simp)) t).hasDerivAt
  have hpos : 0 < 1 + t ^ 2 := by positivity
  -- `2 r r' = t / √(1 + t²)` is the derivative of `r² = √(1 + t²) - 1`.
  have hsq : HasDerivAt (fun t ↦ modularRoot t ^ 2) (2 * modularRoot t * deriv modularRoot t) t :=
    by simpa using hd.fun_pow 2
  have hg : HasDerivAt (fun t ↦ modularRoot t ^ 2) (t / √(1 + t ^ 2)) t := by
    have h1 : HasDerivAt (fun t ↦ 1 + t ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add 1
    have h2 := (h1.sqrt hpos.ne').sub_const 1
    rw [show (fun t ↦ modularRoot t ^ 2) = fun t ↦ √(1 + t ^ 2) - 1 from funext modularRoot_sq]
    convert h2 using 1
    field_simp
  have heq := hsq.unique hg
  convert hd.fun_pow 3 using 1
  simp only [Nat.cast_ofNat]
  rw [← heq]
  ring

/-- Composition with `r` preserves continuity and compact support. -/
private theorem continuous_hasCompactSupport_modularRoot_comp {X : Type*} [TopologicalSpace X]
    {w : X → ℝ} (hw : Continuous w) (hws : HasCompactSupport w) :
    (Continuous fun x ↦ modularRoot (w x)) ∧ HasCompactSupport fun x ↦ modularRoot (w x) :=
  ⟨contDiff_modularRoot.continuous.comp hw,
    hws.comp_left (g := modularRoot) (by simp [modularRoot])⟩

/-! ### Integral inequalities -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The Gagliardo–Nirenberg–Sobolev inequality in dimension two**, `∫ f² ≤ G (∫ ‖Df‖)²` for
compactly supported `C¹` real functions, as an inequality of Bochner integrals. The constant `G`
is Mathlib's `lintegralPowLePowLIntegralFDerivConst μ 2`. -/
theorem integral_sq_le_mul_sq_integral_norm_fderiv (hE : finrank ℝ E = 2) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f) :
    ∫ x, f x ^ 2 ∂μ ≤
      (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) * (∫ x, ‖fderiv ℝ f x‖ ∂μ) ^ 2 := by
  have hp : Real.HolderConjugate (finrank ℝ E) 2 := by
    rw [hE, Nat.cast_ofNat]
    exact Real.HolderConjugate.two_two
  have h := lintegral_pow_le_pow_lintegral_fderiv μ hf hfs hp
  have hint : Integrable (fun x ↦ f x ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hfs.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp))
  have hcd : Continuous fun x ↦ fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
  have hintd : Integrable (fun x ↦ ‖fderiv ℝ f x‖) μ :=
    hcd.norm.integrable_of_hasCompactSupport (hfs.fderiv (𝕜 := ℝ)).norm
  have hl : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦ sq_nonneg _)]
    refine lintegral_congr fun x ↦ ?_
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs]
  have hr : ∫⁻ x, ‖fderiv ℝ f x‖ₑ ∂μ = ENNReal.ofReal (∫ x, ‖fderiv ℝ f x‖ ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hintd (Eventually.of_forall fun x ↦ norm_nonneg _)]
    exact lintegral_congr fun x ↦ (ofReal_norm _).symm
  rw [hl, hr, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x ↦ norm_nonneg _)
    (by norm_num), ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    Real.rpow_two] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Gagliardo–Nirenberg–Sobolev applied to `r(w)³`, whose derivative is at most
`(3/2) |r(w)| ‖Dw‖`, followed by Cauchy–Schwarz: `∫ g(w)³ ≤ (9/4) G ∫ g(w) ∫ ‖Dw‖²`. -/
private theorem integral_modularRoot_pow_three_sq_le (hE : finrank ℝ E = 2) {w : E → ℝ}
    (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) :
    ∫ x, (modularRoot (w x) ^ 3) ^ 2 ∂μ ≤
      9 / 4 * (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) *
        (∫ x, modularRoot (w x) ^ 2 ∂μ) * ∫ x, ‖fderiv ℝ w x‖ ^ 2 ∂μ := by
  set G : ℝ := (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ)
  obtain ⟨hrc, hrs⟩ := continuous_hasCompactSupport_modularRoot_comp hw.continuous hws
  have hdc : Continuous fun x ↦ fderiv ℝ w x := hw.continuous_fderiv one_ne_zero
  have hds : HasCompactSupport fun x ↦ fderiv ℝ w x := hws.fderiv (𝕜 := ℝ)
  have hf3 : ContDiff ℝ 1 fun x ↦ modularRoot (w x) ^ 3 :=
    ((contDiff_modularRoot.of_le le_top).comp hw).pow 3
  have hf3s : HasCompactSupport fun x ↦ modularRoot (w x) ^ 3 :=
    hrs.comp_left (g := (· ^ 3)) (by simp)
  have habs : HasCompactSupport fun x ↦ |modularRoot (w x)| := hrs.comp_left (g := abs) abs_zero
  have hder (x : E) : ‖fderiv ℝ (fun x ↦ modularRoot (w x) ^ 3) x‖ ≤
      3 / 2 * (|modularRoot (w x)| * ‖fderiv ℝ w x‖) := by
    have h : HasFDerivAt (fun x ↦ modularRoot (w x) ^ 3) _ x :=
      (hasDerivAt_modularRoot_pow_three (w x)).comp_hasFDerivAt x
        ((hw.differentiable one_ne_zero) x).hasFDerivAt
    rw [h.fderiv, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have h1 := Real.abs_div_sqrt_one_add_sq_le_one (w x)
    calc 3 / 2 * |modularRoot (w x)| * |w x / √(1 + w x ^ 2)| * ‖fderiv ℝ w x‖ ≤
          3 / 2 * |modularRoot (w x)| * 1 * ‖fderiv ℝ w x‖ := by gcongr
      _ = 3 / 2 * (|modularRoot (w x)| * ‖fderiv ℝ w x‖) := by ring
  have hL1 : ∫ x, ‖fderiv ℝ (fun x ↦ modularRoot (w x) ^ 3) x‖ ∂μ ≤
      3 / 2 * ∫ x, |modularRoot (w x)| * ‖fderiv ℝ w x‖ ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ norm_nonneg _)
      (((hrc.abs.mul hdc.norm).integrable_of_hasCompactSupport habs.mul_right).const_mul _)
      (Eventually.of_forall hder)
  have hCS := sq_integral_mul_le_integral_sq_mul_integral_sq
    (hrc.abs.memLp_of_hasCompactSupport (μ := μ) habs)
    (hdc.norm.memLp_of_hasCompactSupport hds.norm)
  simp only [sq_abs] at hCS
  have hI0 : 0 ≤ ∫ x, ‖fderiv ℝ (fun x ↦ modularRoot (w x) ^ 3) x‖ ∂μ :=
    integral_nonneg fun x ↦ norm_nonneg _
  calc ∫ x, (modularRoot (w x) ^ 3) ^ 2 ∂μ
      ≤ G * (∫ x, ‖fderiv ℝ (fun x ↦ modularRoot (w x) ^ 3) x‖ ∂μ) ^ 2 :=
        integral_sq_le_mul_sq_integral_norm_fderiv μ hE hf3 hf3s
    _ ≤ G * (3 / 2 * ∫ x, |modularRoot (w x)| * ‖fderiv ℝ w x‖ ∂μ) ^ 2 := by gcongr
    _ = 9 / 4 * G * (∫ x, |modularRoot (w x)| * ‖fderiv ℝ w x‖ ∂μ) ^ 2 := by ring
    _ ≤ 9 / 4 * G * ((∫ x, modularRoot (w x) ^ 2 ∂μ) * ∫ x, ‖fderiv ℝ w x‖ ^ 2 ∂μ) := by
        gcongr
    _ = _ := by ring

/-- The `L²` norm is controlled by the modular alone, with a factor depending on the energy:
`∫ w² ≤ (2 + (3/2) √(G ∫ ‖Dw‖²)) ∫ (√(1 + w²) - 1)`. Since `w² = g(w)² + 2 g(w)` for
`g(t) = √(1 + t²) - 1`, it suffices to bound `∫ g(w)²` by the geometric mean of `∫ g(w)` and
`∫ g(w)³`. -/
private theorem integral_sq_le_mul_integral_modular (hE : finrank ℝ E = 2) {w : E → ℝ}
    (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) :
    ∫ x, w x ^ 2 ∂μ ≤
      (2 + 3 / 2 * √(lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) *
          √(∫ x, ‖fderiv ℝ w x‖ ^ 2 ∂μ)) * ∫ x, (√(1 + w x ^ 2) - 1) ∂μ := by
  set G : ℝ := (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ)
  set A := ∫ x, ‖fderiv ℝ w x‖ ^ 2 ∂μ
  set X := ∫ x, modularRoot (w x) ^ 2 ∂μ
  have hG : 0 ≤ G := NNReal.coe_nonneg _
  have hA : 0 ≤ A := integral_nonneg fun x ↦ by positivity
  obtain ⟨hrc, hrs⟩ := continuous_hasCompactSupport_modularRoot_comp hw.continuous hws
  have hrs2 : HasCompactSupport fun x ↦ modularRoot (w x) ^ 2 :=
    hrs.comp_left (g := (· ^ 2)) (by simp)
  -- Cauchy–Schwarz: `(∫ g(w)²)² ≤ X Y ≤ ((3/2) √(G A) X)²`.
  have hg2 : ∫ x, (modularRoot (w x) ^ 2) ^ 2 ∂μ ≤ 3 / 2 * √G * √A * X := by
    have hm1 : MemLp (fun x ↦ |modularRoot (w x)|) 2 μ :=
      hrc.abs.memLp_of_hasCompactSupport (hrs.comp_left (g := abs) abs_zero)
    have hc3 : Continuous fun x ↦ |modularRoot (w x) ^ 3| := (hrc.pow 3).abs
    have hm3 : MemLp (fun x ↦ |modularRoot (w x) ^ 3|) 2 μ :=
      hc3.memLp_of_hasCompactSupport (hrs.comp_left (g := fun t ↦ |t ^ 3|) (by simp))
    have hCS := sq_integral_mul_le_integral_sq_mul_integral_sq hm1 hm3
    have heq : (fun x ↦ |modularRoot (w x)| * |modularRoot (w x) ^ 3|) =
        fun x ↦ (modularRoot (w x) ^ 2) ^ 2 := by
      funext x
      rw [← abs_mul, show modularRoot (w x) * modularRoot (w x) ^ 3 =
        (modularRoot (w x) ^ 2) ^ 2 by ring]
      exact abs_of_nonneg (by positivity)
    simp only [heq, sq_abs] at hCS
    have h0 : 0 ≤ ∫ x, (modularRoot (w x) ^ 2) ^ 2 ∂μ := integral_nonneg fun x ↦ by positivity
    refine (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp ?_
    calc (∫ x, (modularRoot (w x) ^ 2) ^ 2 ∂μ) ^ 2
        ≤ X * ∫ x, (modularRoot (w x) ^ 3) ^ 2 ∂μ := hCS
      _ ≤ X * (9 / 4 * G * X * A) :=
          mul_le_mul_of_nonneg_left (integral_modularRoot_pow_three_sq_le μ hE hw hws)
            (integral_nonneg fun x ↦ sq_nonneg _)
      _ = (3 / 2 * √G * √A * X) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hA]
          ring
  -- `w² = g(w)² + 2 g(w)`.
  have hw2 (x : E) : w x ^ 2 = (modularRoot (w x) ^ 2) ^ 2 + 2 * modularRoot (w x) ^ 2 := by
    rw [modularRoot_sq]
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + w x ^ 2)]
  have hc2 : Continuous fun x ↦ modularRoot (w x) ^ 2 := hrc.pow 2
  have hc4 : Continuous fun x ↦ (modularRoot (w x) ^ 2) ^ 2 := hc2.pow 2
  have hi1 : Integrable (fun x ↦ (modularRoot (w x) ^ 2) ^ 2) μ :=
    hc4.integrable_of_hasCompactSupport (hrs2.comp_left (g := (· ^ 2)) (by simp))
  have hi2 : Integrable (fun x ↦ modularRoot (w x) ^ 2) μ :=
    hc2.integrable_of_hasCompactSupport hrs2
  have hX : X = ∫ x, (√(1 + w x ^ 2) - 1) ∂μ := by simp only [X, modularRoot_sq]
  have hW : ∫ x, w x ^ 2 ∂μ =
      ∫ x, ((modularRoot (w x) ^ 2) ^ 2 + 2 * modularRoot (w x) ^ 2) ∂μ :=
    integral_congr_ae (Eventually.of_forall hw2)
  rw [hW, integral_add hi1 (hi2.const_mul 2), integral_const_mul, ← hX]
  linarith

/-- The absorption step: `W ≤ k (Q + Z)` and `Z² ≤ S W` give `W ≤ 2 k Q + k² S`. -/
private theorem le_two_mul_add_sq_mul_of_le_mul_add {W k Q Z S : ℝ} (hk : 0 ≤ k) (hQ : 0 ≤ Q)
    (hS : 0 ≤ S) (hW : W ≤ k * (Q + Z)) (hZ : Z ^ 2 ≤ S * W) :
    W ≤ 2 * k * Q + k ^ 2 * S := by
  have hkQ : 0 ≤ k * Q := mul_nonneg hk hQ
  have hkS : 0 ≤ k ^ 2 * S := by positivity
  rcases le_or_gt W (k * Q) with h | h
  · linarith
  have h1 : (W - k * Q) ^ 2 ≤ k ^ 2 * (S * W) := by
    calc (W - k * Q) ^ 2 ≤ (k * Z) ^ 2 := by gcongr; linarith
      _ = k ^ 2 * Z ^ 2 := by ring
      _ ≤ k ^ 2 * (S * W) := by gcongr
  have h2 : W * W ≤ W * (2 * k * Q + k ^ 2 * S) := by
    have e : W * (2 * k * Q + k ^ 2 * S) - W * W =
        k ^ 2 * (S * W) - (W - k * Q) ^ 2 + (k * Q) ^ 2 := by ring
    linarith [sq_nonneg (k * Q)]
  exact le_of_mul_le_mul_left h2 (hkQ.trans_lt h)

/-- **An `L²` bound for planar functions.** In dimension two there is a constant `C`, depending
only on the Haar measure `μ`, such that for every compactly supported `C¹` function `w` and every
measurable set `s` of finite measure,

`∫ w² ≤ 2 k ∫_{sᶜ} (√(1 + w²) - 1) + k² μ(s)`,    `k = 2 + C √(∫ ‖Dw‖²)`.

The modular `√(1 + t²) - 1` grows only linearly in `|t|`, and outside `s` it is the only control
on `w` apart from the Dirichlet energy. -/
theorem exists_integral_sq_le_of_finrank_eq_two (hE : finrank ℝ E = 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : E → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
      ∀ s : Set E, MeasurableSet s → μ s ≠ ∞ →
        ∫ x, w x ^ 2 ∂μ ≤
          2 * (2 + C * √(∫ x, ‖fderiv ℝ w x‖ ^ 2 ∂μ)) *
              ∫ x in sᶜ, (√(1 + w x ^ 2) - 1) ∂μ +
            (2 + C * √(∫ x, ‖fderiv ℝ w x‖ ^ 2 ∂μ)) ^ 2 * μ.real s := by
  refine ⟨3 / 2 * √(lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ), by positivity,
    fun w hw hws s hs hμs ↦ ?_⟩
  have hwc : Continuous w := hw.continuous
  have habs : HasCompactSupport fun x ↦ |w x| := hws.comp_left (g := abs) abs_zero
  have hmod : Integrable (fun x ↦ √(1 + w x ^ 2) - 1) μ :=
    (by fun_prop : Continuous fun x ↦ √(1 + w x ^ 2) - 1).integrable_of_hasCompactSupport
      (hws.comp_left (g := fun t ↦ √(1 + t ^ 2) - 1) (by simp))
  -- Split the modular over `s` and `sᶜ`; over `s` use `g(t) ≤ |t|`.
  have hsplit : ∫ x, (√(1 + w x ^ 2) - 1) ∂μ ≤
      ∫ x in sᶜ, (√(1 + w x ^ 2) - 1) ∂μ + ∫ x in s, |w x| ∂μ := by
    rw [← integral_add_compl hs hmod]
    have := setIntegral_mono_on hmod.integrableOn
      (hwc.abs.integrable_of_hasCompactSupport habs).integrableOn hs
      fun x _ ↦ Real.sqrt_one_add_sq_sub_one_le_abs (w x)
    linarith
  -- Cauchy–Schwarz over `s`: `(∫_s |w|)² ≤ μ(s) ∫ w²`.
  have hZ : (∫ x in s, |w x| ∂μ) ^ 2 ≤ μ.real s * ∫ x, w x ^ 2 ∂μ := by
    have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
    have hCS := sq_integral_mul_le_integral_sq_mul_integral_sq (μ := μ.restrict s)
      (f := fun _ ↦ (1 : ℝ)) (g := fun x ↦ |w x|) (memLp_const 1)
      ((hwc.abs.memLp_of_hasCompactSupport habs).restrict s)
    simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one, sq_abs,
      measureReal_restrict_apply_univ] at hCS
    refine hCS.trans (mul_le_mul_of_nonneg_left ?_ measureReal_nonneg)
    have hc2 : Continuous fun x ↦ w x ^ 2 := hwc.pow 2
    exact setIntegral_le_integral
      (hc2.integrable_of_hasCompactSupport (hws.comp_left (g := (· ^ 2)) (by simp)))
      (Eventually.of_forall fun x ↦ sq_nonneg _)
  have hk : 0 ≤ 2 + 3 / 2 * √(lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) *
      √(∫ x, ‖fderiv ℝ w x‖ ^ 2 ∂μ) := by positivity
  have hQ : 0 ≤ ∫ x in sᶜ, (√(1 + w x ^ 2) - 1) ∂μ :=
    integral_nonneg fun x ↦ sub_nonneg.mpr (Real.one_le_sqrt_one_add_sq (w x))
  have hW := (integral_sq_le_mul_integral_modular μ hE hw hws).trans
    (mul_le_mul_of_nonneg_left hsplit hk)
  exact le_two_mul_add_sq_mul_of_le_mul_add hk hQ measureReal_nonneg hW hZ

end TauCeti
