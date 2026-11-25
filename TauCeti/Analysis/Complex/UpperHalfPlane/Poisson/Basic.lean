/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Probability.Distributions.Cauchy
public import TauCeti.Analysis.Complex.Pick.Herglotz.Basic
public import TauCeti.Analysis.PDE.GreenFunction.HalfSpace
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.PDE.GreenFunction.HalfPlane
import TauCeti.Basic.Complex.OfRealSub
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity

/-!
# Poisson and Schwarz integrals on the upper half-plane

For `z` in the upper half-plane `ℂ₊ = {Im z > 0}` and `x ∈ ℝ`, the **Poisson kernel**

`P(z, x) = Im z / (π |x - z| ^ 2)`

is the two-dimensional half-space Poisson kernel `TauCeti.halfSpacePoissonKernel 2` with unit
inward normal `i`, read in the coordinates `Complex.orthonormalBasisOneI`. It has mass one on the
real line and is dominated by a multiple of `1 / (1 + x ^ 2)`, so it can be integrated against
every **Poisson-finite** measure `ν`, that is one with `∫ dν / (1 + x ^ 2) < ∞`.

The **Poisson integral** of `ν` is `P[ν](z) = ∫ P(z, x) dν(x)` and its **Schwarz integral** is

`S[ν](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) dν(x)`.

The Schwarz kernel is Tau Ceti's subtracted resolvent kernel `TauCeti.subtractedResolventKernel`,
the Nevanlinna kernel `(1 + x z) / (x - z)` divided by `1 + x ^ 2`, hence bounded by a multiple of
`1 / (1 + x ^ 2)`; its imaginary part is `π P(z, x)`. Integrating a locally dominated holomorphic
kernel, `S[ν]` is holomorphic on `ℂ₊`, and `P[ν] = Re S[ν]` is therefore harmonic there.

## Main declarations

* `TauCeti.upperHalfPlanePoissonKernel`: the Poisson kernel `P(z, x)`, with its explicit formula
  `TauCeti.upperHalfPlanePoissonKernel_eq`.
* `TauCeti.upperHalfPlanePoissonKernel_eq_cauchyPDFReal`: `P(z, ·)` is `cauchyPDFReal` with
  location `Re z` and scale `Im z`, the Cauchy density when `Im z > 0` (for `Im z = 0` both vanish);
  hence `TauCeti.integral_upperHalfPlanePoissonKernel`, `∫ P(z, x) dx = 1` on `ℂ₊`.
* `TauCeti.setOf_lt_upperHalfPlanePoissonKernel`: the superlevel sets of `P(z, ·)` are balls
  centred at `Re z`.
* `TauCeti.upperHalfPlanePoissonKernel_le`: `P(z, x) ≤ C(z) / (1 + x ^ 2)`.
* `TauCeti.subtractedResolventKernel_im_eq_pi_mul_upperHalfPlanePoissonKernel`: the imaginary part
  of the Schwarz kernel is `π P(z, x)`.
* `TauCeti.upperHalfPlanePoissonMeasure`, `TauCeti.IsPoissonFinite`: the Poisson measure
  `dx / (1 + x ^ 2)`, which is `π` times the standard Cauchy distribution, and Poisson-finite
  measures.
* `TauCeti.integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul`: `h` is integrable for the
  Poisson measure exactly when `h(x) / (1 + x ^ 2)` is Lebesgue integrable.
* `TauCeti.upperHalfPlanePoissonIntegral`, `TauCeti.upperHalfPlaneSchwarzIntegral`: the Poisson and
  Schwarz integrals of a measure on `ℝ`, which vanish off the real axis for a measure that is not
  Poisson-finite (`TauCeti.upperHalfPlanePoissonIntegral_of_not_isPoissonFinite`,
  `TauCeti.upperHalfPlaneSchwarzIntegral_of_not_isPoissonFinite`).
* `TauCeti.upperHalfPlanePoissonLIntegral`: the extended Poisson integral in `[0, ∞]`, infinite on
  `ℂ₊` exactly for measures that are not Poisson-finite
  (`TauCeti.upperHalfPlanePoissonLIntegral_eq_top_iff`).
* `TauCeti.isPoissonFinite_iff_integrable_upperHalfPlanePoissonKernel`: `ν` is Poisson-finite
  exactly when `P(z, ·)` is `ν`-integrable.
* `TauCeti.integrable_upperHalfPlanePoissonMeasure_iff`: for a.e. strongly measurable `h`,
  `h ∈ L¹(Π)` for the Poisson measure `Π` exactly when `P[|h| dx](i) < ∞`.
* `TauCeti.differentiableOn_upperHalfPlaneSchwarzIntegral`: `S[ν]` is holomorphic on `ℂ₊`.
* `TauCeti.re_upperHalfPlaneSchwarzIntegral`: `Re S[ν] = P[ν]`.
* `TauCeti.I_mul_upperHalfPlaneSchwarzIntegral`: `i S[ν]` is the integral of the subtracted
  resolvent kernel against `ν / π`.
* `TauCeti.harmonicOnNhd_upperHalfPlanePoissonIntegral`: `P[ν]` is harmonic on `ℂ₊`.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. **200**
  (2024), Section 2.
* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §3.
-/

public section

noncomputable section

open Complex InnerProductSpace MeasureTheory Metric Set Filter

open scoped Real Topology ENNReal ComplexConjugate

namespace TauCeti

/-! ### The Poisson kernel -/

/-- The **Poisson kernel of the upper half-plane**, `P(z, x) = Im z / (π |x - z| ^ 2)` for a pole
`z ∈ ℂ₊` and a boundary point `x ∈ ℝ`. It is the half-space Poisson kernel
`TauCeti.halfSpacePoissonKernel 2` with unit inward normal `i`, pole `z` and boundary point `x`,
read through `Complex.orthonormalBasisOneI`; `TauCeti.upperHalfPlanePoissonKernel_eq` gives the
explicit formula. -/
def upperHalfPlanePoissonKernel (z : ℂ) (x : ℝ) : ℝ :=
  halfSpacePoissonKernel 2 ⟨Complex.orthonormalBasisOneI.repr I, by simp⟩
    (Complex.orthonormalBasisOneI.repr z) (Complex.orthonormalBasisOneI.repr x)

/-- The defining formula of `TauCeti.upperHalfPlanePoissonKernel`. -/
theorem upperHalfPlanePoissonKernel_def (z : ℂ) (x : ℝ) :
    upperHalfPlanePoissonKernel z x =
      halfSpacePoissonKernel 2 ⟨Complex.orthonormalBasisOneI.repr I, by simp⟩
        (Complex.orthonormalBasisOneI.repr z) (Complex.orthonormalBasisOneI.repr x) := by
  rw [upperHalfPlanePoissonKernel]

/-- The explicit formula `P(z, x) = Im z / (π |x - z| ^ 2)` for the Poisson kernel of the upper
half-plane. -/
theorem upperHalfPlanePoissonKernel_eq (z : ℂ) (x : ℝ) :
    upperHalfPlanePoissonKernel z x = z.im / (π * normSq ((x : ℂ) - z)) := by
  have hinner : ⟪(I : ℂ), z⟫_ℝ = z.im := by simp [Complex.inner]
  rw [upperHalfPlanePoissonKernel_def,
    halfSpacePoissonKernel_orthonormalBasisOneI_repr ⟨I, norm_I⟩, hinner, normSq_eq_norm_sq]

/-- The Poisson kernel is measurable in its boundary point. -/
@[fun_prop]
theorem measurable_upperHalfPlanePoissonKernel (z : ℂ) :
    Measurable (upperHalfPlanePoissonKernel z) := by
  simp_rw [funext (upperHalfPlanePoissonKernel_eq z)]
  fun_prop

/-- The Poisson kernel is nonnegative for a pole in the closed upper half-plane. -/
theorem upperHalfPlanePoissonKernel_nonneg {z : ℂ} (hz : 0 ≤ z.im) (x : ℝ) :
    0 ≤ upperHalfPlanePoissonKernel z x := by
  rw [upperHalfPlanePoissonKernel_eq]
  exact div_nonneg hz (mul_nonneg Real.pi_pos.le (normSq_nonneg _))

/-- The Poisson kernel is nonpositive for a pole in the closed lower half-plane. -/
theorem upperHalfPlanePoissonKernel_nonpos {z : ℂ} (hz : z.im ≤ 0) (x : ℝ) :
    upperHalfPlanePoissonKernel z x ≤ 0 := by
  rw [upperHalfPlanePoissonKernel_eq]
  exact div_nonpos_of_nonpos_of_nonneg hz (mul_nonneg Real.pi_pos.le (normSq_nonneg _))

/-- The Poisson kernel is positive for a pole in the open upper half-plane. -/
theorem upperHalfPlanePoissonKernel_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    0 < upperHalfPlanePoissonKernel z x := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub]
  positivity

/-- At the pole `i`, `P(i, x) = 1 / (π (1 + x ^ 2))`. -/
@[simp]
theorem upperHalfPlanePoissonKernel_I (x : ℝ) :
    upperHalfPlanePoissonKernel I x = (π * (1 + x ^ 2))⁻¹ := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub]
  simp only [I_im, I_re, sub_zero, one_pow, one_div]
  ring

/-- For a pole `z` in the closed upper half-plane, `P(z, ·)` is `cauchyPDFReal` with location
`Re z` and scale `Im z`. For `0 < Im z` this is the density of the Cauchy distribution; for
`Im z = 0` both sides vanish. -/
theorem upperHalfPlanePoissonKernel_eq_cauchyPDFReal {z : ℂ} (hz : 0 ≤ z.im) (x : ℝ) :
    upperHalfPlanePoissonKernel z x = ProbabilityTheory.cauchyPDFReal z.re z.im.toNNReal x := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub, ProbabilityTheory.cauchyPDFReal_def,
    Real.coe_toNNReal _ hz, div_eq_mul_inv, mul_inv]
  ring

/-- **The Poisson kernel of the upper half-plane has mass one**: `∫ P(z, x) dx = 1` for every pole
`z ∈ ℂ₊`. -/
theorem integral_upperHalfPlanePoissonKernel {z : ℂ} (hz : 0 < z.im) :
    ∫ x : ℝ, upperHalfPlanePoissonKernel z x = 1 := by
  simp_rw [upperHalfPlanePoissonKernel_eq_cauchyPDFReal hz.le]
  exact ProbabilityTheory.integral_cauchyPDFReal_eq_one _ (Real.toNNReal_pos.2 hz).ne'

/-- The superlevel sets of the Poisson kernel are balls centred at the real part of the pole: for
`0 < t`, `t < P(z, s)` exactly when `|s - Re z| < √(Im z / (π t) - Im z ^ 2)`. For `Im z ≤ 0`
both sides are empty. -/
theorem setOf_lt_upperHalfPlanePoissonKernel (z : ℂ) {t : ℝ} (ht : 0 < t) :
    {s | t < upperHalfPlanePoissonKernel z s} =
      ball z.re (√(z.im / (π * t) - z.im ^ 2)) := by
  rcases le_or_gt z.im 0 with hz | hz
  · have hr : z.im / (π * t) - z.im ^ 2 ≤ 0 := by
      have : z.im / (π * t) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hz (by positivity)
      nlinarith [sq_nonneg z.im]
    rw [Real.sqrt_eq_zero'.2 hr, ball_zero, eq_empty_iff_forall_notMem]
    exact fun s hs => (ht.trans hs).not_ge (upperHalfPlanePoissonKernel_nonpos hz s)
  ext s
  simp only [mem_ofPred_eq, mem_ball, Real.dist_eq, upperHalfPlanePoissonKernel_eq,
    normSq_ofReal_sub]
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs, lt_div_iff₀ (by positivity),
    lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- **The Poisson kernel decays like `1 / (1 + x ^ 2)`**: for a pole in the closed upper
half-plane, `P(z, x) ≤ C(z) / (1 + x ^ 2)` with
`C(z) = 2 (1 + (Re z) ^ 2) max (Im z) (1 / Im z) / π`. -/
theorem upperHalfPlanePoissonKernel_le {z : ℂ} (hz : 0 ≤ z.im) (x : ℝ) :
    upperHalfPlanePoissonKernel z x ≤
      2 * (1 + z.re ^ 2) * max z.im z.im⁻¹ / π / (1 + x ^ 2) := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub]
  set a := z.re
  set b := z.im
  rcases hz.eq_or_lt with hb | hb
  · rw [← hb]
    simp
  set t := (x - a) ^ 2
  have hx : 1 + x ^ 2 ≤ 2 * (1 + a ^ 2) * (1 + t) := by
    nlinarith [sq_nonneg (x - 2 * a), sq_nonneg a, sq_nonneg (a * (x - a)), sq_nonneg (x - a)]
  have hM : b * (1 + t) ≤ max b b⁻¹ * (t + b ^ 2) := by
    have ht : 0 ≤ t := sq_nonneg _
    rcases le_total b 1 with h1 | h1
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      rw [inv_mul_eq_div, le_div_iff₀ hb]
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul h1 h1 hb.le zero_le_one) ht]
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      nlinarith [mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) h1) hb.le]
  have hden : 0 < π * (t + b ^ 2) := by positivity
  rw [div_div, div_le_div_iff₀ hden (by positivity)]
  calc b * (π * (1 + x ^ 2)) ≤ b * (π * (2 * (1 + a ^ 2) * (1 + t))) := by gcongr
    _ = 2 * (1 + a ^ 2) * π * (b * (1 + t)) := by ring
    _ ≤ 2 * (1 + a ^ 2) * π * (max b b⁻¹ * (t + b ^ 2)) := by gcongr
    _ = 2 * (1 + a ^ 2) * max b b⁻¹ * (π * (t + b ^ 2)) := by ring

/-- The imaginary part of the Schwarz kernel `TauCeti.subtractedResolventKernel` is `π P(z, x)`. -/
theorem subtractedResolventKernel_im_eq_pi_mul_upperHalfPlanePoissonKernel (z : ℂ) (x : ℝ) :
    (subtractedResolventKernel z x).im = π * upperHalfPlanePoissonKernel z x := by
  rw [subtractedResolventKernel_im, upperHalfPlanePoissonKernel_eq]
  rcases eq_or_ne (normSq ((x : ℂ) - z)) 0 with h | h
  · simp [h]
  · field_simp

/-! ### Poisson-finite measures -/

/-- The **Poisson measure** `Π = dx / (1 + x ^ 2)` on the real line, the boundary weight of the
upper half-plane Poisson kernel. Defined as `π` times the standard Cauchy distribution; it has
density `1 / (1 + x ^ 2)` (`TauCeti.upperHalfPlanePoissonMeasure_eq_withDensity`). -/
def upperHalfPlanePoissonMeasure : Measure ℝ :=
  ENNReal.ofReal π • ProbabilityTheory.cauchyMeasure 0 1

/-- The defining formula of `TauCeti.upperHalfPlanePoissonMeasure`. -/
theorem upperHalfPlanePoissonMeasure_def :
    upperHalfPlanePoissonMeasure = ENNReal.ofReal π • ProbabilityTheory.cauchyMeasure 0 1 := by
  rw [upperHalfPlanePoissonMeasure]

/-- The Poisson measure has density `1 / (1 + x ^ 2)` with respect to Lebesgue measure. -/
theorem upperHalfPlanePoissonMeasure_eq_withDensity :
    upperHalfPlanePoissonMeasure = volume.withDensity fun x ↦ ENNReal.ofReal (1 + x ^ 2)⁻¹ := by
  rw [upperHalfPlanePoissonMeasure_def,
    ProbabilityTheory.cauchyMeasure_of_scale_ne_zero _ one_ne_zero,
    ← withDensity_smul _ (ProbabilityTheory.measurable_cauchyPDF _ _)]
  congr 1
  funext x
  rw [Pi.smul_apply, smul_eq_mul, ProbabilityTheory.cauchyPDF_def,
    ← ENNReal.ofReal_mul Real.pi_pos.le, ProbabilityTheory.cauchyPDFReal_def]
  congr 1
  field_simp
  simp [add_comm]

/-- The Poisson measure has total mass `π`. -/
@[simp]
theorem upperHalfPlanePoissonMeasure_univ :
    upperHalfPlanePoissonMeasure univ = ENNReal.ofReal π := by
  simp [upperHalfPlanePoissonMeasure_def]

/-- The Poisson measure is finite. -/
instance instIsFiniteMeasureUpperHalfPlanePoissonMeasure :
    IsFiniteMeasure upperHalfPlanePoissonMeasure :=
  ⟨by simp [upperHalfPlanePoissonMeasure_univ]⟩

/-- A function is integrable for the Poisson measure `dx / (1 + x ^ 2)` exactly when
`h(x) / (1 + x ^ 2)` is Lebesgue integrable. -/
theorem integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ → E} :
    Integrable h upperHalfPlanePoissonMeasure ↔ Integrable (fun x ↦ (1 + x ^ 2)⁻¹ • h x) := by
  rw [upperHalfPlanePoissonMeasure_eq_withDensity,
    TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff (by fun_prop)
      (.of_forall fun _ ↦ by positivity)]

/-- A function integrable for the Poisson measure is Lebesgue a.e. strongly measurable, since the
Poisson measure has an everywhere positive density. -/
theorem aestronglyMeasurable_of_integrable_upperHalfPlanePoissonMeasure {E : Type*}
    [NormedAddCommGroup E] {h : ℝ → E} (hh : Integrable h upperHalfPlanePoissonMeasure) :
    AEStronglyMeasurable h :=
  hh.aestronglyMeasurable.mono_ac (upperHalfPlanePoissonMeasure_eq_withDensity ▸
    withDensity_absolutelyContinuous' (by fun_prop)
      (.of_forall fun _ ↦ (ENNReal.ofReal_pos.2 (by positivity)).ne'))

/-- On `[-R, R]` the Lebesgue integral of `f` is at most `1 + R ^ 2` times its integral against
the Poisson measure `dx / (1 + x ^ 2)`. -/
theorem setLIntegral_Icc_le_mul_lintegral_upperHalfPlanePoissonMeasure (f : ℝ → ℝ≥0∞) (R : ℝ) :
    ∫⁻ s in Icc (-R) R, f s ≤
      ENNReal.ofReal (1 + R ^ 2) * ∫⁻ s, f s ∂upperHalfPlanePoissonMeasure := by
  rw [upperHalfPlanePoissonMeasure_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (by fun_prop)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (setLIntegral_le_lintegral _ _).trans' (setLIntegral_mono' measurableSet_Icc
    fun s hs ↦ ?_)
  rw [Pi.mul_apply, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hs2 : s ^ 2 ≤ R ^ 2 := sq_le_sq' hs.1 hs.2
  have h1 : 1 ≤ (1 + R ^ 2) * (1 + s ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, one_le_div (by positivity)]
    linarith
  calc f s = ENNReal.ofReal 1 * f s := by simp
    _ ≤ _ := by gcongr

/-- A measure `ν` on `ℝ` is **Poisson-finite** when `∫ dν / (1 + x ^ 2) < ∞`, that is when
`x ↦ 1 / (1 + x ^ 2)` is `ν`-integrable. -/
def IsPoissonFinite (ν : Measure ℝ) : Prop :=
  Integrable (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) ν

/-- The defining property of `TauCeti.IsPoissonFinite`. -/
theorem isPoissonFinite_iff (ν : Measure ℝ) :
    IsPoissonFinite ν ↔ Integrable (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) ν := by
  rw [IsPoissonFinite]

/-- `ν` is Poisson-finite exactly when `∫⁻ dν / (1 + x ^ 2) < ∞`. -/
theorem isPoissonFinite_iff_lintegral_lt_top (ν : Measure ℝ) :
    IsPoissonFinite ν ↔ ∫⁻ x, ENNReal.ofReal (1 + x ^ 2)⁻¹ ∂ν < ∞ := by
  rw [isPoissonFinite_iff, Integrable, ← hasFiniteIntegral_iff_ofReal
    (.of_forall fun x ↦ by positivity)]
  exact and_iff_right (by fun_prop)

/-- Lebesgue measure is Poisson-finite. -/
theorem isPoissonFinite_volume : IsPoissonFinite volume :=
  (isPoissonFinite_iff _).2 integrable_inv_one_add_sq

/-- Every finite measure is Poisson-finite. -/
theorem isPoissonFinite_of_isFiniteMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsPoissonFinite ν :=
  (isPoissonFinite_iff_lintegral_lt_top ν).2 (lintegral_inv_one_add_sq_lt_top ν)

/-- A finite multiple of a Poisson-finite measure is Poisson-finite. -/
theorem IsPoissonFinite.smul_measure {ν : Measure ℝ} (hν : IsPoissonFinite ν) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : IsPoissonFinite (c • ν) :=
  (isPoissonFinite_iff _).2 (((isPoissonFinite_iff ν).1 hν).smul_measure hc)

/-- Reflecting the pole in the real axis changes the sign of the Poisson kernel. -/
@[simp]
theorem upperHalfPlanePoissonKernel_conj (z : ℂ) (x : ℝ) :
    upperHalfPlanePoissonKernel (conj z) x = -upperHalfPlanePoissonKernel z x := by
  rw [upperHalfPlanePoissonKernel_eq, upperHalfPlanePoissonKernel_eq, conj_im, neg_div,
    ← normSq_conj, map_sub, conj_ofReal, conj_conj]

/-- For a Poisson-finite measure, the Poisson kernel is integrable in the boundary point. -/
theorem IsPoissonFinite.integrable_upperHalfPlanePoissonKernel {ν : Measure ℝ}
    (hν : IsPoissonFinite ν) (z : ℂ) : Integrable (upperHalfPlanePoissonKernel z) ν := by
  have key : ∀ w : ℂ, 0 ≤ w.im → Integrable (upperHalfPlanePoissonKernel w) ν := fun w hw ↦ by
    refine (((isPoissonFinite_iff ν).1 hν).const_mul
      (2 * (1 + w.re ^ 2) * max w.im w.im⁻¹ / π)).mono' (by fun_prop) (.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (upperHalfPlanePoissonKernel_nonneg hw x), ← div_eq_mul_inv]
    exact upperHalfPlanePoissonKernel_le hw x
  rcases le_total 0 z.im with hz | hz
  · exact key z hz
  · have h : upperHalfPlanePoissonKernel z = fun x ↦ -upperHalfPlanePoissonKernel (conj z) x :=
      funext fun x ↦ by simp
    rw [h]
    exact (key (conj z) (by simpa using hz)).neg

/-- Off the real axis, a measure is Poisson-finite exactly when the Poisson kernel is integrable
against it. -/
theorem isPoissonFinite_iff_integrable_upperHalfPlanePoissonKernel {ν : Measure ℝ} {z : ℂ}
    (hz : z.im ≠ 0) : IsPoissonFinite ν ↔ Integrable (upperHalfPlanePoissonKernel z) ν := by
  refine ⟨fun hν ↦ hν.integrable_upperHalfPlanePoissonKernel z, fun h ↦ ?_⟩
  refine (isPoissonFinite_iff ν).2
    ((h.norm.const_mul (2 * (1 + ‖z‖ ^ 2) / |z.im| * π)).mono' (by fun_prop)
      (.of_forall fun x ↦ ?_))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, mul_assoc (2 * (1 + ‖z‖ ^ 2) / |z.im|),
    ← abs_of_pos Real.pi_pos, ← abs_mul,
    ← subtractedResolventKernel_im_eq_pi_mul_upperHalfPlanePoissonKernel]
  exact inv_one_add_sq_le_mul_abs_im_subtractedResolventKernel hz x

/-! ### The Poisson integral -/

/-- The **Poisson integral** `P[ν](z) = ∫ P(z, x) dν(x)` of a measure `ν` on `ℝ`, as a real
number. It is meaningful for a Poisson-finite measure `ν`; otherwise the Bochner integral takes the
junk value `0` (`TauCeti.upperHalfPlanePoissonIntegral_of_not_isPoissonFinite`), and the divergent
case `P[ν] = ∞` is expressed by the extended integral
`TauCeti.upperHalfPlanePoissonLIntegral` (`TauCeti.upperHalfPlanePoissonLIntegral_eq_top_iff`). -/
def upperHalfPlanePoissonIntegral (ν : Measure ℝ) (z : ℂ) : ℝ :=
  ∫ x, upperHalfPlanePoissonKernel z x ∂ν

/-- The defining formula of `TauCeti.upperHalfPlanePoissonIntegral`. -/
theorem upperHalfPlanePoissonIntegral_def (ν : Measure ℝ) (z : ℂ) :
    upperHalfPlanePoissonIntegral ν z = ∫ x, upperHalfPlanePoissonKernel z x ∂ν := by
  rw [upperHalfPlanePoissonIntegral]

/-- For a measure that is not Poisson-finite, the Poisson integral takes the junk value `0`: off the
real axis the Poisson kernel is not integrable, and on it the kernel vanishes. -/
theorem upperHalfPlanePoissonIntegral_of_not_isPoissonFinite {ν : Measure ℝ}
    (hν : ¬IsPoissonFinite ν) (z : ℂ) : upperHalfPlanePoissonIntegral ν z = 0 := by
  rcases eq_or_ne z.im 0 with hz | hz
  · simp [upperHalfPlanePoissonIntegral_def, upperHalfPlanePoissonKernel_eq, hz]
  · rw [upperHalfPlanePoissonIntegral_def,
      integral_undef ((isPoissonFinite_iff_integrable_upperHalfPlanePoissonKernel hz).not.1 hν)]

/-- The Poisson integral of a measure is nonnegative on the closed upper half-plane. -/
theorem upperHalfPlanePoissonIntegral_nonneg (ν : Measure ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ upperHalfPlanePoissonIntegral ν z :=
  integral_nonneg (upperHalfPlanePoissonKernel_nonneg hz)

/-- The Poisson integral scales with the measure: `P[c • ν] = c.toReal P[ν]`. -/
@[simp]
theorem upperHalfPlanePoissonIntegral_smul_measure (ν : Measure ℝ) (c : ℝ≥0∞) (z : ℂ) :
    upperHalfPlanePoissonIntegral (c • ν) z = c.toReal * upperHalfPlanePoissonIntegral ν z := by
  rw [upperHalfPlanePoissonIntegral_def, integral_smul_measure, smul_eq_mul,
    ← upperHalfPlanePoissonIntegral_def]

/-- The Poisson integral of Lebesgue measure is `1` on the upper half-plane. -/
@[simp]
theorem upperHalfPlanePoissonIntegral_volume {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePoissonIntegral volume z = 1 :=
  integral_upperHalfPlanePoissonKernel hz

/-- The Poisson integral of the Dirac mass at `a` is the Poisson kernel `P(z, a)`. -/
@[simp]
theorem upperHalfPlanePoissonIntegral_dirac (a : ℝ) (z : ℂ) :
    upperHalfPlanePoissonIntegral (Measure.dirac a) z = upperHalfPlanePoissonKernel z a := by
  rw [upperHalfPlanePoissonIntegral_def, integral_dirac]

/-- The **extended Poisson integral** `P[ν](z) = ∫⁻ P(z, x) dν(x) ∈ [0, ∞]` of a measure `ν` on
`ℝ`. On the upper half-plane it is finite exactly for Poisson-finite `ν`
(`TauCeti.upperHalfPlanePoissonLIntegral_eq_top_iff`), where it agrees with the real-valued
`TauCeti.upperHalfPlanePoissonIntegral` (`TauCeti.ofReal_upperHalfPlanePoissonIntegral`). -/
def upperHalfPlanePoissonLIntegral (ν : Measure ℝ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (upperHalfPlanePoissonKernel z x) ∂ν

/-- The defining formula of `TauCeti.upperHalfPlanePoissonLIntegral`. -/
theorem upperHalfPlanePoissonLIntegral_def (ν : Measure ℝ) (z : ℂ) :
    upperHalfPlanePoissonLIntegral ν z =
      ∫⁻ x, ENNReal.ofReal (upperHalfPlanePoissonKernel z x) ∂ν := by
  rw [upperHalfPlanePoissonLIntegral]

/-- On the upper half-plane, the extended Poisson integral of `ν` is infinite exactly when `ν` is
not Poisson-finite. -/
theorem upperHalfPlanePoissonLIntegral_eq_top_iff {ν : Measure ℝ} {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePoissonLIntegral ν z = ∞ ↔ ¬IsPoissonFinite ν := by
  rw [isPoissonFinite_iff_integrable_upperHalfPlanePoissonKernel hz.ne', Integrable,
    hasFiniteIntegral_iff_ofReal (.of_forall (upperHalfPlanePoissonKernel_nonneg hz.le)),
    upperHalfPlanePoissonLIntegral_def]
  simp [(measurable_upperHalfPlanePoissonKernel z).aestronglyMeasurable, lt_top_iff_ne_top]

/-- For a Poisson-finite measure, the real-valued Poisson integral is the extended one. In the
closed lower half-plane both sides are `0`, since the kernel is nonpositive there and
`ENNReal.ofReal` sends nonpositive reals to `0`. -/
theorem ofReal_upperHalfPlanePoissonIntegral {ν : Measure ℝ} (hν : IsPoissonFinite ν) (z : ℂ) :
    ENNReal.ofReal (upperHalfPlanePoissonIntegral ν z) = upperHalfPlanePoissonLIntegral ν z := by
  rw [upperHalfPlanePoissonIntegral_def, upperHalfPlanePoissonLIntegral_def]
  rcases le_total 0 z.im with hz | hz
  · rw [ofReal_integral_eq_lintegral_ofReal (hν.integrable_upperHalfPlanePoissonKernel z)
      (.of_forall (upperHalfPlanePoissonKernel_nonneg hz))]
  · have hP := upperHalfPlanePoissonKernel_nonpos hz
    rw [ENNReal.ofReal_of_nonpos (integral_nonpos hP)]
    simp [ENNReal.ofReal_of_nonpos, hP]

/-- **Integrability against the Poisson measure through the Poisson integral at `i`.** An almost
everywhere strongly measurable `h : ℝ → E` lies in `L¹(Π)`, for the Poisson measure
`Π = dx / (1 + x ^ 2)`, exactly when the extended Poisson integral of `|h| dx` is finite at `i`,
as `P(i, x) = 1 / (π (1 + x ^ 2))`. -/
theorem integrable_upperHalfPlanePoissonMeasure_iff {E : Type*} [NormedAddCommGroup E]
    {h : ℝ → E} (hh : AEStronglyMeasurable h volume) :
    Integrable h upperHalfPlanePoissonMeasure ↔
      upperHalfPlanePoissonLIntegral (volume.withDensity fun x ↦ ‖h x‖ₑ) I < ∞ := by
  have hd : Measurable fun x : ℝ ↦ ENNReal.ofReal (1 + x ^ 2)⁻¹ := by fun_prop
  have hPi : upperHalfPlanePoissonMeasure ≪ volume := by
    rw [upperHalfPlanePoissonMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hP : upperHalfPlanePoissonLIntegral (volume.withDensity fun x ↦ ‖h x‖ₑ) I =
      ENNReal.ofReal π⁻¹ * ∫⁻ x, ‖h x‖ₑ ∂upperHalfPlanePoissonMeasure := by
    rw [upperHalfPlanePoissonLIntegral_def, upperHalfPlanePoissonMeasure_eq_withDensity,
      lintegral_withDensity_eq_lintegral_mul₀ hh.eNorm (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable hh.eNorm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x ↦ ?_
    simp only [Pi.mul_apply, upperHalfPlanePoissonKernel_I, mul_inv]
    rw [ENNReal.ofReal_mul (by positivity)]
    ring
  rw [hP, Integrable, and_iff_right (hh.mono_ac hPi), HasFiniteIntegral,
    ENNReal.mul_lt_top_iff]
  simp only [ENNReal.ofReal_lt_top, true_and, ENNReal.ofReal_eq_zero, not_le.mpr
    (inv_pos.mpr Real.pi_pos), false_or, iff_self_or]
  exact fun h0 ↦ h0 ▸ ENNReal.zero_lt_top

/-- The extended Poisson integral of Lebesgue measure is `1` on the upper half-plane. -/
@[simp]
theorem upperHalfPlanePoissonLIntegral_volume {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePoissonLIntegral volume z = 1 := by
  rw [← ofReal_upperHalfPlanePoissonIntegral isPoissonFinite_volume,
    upperHalfPlanePoissonIntegral_volume hz, ENNReal.ofReal_one]

/-- The norm of the Poisson integral is at most the extended Poisson integral in the closed upper
half-plane: they agree for a Poisson-finite measure, and otherwise the Poisson integral is `0`. -/
theorem enorm_upperHalfPlanePoissonIntegral_le (ν : Measure ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖upperHalfPlanePoissonIntegral ν z‖ₑ ≤ upperHalfPlanePoissonLIntegral ν z := by
  by_cases hν : IsPoissonFinite ν
  · rw [Real.eNorm_of_nonneg (upperHalfPlanePoissonIntegral_nonneg ν hz),
      ofReal_upperHalfPlanePoissonIntegral hν]
  · simp [upperHalfPlanePoissonIntegral_of_not_isPoissonFinite hν]

/-! ### The Schwarz integral -/

/-- The **Schwarz integral** `S[ν](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) dν(x)` of a
measure `ν` on `ℝ`, the integral of the subtracted resolvent kernel
`TauCeti.subtractedResolventKernel` divided by `π i`. -/
def upperHalfPlaneSchwarzIntegral (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ((π : ℂ) * I)⁻¹ * ∫ x, subtractedResolventKernel z x ∂ν

/-- The defining formula of `TauCeti.upperHalfPlaneSchwarzIntegral`. -/
theorem upperHalfPlaneSchwarzIntegral_def (ν : Measure ℝ) (z : ℂ) :
    upperHalfPlaneSchwarzIntegral ν z =
      ((π : ℂ) * I)⁻¹ * ∫ x, subtractedResolventKernel z x ∂ν := by
  rw [upperHalfPlaneSchwarzIntegral]

/-- `i S[ν](z) = (1 / π) ∫ (1 / (x - z) - x / (1 + x ^ 2)) dν(x)` is the integral of the
subtracted resolvent kernel against the measure `ν / π`, the form of a Herglotz representation. -/
theorem I_mul_upperHalfPlaneSchwarzIntegral (ν : Measure ℝ) (z : ℂ) :
    I * upperHalfPlaneSchwarzIntegral ν z =
      ∫ x, subtractedResolventKernel z x ∂(ENNReal.ofReal π⁻¹ • ν) := by
  rw [upperHalfPlaneSchwarzIntegral_def, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul, ← mul_assoc]
  congr 1
  push_cast
  field_simp

/-- Off the real axis, the Schwarz integral of a measure that is not Poisson-finite takes the junk
value `0`, since the subtracted resolvent kernel is not integrable there. -/
theorem upperHalfPlaneSchwarzIntegral_of_not_isPoissonFinite {ν : Measure ℝ}
    (hν : ¬IsPoissonFinite ν) {z : ℂ} (hz : z.im ≠ 0) : upperHalfPlaneSchwarzIntegral ν z = 0 := by
  rw [upperHalfPlaneSchwarzIntegral_def, integral_subtractedResolventKernel_eq_zero
    (mt (isPoissonFinite_iff_lintegral_lt_top ν).2 hν) hz, mul_zero]

/-- At `z = i` the Schwarz integral is real: `S[ν](i) = (1 / π) ∫ dν / (1 + x ^ 2)`. -/
@[simp]
theorem upperHalfPlaneSchwarzIntegral_I (ν : Measure ℝ) :
    upperHalfPlaneSchwarzIntegral ν I = ((π⁻¹ * ∫ x, (1 + x ^ 2)⁻¹ ∂ν : ℝ) : ℂ) := by
  simp_rw [upperHalfPlaneSchwarzIntegral_def, subtractedResolventKernel_I, integral_const_mul,
    integral_complex_ofReal]
  push_cast
  field_simp

/-- **The Poisson integral is the real part of the Schwarz integral**: `Re S[ν] = P[ν]`. For a
measure that is not Poisson-finite both sides take the junk value `0`. -/
theorem re_upperHalfPlaneSchwarzIntegral (ν : Measure ℝ) (z : ℂ) :
    (upperHalfPlaneSchwarzIntegral ν z).re = upperHalfPlanePoissonIntegral ν z := by
  rw [upperHalfPlaneSchwarzIntegral_def]
  by_cases hK : Integrable (subtractedResolventKernel z) ν
  · have him := integral_im (𝕜 := ℂ) hK
    simp only [RCLike.im_to_complex,
      subtractedResolventKernel_im_eq_pi_mul_upperHalfPlanePoissonKernel, integral_const_mul] at him
    have hre (w : ℂ) : (((π : ℂ) * I)⁻¹ * w).re = π⁻¹ * w.im := by
      simp [← ofReal_inv]
    rw [hre, ← him, upperHalfPlanePoissonIntegral_def]
    field_simp
  · rw [integral_undef hK, mul_zero, zero_re]
    rcases eq_or_ne z.im 0 with hz | hz
    · simp [upperHalfPlanePoissonIntegral_def, upperHalfPlanePoissonKernel_eq, hz]
    · refine (upperHalfPlanePoissonIntegral_of_not_isPoissonFinite (fun hν ↦ hK ?_) z).symm
      exact integrable_subtractedResolventKernel ((isPoissonFinite_iff_lintegral_lt_top ν).1 hν) hz

/-- The imaginary part of the integrated Schwarz kernel `TauCeti.subtractedResolventKernel` is `π`
times the Poisson integral; this is `TauCeti.re_upperHalfPlaneSchwarzIntegral` before the
normalization by `(π i)⁻¹`. If `ν` is not Poisson-finite, both sides take the junk value `0`. -/
theorem im_integral_subtractedResolventKernel (ν : Measure ℝ) (z : ℂ) :
    (∫ t, subtractedResolventKernel z t ∂ν).im = π * upperHalfPlanePoissonIntegral ν z := by
  rw [← re_upperHalfPlaneSchwarzIntegral, upperHalfPlaneSchwarzIntegral_def]
  simp [← ofReal_inv]

/-- **The Schwarz integral is holomorphic** on the upper half-plane, for every measure `ν`. For a
measure that is not Poisson-finite it is the junk value `0` there
(`TauCeti.upperHalfPlaneSchwarzIntegral_of_not_isPoissonFinite`). -/
theorem differentiableOn_upperHalfPlaneSchwarzIntegral (ν : Measure ℝ) :
    DifferentiableOn ℂ (upperHalfPlaneSchwarzIntegral ν) UpperHalfPlane.upperHalfPlaneSet := by
  by_cases hν : IsPoissonFinite ν
  swap
  · exact (differentiableOn_const (0 : ℂ)).congr fun z hz ↦
      upperHalfPlaneSchwarzIntegral_of_not_isPoissonFinite hν (ne_of_gt hz)
  -- The Cayley factor of `norm_subtractedResolventKernel_le` is continuous on `ℂ₊`, hence locally
  -- bounded, which gives a local integrable bound `(C + 1) / (1 + x ^ 2)`.
  set c : ℂ → ℝ := fun w ↦ (‖w + I‖ + ‖w - I‖) / (‖w + I‖ - ‖w - I‖)
  have hS := analyticOnNhd_integral_of_dominated (μ := ν) (F := subtractedResolventKernel)
    UpperHalfPlane.isOpen_upperHalfPlaneSet
    (fun w _ ↦ (measurable_subtractedResolventKernel w).aestronglyMeasurable) (fun z₀ hz₀ ↦ ?_)
    (.of_forall fun x w hw ↦ ?_)
  · exact fun z hz ↦ ((hS z hz).differentiableAt.const_mul _).differentiableWithinAt
  · have hz₀' : 0 < z₀.im := hz₀
    have hlt : ‖z₀ - I‖ < ‖z₀ + I‖ := norm_sub_I_lt_norm_add_I_iff.2 hz₀'
    have hc : ContinuousAt c z₀ :=
      ((by fun_prop : Continuous fun w : ℂ ↦ ‖w + I‖ + ‖w - I‖).continuousAt).div
        ((by fun_prop : Continuous fun w : ℂ ↦ ‖w + I‖ - ‖w - I‖).continuousAt)
        (sub_ne_zero.2 hlt.ne')
    refine ⟨{w | c w < c z₀ + 1} ∩ UpperHalfPlane.upperHalfPlaneSet,
      inter_mem (hc.eventually (gt_mem_nhds (lt_add_one _)))
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz₀),
      fun x ↦ (c z₀ + 1) * (1 + x ^ 2)⁻¹, ((isPoissonFinite_iff ν).1 hν).const_mul _,
      .of_forall fun x w hw ↦ ?_⟩
    exact (norm_subtractedResolventKernel_le hw.2 x).trans
      (mul_le_mul_of_nonneg_right hw.1.le (by positivity))
  · have hxw : (x : ℂ) - w ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (ne_of_gt hw) x
    simp_rw [subtractedResolventKernel_def]
    exact ((((differentiableAt_const _).sub differentiableAt_id).inv hxw).sub_const
      _).differentiableWithinAt

/-- **The Poisson integral is harmonic** on the upper half-plane, for every measure `ν` (for a
measure that is not Poisson-finite it is the junk value `0` there). -/
theorem harmonicOnNhd_upperHalfPlanePoissonIntegral (ν : Measure ℝ) :
    HarmonicOnNhd (upperHalfPlanePoissonIntegral ν) UpperHalfPlane.upperHalfPlaneSet := by
  intro z hz
  have hS : AnalyticAt ℂ (upperHalfPlaneSchwarzIntegral ν) z :=
    (differentiableOn_upperHalfPlaneSchwarzIntegral ν).analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have h : upperHalfPlanePoissonIntegral ν = fun w ↦ (upperHalfPlaneSchwarzIntegral ν w).re :=
    funext fun w ↦ (re_upperHalfPlaneSchwarzIntegral ν w).symm
  rw [h]
  exact hS.harmonicAt_re

end TauCeti
