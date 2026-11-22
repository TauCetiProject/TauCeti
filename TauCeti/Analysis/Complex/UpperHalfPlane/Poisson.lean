/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Probability.Distributions.Cauchy
public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import TauCeti.Analysis.PDE.GreenFunction.HalfSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Complex.Basic
import TauCeti.Basic.Complex.OfRealSub

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

The Schwarz kernel is the Nevanlinna kernel `(1 + x z) / (x - z)` divided by `1 + x ^ 2`, hence
bounded by a multiple of `1 / (1 + x ^ 2)`; its imaginary part is `π P(z, x)`. Differentiating under
the integral sign, `S[ν]` is holomorphic on `ℂ₊`, and `P[ν] = Re S[ν]` is therefore harmonic there.

## Main declarations

* `TauCeti.upperHalfPlanePoissonKernel`: the Poisson kernel `P(z, x)`, with its explicit formula
  `TauCeti.upperHalfPlanePoissonKernel_eq`.
* `TauCeti.upperHalfPlanePoissonKernel_eq_cauchyPDFReal`: `P(z, ·)` is the Cauchy density with
  location `Re z` and scale `Im z`; hence `TauCeti.integral_upperHalfPlanePoissonKernel`,
  `∫ P(z, x) dx = 1`.
* `TauCeti.upperHalfPlanePoissonKernel_le`: `P(z, x) ≤ C(z) / (1 + x ^ 2)`.
* `TauCeti.poissonMeasure`, `TauCeti.IsPoissonFinite`: the measure `dx / (1 + x ^ 2)` and
  Poisson-finite measures.
* `TauCeti.upperHalfPlanePoissonIntegral`, `TauCeti.upperHalfPlaneSchwarzIntegral`: the Poisson and
  Schwarz integrals of a measure on `ℝ`.
* `TauCeti.upperHalfPlanePoissonLIntegral`: the extended Poisson integral in `[0, ∞]`, infinite on
  `ℂ₊` exactly for measures that are not Poisson-finite
  (`TauCeti.upperHalfPlanePoissonLIntegral_eq_top_iff`).
* `TauCeti.isPoissonFinite_iff_integrable_upperHalfPlanePoissonKernel`: `ν` is Poisson-finite
  exactly when `P(z, ·)` is `ν`-integrable.
* `TauCeti.differentiableOn_upperHalfPlaneSchwarzIntegral`: `S[ν]` is holomorphic on `ℂ₊`.
* `TauCeti.re_upperHalfPlaneSchwarzIntegral`: `Re S[ν] = P[ν]` for Poisson-finite `ν`.
* `TauCeti.harmonicOnNhd_upperHalfPlanePoissonIntegral`: `P[ν]` is harmonic on `ℂ₊` for
  Poisson-finite `ν`.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. **200**
  (2024), Section 2.
* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §3.
-/

public section

noncomputable section

namespace TauCeti

open Complex InnerProductSpace MeasureTheory Metric Set Filter

open scoped Real Topology ENNReal ComplexConjugate

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
  have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = π := by
    simp [Measure.real, Real.pi_pos.le]
  rw [upperHalfPlanePoissonKernel_def, halfSpacePoissonKernel_eq_div,
    LinearIsometryEquiv.inner_map_map, ← map_sub, LinearIsometryEquiv.norm_map, hvol,
    normSq_eq_norm_sq]
  have hinner : ⟪(I : ℂ), z⟫_ℝ = z.im := by simp [Complex.inner]
  rw [hinner]
  push_cast
  rw [mul_assoc (2 : ℝ), mul_div_mul_left _ _ two_ne_zero]

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

/-- For a pole `z` in the closed upper half-plane, `P(z, ·)` is the density of the Cauchy
distribution with location `Re z` and scale `Im z`. -/
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

/-! ### Poisson-finite measures -/

/-- The **Poisson measure** `Π = dx / (1 + x ^ 2)` on the real line. -/
def poissonMeasure : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (1 + x ^ 2)⁻¹

/-- The defining formula of `TauCeti.poissonMeasure`. -/
theorem poissonMeasure_def :
    poissonMeasure = volume.withDensity fun x ↦ ENNReal.ofReal (1 + x ^ 2)⁻¹ := by
  rw [poissonMeasure]

/-- The Poisson measure has total mass `π`. -/
@[simp]
theorem poissonMeasure_univ : poissonMeasure univ = ENNReal.ofReal π := by
  rw [poissonMeasure_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
      (.of_forall fun x ↦ by positivity), integral_univ_inv_one_add_sq]

/-- The Poisson measure is finite. -/
instance instIsFiniteMeasurePoissonMeasure : IsFiniteMeasure poissonMeasure :=
  ⟨by simp [poissonMeasure_univ]⟩

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
  (isPoissonFinite_iff _).2 <| .of_bound (by fun_prop) 1 <| .of_forall fun x ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])

/-- Reflecting the pole in the real axis changes the sign of the Poisson kernel. -/
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
      funext fun x ↦ by simpa using upperHalfPlanePoissonKernel_conj (conj z) x
    rw [h]
    exact (key (conj z) (by simpa using hz)).neg

/-- Off the real axis, a measure is Poisson-finite exactly when the Poisson kernel is integrable
against it. -/
theorem isPoissonFinite_iff_integrable_upperHalfPlanePoissonKernel {ν : Measure ℝ} {z : ℂ}
    (hz : z.im ≠ 0) : IsPoissonFinite ν ↔ Integrable (upperHalfPlanePoissonKernel z) ν := by
  refine ⟨fun hν ↦ hν.integrable_upperHalfPlanePoissonKernel z, fun h ↦ ?_⟩
  have hb : 0 < |z.im| := abs_pos.2 hz
  refine (isPoissonFinite_iff ν).2
    ((h.norm.const_mul ((2 + 2 * z.re ^ 2 + z.im ^ 2) * π / |z.im|)).mono'
      (by fun_prop) (.of_forall fun x ↦ ?_))
  have hN : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, upperHalfPlanePoissonKernel_eq,
    normSq_ofReal_sub, abs_div, abs_of_pos (by positivity : 0 < π * ((x - z.re) ^ 2 + z.im ^ 2))]
  calc (1 + x ^ 2)⁻¹ ≤ (2 + 2 * z.re ^ 2 + z.im ^ 2) / ((x - z.re) ^ 2 + z.im ^ 2) := by
        rw [le_div_iff₀ hN, inv_mul_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (x + z.re), mul_nonneg (sq_nonneg x) (sq_nonneg z.re),
          mul_nonneg (sq_nonneg x) (sq_nonneg z.im)]
    _ = _ := by field_simp [hb.ne']

/-! ### The Poisson integral -/

/-- The **Poisson integral** `P[ν](z) = ∫ P(z, x) dν(x)` of a measure `ν` on `ℝ`, as a real
number. It is meaningful for a Poisson-finite measure `ν`; otherwise the Bochner integral takes the
junk value `0` on `ℂ₊`, and the divergent case `P[ν] = ∞` is expressed by the extended integral
`TauCeti.upperHalfPlanePoissonLIntegral` (`TauCeti.upperHalfPlanePoissonLIntegral_eq_top_iff`). -/
def upperHalfPlanePoissonIntegral (ν : Measure ℝ) (z : ℂ) : ℝ :=
  ∫ x, upperHalfPlanePoissonKernel z x ∂ν

/-- The defining formula of `TauCeti.upperHalfPlanePoissonIntegral`. -/
theorem upperHalfPlanePoissonIntegral_def (ν : Measure ℝ) (z : ℂ) :
    upperHalfPlanePoissonIntegral ν z = ∫ x, upperHalfPlanePoissonKernel z x ∂ν := by
  rw [upperHalfPlanePoissonIntegral]

/-- The Poisson integral of a measure is nonnegative on the closed upper half-plane. -/
theorem upperHalfPlanePoissonIntegral_nonneg (ν : Measure ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ upperHalfPlanePoissonIntegral ν z :=
  integral_nonneg (upperHalfPlanePoissonKernel_nonneg hz)

/-- The Poisson integral of Lebesgue measure is `1` on the upper half-plane. -/
@[simp]
theorem upperHalfPlanePoissonIntegral_volume {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePoissonIntegral volume z = 1 :=
  integral_upperHalfPlanePoissonKernel hz

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

/-- For a Poisson-finite measure and a pole in the closed upper half-plane, the real-valued Poisson
integral is the extended one. -/
theorem ofReal_upperHalfPlanePoissonIntegral {ν : Measure ℝ} (hν : IsPoissonFinite ν) {z : ℂ}
    (hz : 0 ≤ z.im) :
    ENNReal.ofReal (upperHalfPlanePoissonIntegral ν z) = upperHalfPlanePoissonLIntegral ν z := by
  rw [upperHalfPlanePoissonIntegral_def, upperHalfPlanePoissonLIntegral_def,
    ofReal_integral_eq_lintegral_ofReal (hν.integrable_upperHalfPlanePoissonKernel z)
      (.of_forall (upperHalfPlanePoissonKernel_nonneg hz))]

/-! ### The Schwarz integral -/

/-- The **Schwarz kernel** `1 / (x - z) - x / (1 + x ^ 2)` of the upper half-plane. -/
def upperHalfPlaneSchwarzKernel (z : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) - z)⁻¹ - ((x / (1 + x ^ 2) : ℝ) : ℂ)

/-- The defining formula of `TauCeti.upperHalfPlaneSchwarzKernel`. -/
theorem upperHalfPlaneSchwarzKernel_def (z : ℂ) (x : ℝ) :
    upperHalfPlaneSchwarzKernel z x = ((x : ℂ) - z)⁻¹ - ((x / (1 + x ^ 2) : ℝ) : ℂ) := by
  rw [upperHalfPlaneSchwarzKernel]

/-- The Schwarz kernel is measurable in its boundary point. -/
@[fun_prop]
theorem measurable_upperHalfPlaneSchwarzKernel (z : ℂ) :
    Measurable (upperHalfPlaneSchwarzKernel z) := by
  simp_rw [funext (upperHalfPlaneSchwarzKernel_def z)]
  fun_prop

/-- Away from its pole, the Schwarz kernel is the Nevanlinna kernel `(1 + x z) / (x - z)` divided
by `1 + x ^ 2`. -/
theorem upperHalfPlaneSchwarzKernel_eq_nevanlinnaKernel_mul {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    upperHalfPlaneSchwarzKernel z x = nevanlinnaKernel z x * (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) := by
  have h' : (x : ℂ) - z ≠ 0 := sub_ne_zero.2 h
  have h1 : (1 + (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity : (1 + x ^ 2) ≠ 0)
  rw [upperHalfPlaneSchwarzKernel_def, nevanlinnaKernel_def]
  push_cast
  field_simp
  ring

/-- The imaginary part of the Schwarz kernel is `π P(z, x)`. -/
theorem im_upperHalfPlaneSchwarzKernel (z : ℂ) (x : ℝ) :
    (upperHalfPlaneSchwarzKernel z x).im = π * upperHalfPlanePoissonKernel z x := by
  rw [upperHalfPlaneSchwarzKernel_def, upperHalfPlanePoissonKernel_eq, sub_im, ofReal_im,
    sub_zero, inv_im, sub_im, ofReal_im, zero_sub, neg_neg]
  rcases eq_or_ne (normSq ((x : ℂ) - z)) 0 with h | h
  · simp [h]
  · field_simp

/-- At the pole `i`, the Schwarz kernel is `i / (1 + x ^ 2)`. -/
@[simp]
theorem upperHalfPlaneSchwarzKernel_I (x : ℝ) :
    upperHalfPlaneSchwarzKernel I x = (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) * I := by
  have h' : (x : ℂ) - I ≠ 0 := fun h ↦ by simpa using congrArg im h
  have h3 : (x : ℂ) + I ≠ 0 := fun h ↦ by simpa using congrArg im h
  have h1 : (1 + (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity : (1 + x ^ 2) ≠ 0)
  have h2 : (1 + (x : ℂ) ^ 2) = ((x : ℂ) - I) * ((x : ℂ) + I) := by
    ring_nf
    rw [I_sq]
    ring
  rw [upperHalfPlaneSchwarzKernel_def]
  push_cast
  rw [h2] at h1 ⊢
  field_simp
  ring

/-- For a pole `z ∈ ℂ₊`, the Schwarz kernel is bounded by a multiple of `1 / (1 + x ^ 2)`. -/
theorem norm_upperHalfPlaneSchwarzKernel_le {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    ‖upperHalfPlaneSchwarzKernel z x‖ ≤
      (‖z + I‖ + ‖z - I‖) / (‖z + I‖ - ‖z - I‖) * (1 + x ^ 2)⁻¹ := by
  have hxz : (x : ℂ) ≠ z := fun h ↦ by
    have := congrArg im h
    simp only [ofReal_im] at this
    linarith
  rw [upperHalfPlaneSchwarzKernel_eq_nevanlinnaKernel_mul hxz, norm_mul, norm_real,
    Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (norm_nevanlinnaKernel_le hz x) (by positivity)

/-- Reflecting the pole in the real axis conjugates the Schwarz kernel. -/
theorem upperHalfPlaneSchwarzKernel_conj (z : ℂ) (x : ℝ) :
    upperHalfPlaneSchwarzKernel (conj z) x = conj (upperHalfPlaneSchwarzKernel z x) := by
  simp only [upperHalfPlaneSchwarzKernel_def, map_sub, map_inv₀, conj_ofReal]

/-- For a Poisson-finite measure and a pole off the real axis, the Schwarz kernel is integrable in
the boundary point. -/
theorem IsPoissonFinite.integrable_upperHalfPlaneSchwarzKernel {ν : Measure ℝ}
    (hν : IsPoissonFinite ν) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (upperHalfPlaneSchwarzKernel z) ν := by
  rcases hz.lt_or_gt with hz | hz
  · refine (((isPoissonFinite_iff ν).1 hν).const_mul
      ((‖conj z + I‖ + ‖conj z - I‖) / (‖conj z + I‖ - ‖conj z - I‖))).mono' (by fun_prop)
      (.of_forall fun x ↦ ?_)
    have := norm_upperHalfPlaneSchwarzKernel_le (z := conj z) (by simpa using hz) x
    rwa [upperHalfPlaneSchwarzKernel_conj, Complex.norm_conj] at this
  · exact (((isPoissonFinite_iff ν).1 hν).const_mul _).mono' (by fun_prop)
      (.of_forall (norm_upperHalfPlaneSchwarzKernel_le hz))

/-- Off the real axis, a measure is Poisson-finite exactly when the Schwarz kernel is integrable
against it. -/
theorem isPoissonFinite_iff_integrable_upperHalfPlaneSchwarzKernel {ν : Measure ℝ} {z : ℂ}
    (hz : z.im ≠ 0) : IsPoissonFinite ν ↔ Integrable (upperHalfPlaneSchwarzKernel z) ν := by
  refine ⟨fun hν ↦ hν.integrable_upperHalfPlaneSchwarzKernel hz, fun h ↦ ?_⟩
  refine (isPoissonFinite_iff_integrable_upperHalfPlanePoissonKernel hz).2
    ((h.norm.const_mul π⁻¹).mono' (by fun_prop) (.of_forall fun x ↦ ?_))
  have := abs_im_le_norm (upperHalfPlaneSchwarzKernel z x)
  rw [im_upperHalfPlaneSchwarzKernel, abs_mul, abs_of_pos Real.pi_pos] at this
  rw [Real.norm_eq_abs, inv_mul_eq_div, le_div_iff₀ Real.pi_pos]
  linarith

/-- The **Schwarz integral** `S[ν](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) dν(x)` of a
measure `ν` on `ℝ`. -/
def upperHalfPlaneSchwarzIntegral (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ((π : ℂ) * I)⁻¹ * ∫ x, upperHalfPlaneSchwarzKernel z x ∂ν

/-- The defining formula of `TauCeti.upperHalfPlaneSchwarzIntegral`. -/
theorem upperHalfPlaneSchwarzIntegral_def (ν : Measure ℝ) (z : ℂ) :
    upperHalfPlaneSchwarzIntegral ν z =
      ((π : ℂ) * I)⁻¹ * ∫ x, upperHalfPlaneSchwarzKernel z x ∂ν := by
  rw [upperHalfPlaneSchwarzIntegral]

/-- At `z = i` the Schwarz integral is real: `S[ν](i) = (1 / π) ∫ dν / (1 + x ^ 2)`. -/
@[simp]
theorem upperHalfPlaneSchwarzIntegral_I (ν : Measure ℝ) :
    upperHalfPlaneSchwarzIntegral ν I = ((π⁻¹ * ∫ x, (1 + x ^ 2)⁻¹ ∂ν : ℝ) : ℂ) := by
  simp_rw [upperHalfPlaneSchwarzIntegral_def, upperHalfPlaneSchwarzKernel_I, integral_mul_const,
    integral_complex_ofReal]
  push_cast
  field_simp

/-- **The Poisson integral is the real part of the Schwarz integral**: `Re S[ν] = P[ν]` for a
Poisson-finite measure `ν`. -/
theorem re_upperHalfPlaneSchwarzIntegral {ν : Measure ℝ} (hν : IsPoissonFinite ν) (z : ℂ) :
    (upperHalfPlaneSchwarzIntegral ν z).re = upperHalfPlanePoissonIntegral ν z := by
  rw [upperHalfPlaneSchwarzIntegral_def, upperHalfPlanePoissonIntegral_def]
  by_cases hK : Integrable (upperHalfPlaneSchwarzKernel z) ν
  · have him := integral_im (𝕜 := ℂ) hK
    simp only [RCLike.im_to_complex, im_upperHalfPlaneSchwarzKernel, integral_const_mul] at him
    rw [mul_inv, inv_I, ← ofReal_inv, mul_neg, neg_mul, neg_re, mul_assoc, re_ofReal_mul,
      I_mul_re, ← him, mul_neg, neg_neg, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  · have hz : z.im = 0 := by
      by_contra hz
      exact hK (hν.integrable_upperHalfPlaneSchwarzKernel hz)
    rw [integral_undef hK, mul_zero, zero_re]
    simp [upperHalfPlanePoissonKernel_eq, hz]

/-- **The Schwarz integral is holomorphic** on the upper half-plane. For a measure that is not
Poisson-finite it vanishes there. -/
theorem differentiableOn_upperHalfPlaneSchwarzIntegral (ν : Measure ℝ) :
    DifferentiableOn ℂ (upperHalfPlaneSchwarzIntegral ν) UpperHalfPlane.upperHalfPlaneSet := by
  by_cases hν : IsPoissonFinite ν
  swap
  · refine (differentiableOn_const (0 : ℂ)).congr fun z hz ↦ ?_
    rw [upperHalfPlaneSchwarzIntegral_def, integral_undef fun h ↦ hν
      ((isPoissonFinite_iff_integrable_upperHalfPlaneSchwarzKernel (ne_of_gt hz)).2 h), mul_zero]
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  have hball : ball z₀ (z₀.im / 2) ∈ 𝓝 z₀ := ball_mem_nhds _ (by positivity)
  -- Near the pole `z₀`, `‖x - z₀‖ ≤ 2 ‖x - w‖` for every real `x`.
  have norm_sub_le_two_mul {w : ℂ} (hw : w ∈ ball z₀ (z₀.im / 2)) (x : ℝ) :
      ‖(x : ℂ) - z₀‖ ≤ 2 * ‖(x : ℂ) - w‖ := by
    refine norm_ofReal_sub_le_two_mul_norm_ofReal_sub ?_ x
    rw [abs_of_pos hz₀']
    exact (mem_ball_iff_norm.1 hw).le
  have hne : ∀ w ∈ ball z₀ (z₀.im / 2), ∀ x : ℝ, (x : ℂ) - w ≠ 0 := fun w hw x h ↦ by
    have := norm_sub_le_two_mul hw x
    rw [h, norm_zero, mul_zero] at this
    have him : z₀.im ≤ ‖(x : ℂ) - z₀‖ :=
      (le_abs_self _).trans (by simpa using abs_im_le_norm ((x : ℂ) - z₀))
    linarith
  have hbound_int : Integrable (fun x : ℝ ↦ 4 * π / z₀.im * upperHalfPlanePoissonKernel z₀ x) ν :=
    (hν.integrable_upperHalfPlanePoissonKernel z₀).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := upperHalfPlaneSchwarzKernel) (F' := fun w x ↦ (((x : ℂ) - w) ^ 2)⁻¹) hball
    (.of_forall fun w ↦ (measurable_upperHalfPlaneSchwarzKernel w).aestronglyMeasurable)
    (hν.integrable_upperHalfPlaneSchwarzKernel hz₀'.ne') (by fun_prop)
    (.of_forall fun x w hw ↦ ?_) hbound_int (.of_forall fun x w hw ↦ ?_)
  · exact ((key.2.const_mul _).differentiableAt.differentiableWithinAt :)
  · have h2 := norm_sub_le_two_mul hw x
    have hpos : 0 < ‖(x : ℂ) - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h ↦ by
      have := congrArg im h
      simp only [ofReal_im] at this
      linarith)
    rw [upperHalfPlanePoissonKernel_eq, normSq_eq_norm_sq, norm_inv, norm_pow]
    have hpos' : 0 < ‖(x : ℂ) - w‖ := by linarith
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    field_simp
    nlinarith [mul_le_mul h2 h2 hpos.le (by positivity)]
  · have hxw := hne w hw x
    have := (((hasDerivAt_id w).const_sub (x : ℂ)).inv hxw).sub_const
      (((x / (1 + x ^ 2) : ℝ) : ℂ))
    convert this using 1
    · funext v
      simp [upperHalfPlaneSchwarzKernel_def]
    · simp [div_eq_mul_inv]

/-- **The Poisson integral is harmonic** on the upper half-plane, for a Poisson-finite measure
`ν`. -/
theorem harmonicOnNhd_upperHalfPlanePoissonIntegral {ν : Measure ℝ} (hν : IsPoissonFinite ν) :
    HarmonicOnNhd (upperHalfPlanePoissonIntegral ν) UpperHalfPlane.upperHalfPlaneSet := by
  intro z hz
  have hopen : IsOpen UpperHalfPlane.upperHalfPlaneSet := isOpen_lt continuous_const continuous_im
  have hS : AnalyticAt ℂ (upperHalfPlaneSchwarzIntegral ν) z :=
    (differentiableOn_upperHalfPlaneSchwarzIntegral ν).analyticAt (hopen.mem_nhds hz)
  have h : upperHalfPlanePoissonIntegral ν = fun w ↦ (upperHalfPlaneSchwarzIntegral ν w).re :=
    funext fun w ↦ (re_upperHalfPlaneSchwarzIntegral hν w).symm
  rw [h]
  exact hS.harmonicAt_re

end TauCeti
