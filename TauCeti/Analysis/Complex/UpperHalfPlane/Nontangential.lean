/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson
public import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.Basic.Complex.OfRealSub

/-!
# Nontangential cones and the maximal bound for Poisson integrals

For `x ∈ ℝ`, an aperture `α` and a height `0 < h ≤ ∞`, the *cone*
`Γ^α_h(x) = {z ∈ ℂ₊ : |Re z - x| < α Im z, Im z < h}` is
`TauCeti.nontangentialCone α h x`; the cone `Γ_h(x)` of aperture one is `nontangentialCone 1 h x`.
The *nontangential maximal function* of `u : ℂ → E` is `M^α_h u(x) = sup_{z ∈ Γ^α_h(x)} ‖u z‖`,
with values in `[0, ∞]` (`TauCeti.nontangentialMaximalFunction`).

The Poisson kernel `P(z, s) = Im z / (π |s - z| ^ 2)` is compared along a cone with the kernel at
the vertical pole of the same height: for `z = x' + iy ∈ Γ^α_∞(x)`,
`P(x' + iy, s) ≤ max 2 (1 + 2 α ^ 2) · P(x + iy, s)`, which is `3 P(x + iy, s)` for `α = 1`,
since `(s - x) ^ 2 ≤ 2 (s - x') ^ 2 + 2 α ^ 2 y ^ 2`. The kernel `P(x + iy, ·)` is radially
decreasing about `x` with mass one, so its superlevel sets are balls centred at `x` and the layer
cake formula bounds its integral against `|g|` by the Hardy–Littlewood maximal function
`TauCeti.maximalFunction volume g x`. Together:
`M^α_∞ P[|g| dx](x) ≤ max 2 (1 + 2 α ^ 2) · M g(x)`, in particular `M_∞ P[|g| dx] ≤ 3 M g`.

## Main definitions

* `TauCeti.nontangentialCone`: the cone `Γ^α_h(x)`.
* `TauCeti.nontangentialMaximalFunction`: the nontangential maximal function `M^α_h u`.

## Main results

* `TauCeti.upperHalfPlanePoissonKernel_le_mul_of_mem_nontangentialCone`: the cone comparison of
  Poisson kernels.
* `TauCeti.upperHalfPlanePoissonLIntegral_withDensity_le_maximalFunction`: the Poisson integral of
  `|g| dx` at the vertical pole over `x` is at most `M g(x)`.
* `TauCeti.nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le` and
  `TauCeti.nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le`: the maximal bound
  `M^α_h P[|g| dx] ≤ max 2 (1 + 2 α ^ 2) · M g`.
-/

public section

noncomputable section

namespace TauCeti

open Complex MeasureTheory Metric Set

open scoped Real ENNReal

/-- The **nontangential cone** `Γ^α_h(x) = {z : 0 < Im z, |Re z - x| < α Im z, Im z < h}` with
vertex `x ∈ ℝ`, aperture `α` and height `h ∈ [0, ∞]`. -/
def nontangentialCone (α : ℝ) (h : ℝ≥0∞) (x : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ |z.re - x| < α * z.im ∧ ENNReal.ofReal z.im < h}

theorem mem_nontangentialCone {α : ℝ} {h : ℝ≥0∞} {x : ℝ} {z : ℂ} :
    z ∈ nontangentialCone α h x ↔
      0 < z.im ∧ |z.re - x| < α * z.im ∧ ENNReal.ofReal z.im < h :=
  Iff.rfl

/-- Cones grow with the aperture and the height. -/
theorem nontangentialCone_mono {α β : ℝ} {h k : ℝ≥0∞} (hαβ : α ≤ β) (hhk : h ≤ k) (x : ℝ) :
    nontangentialCone α h x ⊆ nontangentialCone β k x := fun _ hz =>
  ⟨hz.1, hz.2.1.trans_le (mul_le_mul_of_nonneg_right hαβ hz.1.le), hz.2.2.trans_le hhk⟩

/-- The **nontangential maximal function** `M^α_h u(x) = sup_{z ∈ Γ^α_h(x)} ‖u z‖ₑ` of a function
on `ℂ`, with values in `[0, ∞]`. -/
def nontangentialMaximalFunction {E : Type*} [ENorm E] (α : ℝ) (h : ℝ≥0∞) (u : ℂ → E)
    (x : ℝ) : ℝ≥0∞ :=
  ⨆ z ∈ nontangentialCone α h x, ‖u z‖ₑ

theorem nontangentialMaximalFunction_def {E : Type*} [ENorm E] (α : ℝ) (h : ℝ≥0∞) (u : ℂ → E)
    (x : ℝ) : nontangentialMaximalFunction α h u x = ⨆ z ∈ nontangentialCone α h x, ‖u z‖ₑ :=
  (rfl)

/-- The nontangential maximal function grows with the aperture and the height. -/
theorem nontangentialMaximalFunction_mono {E : Type*} [ENorm E] {α β : ℝ} {h k : ℝ≥0∞}
    (hαβ : α ≤ β) (hhk : h ≤ k) (u : ℂ → E) (x : ℝ) :
    nontangentialMaximalFunction α h u x ≤ nontangentialMaximalFunction β k u x :=
  biSup_mono fun _ hz => nontangentialCone_mono hαβ hhk x hz

/-- **The cone comparison.** For `z = x' + iy` in the cone `Γ^α_∞(x)`, the Poisson kernel with
pole `z` is at most `max 2 (1 + 2 α ^ 2)` times the Poisson kernel with pole `x + iy`: indeed
`(s - x) ^ 2 + y ^ 2 ≤ 2 (s - x') ^ 2 + (1 + 2 α ^ 2) y ^ 2`. For `α = 1` the constant is `3`. -/
theorem upperHalfPlanePoissonKernel_le_mul_of_mem_nontangentialCone {α : ℝ} {h : ℝ≥0∞} {x : ℝ}
    {z : ℂ} (hz : z ∈ nontangentialCone α h x) (s : ℝ) :
    upperHalfPlanePoissonKernel z s ≤
      max 2 (1 + 2 * α ^ 2) * upperHalfPlanePoissonKernel (x + z.im * I) s := by
  obtain ⟨hy, hcone, -⟩ := hz
  rw [upperHalfPlanePoissonKernel_eq, upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub,
    normSq_ofReal_sub]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add, add_re, mul_re, sub_zero]
  set y := z.im
  set a := z.re
  have hax : (a - x) ^ 2 ≤ α ^ 2 * y ^ 2 := by
    rw [← mul_pow]
    exact sq_le_sq' (by linarith [neg_abs_le (a - x)]) (by linarith [le_abs_self (a - x)])
  have hC : (s - x) ^ 2 + y ^ 2 ≤ max 2 (1 + 2 * α ^ 2) * ((s - a) ^ 2 + y ^ 2) := by
    have h2 := le_max_left 2 (1 + 2 * α ^ 2)
    have h3 := le_max_right 2 (1 + 2 * α ^ 2)
    nlinarith [sq_nonneg (s - a + (a - x)), sq_nonneg (s - a - (a - x)), sq_nonneg (s - a),
      sq_nonneg y]
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  calc y * (π * ((s - x) ^ 2 + y ^ 2))
      ≤ y * (π * (max 2 (1 + 2 * α ^ 2) * ((s - a) ^ 2 + y ^ 2))) := by gcongr
    _ = max 2 (1 + 2 * α ^ 2) * y * (π * ((s - a) ^ 2 + y ^ 2)) := by ring

/-- The superlevel sets of the Poisson kernel are balls centred at the real part of the pole: for
`0 < Im z` and `0 < t`, `t < P(z, s)` exactly when `|s - Re z| < √(Im z / (π t) - Im z ^ 2)`. -/
theorem setOf_lt_upperHalfPlanePoissonKernel {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : 0 < t) :
    {s | t < upperHalfPlanePoissonKernel z s} =
      ball z.re (√(z.im / (π * t) - z.im ^ 2)) := by
  ext s
  simp only [mem_ofPred_eq, mem_ball, Real.dist_eq, upperHalfPlanePoissonKernel_eq,
    normSq_ofReal_sub]
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs, lt_div_iff₀ (by positivity),
    lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- The extended Poisson integral of Lebesgue measure has value one on the upper half-plane. -/
theorem lintegral_ofReal_upperHalfPlanePoissonKernel {z : ℂ} (hz : 0 < z.im) :
    ∫⁻ s, ENNReal.ofReal (upperHalfPlanePoissonKernel z s) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (isPoissonFinite_volume.integrable_upperHalfPlanePoissonKernel z)
    (.of_forall (upperHalfPlanePoissonKernel_nonneg hz.le)),
    integral_upperHalfPlanePoissonKernel hz, ENNReal.ofReal_one]

variable {F : Type*} [ENorm F]

/-- **The Poisson integral is dominated by the maximal function.** At a pole `z` of the upper
half-plane, the Poisson integral of `‖g‖ dx` is at most the Hardy–Littlewood maximal function of
`g` at `Re z`. The superlevel sets of `P(z, ·)` are balls centred at `Re z`, so by the layer cake
formula the integral is an average of ball integrals of `‖g‖`, each at most the measure of the
ball times `M g(Re z)`, and the measures of the superlevel sets integrate to `∫ P(z, ·) = 1`. -/
theorem upperHalfPlanePoissonLIntegral_withDensity_le_maximalFunction (g : ℝ → F) {z : ℂ}
    (hz : 0 < z.im) :
    upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ) z ≤
      maximalFunction volume g z.re := by
  have hnn := upperHalfPlanePoissonKernel_nonneg hz.le
  have hmeas := measurable_upperHalfPlanePoissonKernel z
  rw [upperHalfPlanePoissonLIntegral_def,
    lintegral_eq_lintegral_meas_lt _ (.of_forall hnn) hmeas.aemeasurable]
  calc ∫⁻ t in Ioi 0, volume.withDensity (fun s => ‖g s‖ₑ)
          {s | t < upperHalfPlanePoissonKernel z s}
      ≤ ∫⁻ t in Ioi 0, volume {s | t < upperHalfPlanePoissonKernel z s} *
          maximalFunction volume g z.re := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        rw [setOf_lt_upperHalfPlanePoissonKernel hz ht, withDensity_apply _ measurableSet_ball]
        exact setLIntegral_ball_le_measure_mul_maximalFunction measure_ball_lt_top.ne
    _ = maximalFunction volume g z.re := by
        have hanti : Antitone fun t : ℝ => volume {s | t < upperHalfPlanePoissonKernel z s} :=
          fun _ _ hab => measure_mono fun _ hs => lt_of_le_of_lt hab hs
        rw [lintegral_mul_const _ hanti.measurable,
          ← lintegral_eq_lintegral_meas_lt _ (.of_forall hnn) hmeas.aemeasurable,
          lintegral_ofReal_upperHalfPlanePoissonKernel hz, one_mul]

/-- **The nontangential maximal bound for the extended Poisson integral.** The nontangential
maximal function of the Poisson integral of `‖g‖ dx`, over cones of aperture `α` and any height,
is at most `max 2 (1 + 2 α ^ 2)` times the Hardy–Littlewood maximal function of `g`; for `α = 1`
the constant is `3`. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le (α : ℝ) (h : ℝ≥0∞)
    (g : ℝ → F) (x : ℝ) :
    nontangentialMaximalFunction α h
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume g x := by
  refine iSup₂_le fun z hz => ?_
  have hy := hz.1
  have hw : 0 < ((x : ℂ) + z.im * I).im := by simpa using hy
  rw [eNorm_eq_self]
  calc upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ) z
      ≤ ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) *
          upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)
            ((x : ℂ) + z.im * I) := by
        rw [upperHalfPlanePoissonLIntegral_def, upperHalfPlanePoissonLIntegral_def,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun s => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal
          (upperHalfPlanePoissonKernel_le_mul_of_mem_nontangentialCone hz s)
    _ ≤ ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume g x := by
        gcongr
        simpa using upperHalfPlanePoissonLIntegral_withDensity_le_maximalFunction g hw

/-- The norm of the Poisson integral is at most the extended Poisson integral in the closed upper
half-plane: they agree for a Poisson-finite measure, and otherwise the Poisson integral is `0`. -/
theorem enorm_upperHalfPlanePoissonIntegral_le (ν : Measure ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖upperHalfPlanePoissonIntegral ν z‖ₑ ≤ upperHalfPlanePoissonLIntegral ν z := by
  by_cases hν : IsPoissonFinite ν
  · rw [Real.eNorm_of_nonneg (upperHalfPlanePoissonIntegral_nonneg ν hz),
      ofReal_upperHalfPlanePoissonIntegral hν]
  · simp [upperHalfPlanePoissonIntegral_of_not_isPoissonFinite hν]

/-- **The nontangential maximal bound.** The nontangential maximal function of the Poisson
integral `P[‖g‖ dx]`, over cones of aperture `α` and any height, is at most
`max 2 (1 + 2 α ^ 2)` times the Hardy–Littlewood maximal function of `g`; for `α = 1` it is at
most `3 M g`. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le (α : ℝ) (h : ℝ≥0∞)
    (g : ℝ → F) (x : ℝ) :
    nontangentialMaximalFunction α h
        (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume g x :=
  iSup₂_le fun z hz => (enorm_upperHalfPlanePoissonIntegral_le _ hz.1.le).trans <|
    le_trans (le_iSup₂_of_le (f := fun z (_ : z ∈ nontangentialCone α h x) =>
        ‖upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ) z‖ₑ) z hz
        (by rw [eNorm_eq_self]))
      (nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α h g x)

end TauCeti
