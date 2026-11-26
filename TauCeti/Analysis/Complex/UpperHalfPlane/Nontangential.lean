/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
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
  Poisson kernels, and `TauCeti.upperHalfPlanePoissonKernel_le_three_mul_of_mem_nontangentialCone`
  its form with constant `3` for aperture one.
* `TauCeti.upperHalfPlanePoissonLIntegral_le_mul_of_mem_nontangentialCone`: the cone comparison
  for the Poisson integral of a measure.
* `TauCeti.upperHalfPlanePoissonLIntegral_le_of_measure_ball_le`: the Poisson integral of a
  measure `μ` at `z` is at most any `M` with `μ(B(Re z, r)) ≤ M |B(Re z, r)|` for all `r > 0`;
  in particular (`TauCeti.upperHalfPlanePoissonLIntegral_withDensity_le_maximalFunction`) the
  Poisson integral of `|g| dx` at a pole `z` is at most `M g(Re z)`.
* `TauCeti.nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le` and
  `TauCeti.nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le`: the maximal bound
  `M^α_h P[|g| dx] ≤ max 2 (1 + 2 α ^ 2) · M g`, and their forms
  `M_h P[|g| dx] ≤ 3 M g` for aperture one,
  `TauCeti.nontangentialMaximalFunction_one_upperHalfPlanePoissonLIntegral_le` and
  `TauCeti.nontangentialMaximalFunction_one_upperHalfPlanePoissonIntegral_le`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §4.
* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. **200**
  (2024), Section 2.
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

@[simp]
theorem mem_nontangentialCone {α : ℝ} {h : ℝ≥0∞} {x : ℝ} {z : ℂ} :
    z ∈ nontangentialCone α h x ↔
      0 < z.im ∧ |z.re - x| < α * z.im ∧ ENNReal.ofReal z.im < h :=
  Iff.rfl

/-- A point of the cone `Γ^α_h(x)` lies within `(|α| + 1) Im z` of the vertex. -/
theorem dist_lt_of_mem_nontangentialCone {α : ℝ} {h : ℝ≥0∞} {x : ℝ} {z : ℂ}
    (hz : z ∈ nontangentialCone α h x) : dist z x < (|α| + 1) * z.im := by
  obtain ⟨hz0, hzα, -⟩ := mem_nontangentialCone.1 hz
  have hre : |z.re - x| < |α| * z.im :=
    hzα.trans_le (mul_le_mul_of_nonneg_right (le_abs_self α) hz0.le)
  calc dist z x ≤ |(z - x).re| + |(z - x).im| := by
        rw [dist_eq_norm]; exact norm_le_abs_re_add_abs_im _
    _ < |α| * z.im + z.im := by
        simpa [abs_of_pos hz0] using add_lt_add_of_lt_of_le hre (le_refl z.im)
    _ = (|α| + 1) * z.im := by ring

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

/-- The nontangential maximal function bounds `‖u z‖ₑ` at every point of the cone. -/
theorem le_nontangentialMaximalFunction {E : Type*} [ENorm E] {α : ℝ} {h : ℝ≥0∞} {u : ℂ → E}
    {x : ℝ} {z : ℂ} (hz : z ∈ nontangentialCone α h x) :
    ‖u z‖ₑ ≤ nontangentialMaximalFunction α h u x :=
  le_iSup₂ (f := fun z (_ : z ∈ nontangentialCone α h x) => ‖u z‖ₑ) z hz

/-- The nontangential maximal function is at most `c` exactly when `‖u‖ₑ ≤ c` on the cone. -/
theorem nontangentialMaximalFunction_le_iff {E : Type*} [ENorm E] {α : ℝ} {h : ℝ≥0∞}
    {u : ℂ → E} {x : ℝ} {c : ℝ≥0∞} :
    nontangentialMaximalFunction α h u x ≤ c ↔ ∀ z ∈ nontangentialCone α h x, ‖u z‖ₑ ≤ c :=
  iSup₂_le_iff

/-- A pointwise bound on the cone bounds the nontangential maximal function. -/
theorem nontangentialMaximalFunction_mono_fun {E E' : Type*} [ENorm E] [ENorm E'] {α : ℝ}
    {h : ℝ≥0∞} {u : ℂ → E} {v : ℂ → E'} {x : ℝ}
    (huv : ∀ z ∈ nontangentialCone α h x, ‖u z‖ₑ ≤ ‖v z‖ₑ) :
    nontangentialMaximalFunction α h u x ≤ nontangentialMaximalFunction α h v x :=
  iSup₂_mono huv

/-- The nontangential maximal function grows with the aperture and the height. -/
theorem nontangentialMaximalFunction_mono {E : Type*} [ENorm E] {α β : ℝ} {h k : ℝ≥0∞}
    (hαβ : α ≤ β) (hhk : h ≤ k) (u : ℂ → E) (x : ℝ) :
    nontangentialMaximalFunction α h u x ≤ nontangentialMaximalFunction β k u x :=
  biSup_mono fun _ hz => nontangentialCone_mono hαβ hhk x hz

/-- The nontangential maximal function of the Poisson integral is at most that of the extended
Poisson integral. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le_upperHalfPlanePoissonLIntegral
    (α : ℝ) (h : ℝ≥0∞) (ν : Measure ℝ) (x : ℝ) :
    nontangentialMaximalFunction α h (upperHalfPlanePoissonIntegral ν) x ≤
      nontangentialMaximalFunction α h (upperHalfPlanePoissonLIntegral ν) x :=
  nontangentialMaximalFunction_mono_fun fun z hz => by
    simpa using enorm_upperHalfPlanePoissonIntegral_le ν (mem_nontangentialCone.1 hz).1.le

/-- **The cone comparison.** For `z = x' + iy` in the cone `Γ^α_∞(x)`, the Poisson kernel with
pole `z` is at most `max 2 (1 + 2 α ^ 2)` times the Poisson kernel with pole `x + iy`. For
`α = 1` the constant is `3`. -/
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

/-- **The cone comparison for aperture one.** For `z = x' + iy` in the cone `Γ_h(x)`, the Poisson
kernel with pole `z` is at most `3` times the Poisson kernel with pole `x + iy`. -/
theorem upperHalfPlanePoissonKernel_le_three_mul_of_mem_nontangentialCone {h : ℝ≥0∞} {x : ℝ}
    {z : ℂ} (hz : z ∈ nontangentialCone 1 h x) (s : ℝ) :
    upperHalfPlanePoissonKernel z s ≤ 3 * upperHalfPlanePoissonKernel (x + z.im * I) s :=
  (upperHalfPlanePoissonKernel_le_mul_of_mem_nontangentialCone hz s).trans_eq (by norm_num)

/-- **The cone comparison for the Poisson integral of a measure.** For `z` in the cone `Γ^α_h(x)`,
the extended Poisson integral of `μ` at `z` is at most `max 2 (1 + 2 α ^ 2)` times that at the
vertical pole `x + i Im z`. -/
theorem upperHalfPlanePoissonLIntegral_le_mul_of_mem_nontangentialCone (μ : Measure ℝ) {α : ℝ}
    {h : ℝ≥0∞} {x : ℝ} {z : ℂ} (hz : z ∈ nontangentialCone α h x) :
    upperHalfPlanePoissonLIntegral μ z ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) *
        upperHalfPlanePoissonLIntegral μ ((x : ℂ) + z.im * I) := by
  rw [upperHalfPlanePoissonLIntegral_def, upperHalfPlanePoissonLIntegral_def,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun s => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (upperHalfPlanePoissonKernel_le_mul_of_mem_nontangentialCone hz s)

/-- **The Poisson integral of a measure is dominated by its ball averages.** If
`μ(B(Re z, r)) ≤ M |B(Re z, r)|` for every open ball of radius `r > 0`, then the extended Poisson
integral of `μ` at `z` is at most `M`. -/
theorem upperHalfPlanePoissonLIntegral_le_of_measure_ball_le {μ : Measure ℝ} {z : ℂ}
    {M : ℝ≥0∞} (hM : ∀ r > 0, μ (ball z.re r) ≤ M * volume (ball z.re r)) :
    upperHalfPlanePoissonLIntegral μ z ≤ M := by
  rcases le_or_gt z.im 0 with hz | hz
  · simp [upperHalfPlanePoissonLIntegral_def, ENNReal.ofReal_of_nonpos,
      upperHalfPlanePoissonKernel_nonpos hz]
  have hnn := upperHalfPlanePoissonKernel_nonneg hz.le
  have hmeas := measurable_upperHalfPlanePoissonKernel z
  have hball : ∀ ρ : ℝ, μ (ball z.re ρ) ≤ volume (ball z.re ρ) * M := fun ρ => by
    rcases le_or_gt ρ 0 with hρ | hρ
    · simp [ball_eq_empty.2 hρ]
    · exact (hM ρ hρ).trans_eq (mul_comm _ _)
  rw [upperHalfPlanePoissonLIntegral_def,
    lintegral_eq_lintegral_meas_lt _ (.of_forall hnn) hmeas.aemeasurable]
  calc ∫⁻ t in Ioi 0, μ {s | t < upperHalfPlanePoissonKernel z s}
      ≤ ∫⁻ t in Ioi 0, volume {s | t < upperHalfPlanePoissonKernel z s} * M := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        rw [setOf_lt_upperHalfPlanePoissonKernel z ht]
        exact hball _
    _ = M := by
        have hanti : Antitone fun t : ℝ => volume {s | t < upperHalfPlanePoissonKernel z s} :=
          fun _ _ hab => measure_mono fun _ hs => lt_of_le_of_lt hab hs
        rw [lintegral_mul_const _ hanti.measurable,
          ← lintegral_eq_lintegral_meas_lt _ (.of_forall hnn) hmeas.aemeasurable,
          ← upperHalfPlanePoissonLIntegral_def, upperHalfPlanePoissonLIntegral_volume hz, one_mul]

variable {F : Type*} [ENorm F]

/-- **The Poisson integral is dominated by the maximal function.** At every pole `z`, the
extended Poisson integral of `‖g‖ dx` is at most the Hardy–Littlewood maximal function of `g` at
`Re z`; off the upper half-plane the left side is `0`. -/
theorem upperHalfPlanePoissonLIntegral_withDensity_le_maximalFunction (g : ℝ → F) (z : ℂ) :
    upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ) z ≤
      maximalFunction volume g z.re :=
  upperHalfPlanePoissonLIntegral_le_of_measure_ball_le fun _ _ => by
    rw [withDensity_apply _ measurableSet_ball, mul_comm]
    exact setLIntegral_ball_le_measure_mul_maximalFunction measure_ball_lt_top.ne

/-- **The nontangential maximal bound for the extended Poisson integral.** The nontangential
maximal function of the Poisson integral of `‖g‖ dx`, over cones of aperture `α` and any height,
is at most `max 2 (1 + 2 α ^ 2)` times the Hardy–Littlewood maximal function of `g`; for `α = 1`
the constant is `3`. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le (α : ℝ) (h : ℝ≥0∞)
    (g : ℝ → F) (x : ℝ) :
    nontangentialMaximalFunction α h
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume g x := by
  refine nontangentialMaximalFunction_le_iff.2 fun z hz => ?_
  rw [eNorm_eq_self]
  calc upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ) z
      ≤ ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) *
          upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)
            ((x : ℂ) + z.im * I) :=
        upperHalfPlanePoissonLIntegral_le_mul_of_mem_nontangentialCone _ hz
    _ ≤ ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume g x := by
        gcongr
        simpa using upperHalfPlanePoissonLIntegral_withDensity_le_maximalFunction g
          ((x : ℂ) + z.im * I)

/-- **The nontangential maximal bound.** The nontangential maximal function of the Poisson
integral `P[‖g‖ dx]`, over cones of aperture `α` and any height, is at most
`max 2 (1 + 2 α ^ 2)` times the Hardy–Littlewood maximal function of `g`; for `α = 1` it is at
most `3 M g`. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le (α : ℝ) (h : ℝ≥0∞)
    (g : ℝ → F) (x : ℝ) :
    nontangentialMaximalFunction α h
        (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume g x :=
  (nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le_upperHalfPlanePoissonLIntegral
    α h _ x).trans (nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α h g x)

/-- **The nontangential maximal bound for aperture one.** The nontangential maximal function of
the Poisson integral of `‖g‖ dx`, over cones of aperture one and any height, is at most `3` times
the Hardy–Littlewood maximal function of `g`. -/
theorem nontangentialMaximalFunction_one_upperHalfPlanePoissonLIntegral_le (h : ℝ≥0∞)
    (g : ℝ → F) (x : ℝ) :
    nontangentialMaximalFunction 1 h
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      3 * maximalFunction volume g x :=
  (nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le 1 h g x).trans_eq (by norm_num)

/-- **The nontangential maximal bound for aperture one.** The nontangential maximal function of
the Poisson integral `P[‖g‖ dx]`, over cones of aperture one and any height, is at most `3 M g`. -/
theorem nontangentialMaximalFunction_one_upperHalfPlanePoissonIntegral_le (h : ℝ≥0∞)
    (g : ℝ → F) (x : ℝ) :
    nontangentialMaximalFunction 1 h
        (upperHalfPlanePoissonIntegral (volume.withDensity fun s => ‖g s‖ₑ)) x ≤
      3 * maximalFunction volume g x :=
  (nontangentialMaximalFunction_upperHalfPlanePoissonIntegral_le 1 h g x).trans_eq (by norm_num)

end TauCeti
