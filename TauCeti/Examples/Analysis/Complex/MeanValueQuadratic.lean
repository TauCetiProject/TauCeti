/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Analysis.InnerProductSpace.Laplacian.Projection

/-!
# Circle averages of `x² - y²` and of `x²`

On the plane `ℂ = ℝ²`, write `z = x + i y`. The quadratic `u = x² - y²` is the real part of the
holomorphic function `z²`, hence harmonic, and the mean value property of harmonic functions
(`InnerProductSpace.HarmonicOnNhd.circleAverage_eq`) gives its average over every circle: the
average of `u` over the circle of radius `R` about `c = a + i b` is `a² - b²`
(`TauCeti.Examples.MeanValueQuadratic.circleAverage_re_sq_sub_im_sq`).

The quadratic `v = x²` behaves differently. Its average over the same circle is `a² + R² / 2`
(`TauCeti.Examples.MeanValueQuadratic.circleAverage_re_sq`), which differs from `v(c) = a²` for
every `R ≠ 0`. So `v` has the mean value property on no circle of positive radius, and it is
harmonic at no point (`TauCeti.Examples.MeanValueQuadratic.not_harmonicAt_re_sq`), in agreement
with its Laplacian `Δv = 2` (`TauCeti.Examples.MeanValueQuadratic.laplacian_re_sq`).

The average of `v` is computed without integrating. On the circle `|z - c| = R`,
`x² = ½ (x² - y²) + ½ |z|²` and `|z|² = R² + 2 (a x + b y) - |c|²`, so `v` agrees there with
the real part of the polynomial `z² / 2 + conj c · z + (R² - |c|²) / 2`, which is harmonic. Its
value at the centre is `a² + R² / 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.2.2 (mean-value formulas).
-/

public section

noncomputable section

namespace TauCeti.Examples.MeanValueQuadratic

open Complex InnerProductSpace Metric Real
open scoped ComplexConjugate Laplacian

/-- The quadratic `x² - y²` is harmonic on the plane: it is the real part of `z²`. -/
theorem harmonicAt_re_sq_sub_im_sq (z : ℂ) :
    HarmonicAt (fun w : ℂ ↦ w.re ^ 2 - w.im ^ 2) z := by
  have h : (fun w : ℂ ↦ w.re ^ 2 - w.im ^ 2) = fun w ↦ (w ^ 2).re := by
    funext w
    simp [sq]
  rw [h]
  exact AnalyticAt.harmonicAt_re ((by fun_prop : Differentiable ℂ fun w : ℂ ↦ w ^ 2).analyticAt z)

/-- **The mean value property for `x² - y²`.** The average of `x² - y²` over the circle of radius
`R` about `c = a + i b` is its value `a² - b²` at the centre. -/
theorem circleAverage_re_sq_sub_im_sq (c : ℂ) (R : ℝ) :
    circleAverage (fun z : ℂ ↦ z.re ^ 2 - z.im ^ 2) c R = c.re ^ 2 - c.im ^ 2 :=
  InnerProductSpace.HarmonicOnNhd.circleAverage_eq fun z _ ↦ harmonicAt_re_sq_sub_im_sq z

/-- On the circle of radius `R` about `c`, the quadratic `x²` agrees with the real part of the
polynomial `z² / 2 + conj c · z + (R² - |c|²) / 2`. -/
private theorem re_sq_eq_re_of_mem_sphere {c z : ℂ} {R : ℝ} (hz : z ∈ sphere c |R|) :
    z.re ^ 2 = (z ^ 2 / 2 + conj c * z + ((R ^ 2 - ‖c‖ ^ 2) / 2 : ℝ)).re := by
  have hR : (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 = R ^ 2 := by
    rw [mem_sphere_iff_norm, Complex.norm_eq_sqrt_sq_add_sq, sub_re, sub_im] at hz
    rw [← sq_abs R, ← hz, Real.sq_sqrt (by positivity)]
  simp only [add_re, div_ofNat_re, sq, mul_re, conj_re, conj_im, ofReal_re]
  rw [norm_mul_self_eq_normSq, normSq_apply]
  nlinarith [hR]

/-- **The circle averages of `x²`.** The average of `x²` over the circle of radius `R` about
`c = a + i b` is `a² + R² / 2`, which exceeds the value `a²` at the centre whenever `R ≠ 0`. -/
theorem circleAverage_re_sq (c : ℂ) (R : ℝ) :
    circleAverage (fun z : ℂ ↦ z.re ^ 2) c R = c.re ^ 2 + R ^ 2 / 2 := by
  set p : ℂ → ℂ := fun z ↦ z ^ 2 / 2 + conj c * z + ((R ^ 2 - ‖c‖ ^ 2) / 2 : ℝ)
  have hp : HarmonicOnNhd (fun z ↦ (p z).re) (closedBall c |R|) := fun z _ ↦
    AnalyticAt.harmonicAt_re ((by fun_prop : Differentiable ℂ p).analyticAt z)
  rw [circleAverage_congr_sphere fun z hz ↦ re_sq_eq_re_of_mem_sphere hz,
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq hp]
  simp only [p, add_re, div_ofNat_re, sq, mul_re, conj_re, conj_im, ofReal_re]
  rw [norm_mul_self_eq_normSq, normSq_apply]
  ring

/-- **The quadratic `x²` is harmonic nowhere**: it is harmonic at no point of the plane. -/
theorem not_harmonicAt_re_sq (z : ℂ) : ¬HarmonicAt (fun w : ℂ ↦ w.re ^ 2) z := by
  -- Harmonicity at `z` would give the mean value property on a small circle about `z`, whose
  -- average `z.re² + R² / 2` differs from the value `z.re²` at the centre.
  intro h
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 h.eventually
  have hR2 : 0 < R / 2 := half_pos hR
  have hmv := InnerProductSpace.HarmonicOnNhd.circleAverage_eq (c := z) (R := R / 2)
    fun w hw ↦ hball w <| closedBall_subset_ball (by rw [abs_of_pos hR2]; linarith) hw
  rw [circleAverage_re_sq] at hmv
  nlinarith

/-- **The Laplacian of `x²`** is the constant `2`. -/
theorem laplacian_re_sq : Δ (fun w : ℂ ↦ w.re ^ 2) = fun _ ↦ 2 := by
  funext z
  have h : (fun w : ℂ ↦ w.re ^ 2) = fun w ↦ ⟪(1 : ℂ), w⟫_ℝ ^ 2 := by
    funext w
    simp [Complex.inner]
  rw [h, TauCeti.laplacian_inner_sq]
  simp

end TauCeti.Examples.MeanValueQuadratic
