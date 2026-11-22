/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# The Sobolev space `W^{1,2}` of the pair of pants

The Fredholm theory of the linearized Floer operator on the pair of pants `S = ℂ ∖ {0, 1}` uses
Sobolev norms of a metric that is cylindrical on the three ends: on the end `q` it is
`ds² + dt²` in the end coordinates `(s, t)` of the end chart `φ_q`
(`TauCeti.Floer.endChart`). In the coordinate `w` of `ℂ` this metric is conformal, of the form
`ρ |dw|²` with `ρ ≍ |w - c|⁻²` near a finite puncture `c` and `ρ ≍ |w|⁻²` near `∞`, so the
`W^{1,2}` norm of a section is `∫_S (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` in the coordinates of `ℂ`, up to
constants. This file fixes the conformal weight

`ρ(w) = |w|⁻² + |w - 1|⁻²` (`TauCeti.Floer.cylindricalWeight`),

a conformal weight on `S` (`TauCeti.Floer.isWeight_cylindricalWeight`). The Sobolev space
`TauCeti.ConformalSobolev.H1 V thricePuncturedSphereReal cylindricalWeight` of
`TauCeti.Analysis.Sobolev.Conformal` is then the completion of the compactly supported sections of
`S` in a norm that agrees on the ends, up to constants, with the `W^{1,2}` norm of the cylindrical
metric, and it comes with Rellich's theorem on compact subsets of `S` and Peetre's argument.

The comparison with the cylindrical metric on the ends is exact up to constants. The end chart
`φ_q(z) = c_q + b_q exp (-2πz)` is holomorphic with Jacobian `4π² |φ_q(z) - c_q|²`, and on the part
`±s ≥ 0` of each end the product of the weight and the Jacobian lies between `4π²` and `20π²`
(`TauCeti.Floer.cylindricalWeight_endChart_mul_det_fderiv_mem_Icc`). Since the Dirichlet density
changes by the Jacobian under a holomorphic change of coordinates, up to a factor `2` in a normed
space (`TauCeti.norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq_le`), the `W^{1,2}` density
`‖∂s ζ‖² + ‖∂t ζ‖² + ‖ζ‖²` of `ζ = ξ ∘ φ_q` in the end coordinates and the weighted density of `ξ`
times the Jacobian agree up to the factors `2` and `20π²`
(`TauCeti.Floer.norm_fderiv_comp_endChart_sq_add_le`,
`TauCeti.Floer.det_fderiv_endChart_mul_le`). By the change of variables formula, the
`W^{1,2}` energy of `ξ` over the image `φ_q(P × [0, 1))` of a band of the end and the energy of
`ζ` over the band agree up to the same factors
(`TauCeti.Floer.lintegral_comp_endChart_le`, `TauCeti.Floer.lintegral_image_endChart_le`), and
the same comparison holds in the positive end charts `φ'_q`, which read every end as a positive end
(`TauCeti.Floer.det_fderiv_positiveEndChart_mul_le`,
`TauCeti.Floer.lintegral_image_positiveEndChart_le`). So estimates stated in the end coordinates,
such as the semi-Fredholm estimate of the linearized Floer operator along a Floer pair of pants,
transfer to the norm of `H1`. Pointwise, the weight is at least `|w - c_q|⁻²` for the center `c_q`
of every end
(`TauCeti.Floer.inv_norm_sub_endCenter_sq_le_cylindricalWeight`,
`TauCeti.Floer.inv_sqrt_cylindricalWeight_le_norm_sub_endCenter`): the distance `|w - c_q|` to the
center of the end is, up to the constant `2π`, the conformal factor of the end chart.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on Sobolev spaces on punctured Riemann surfaces with cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator.
-/

public section

noncomputable section

open Set Real MeasureTheory TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The **cylindrical weight** of the pair of pants `S = ℂ ∖ {0, 1}`, in the real coordinates
`ℝ × ℝ ≃ ℂ`: `ρ(w) = |w|⁻² + |w - 1|⁻²`. The conformal metric `ρ |dw|²` agrees with the cylindrical
metric `ds² + dt²` of each end up to constants
(`TauCeti.Floer.cylindricalWeight_endChart_mul_det_fderiv_mem_Icc`). -/
def cylindricalWeight (z : ℝ × ℝ) : ℝ :=
  (Complex.normSq (Complex.equivRealProdCLM.symm z))⁻¹ +
    (Complex.normSq (Complex.equivRealProdCLM.symm z - 1))⁻¹

theorem cylindricalWeight_apply (z : ℝ × ℝ) :
    cylindricalWeight z = (Complex.normSq (Complex.equivRealProdCLM.symm z))⁻¹ +
      (Complex.normSq (Complex.equivRealProdCLM.symm z - 1))⁻¹ :=
  (rfl)

/-- The cylindrical weight is nonnegative everywhere. -/
theorem cylindricalWeight_nonneg (z : ℝ × ℝ) : 0 ≤ cylindricalWeight z :=
  add_nonneg (inv_nonneg.2 (Complex.normSq_nonneg _)) (inv_nonneg.2 (Complex.normSq_nonneg _))

/-- The cylindrical weight is a conformal weight on the pair of pants: it is continuous and
positive on `S`. -/
theorem isWeight_cylindricalWeight :
    ConformalSobolev.IsWeight thricePuncturedSphereReal cylindricalWeight where
  isOpen := isOpen_thricePuncturedSphereReal
  continuousOn := by
    have he := Complex.equivRealProdCLM.symm.continuous
    refine ((Complex.continuous_normSq.comp he).continuousOn.inv₀ fun z hz ↦ ?_).add
      ((Complex.continuous_normSq.comp (he.sub continuous_const)).continuousOn.inv₀ fun z hz ↦ ?_)
    · exact Complex.normSq_eq_zero.not.2 (mem_thricePuncturedSphereReal_iff.1 hz).1
    · exact Complex.normSq_eq_zero.not.2 (sub_ne_zero.2 (mem_thricePuncturedSphereReal_iff.1 hz).2)
  pos z hz := by
    obtain ⟨h₀, h₁⟩ := mem_thricePuncturedSphereReal_iff.1 hz
    exact add_pos (inv_pos.2 (Complex.normSq_pos.2 h₀))
      (inv_pos.2 (Complex.normSq_pos.2 (sub_ne_zero.2 h₁)))

/-- The arithmetic of the weight on an end: if a point lies at distance `x > 0` from the center of
its end and at distance `y ≥ x / 2` from the other finite puncture, then
`(x⁻² + y⁻²) 4π² x² ∈ [4π², 20π²]`. -/
private theorem inv_sq_add_inv_sq_mul_mem_Icc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ 2 * y) :
    ((x ^ 2)⁻¹ + (y ^ 2)⁻¹) * (4 * π ^ 2 * x ^ 2) ∈ Icc (4 * π ^ 2) (20 * π ^ 2) := by
  have hy : 0 < y := by linarith
  have hr : x ^ 2 / y ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hr0 : 0 ≤ x ^ 2 / y ^ 2 := by positivity
  have h : ((x ^ 2)⁻¹ + (y ^ 2)⁻¹) * (4 * π ^ 2 * x ^ 2) = 4 * π ^ 2 * (1 + x ^ 2 / y ^ 2) := by
    field_simp
  rw [h]
  constructor <;> nlinarith [pi_pos]

/-- **The cylindrical weight on the ends.** On the part `±s ≥ 0` of the end `q`, the cylindrical
weight times the Jacobian of the end chart lies between `4π²` and `20π²`: the conformal metric
`ρ |dw|²` and the cylindrical metric `ds² + dt²` of the end agree up to these factors. -/
theorem cylindricalWeight_endChart_mul_det_fderiv_mem_Icc (q : Puncture) {z : ℝ × ℝ}
    (hz : 0 ≤ q.endSign * z.1) :
    cylindricalWeight (endChart q z) * (fderiv ℝ (endChart q) z).det ∈
      Icc (4 * π ^ 2) (20 * π ^ 2) := by
  rw [det_fderiv_endChart, cylindricalWeight_apply, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  set w := Complex.equivRealProdCLM.symm (endChart q z)
  have hd : ‖w - q.endCenter‖ = ‖q.endScale‖ * Real.exp (-(2 * π * z.1)) := by
    simp only [w, equivRealProdCLM_symm_endChart, norm_cylindricalEndLift_sub_endCenter]
    simp [Complex.equivRealProdCLM_symm_apply]
  cases q with
  | zero =>
    -- Near `0` the point is within `1/2` of `0`, hence at least `1/2` from `1`.
    simp only [endSign_zero, one_mul, endCenter_zero, sub_zero, endScale_zero] at hz hd ⊢
    have hle : Real.exp (-(2 * π * z.1)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg pi_pos.le hz])
    have hb : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    have h₁ : ‖w‖ ≤ 1 / 2 := by rw [hd, hb]; linarith
    have h₂ : 1 - ‖w‖ ≤ ‖w - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) w
      rwa [norm_one, norm_sub_rev] at this
    exact inv_sq_add_inv_sq_mul_mem_Icc (by rw [hd, hb]; positivity) (by linarith)
  | one =>
    -- Near `1` the point is within `1/2` of `1`, hence at least `1/2` from `0`.
    simp only [endSign_one, one_mul, endCenter_one, endScale_one] at hz hd ⊢
    have hle : Real.exp (-(2 * π * z.1)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg pi_pos.le hz])
    have hb : ‖(-(1 / 2) : ℂ)‖ = 1 / 2 := by norm_num
    have h₁ : ‖w - 1‖ ≤ 1 / 2 := by rw [hd, hb]; linarith
    have h₂ : 1 - ‖w - 1‖ ≤ ‖w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - w)
      rwa [norm_one, sub_sub_cancel, norm_sub_rev] at this
    rw [add_comm]
    exact inv_sq_add_inv_sq_mul_mem_Icc (by rw [hd, hb]; positivity) (by linarith)
  | inf =>
    -- Near `∞` the point is at distance at least `2` from `0`, hence comparable to its distance
    -- from `1`.
    simp only [endSign_inf, neg_one_mul, endCenter_inf, sub_zero, endScale_inf] at hz hd ⊢
    have hge : 1 ≤ Real.exp (-(2 * π * z.1)) :=
      Real.one_le_exp_iff.2 (by nlinarith [mul_nonneg pi_pos.le hz])
    have hb : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h₁ : 2 ≤ ‖w‖ := by rw [hd, hb]; linarith
    have h₂ : ‖w‖ - 1 ≤ ‖w - 1‖ := by
      have := norm_sub_norm_le w 1
      rwa [norm_one] at this
    exact inv_sq_add_inv_sq_mul_mem_Icc (by linarith) (by linarith)

/-- The cylindrical weight of the pair of pants is at least `|z - c_q|⁻²` for the center `c_q` of
every end: `0` for the ends at `0` and `∞`, and `1` for the end at `1`. -/
theorem inv_norm_sub_endCenter_sq_le_cylindricalWeight (q : Puncture) (z : ℝ × ℝ) :
    (‖Complex.equivRealProdCLM.symm z - q.endCenter‖ ^ 2)⁻¹ ≤ cylindricalWeight z := by
  rw [cylindricalWeight_apply, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h₀ : 0 ≤ (‖Complex.equivRealProdCLM.symm z‖ ^ 2)⁻¹ := by positivity
  have h₁ : 0 ≤ (‖Complex.equivRealProdCLM.symm z - 1‖ ^ 2)⁻¹ := by positivity
  cases q
  · simp only [endCenter_zero, sub_zero]
    linarith
  · simp only [endCenter_one]
    linarith
  · simp only [endCenter_inf, sub_zero]
    linarith

/-- Away from the center `c_q` of an end, the inverse square root of the cylindrical weight is at
most the distance `|z - c_q|`. -/
theorem inv_sqrt_cylindricalWeight_le_norm_sub_endCenter (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    (√(cylindricalWeight z))⁻¹ ≤ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ := by
  have hd : 0 < ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 hz)
  have h := Real.sqrt_le_sqrt (inv_norm_sub_endCenter_sq_le_cylindricalWeight q z)
  rw [Real.sqrt_inv, Real.sqrt_sq hd.le] at h
  simpa using inv_anti₀ (inv_pos.2 hd) h

/-- **The `W^{1,2}` density on the ends, from the weighted density.** On the part `±s ≥ 0` of the
end `q`, the `W^{1,2}` density `‖∂s ζ‖² + ‖∂t ζ‖² + ‖ζ‖²` of `ζ = ξ ∘ φ_q` in the end coordinates
is at most twice the Jacobian of `φ_q` times the weighted density
`ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²` at `φ_q(z)`. -/
theorem norm_fderiv_comp_endChart_sq_add_le (q : Puncture) {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hz : 0 ≤ q.endSign * z.1) (hξ : DifferentiableAt ℝ ξ (endChart q z)) :
    ‖fderiv ℝ (ξ ∘ endChart q) z (1, 0)‖ ^ 2 + ‖fderiv ℝ (ξ ∘ endChart q) z (0, 1)‖ ^ 2 +
        ‖ξ (endChart q z)‖ ^ 2 ≤
      2 * ((fderiv ℝ (endChart q) z).det *
        (cylindricalWeight (endChart q z) * ‖ξ (endChart q z)‖ ^ 2 +
          ‖fderiv ℝ ξ (endChart q z) (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ (endChart q z) (0, 1)‖ ^ 2)) := by
  obtain ⟨c, hc⟩ : ∃ c, HasDerivAt q.cylindricalEndLift c (Complex.equivRealProdCLM.symm z) :=
    ⟨_, q.hasDerivAt_cylindricalEndLift _⟩
  have hρ := (cylindricalWeight_endChart_mul_det_fderiv_mem_Icc q hz).1
  rw [endChart_eq_realChart] at hξ hρ ⊢
  have hconf := norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq_le c.re c.im
    (fderiv ℝ ξ (Complex.realChart q.cylindricalEndLift z) (1, 0))
    (fderiv ℝ ξ (Complex.realChart q.cylindricalEndLift z) (0, 1))
  rw [Complex.fderiv_comp_realChart_apply_one_zero hc hξ,
    Complex.fderiv_comp_realChart_apply_zero_one hc hξ]
  rw [Complex.det_fderiv_realChart hc, Complex.normSq_apply] at hρ ⊢
  have hπ : 1 ≤ 4 * π ^ 2 := by nlinarith [two_le_pi]
  nlinarith [sq_nonneg ‖ξ (endChart q z)‖]

/-- **The weighted density, from the `W^{1,2}` density on the ends.** On the part `±s ≥ 0` of the
end `q`, the Jacobian of `φ_q` times the weighted density `ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²` at
`φ_q(z)` is at most `20π²` times the `W^{1,2}` density of `ζ = ξ ∘ φ_q` in the end coordinates. -/
theorem det_fderiv_endChart_mul_le (q : Puncture) {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hz : 0 ≤ q.endSign * z.1) (hξ : DifferentiableAt ℝ ξ (endChart q z)) :
    (fderiv ℝ (endChart q) z).det *
        (cylindricalWeight (endChart q z) * ‖ξ (endChart q z)‖ ^ 2 +
          ‖fderiv ℝ ξ (endChart q z) (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ (endChart q z) (0, 1)‖ ^ 2) ≤
      20 * π ^ 2 * (‖fderiv ℝ (ξ ∘ endChart q) z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (ξ ∘ endChart q) z (0, 1)‖ ^ 2 + ‖ξ (endChart q z)‖ ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c, HasDerivAt q.cylindricalEndLift c (Complex.equivRealProdCLM.symm z) :=
    ⟨_, q.hasDerivAt_cylindricalEndLift _⟩
  have hρ := (cylindricalWeight_endChart_mul_det_fderiv_mem_Icc q hz).2
  rw [endChart_eq_realChart] at hξ hρ ⊢
  set φ := Complex.realChart q.cylindricalEndLift
  have hconf := le_two_mul_norm_smul_add_smul_sq_add_norm_neg_smul_add_smul_sq c.re c.im
    (fderiv ℝ ξ (φ z) (1, 0)) (fderiv ℝ ξ (φ z) (0, 1))
  rw [Complex.fderiv_comp_realChart_apply_one_zero hc hξ,
    Complex.fderiv_comp_realChart_apply_zero_one hc hξ]
  rw [Complex.det_fderiv_realChart hc, Complex.normSq_apply] at hρ ⊢
  have hπ : 2 ≤ 20 * π ^ 2 := by nlinarith [two_le_pi]
  nlinarith [sq_nonneg ‖ξ (φ z)‖,
    sq_nonneg ‖c.re • fderiv ℝ ξ (φ z) (1, 0) + c.im • fderiv ℝ ξ (φ z) (0, 1)‖,
    sq_nonneg ‖(-c.im) • fderiv ℝ ξ (φ z) (1, 0) + c.re • fderiv ℝ ξ (φ z) (0, 1)‖]

/-- The change of variables along the end chart, on a band `P × [0, 1)` of the end. -/
private theorem lintegral_image_endChart (q : Puncture) {P : Set ℝ} (hP : MeasurableSet P)
    (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ w in endChart q '' (P ×ˢ Ico 0 1), g w =
      ∫⁻ z in P ×ˢ Ico 0 1, ENNReal.ofReal |(fderiv ℝ (endChart q) z).det| * g (endChart q z) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hP.prod measurableSet_Ico)
    (fun z _ ↦ ((contDiff_endChart q 1).differentiable one_ne_zero z).hasFDerivAt.hasFDerivWithinAt)
    ((injOn_endChart_univ_prod_Ico q 0).mono (prod_mono (subset_univ _) (by norm_num))) g

/-- **The `W^{1,2}` energy on a band of an end, from the weighted energy.** For a band
`P × [0, 1)` of the part `±s ≥ 0` of the end `q` and a `ξ` differentiable on the image of the
band, the `W^{1,2}` energy of `ζ = ξ ∘ φ_q` over the band is at most twice the weighted energy
`∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ` over the image of the band. -/
theorem lintegral_comp_endChart_le (q : Puncture) {P : Set ℝ} (hP : MeasurableSet P)
    (hP0 : ∀ s ∈ P, 0 ≤ q.endSign * s) {ξ : ℝ × ℝ → V}
    (hξ : ∀ z ∈ P ×ˢ Ico 0 1, DifferentiableAt ℝ ξ (endChart q z)) :
    ∫⁻ z in P ×ˢ Ico 0 1, ENNReal.ofReal (‖fderiv ℝ (ξ ∘ endChart q) z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (ξ ∘ endChart q) z (0, 1)‖ ^ 2 + ‖ξ (endChart q z)‖ ^ 2) ≤
      2 * ∫⁻ w in endChart q '' (P ×ˢ Ico 0 1), ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 +
        ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) := by
  rw [lintegral_image_endChart q hP, ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  refine setLIntegral_mono' (hP.prod measurableSet_Ico) fun z hz ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), abs_of_pos (det_fderiv_endChart_pos q z)]
  exact ENNReal.ofReal_le_ofReal (norm_fderiv_comp_endChart_sq_add_le q (hP0 z.1 hz.1) (hξ z hz))

/-- **The weighted energy on the image of a band of an end, from the `W^{1,2}` energy.** For a
band `P × [0, 1)` of the part `±s ≥ 0` of the end `q` and a `ξ` differentiable on the image of
the band, the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ` over the image of the band
is at most `20π²` times the `W^{1,2}` energy of `ζ = ξ ∘ φ_q` over the band. -/
theorem lintegral_image_endChart_le (q : Puncture) {P : Set ℝ} (hP : MeasurableSet P)
    (hP0 : ∀ s ∈ P, 0 ≤ q.endSign * s) {ξ : ℝ × ℝ → V}
    (hξ : ∀ z ∈ P ×ˢ Ico 0 1, DifferentiableAt ℝ ξ (endChart q z)) :
    ∫⁻ w in endChart q '' (P ×ˢ Ico 0 1), ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 +
        ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (20 * π ^ 2) * ∫⁻ z in P ×ˢ Ico 0 1,
        ENNReal.ofReal (‖fderiv ℝ (ξ ∘ endChart q) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ endChart q) z (0, 1)‖ ^ 2 + ‖ξ (endChart q z)‖ ^ 2) := by
  rw [lintegral_image_endChart q hP, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (hP.prod measurableSet_Ico) fun z hz ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (det_fderiv_endChart_pos q z)]
  exact ENNReal.ofReal_le_ofReal (det_fderiv_endChart_mul_le q (hP0 z.1 hz.1) (hξ z hz))

/-- **The weighted density, from the `W^{1,2}` density in the positive end chart.** On the part
`s ≥ 0` of the positive end chart `φ'_q`, the Jacobian of `φ'_q` times the weighted density
`ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²` at `φ'_q(ζ)` is at most `20π²` times the `W^{1,2}` density of
`ξ ∘ φ'_q` at `ζ`. -/
theorem det_fderiv_positiveEndChart_mul_le (q : Puncture) {ξ : ℝ × ℝ → V} {ζ : ℝ × ℝ}
    (hζ : 0 ≤ ζ.1) (hξ : DifferentiableAt ℝ ξ (positiveEndChart q ζ)) :
    (fderiv ℝ (positiveEndChart q) ζ).det *
        (cylindricalWeight (positiveEndChart q ζ) * ‖ξ (positiveEndChart q ζ)‖ ^ 2 +
          ‖fderiv ℝ ξ (positiveEndChart q ζ) (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ (positiveEndChart q ζ) (0, 1)‖ ^ 2) ≤
      20 * π ^ 2 * (‖fderiv ℝ (ξ ∘ positiveEndChart q) ζ (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (ξ ∘ positiveEndChart q) ζ (0, 1)‖ ^ 2 + ‖ξ (positiveEndChart q ζ)‖ ^ 2) := by
  -- The positive end chart is the end chart at the reflected point `±ζ`.
  have hφ : positiveEndChart q ζ = endChart q (q.endSign • ζ) := positiveEndChart_apply q ζ
  have hz : 0 ≤ q.endSign * (q.endSign • ζ).1 := by
    rwa [Prod.smul_fst, smul_eq_mul, ← mul_assoc, endSign_mul_self, one_mul]
  have hdet : (fderiv ℝ (positiveEndChart q) ζ).det =
      (fderiv ℝ (endChart q) (q.endSign • ζ)).det := by
    rw [det_fderiv_positiveEndChart, det_fderiv_endChart, hφ]
  have hd (v : ℝ × ℝ) : ‖fderiv ℝ (ξ ∘ endChart q) (q.endSign • ζ) v‖ =
      ‖fderiv ℝ (ξ ∘ positiveEndChart q) ζ v‖ := by
    rw [fderiv_comp_endChart]
    simp [smul_smul, norm_smul, abs_endSign]
  have h := det_fderiv_endChart_mul_le q hz (hφ ▸ hξ)
  rwa [hd, hd, ← hdet, ← hφ] at h

/-- **The weighted energy on the image of a band of the positive end chart, from the `W^{1,2}`
energy.** For a band `P × [0, 1)` of the part `s ≥ 0` of the positive end chart `φ'_q` and a `ξ`
differentiable on the image of the band, the weighted energy `∫ (ρ ‖ξ‖² + ‖∂s ξ‖² + ‖∂t ξ‖²)` of `ξ`
over the image of the band is at most `20π²` times the `W^{1,2}` energy of `ξ ∘ φ'_q` over the
band. -/
theorem lintegral_image_positiveEndChart_le (q : Puncture) {P : Set ℝ} (hP : MeasurableSet P)
    (hP0 : ∀ s ∈ P, 0 ≤ s) {ξ : ℝ × ℝ → V}
    (hξ : ∀ ζ ∈ P ×ˢ Ico 0 1, DifferentiableAt ℝ ξ (positiveEndChart q ζ)) :
    ∫⁻ w in positiveEndChart q '' (P ×ˢ Ico 0 1),
        ENNReal.ofReal (cylindricalWeight w * ‖ξ w‖ ^ 2 + ‖fderiv ℝ ξ w (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ w (0, 1)‖ ^ 2) ≤
      ENNReal.ofReal (20 * π ^ 2) * ∫⁻ ζ in P ×ˢ Ico 0 1,
        ENNReal.ofReal (‖fderiv ℝ (ξ ∘ positiveEndChart q) ζ (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (ξ ∘ positiveEndChart q) ζ (0, 1)‖ ^ 2 + ‖ξ (positiveEndChart q ζ)‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hP.prod measurableSet_Ico)
    (fun ζ _ ↦ ((contDiff_positiveEndChart q 1).differentiable one_ne_zero
      ζ).hasFDerivAt.hasFDerivWithinAt)
    ((injOn_positiveEndChart q 0).mono (prod_mono (subset_univ _) (by norm_num))),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (hP.prod measurableSet_Ico) fun ζ hζ ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (det_fderiv_positiveEndChart_pos q ζ)]
  exact ENNReal.ofReal_le_ofReal (det_fderiv_positiveEndChart_mul_le q (hP0 ζ.1 hζ.1) (hξ ζ hζ))

end TauCeti.Floer
