/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Real charts on the cylindrical ends of the pair of pants

Integrals of Floer data over the thrice-punctured sphere `S = ℂ ∖ {0, 1}` are computed end by
end, in the cylinder coordinates `(s, t)` of each end. This file packages the end lift
`TauCeti.ThricePuncturedSphere.Puncture.cylindricalEndLift` as a map of `ℝ × ℝ`, the end chart
`TauCeti.ThricePuncturedSphere.Puncture.endChart`, so that the change of variables formula and the
pullback of perturbation data `TauCeti.Floer.perturbationPullback` apply to it.

* `Puncture.endChart q` is `C^n` (`Puncture.contDiff_endChart`), its derivative is multiplication
  by the complex derivative of the end lift (`Puncture.fderiv_endChart_apply`), and it preserves
  orientation (`Puncture.det_fderiv_endChart_nonneg`).
* On the strip `Puncture.endStrip q` of points with `±s > 1/2` and `t ∈ [-1/2, 1/2)` it is
  injective (`Puncture.injOn_endChart`), and every point of `S` with `±s > 1/2` on the end `q` is
  the image of a point of this strip (`Puncture.mem_image_endChart`).
* A cutoff `β(±s - c)` or `β(c - ±s)` along an end, for the smooth transition `β`, has total
  variation one (`Puncture.lintegral_ofReal_deriv_smoothTransition_endSign_mul_sub`,
  `Puncture.lintegral_ofReal_deriv_smoothTransition_sub_endSign_mul`). This is the curvature
  allowance of a transition collar of Floer perturbation data.
* For a perturbation one-form `K` on `ℂ`, written in the global coordinate `z = s + i t` by its
  values on `1` and `i`, the pullback along the end chart is `K` evaluated on the image under the
  end lift of a tangent vector of the cylinder (`TauCeti.Floer.perturbationPullback_endChart`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 4, on
  cylindrical end coordinates of punctured Riemann surfaces.
-/

public noncomputable section

open Set Real MeasureTheory

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

theorem endChart_def (q : Puncture) (z : ℝ × ℝ) :
    q.endChart z =
      Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

/-- In complex coordinates the end chart is the end lift. -/
@[simp]
theorem equivRealProdCLM_symm_endChart (q : Puncture) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (q.endChart z) =
      q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_def, ContinuousLinearEquiv.symm_apply_apply]

/-- The part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates. The end
lift is injective on it, and it covers the part `±s > 1/2` of the end. -/
def endStrip (q : Puncture) : Set (ℝ × ℝ) :=
  {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2)

theorem endStrip_def (q : Puncture) :
    q.endStrip = {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2) :=
  (rfl)

theorem mem_endStrip {q : Puncture} {z : ℝ × ℝ} :
    z ∈ q.endStrip ↔ 1 / 2 < q.endSign * z.1 ∧ z.2 ∈ Ico (-1 / 2 : ℝ) (1 / 2) :=
  Iff.rfl

theorem measurableSet_endStrip (q : Puncture) : MeasurableSet q.endStrip :=
  (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).prod measurableSet_Ico

theorem endSign_mul_pos_of_mem_endStrip {q : Puncture} {z : ℝ × ℝ}
    (hz : z ∈ q.endStrip) : 0 < q.endSign * z.1 := by
  have h : 1 / 2 < q.endSign * z.1 := hz.1
  linarith

/-- The derivative of the end chart is multiplication by the derivative of the end lift. -/
theorem hasFDerivAt_endChart (q : Puncture) (z : ℝ × ℝ) :
    HasFDerivAt q.endChart
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))).restrictScalars ℝ).comp
            (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z := by
  have h := ((q.hasDerivAt_cylindricalEndLift
    (Complex.equivRealProdCLM.symm z)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  exact Complex.equivRealProdCLM.hasFDerivAt.comp z
    (h.comp z Complex.equivRealProdCLM.symm.hasFDerivAt)

theorem fderiv_endChart_apply (q : Puncture) (z v : ℝ × ℝ) :
    fderiv ℝ q.endChart z v = Complex.equivRealProdCLM
      (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
        Complex.equivRealProdCLM.symm v) := by
  rw [(hasFDerivAt_endChart q z).fderiv]
  simp [mul_comm]

theorem contDiff_endChart (q : Puncture) {n : WithTop ℕ∞} : ContDiff ℝ n q.endChart :=
  Complex.equivRealProdCLM.contDiff.comp
    (((q.contDiff_cylindricalEndLift n).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff)

/-- The end chart is holomorphic, so it preserves orientation. -/
theorem det_fderiv_endChart_nonneg (q : Puncture) (z : ℝ × ℝ) :
    0 ≤ (fderiv ℝ q.endChart z).det := by
  rw [(hasFDerivAt_endChart q z).fderiv]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_nonneg]

/-- The end chart sends the part `±s > 0` of the end into `S`. -/
theorem endChart_mem_puncturedSphere (q : Puncture) {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) :
    Complex.equivRealProdCLM.symm (q.endChart z) ≠ 0 ∧
      Complex.equivRealProdCLM.symm (q.endChart z) ≠ 1 := by
  rw [equivRealProdCLM_symm_endChart]
  exact cylindricalEndLift_ne_zero_and_ne_one q (by simpa using hz)

/-- The longitudinal coordinate of the end `q` at the image of `(s, t)` is `s`. -/
theorem re_endCoord_endChart (q : Puncture) (z : ℝ × ℝ) :
    (q.endCoord (Complex.equivRealProdCLM.symm (q.endChart z))).re = z.1 := by
  obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift (Complex.equivRealProdCLM.symm z)
  rw [equivRealProdCLM_symm_endChart, hk]
  simp

/-- The end chart is injective on the strip `endStrip q`, whose angular coordinate ranges over
one period. -/
theorem injOn_endChart (q : Puncture) : InjOn q.endChart q.endStrip := by
  intro a ha b hb hab
  have h := q.injOn_cylindricalEndLift (by simpa using ha.2) (by simpa using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- Every point other than the center of the end `q` at which its signed longitudinal coordinate
is greater than `1/2` is the image of a point of the strip of `q`. -/
theorem mem_image_endChart {q : Puncture} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (hq : 1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ q.endChart '' q.endStrip := by
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨by simpa using hq, by simpa using q.im_endCoord_mem_Ico _⟩, ?_⟩
  rw [endChart_def, ContinuousLinearEquiv.symm_apply_apply, q.cylindricalEndLift_endCoord hz,
    ContinuousLinearEquiv.apply_symm_apply]

/-- A cutoff `β(±s - c)` rising along the end `q` has total increase one. -/
theorem lintegral_ofReal_deriv_smoothTransition_endSign_mul_sub (q : Puncture) (c : ℝ) :
    ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (q.endSign * s - c)) = 1 := by
  have h₁ : ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (s - c)) = 1 := by
    rw [lintegral_sub_right_eq_self (fun s ↦ ENNReal.ofReal (deriv smoothTransition s)) c,
      ← ofReal_integral_eq_lintegral_ofReal smoothTransition.integrable_deriv
        (ae_of_all _ fun _ ↦ smoothTransition.monotone.deriv_nonneg),
      smoothTransition.integral_deriv, ENNReal.ofReal_one]
  cases q
  · simpa using h₁
  · simpa using h₁
  · convert smoothTransition.lintegral_ofReal_mul_deriv (-c) one_pos using 4 with s
    simp only [endSign_inf, one_mul]
    ring_nf

/-- A cutoff `β(c - ±s)` falling along the end `q` has total decrease one. -/
theorem lintegral_ofReal_deriv_smoothTransition_sub_endSign_mul (q : Puncture) (c : ℝ) :
    ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (c - q.endSign * s)) = 1 := by
  have h₁ : ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (c - s)) = 1 := by
    simpa using smoothTransition.lintegral_ofReal_mul_deriv c one_pos
  cases q
  · simpa using h₁
  · simpa using h₁
  · convert lintegral_ofReal_deriv_smoothTransition_endSign_mul_sub zero (-c) using 4 with s
    simp only [endSign_inf, endSign_zero]
    ring_nf

end TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

open TauCeti.ThricePuncturedSphere

variable {X : Type*}

/-- **Perturbation data in end coordinates.** Let `K` be a perturbation one-form on `ℂ`, with
`ds` and `dt` components `K(z)(1)` and `K(z)(i)` in the global coordinate `z = s + i t`. Its
pullback along the end chart of `q`, evaluated on a tangent vector `v` of the cylinder, is `K` at
the image point evaluated on the image `φ'(z) v` of `v` under the end lift `φ`. -/
theorem perturbationPullback_endChart (K : ℂ → X → ℂ →L[ℝ] ℝ) (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback q.endChart
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      fun z x ↦ K (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) x
        (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
          Complex.equivRealProdCLM.symm v) := by
  -- A real-linear functional `L` on `ℂ` satisfies `L w = Re w · L 1 + Im w · L i`.
  have hL (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      (Complex.equivRealProdCLM w).1 * L 1 + (Complex.equivRealProdCLM w).2 * L Complex.I =
        L w := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp
    conv_rhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp
  funext z x
  rw [perturbationPullback_apply, Puncture.fderiv_endChart_apply,
    Puncture.equivRealProdCLM_symm_endChart, hL]

end TauCeti.Floer
