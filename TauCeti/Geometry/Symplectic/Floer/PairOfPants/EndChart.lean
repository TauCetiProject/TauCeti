/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The end charts of the pair of pants in real coordinates

Integrals over the pair of pants `S = ℂ ∖ {0, 1}` are computed in the real coordinates
`ℝ × ℝ ≃ ℂ`, where the coordinate formulas of `TauCeti.Geometry.Symplectic.Floer.Energy` and
`TauCeti.Geometry.Symplectic.Floer.Pullback` live. This file transports the cylindrical end lifts
of `S` to these coordinates. The end chart `φ_q` (`TauCeti.Floer.endChart q`) is the end lift of
the end `q` in real coordinates, a holomorphic change of coordinates from the cylinder of the end
to `S`. On the strip `±s > 1/2`, `t ∈ [-1/2, 1/2)` (`TauCeti.Floer.endStrip q`) it is injective,
and it preserves orientation, so the change of variables formula applies on the images of the
three strips; these images are disjoint and measurable. Along the end chart, the pair-of-pants
perturbation pulls back to its components in the end coordinates.

## Main definitions

* `TauCeti.Floer.endChart q`: the end lift of `q` in the real coordinates `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.endStrip q`: the part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the cylinder of the end
  `q`.

## Main results

* `TauCeti.Floer.injOn_endChart`, `TauCeti.Floer.det_fderiv_endChart_nonneg`: the end chart is
  injective on the strip and preserves orientation.
* `TauCeti.Floer.pairwise_disjoint_image_endChart`: the images of the three strips are disjoint.
* `TauCeti.Floer.mem_image_endChart`: they contain every point of `S` with signed longitudinal
  coordinate greater than `1/2` on some end.
* `TauCeti.Floer.perturbationPullback_endChart`: the pullback of the pair-of-pants perturbation
  along the end chart is its component in the end coordinates.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 4, on the
  cylindrical end coordinates of a punctured Riemann surface.
-/

public section

open Set Real Function MeasureTheory Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

theorem endChart_apply (q : Puncture) (z : ℝ × ℝ) :
    endChart q z =
      Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

/-- The part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates. It
contains the support of the curvature of the end, and the end lift is injective on it. -/
noncomputable def endStrip (q : Puncture) : Set (ℝ × ℝ) :=
  {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2)

theorem endStrip_def (q : Puncture) :
    endStrip q = {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2) :=
  (rfl)

/-- A point lies in the strip of the end `q` when its signed longitudinal coordinate exceeds `1/2`
and its angular coordinate lies in `[-1/2, 1/2)`. -/
@[simp]
theorem mem_endStrip_iff {q : Puncture} {z : ℝ × ℝ} :
    z ∈ endStrip q ↔ 1 / 2 < q.endSign * z.1 ∧ z.2 ∈ Ico (-1 / 2) (1 / 2) :=
  Iff.rfl

/-- Points of the strip of an end have positive signed longitudinal coordinate. -/
theorem endSign_mul_pos_of_mem_endStrip {q : Puncture} {z : ℝ × ℝ}
    (hz : z ∈ endStrip q) : 0 < q.endSign * z.1 := by
  have h : 1 / 2 < q.endSign * z.1 := hz.1
  linarith

/-- The derivative of the end chart is multiplication by the derivative of the end lift. -/
theorem hasFDerivAt_endChart (q : Puncture) (z : ℝ × ℝ) :
    HasFDerivAt (endChart q)
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))).restrictScalars ℝ).comp
            (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z := by
  have h := ((q.hasDerivAt_cylindricalEndLift
    (Complex.equivRealProdCLM.symm z)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  exact Complex.equivRealProdCLM.hasFDerivAt.comp z
    (h.comp z Complex.equivRealProdCLM.symm.hasFDerivAt)

/-- The derivative of the end chart is multiplication by the derivative of the end lift, in real
coordinates. -/
theorem fderiv_endChart_apply (q : Puncture) (z v : ℝ × ℝ) :
    fderiv ℝ (endChart q) z v = Complex.equivRealProdCLM
      (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) *
        Complex.equivRealProdCLM.symm v) := by
  rw [(hasFDerivAt_endChart q z).fderiv]
  simp [mul_comm]

theorem contDiff_endChart (q : Puncture) (n : WithTop ℕ∞) : ContDiff ℝ n (endChart q) := by
  exact Complex.equivRealProdCLM.contDiff.comp
    (((q.contDiff_cylindricalEndLift n).restrict_scalars ℝ).comp
      Complex.equivRealProdCLM.symm.contDiff)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The pullback of the perturbation along the end chart of `q`, evaluated on a tangent vector
`v`, is its component `TauCeti.Floer.pairOfPantsEndComponent` along `v` in the end coordinates. -/
theorem perturbationPullback_endChart (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      pairOfPantsEndComponent H q (Complex.equivRealProdCLM.symm v) := by
  -- A real-linear functional `L` on `ℂ` satisfies `L w = Re w · L 1 + Im w · L i`.
  have hL (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      (Complex.equivRealProdCLM w).1 * L 1 + (Complex.equivRealProdCLM w).2 * L Complex.I =
        L w := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp
    conv_rhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp
  funext z x
  rw [perturbationPullback_apply, fderiv_endChart_apply, endChart,
    ContinuousLinearEquiv.symm_apply_apply, hL, pairOfPantsEndComponent_def]
  rfl

/-- The end lift is injective on the strip `endStrip q`, whose angular coordinate ranges over one
period. -/
theorem injOn_endChart (q : Puncture) : InjOn (endChart q) (endStrip q) := by
  intro a ha b hb hab
  have h := q.injOn_cylindricalEndLift (by simpa using ha.2) (by simpa using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- Every point of `S` where some end has signed longitudinal coordinate greater than `1/2` is the
image of a point of that end's strip. -/
theorem mem_image_endChart {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    {q : Puncture} (hq : 1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ endChart q '' endStrip q := by
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨by simpa using hq, by simpa using q.im_endCoord_mem_Ico _⟩, ?_⟩
  rw [endChart, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter hz q), ContinuousLinearEquiv.apply_symm_apply]

/-- The strip of an end is measurable. -/
theorem measurableSet_endStrip (q : Puncture) : MeasurableSet (endStrip q) := by
  rw [endStrip_def]
  exact (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).prod
    measurableSet_Ico

/-- The end charts preserve orientation. -/
theorem det_fderiv_endChart_nonneg (q : Puncture) (ζ : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (endChart q) ζ).det := by
  simp only [ContinuousLinearMap.det, LinearMap.det_finTwoProd, ContinuousLinearMap.coe_coe,
    fderiv_endChart_apply]
  simp only [Complex.equivRealProdCLM_symm_apply, Complex.equivRealProdCLM_apply,
    Complex.mul_re, Complex.mul_im]
  norm_num
  nlinarith [sq_nonneg (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm ζ)).re,
    sq_nonneg (deriv q.cylindricalEndLift (Complex.equivRealProdCLM.symm ζ)).im]

/-- The three end strips have disjoint images. -/
theorem pairwise_disjoint_image_endChart :
    Pairwise (Disjoint on fun q ↦ endChart q '' endStrip q) := by
  intro q r hqr
  refine Set.disjoint_left.2 ?_
  rintro z ⟨ζ, hζ, rfl⟩ ⟨ζ', hζ', h⟩
  rw [endChart_apply, endChart_apply] at h
  refine cylindricalEndLift_ne_cylindricalEndLift hqr ?_ ?_
    (Complex.equivRealProdCLM.injective h).symm
  · simpa using endSign_mul_pos_of_mem_endStrip hζ
  · simpa using endSign_mul_pos_of_mem_endStrip hζ'

end Floer

end TauCeti
