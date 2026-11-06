/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The pair of pants and its end charts in real coordinates

Integrals over the pair of pants `S = ℂ ∖ {0, 1}` are computed in the real coordinates
`ℝ × ℝ ≃ ℂ`, where the coordinate formulas of `TauCeti.Geometry.Symplectic.Floer.Energy` and
`TauCeti.Geometry.Symplectic.Floer.Pullback` live. This file transports `S`
(`TauCeti.Floer.thricePuncturedSphereReal`), the pair-of-pants perturbation and the cylindrical
end lifts of `S` to these coordinates. The end chart `φ_q` (`TauCeti.Floer.endChart q`) is the end
lift of the end `q` in real coordinates, a holomorphic change of coordinates from the cylinder of
the end to `S`. On the strip `±s > 1/2`, `t ∈ [-1/2, 1/2)` (`TauCeti.Floer.endStrip q`) it is
injective, and it preserves orientation, so the change of variables formula applies on the images
of the three strips; these images are disjoint and measurable. Along the end chart, the
pair-of-pants perturbation pulls back to its components in the end coordinates.

## Main definitions

* `TauCeti.Floer.thricePuncturedSphereReal`: the pair of pants `S` in the real coordinates
  `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.endChart q`: the end lift of `q` in the real coordinates `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.endStrip q`: the part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the cylinder of the end
  `q`.

## Main results

* `TauCeti.Floer.contDiffAt_uncurry_pairOfPantsPerturbation`: in real coordinates, the
  components of the perturbation are `Cⁿ` on `S × V` for `Cⁿ` Hamiltonians.
* `TauCeti.Floer.endChart_mem_thricePuncturedSphereReal`, `TauCeti.Floer.re_endCoord_endChart`:
  the end chart sends the part `±s > 0` of the end into `S` and preserves the longitudinal
  coordinate.
* `TauCeti.Floer.injOn_endChart`, `TauCeti.Floer.det_fderiv_endChart_nonneg`,
  `TauCeti.Floer.det_fderiv_endChart_pos`: the end chart is injective on the strip, preserves
  orientation and is a local diffeomorphism.
* `TauCeti.Floer.pairwise_disjoint_image_endChart`: the images of the three strips are disjoint.
* `TauCeti.Floer.mem_image_endChart`: they contain every point of `S` with signed longitudinal
  coordinate greater than `1/2` on some end.
* `TauCeti.Floer.lintegral_le_sum_setLIntegral_image_endChart`: a function on `S` vanishing
  wherever every signed longitudinal coordinate is at most `1/2` has integral at most the sum of
  its integrals over the images of the three strips.
* `TauCeti.Floer.perturbationPullback_endChart_eq`: the pullback of a datum on `ℂ` along the end
  chart is its evaluation at the end lift; `TauCeti.Floer.perturbationPullback_endChart` is the
  case of the pair-of-pants perturbation, whose pullback is its component in the end coordinates.

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

/-- The pair of pants `S = ℂ ∖ {0, 1}`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
@[expose] def thricePuncturedSphereReal : Set (ℝ × ℝ) :=
  {z | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1}

/-- A point lies in `S` when, as a complex number, it is neither `0` nor `1`. -/
@[simp]
theorem mem_thricePuncturedSphereReal_iff {z : ℝ × ℝ} :
    z ∈ thricePuncturedSphereReal ↔
      Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1 :=
  Iff.rfl

/-- The pair of pants is open in real coordinates. -/
theorem isOpen_thricePuncturedSphereReal : IsOpen thricePuncturedSphereReal :=
  (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
    (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)

/-- In the real coordinates of `S`, the components of the pair-of-pants perturbation are `Cⁿ`
jointly in the domain and target points, for `Cⁿ` Hamiltonians. -/
theorem contDiffAt_uncurry_pairOfPantsPerturbation {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ n (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    ContDiffAt ℝ n
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (z, x) :=
  ((contDiffAt_pairOfPantsPerturbation_prod hH hHs hz x).comp
    (f := fun p : (ℝ × ℝ) × V ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x)
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).clm_apply contDiffAt_const

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

theorem endChart_apply (q : Puncture) (z : ℝ × ℝ) :
    endChart q z =
      Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

/-- In complex coordinates the end chart is the end lift. -/
@[simp]
theorem equivRealProdCLM_symm_endChart (q : Puncture) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (endChart q z) =
      q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The longitudinal coordinate of the end `q` at the image of `(s, t)` is `s`. -/
theorem re_endCoord_endChart (q : Puncture) (z : ℝ × ℝ) :
    (q.endCoord (Complex.equivRealProdCLM.symm (endChart q z))).re = z.1 := by
  obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift (Complex.equivRealProdCLM.symm z)
  rw [equivRealProdCLM_symm_endChart, hk]
  simp

/-- The end chart sends the part `±s > 0` of the end into `S`. -/
theorem endChart_mem_thricePuncturedSphereReal {q : Puncture} {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) :
    endChart q z ∈ thricePuncturedSphereReal := by
  rw [mem_thricePuncturedSphereReal_iff, equivRealProdCLM_symm_endChart]
  exact cylindricalEndLift_ne_zero_and_ne_one q (by simpa using hz)

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
/-- The pullback along the end chart of `q` of the components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` of a covector-valued datum `K` on `ℂ`, evaluated on a tangent vector `v`, is
`K` at the end lift evaluated on the image `φ'(z) v` of `v`. -/
theorem perturbationPullback_endChart_eq (K : ℂ → V → ℂ →L[ℝ] ℝ) (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      fun z x ↦ K (q.cylindricalEndLift ⟨z.1, z.2⟩) x
        (deriv q.cylindricalEndLift ⟨z.1, z.2⟩ * Complex.equivRealProdCLM.symm v) := by
  -- A real-linear functional `L` on `ℂ` satisfies `L w = Re w · L 1 + Im w · L i`.
  have hL (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      (Complex.equivRealProdCLM w).1 * L 1 + (Complex.equivRealProdCLM w).2 * L Complex.I =
        L w := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp
    conv_rhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp
  funext z x
  rw [perturbationPullback_apply, fderiv_endChart_apply, equivRealProdCLM_symm_endChart, hL]
  -- `Complex.equivRealProdCLM.symm z` is the complex number `⟨z.1, z.2⟩` by definition.
  rfl

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The pullback of the perturbation along the end chart of `q`, evaluated on a tangent vector
`v`, is its component `TauCeti.Floer.pairOfPantsEndComponent` along `v` in the end coordinates. -/
theorem perturbationPullback_endChart (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      pairOfPantsEndComponent H q (Complex.equivRealProdCLM.symm v) := by
  funext z x
  rw [perturbationPullback_endChart_eq, pairOfPantsEndComponent_def]

/-- The end lift is injective on the strip `endStrip q`, whose angular coordinate ranges over one
period. -/
theorem injOn_endChart (q : Puncture) : InjOn (endChart q) (endStrip q) := by
  intro a ha b hb hab
  have h := q.injOn_cylindricalEndLift (by simpa using ha.2) (by simpa using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- Every point of `S` where some end has signed longitudinal coordinate greater than `1/2` is the
image of a point of that end's strip. -/
theorem mem_image_endChart {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    {q : Puncture} (hq : 1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ endChart q '' endStrip q := by
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨by simpa using hq, by simpa using q.im_endCoord_mem_Ico _⟩, ?_⟩
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q),
    ContinuousLinearEquiv.apply_symm_apply]

/-- The strip of an end is measurable. -/
theorem measurableSet_endStrip (q : Puncture) : MeasurableSet (endStrip q) := by
  rw [endStrip_def]
  exact (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).prod
    measurableSet_Ico

/-- The end charts preserve orientation. -/
theorem det_fderiv_endChart_nonneg (q : Puncture) (ζ : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (endChart q) ζ).det := by
  -- The derivative is multiplication by a complex number `c`, whose real determinant is the
  -- complex norm `|c|²`.
  rw [(hasFDerivAt_endChart q ζ).fderiv]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_nonneg]

/-- The end charts are local diffeomorphisms: their Jacobian determinants are positive. -/
theorem det_fderiv_endChart_pos (q : Puncture) (ζ : ℝ × ℝ) :
    0 < (fderiv ℝ (endChart q) ζ).det := by
  rw [(hasFDerivAt_endChart q ζ).fderiv]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_pos, q.deriv_cylindricalEndLift_ne_zero]

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

/-- A function on the plane vanishing at every point of `S` where the signed longitudinal
coordinate of every end is at most `1/2` has integral at most the sum of its integrals over the
images of the three strips: off the two punctures, a null set, it is supported in these images. -/
theorem lintegral_le_sum_setLIntegral_image_endChart {f : ℝ × ℝ → ENNReal}
    (hf : ∀ z ∈ thricePuncturedSphereReal,
      (∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1 / 2) →
        f z = 0) :
    ∫⁻ z, f z ≤ ∑ q, ∫⁻ z in endChart q '' endStrip q, f z := by
  set N : Set (ℝ × ℝ) := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1}
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  have hsupp : support f ⊆ (⋃ q, endChart q '' endStrip q) ∪ N := by
    intro z hz
    by_cases h₀ : Complex.equivRealProdCLM.symm z = 0
    · exact Or.inr (Or.inl ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₀)))
    by_cases h₁ : Complex.equivRealProdCLM.symm z = 1
    · exact Or.inr (Or.inr ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₁)))
    have hS : z ∈ thricePuncturedSphereReal := mem_thricePuncturedSphereReal_iff.2 ⟨h₀, h₁⟩
    by_cases hq : ∃ q : Puncture,
        1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
    · obtain ⟨q, hq⟩ := hq
      exact Or.inl (mem_iUnion.2 ⟨q, mem_image_endChart hS hq⟩)
    · simp only [not_exists, not_lt] at hq
      exact absurd (hf z hS hq) hz
  calc _ = ∫⁻ z in (⋃ q, endChart q '' endStrip q) ∪ N, f z :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ = _ := tsum_fintype _

end Floer

end TauCeti
