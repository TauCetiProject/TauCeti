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
* `TauCeti.Floer.signedEndChart q`: the end chart precomposed with `ζ ↦ ±ζ`, whose longitudinal
  coordinate tends to `+∞` towards the puncture on every end.

## Main results

* `TauCeti.Floer.contDiffAt_uncurry_pairOfPantsPerturbation`,
  `TauCeti.Floer.differentiableAt_pairOfPantsPerturbation`: in real coordinates, the
  components of the perturbation are `Cⁿ` on `S × V` for `Cⁿ` Hamiltonians, and in particular
  differentiable in the target point for `C¹` Hamiltonians.
* `TauCeti.Floer.endChart_mem_thricePuncturedSphereReal`, `TauCeti.Floer.re_endCoord_endChart`:
  the end chart sends the part `±s > 0` of the end into `S` and preserves the longitudinal
  coordinate.
* `TauCeti.Floer.injOn_endChart`, `TauCeti.Floer.det_fderiv_endChart_nonneg`,
  `TauCeti.Floer.det_fderiv_endChart_pos`: the end chart is injective on the strip, preserves
  orientation and is a local diffeomorphism.
* `TauCeti.Floer.isComplexLinearMap_fderiv_endChart`: the end chart is holomorphic.
* `TauCeti.Floer.pairwise_disjoint_image_endChart`: the images of the three strips are disjoint.
* `TauCeti.Floer.mem_image_endChart`: they contain every point of `S` with signed longitudinal
  coordinate greater than `1/2` on some end.
* `TauCeti.Floer.injOn_endChart_univ_prod_Ico`: the end chart is injective on every band of
  angular width one.
* `TauCeti.Floer.perturbationPullback_endChart_eq_cylindricalEndLift`: the pullback of a
  perturbation along the end chart is the perturbation evaluated on the image of a tangent vector
  under the end lift.
* `TauCeti.Floer.perturbationPullback_endChart`: the pullback of the pair-of-pants perturbation
  along the end chart is its component in the end coordinates.
* `TauCeti.Floer.isComplexLinearMap_fderiv_signedEndChart`,
  `TauCeti.Floer.injOn_signedEndChart`, `TauCeti.Floer.perturbationPullback_signedEndChart`: the
  signed end chart is holomorphic and injective on every band of angular width one, and on the
  half-cylinder `s ≥ 2` the pair-of-pants perturbation pulls back to the cylindrical datum
  `±H_q(±t) dt`.

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

/-- In the real coordinates of `S`, the components of the pair-of-pants perturbation are
differentiable in the target point, for `C¹` Hamiltonians. -/
theorem differentiableAt_pairOfPantsPerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)
      x :=
  ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).differentiableAt
    one_ne_zero).comp _ ((differentiableAt_const _).prodMk differentiableAt_id)

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

theorem endChart_apply (q : Puncture) (z : ℝ × ℝ) :
    endChart q z =
      Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

/-- The end chart at a point `(s, t)` of the cylinder is the end lift at `s + i t`. -/
theorem endChart_mk (q : Puncture) (s t : ℝ) :
    endChart q (s, t) = Complex.equivRealProdCLM (q.cylindricalEndLift (↑s + ↑t * Complex.I)) := by
  simp [endChart_apply, Complex.equivRealProdCLM_symm_apply]

/-- In complex coordinates the end chart is the end lift. -/
@[simp]
theorem equivRealProdCLM_symm_endChart (q : Puncture) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (endChart q z) =
      q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The longitudinal coordinate of the end `q` at the image of `(s, t)` is `s`. -/
theorem re_endCoord_endChart (q : Puncture) (z : ℝ × ℝ) :
    (q.endCoord (Complex.equivRealProdCLM.symm (endChart q z))).re = z.1 := by
  rw [equivRealProdCLM_symm_endChart, re_endCoord_cylindricalEndLift]
  simp [Complex.equivRealProdCLM_symm_apply]

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

/-- **Perturbation data in end coordinates.** Let `K` be a perturbation one-form on `ℂ`, with
`ds` and `dt` components `K(z)(1)` and `K(z)(i)` in the global coordinate `z = s + i t`. Its
pullback along the end chart of `q`, evaluated on a tangent vector `v` of the cylinder, is `K` at
the image point evaluated on the image `φ'(z) v` of `v` under the end lift `φ`. -/
theorem perturbationPullback_endChart_eq_cylindricalEndLift {X : Type*}
    (K : ℂ → X → ℂ →L[ℝ] ℝ) (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
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
  rw [perturbationPullback_apply, fderiv_endChart_apply, equivRealProdCLM_symm_endChart, hL]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The pullback of the perturbation along the end chart of `q`, evaluated on a tangent vector
`v`, is its component `TauCeti.Floer.pairOfPantsEndComponent` along `v` in the end coordinates. -/
theorem perturbationPullback_endChart (q : Puncture) (v : ℝ × ℝ) :
    perturbationPullback (endChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      pairOfPantsEndComponent H q (Complex.equivRealProdCLM.symm v) := by
  rw [perturbationPullback_endChart_eq_cylindricalEndLift (pairOfPantsPerturbation H)]
  funext z x
  rw [pairOfPantsEndComponent_def, Complex.equivRealProdCLM_symm_apply, ← Complex.mk_eq_add_mul_I]

/-- The end chart is injective on every band `ℝ × [t₀, t₀ + 1)` of angular width one: two points
with the same image differ by an integer multiple of `i`. -/
theorem injOn_endChart_univ_prod_Ico (q : Puncture) (t₀ : ℝ) :
    InjOn (endChart q) (univ ×ˢ Ico t₀ (t₀ + 1)) := by
  intro a ha b hb hab
  have h := q.injOn_cylindricalEndLift t₀ (by simpa using ha.2) (by simpa using hb.2)
    (Complex.equivRealProdCLM.injective hab)
  exact Complex.equivRealProdCLM.symm.injective h

/-- The end lift is injective on the strip `endStrip q`, whose angular coordinate ranges over one
period. -/
theorem injOn_endChart (q : Puncture) : InjOn (endChart q) (endStrip q) :=
  (injOn_endChart_univ_prod_Ico q (-1 / 2)).mono (prod_mono (subset_univ _) (by norm_num))

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

/-- The end charts are holomorphic: their derivatives are complex linear for the standard complex
structure `(v₁, v₂) ↦ (-v₂, v₁)` of `ℝ × ℝ`. -/
theorem isComplexLinearMap_fderiv_endChart (q : Puncture) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (endChart q) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, fderiv_endChart_apply,
    AlmostComplexStructure.product_apply]
  apply Prod.ext <;> simp [Complex.equivRealProdCLM_symm_apply] <;> ring

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

/-- The end loops `t ↦ u(φ_q(R + i t))` of a map on the pair of pants are `1`-periodic. -/
theorem periodic_endLoop {α : Type*} (u : ℝ × ℝ → α) (q : Puncture) (R : ℝ) :
    Periodic (fun t : ℝ ↦ u (Complex.equivRealProdCLM (q.cylindricalEndLift (↑R + ↑t * Complex.I))))
      1 := fun t ↦
  congrArg (fun w ↦ u (Complex.equivRealProdCLM w)) (q.periodic_cylindricalEndLift R t)

/-- The end chart of `q` precomposed with `ζ ↦ ±ζ`, the sign being that of the end. Unlike
`endChart q`, its longitudinal coordinate tends to `+∞` towards the puncture on the output end as
well as on the inputs. -/
noncomputable def signedEndChart (q : Puncture) : ℝ × ℝ → ℝ × ℝ :=
  endChart q ∘ fun ζ ↦ q.endSign • ζ

theorem signedEndChart_apply (q : Puncture) (ζ : ℝ × ℝ) :
    signedEndChart q ζ = endChart q (q.endSign • ζ) :=
  (rfl)

/-- The signed end chart in coordinates: `(s, t) ↦ φ_q(±s ± i t)`. -/
theorem signedEndChart_mk (q : Puncture) (s t : ℝ) :
    signedEndChart q (s, t) = endChart q (q.endSign * s, q.endSign * t) := by
  simp [signedEndChart]

private theorem endSign_mul_fst_smul (q : Puncture) (ζ : ℝ × ℝ) :
    q.endSign * (q.endSign • ζ).1 = ζ.1 := by
  simp

/-- The derivative of the signed end chart is `±` that of the end chart at `±ζ`. -/
theorem hasFDerivAt_signedEndChart (q : Puncture) (ζ : ℝ × ℝ) :
    HasFDerivAt (signedEndChart q) (q.endSign • fderiv ℝ (endChart q) (q.endSign • ζ)) ζ := by
  have h := ((contDiff_endChart q 1).differentiable one_ne_zero (q.endSign • ζ)).hasFDerivAt.comp ζ
    ((hasFDerivAt_id ζ).const_smul q.endSign)
  rwa [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] at h

/-- The signed end charts are smooth. -/
theorem contDiff_signedEndChart (q : Puncture) (n : WithTop ℕ∞) :
    ContDiff ℝ n (signedEndChart q) :=
  (contDiff_endChart q n).comp (contDiff_const_smul _)

/-- The signed end charts preserve orientation. -/
theorem det_fderiv_signedEndChart_nonneg (q : Puncture) (ζ : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (signedEndChart q) ζ).det := by
  rw [(hasFDerivAt_signedEndChart q ζ).fderiv, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
  exact mul_nonneg (by simp [Module.finrank_prod, sq_nonneg]) (det_fderiv_endChart_nonneg q _)

/-- The signed end charts are holomorphic. -/
theorem isComplexLinearMap_fderiv_signedEndChart (q : Puncture) (ζ : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (signedEndChart q) ζ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [(hasFDerivAt_signedEndChart q ζ).fderiv, ContinuousLinearMap.toLinearMap_smul]
  exact (isComplexLinearMap_fderiv_endChart q _).smul _

/-- The signed end chart sends the half-cylinder `s > 0` into `S`. -/
theorem signedEndChart_mem_thricePuncturedSphereReal {q : Puncture} {ζ : ℝ × ℝ}
    (hζ : 0 < ζ.1) : signedEndChart q ζ ∈ thricePuncturedSphereReal :=
  endChart_mem_thricePuncturedSphereReal (by rwa [endSign_mul_fst_smul])

/-- The signed end chart is injective on every band `t ∈ [t₀, t₀ + 1)` of angular width one. -/
theorem injOn_signedEndChart (q : Puncture) (t₀ : ℝ) :
    InjOn (signedEndChart q) (univ ×ˢ Ico t₀ (t₀ + 1)) := by
  intro a ha b hb hab
  -- The angular coordinates of `±a` and `±b` differ by less than one period.
  have hlt : |(q.endSign • a).2 - (q.endSign • b).2| < 1 := by
    rw [Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul, abs_endSign,
      one_mul, abs_sub_lt_iff]
    constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  obtain ⟨h₁, h₂⟩ := abs_sub_lt_iff.1 hlt
  -- So both lie in the band of angular width one starting at the smaller of them.
  have hband (c : ℝ) (hc : c - (q.endSign • a).2 < 1) (hc' : c - (q.endSign • b).2 < 1) :
      c < min (q.endSign • a).2 (q.endSign • b).2 + 1 := by
    rw [← min_add_add_right]
    exact lt_min (by linarith) (by linarith)
  have h := injOn_endChart_univ_prod_Ico q (min (q.endSign • a).2 (q.endSign • b).2)
    ⟨mem_univ _, min_le_left _ _, hband _ (by simp) (by linarith)⟩
    ⟨mem_univ _, min_le_right _ _, hband _ (by linarith) (by simp)⟩ hab
  exact smul_right_injective _ (endSign_ne_zero q) h

/-- On the part `s ≥ 2` of the signed end chart, the pair-of-pants perturbation pulls back to the
cylindrical datum `±H_q(±t) dt`. -/
theorem perturbationPullback_signedEndChart {X : Type*} {H : Puncture → ℝ → X → ℝ}
    (hH : ∀ q, Periodic (H q) 1) {q : Puncture} {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) :
    perturbationPullback (signedEndChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal ζ = (fun _ ↦ 0) ∧
      perturbationPullback (signedEndChart q)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag ζ = fun x ↦ q.endSign * H q (q.endSign * ζ.2) x := by
  have hpos : 0 < q.endSign * (q.endSign • ζ).1 := by
    rw [endSign_mul_fst_smul]
    linarith
  have hd : DifferentiableAt ℝ (endChart q) (q.endSign • ζ) :=
    (contDiff_endChart q 1).differentiable one_ne_zero _
  have hψ : DifferentiableAt ℝ (fun ζ : ℝ × ℝ ↦ q.endSign • ζ) ζ :=
    ((hasFDerivAt_id ζ).const_smul q.endSign).differentiableAt
  have hcomp (v : ℝ × ℝ) : perturbationPullback (signedEndChart q)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v ζ =
        perturbationPullback (fun ζ : ℝ × ℝ ↦ q.endSign • ζ)
          (pairOfPantsEndComponent H q (Complex.equivRealProdCLM.symm stdComplexLineReal))
          (pairOfPantsEndComponent H q (Complex.equivRealProdCLM.symm stdComplexLineImag)) v ζ := by
    rw [← perturbationPullback_endChart, ← perturbationPullback_endChart]
    exact perturbationPullback_comp _ _ hd hψ v
  have hfd : fderiv ℝ (fun ζ : ℝ × ℝ ↦ q.endSign • ζ) ζ = q.endSign • ContinuousLinearMap.id ℝ _ :=
    ((hasFDerivAt_id ζ).const_smul q.endSign).fderiv
  refine ⟨?_, ?_⟩ <;> rw [hcomp] <;> funext x <;>
    simp only [perturbationPullback_apply, hfd, equivRealProdCLM_symm_stdComplexLineReal,
      equivRealProdCLM_symm_stdComplexLineImag, pairOfPantsEndComponent_one_of_pos (hH q) hpos,
      pairOfPantsEndComponent_I_of_pos (hH q) hpos, endSign_mul_fst_smul,
      smoothTransition.one_of_one_le (show 1 ≤ ζ.1 - 1 by linarith)] <;>
    simp [stdComplexLineReal_eq, stdComplexLineImag_eq]

end Floer

end TauCeti
