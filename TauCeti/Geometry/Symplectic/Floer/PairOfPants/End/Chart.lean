/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.Complex.ThricePuncturedSphere.End.Shift
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Normed.Module.Connected

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

On the input ends `0`, `1` the end coordinate `s` tends to `+∞`, on the output end `∞` to `-∞`.
The positive end chart `φ'_q(s, t) = φ_q(±s, ±t)` (`TauCeti.Floer.positiveEndChart q`), with the
sign of the end, reads every end as a positive end; it is again holomorphic, orientation
preserving and `1`-periodic in `t`. Where a perturbation is `H_q(t) dt` on the end `q`, it pulls
back along `φ'_q` to `H'_q(t) dt` for the Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`), so that results about positive Floer half-cylinders
apply to all three ends.

## Main definitions

* `TauCeti.Floer.thricePuncturedSphereReal`: the pair of pants `S` in the real coordinates
  `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.endChart q`: the end lift of `q` in the real coordinates `ℝ × ℝ ≃ ℂ`.
* `TauCeti.Floer.endStrip q`: the part `±s > 1/2`, `t ∈ [-1/2, 1/2)` of the cylinder of the end
  `q`.
* `TauCeti.Floer.positiveEndChart q`: the end chart of `q` read as a positive end.
* `TauCeti.Floer.positiveEndCoord q`: the coordinates of a point in the positive end chart of `q`.
* `TauCeti.Floer.positiveEndHamiltonian H q`: the end Hamiltonian in the positive end chart.

## Main results

* `TauCeti.Floer.continuousAt_endSign_mul_re_endCoord`,
  `TauCeti.Floer.isOpen_endSign_mul_re_endCoord_lt`: in real coordinates the signed longitudinal
  coordinate of an end is continuous away from its center, and the part of `S` where it is less
  than a bound is open.
* `TauCeti.Floer.lt_fst_positiveEndCoord_inf_iff`: away from `0`, the output end lies beyond `r`
  exactly off the disc `‖w‖ ≤ 2 exp (2πr)`; so beyond the height `1` it lies off the disc
  `‖w‖ ≤ 8` (`TauCeti.Floer.eight_lt_norm_of_one_lt_fst_positiveEndCoord_inf`), and off the disc
  `‖w‖ ≤ 2` it lies in `S` (`TauCeti.Floer.mem_thricePuncturedSphereReal_of_two_le_norm`) and in
  the image of the band `(0, ∞) × [0, 1)` under its positive end chart
  (`TauCeti.Floer.mem_image_positiveEndChart_inf_of_two_lt_norm`).
* `TauCeti.Floer.isCompact_preimage_truncation`,
  `TauCeti.Floer.preimage_truncation_subset_thricePuncturedSphereReal`,
  `TauCeti.Floer.exists_lt_fst_positiveEndCoord_of_notMem_truncation`: in real coordinates the
  truncation `S_R` is compact and lies in `S`, and every other point of `S` lies beyond `R` on some
  end.
* `TauCeti.Floer.subset_preimage_truncation_of_isOpen`: an open set on which every signed
  longitudinal coordinate is at most `R` lies in `S_R`.
* `TauCeti.Floer.setIntegral_thricePuncturedSphereReal_eq_setIntegral_truncation`: the integral over
  `S` of a function vanishing beyond `R` on every end is its integral over `S_R`.
* `TauCeti.Floer.contDiffAt_uncurry_pairOfPantsPerturbation`,
  `TauCeti.Floer.contDiffOn_uncurry_pairOfPantsPerturbation`,
  `TauCeti.Floer.differentiableAt_pairOfPantsPerturbation_target`: in real coordinates, the
  components of the perturbation are `Cⁿ` on `S × V` for `Cⁿ` Hamiltonians, and in particular
  differentiable in the target point for `C¹` Hamiltonians.
* `TauCeti.Floer.contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt`: a datum
  which is `C¹` on `S × M` has `C¹` components in the real coordinates of `S`.
* `TauCeti.Floer.contMDiffAt_uncurry_pairOfPantsPerturbation`: in real coordinates, the components
  of the perturbation are `Cⁿ` on `S × M` for `Cⁿ` Hamiltonians on a manifold.
* `TauCeti.Floer.differentiableAt_pairOfPantsPerturbation_domain`,
  `TauCeti.Floer.mdifferentiableAt_pairOfPantsPerturbation_target`: for `C¹` Hamiltonians on a
  manifold, the components of the perturbation are differentiable at points of `S` in the domain
  and in the target point separately.
* `TauCeti.Floer.endChart_mem_thricePuncturedSphereReal`, `TauCeti.Floer.re_endCoord_endChart`:
  the end chart sends the part `±s > 0` of the end into `S` and preserves the longitudinal
  coordinate.
* `TauCeti.Floer.injOn_endChart`, `TauCeti.Floer.det_fderiv_endChart_nonneg`,
  `TauCeti.Floer.det_fderiv_endChart_pos`: the end chart is injective on the strip, preserves
  orientation and is a local diffeomorphism.
* `TauCeti.Floer.det_fderiv_endChart`: the Jacobian of the end chart `φ_q` is
  `4π² |φ_q - c_q|²`, for the center `c_q` of the end.
* `TauCeti.Floer.pairwise_disjoint_image_endChart`: the images of the three strips are disjoint.
* `TauCeti.Floer.mem_image_endChart`: they contain every point of `S` with signed longitudinal
  coordinate greater than `1/2` on some end.
* `TauCeti.Floer.injOn_endChart_univ_prod_Ico`: the end chart is injective on every band of
  angular width one.
* `TauCeti.Floer.image_endChart_prod_Ico`: the image of `P × [0, 1)` under the end chart is the
  set of points of `S` whose longitudinal coordinate lies in `P`, for any set `P` of positive
  signed longitudinal coordinates.
* `TauCeti.Floer.equivRealProdCLM_symm_endChart_ne_endCenter`,
  `TauCeti.Floer.equivRealProdCLM_symm_endChart_zero_ne_zero`,
  `TauCeti.Floer.endChart_re_endCoord_fract_im_endCoord`: the end chart avoids the center of the
  end, and every other point is its image at the point `(s, t)` with `t ∈ [0, 1)` given by the end
  coordinate.
* `TauCeti.Floer.image_endChart_prod_Icc_zero_one`,
  `TauCeti.Floer.exists_subset_image_endChart_Icc_prod_Ico`: closing a band `P × [0, 1)` does not
  change its image, and a compact set avoiding the center of the end lies in the image of a finite
  band `[-N, N] × [0, 1)`.
* `TauCeti.Floer.preimage_truncation_inter_eq_image_endChart`: the part `±s > c` of the end `q`
  in the truncation `S_R` is the image under the end chart of `c < ±s ≤ R`, `t ∈ [0, 1)`.
* `TauCeti.Floer.perturbationPullback_endChart_eq_cylindricalEndLift`: the pullback of a
  perturbation along the end chart is the perturbation evaluated on the image of a tangent vector
  under the end lift.
* `TauCeti.Floer.perturbationPullback_endChart`: the pullback of the pair-of-pants perturbation
  along the end chart is its component in the end coordinates.
* `TauCeti.Floer.isComplexLinearMap_fderiv_endChart`: the end chart is holomorphic.
* `TauCeti.Floer.perturbationPullback_endChart_stdComplexLineImag_of_le`,
  `TauCeti.Floer.perturbationPullback_endChart_stdComplexLineReal_of_le`: where a perturbation is
  `H_q(t) dt` on the end `q`, its pullback along the end chart sends `∂_t` to `H_q(t)` and `∂_s`
  to `0`.
* `TauCeti.Floer.isComplexLinearMap_fderiv_positiveEndChart`,
  `TauCeti.Floer.det_fderiv_positiveEndChart_pos`, `TauCeti.Floer.injOn_positiveEndChart`,
  `TauCeti.Floer.positiveEndChart_add_one`: the positive end chart is holomorphic, orientation
  preserving, injective on every band `ℝ × [t₀, t₀ + 1)` and `1`-periodic in `t`.
* `TauCeti.Floer.positiveEndChart_endSign_mul_endCoord`,
  `TauCeti.Floer.exists_endCoord_positiveEndChart`: the signed end coordinates
  `(±Re ζ_q, ±Im ζ_q)` invert the positive end chart, up to an integer shift of the angular
  coordinate.
* `TauCeti.Floer.positiveEndChart_positiveEndCoord`,
  `TauCeti.Floer.exists_positiveEndCoord_positiveEndChart`,
  `TauCeti.Floer.fst_positiveEndCoord_positiveEndChart`: the positive end coordinates invert
  the positive end chart, up to an integer shift of `t`.
* `TauCeti.Floer.endBandCoord`, `TauCeti.Floer.positiveEndChart_endBandCoord`,
  `TauCeti.Floer.endBandCoord_positiveEndChart`,
  `TauCeti.Floer.image_positiveEndChart_univ_prod_Ico`: the band coordinates, the positive end
  coordinates with `t` reduced to `[0, 1)`, invert the positive end chart on the band
  `ℝ × [0, 1)`, whose image is the plane with the center of the end removed.
* `TauCeti.Floer.positiveEndChartScale`, `TauCeti.Floer.sq_positiveEndChartScale`,
  `TauCeti.Floer.sq_positiveEndChartScale_eq_sq_add_sq`: the derivative of the positive end chart
  at `ζ` is a rotation followed by multiplication by the conformal scale `2π |φ'_q(ζ) - c_q|`,
  whose square is the Jacobian; in particular it vanishes nowhere
  (`TauCeti.Floer.fderiv_positiveEndChart_ne_zero`).
* `TauCeti.Floer.norm_equivRealProdCLM_symm_positiveEndChart_inf`: the output end, read in the
  positive end chart, lies at the norm `2 exp (2πs)`.
* `TauCeti.Floer.fderiv_positiveEndChart_add_fst`, `TauCeti.Floer.positiveEndChartScale_add_fst`,
  `TauCeti.Floer.positiveEndChartScale_inv_smul_fderiv_positiveEndChart_eq_of_snd_eq`: translating
  `ζ` by `L` along the end multiplies both `dφ'_q(ζ)` and the conformal scale by `e^{-2π (±L)}`, so
  the rotation `r⁻¹ dφ'_q(ζ)` depends only on `t`.
* `TauCeti.Floer.subset_preimage_truncation_union_iUnion_image_positiveEndChart`: `S` is covered
  by the truncation `S_T` and the images of the bands `(T, ∞) × [0, 1)` under the three positive
  end charts.
* `TauCeti.Floer.contDiffAt_comp_positiveEndCoord`: a `Cⁿ` function on the cylinder of period one
  in `t`, read in the positive end coordinates, is `Cⁿ` away from the center of the end.
* `TauCeti.Floer.contDiffAt_fst_positiveEndCoord`,
  `TauCeti.Floer.contDiffAt_fst_positiveEndCoord_of_mem`,
  `TauCeti.Floer.fst_positiveEndCoord_nonpos_of_ne`: the longitudinal positive end coordinate is
  smooth away from the center of the end, in particular on `S`, and is positive on at most one
  end.
* `TauCeti.Floer.mem_preimage_truncation_iff`, `TauCeti.Floer.mem_preimage_truncationAt_iff`: a
  point lies in the truncation `S_T`, or in the truncation at heights `R`, exactly when it lies in
  `S` and its longitudinal positive end coordinate on each end `q` is at most `T`, or at most
  `R q`.
* `TauCeti.Floer.exists_forall_comp_positiveEndChart_eventuallyEq_zero`: a function with compact
  support in `S` vanishes in the positive end chart beyond some height.
* `TauCeti.Floer.perturbationPullback_positiveEndChart_stdComplexLineReal_of_le`,
  `TauCeti.Floer.perturbationPullback_positiveEndChart_stdComplexLineImag_of_le`: where a
  perturbation is `H_q(t) dt` on the end `q`, its pullback along the positive end chart is
  `H'_q(t) dt`.
* `TauCeti.Floer.perturbation_positiveEndChart_eq_mul_of_le`,
  `TauCeti.Floer.differentiableAt_perturbation_positiveEndChart`: there, at a point of the end,
  each component of the perturbation is a constant multiple of `H_q(t₀)`, so it is differentiable
  in the target point when `H_q(t₀)` is.

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

/-- The defining equation of `S` in real coordinates, for rewriting between `S` and the set of
points that are neither `0` nor `1` as complex numbers. -/
theorem thricePuncturedSphereReal_def : thricePuncturedSphereReal =
    {z | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1} := (rfl)

/-- A point lies in `S` when, as a complex number, it is neither `0` nor `1`. -/
@[simp]
theorem mem_thricePuncturedSphereReal_iff {z : ℝ × ℝ} :
    z ∈ thricePuncturedSphereReal ↔
      Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1 := Iff.rfl

/-- A point at distance at least `2` from `0` lies in `S`. -/
theorem mem_thricePuncturedSphereReal_of_two_le_norm {z : ℝ × ℝ}
    (hz : 2 ≤ ‖Complex.equivRealProdCLM.symm z‖) : z ∈ thricePuncturedSphereReal := by
  refine mem_thricePuncturedSphereReal_iff.2 ⟨fun h0 ↦ ?_, fun h1 ↦ ?_⟩
  · rw [h0, norm_zero] at hz
    linarith
  · rw [h1, norm_one] at hz
    linarith

/-- The pair of pants is open in real coordinates. -/
theorem isOpen_thricePuncturedSphereReal : IsOpen thricePuncturedSphereReal :=
  (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
    (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)

/-- The pair of pants `S = ℂ ∖ {0, 1}` is connected in real coordinates: it is the complement of
two points in the plane. -/
theorem isConnected_thricePuncturedSphereReal : IsConnected thricePuncturedSphereReal := by
  have hS : thricePuncturedSphereReal =
      ({Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1} : Set (ℝ × ℝ))ᶜ := by
    ext z
    simp [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_eq, Prod.mk_zero_zero]
  rw [hS]
  refine (Set.toFinite _).countable.isConnected_compl_of_one_lt_rank ?_
  rw [rank_prod', Module.rank_self, one_add_one_eq_two]
  exact Cardinal.one_lt_two

/-- The signed longitudinal coordinate `±s` of the end `q` is continuous in real coordinates away
from the center of the end. -/
theorem continuousAt_endSign_mul_re_endCoord (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    ContinuousAt (fun z : ℝ × ℝ ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re)
      z :=
  continuousAt_const.mul ((q.contDiffAt_re_endCoord hz (n := 0)).continuousAt.comp
    Complex.equivRealProdCLM.symm.continuous.continuousAt)

/-- The part of `S` on which the signed longitudinal coordinate `±s` of the end `q` is less than
`a` is open in real coordinates. -/
theorem isOpen_endSign_mul_re_endCoord_lt (q : Puncture) (a : ℝ) :
    IsOpen (thricePuncturedSphereReal ∩
      (fun z : ℝ × ℝ ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) ⁻¹'
        Iio a) :=
  ContinuousOn.isOpen_inter_preimage (fun _ hz ↦ (continuousAt_endSign_mul_re_endCoord q
    (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)).continuousWithinAt)
    isOpen_thricePuncturedSphereReal isOpen_Iio

/-! ### Coordinates of the positive end chart -/

/-- The coordinates of a point in the positive end chart of `q`: `(±s, ±t)` for the end coordinate
`s + i t` of the point (`TauCeti.ThricePuncturedSphere.Puncture.endCoord`), with the sign of the
end. Away from the center of the end the positive end chart sends them back to the point
(`positiveEndChart_positiveEndCoord`), and they recover a point of the cylinder from its image
under the positive end chart up to an integer shift of `t`
(`exists_positiveEndCoord_positiveEndChart`). -/
noncomputable def positiveEndCoord (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  q.endSign • Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z))

theorem positiveEndCoord_apply (q : Puncture) (z : ℝ × ℝ) :
    positiveEndCoord q z =
      q.endSign • Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)) := (rfl)

/-- The first positive end coordinate is the signed longitudinal coordinate `±s`. -/
theorem fst_positiveEndCoord (q : Puncture) (z : ℝ × ℝ) :
    (positiveEndCoord q z).1 = q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
  simp [positiveEndCoord_apply]

/-- Away from `0`, the first positive end coordinate `-s` of the output end exceeds `r` exactly off
the closed disc `‖w‖ ≤ 2 exp (2πr)` bounded by the circle `s = -r` of that end. -/
theorem lt_fst_positiveEndCoord_inf_iff {r : ℝ} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0) :
    r < (positiveEndCoord inf z).1 ↔ 2 * exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z‖ := by
  rw [fst_positiveEndCoord, endSign_inf, neg_one_mul, lt_neg_re_endCoord_inf_iff hz]

/-- Beyond the height `1` of the output end, points are at distance more than `8` from `0`. -/
theorem eight_lt_norm_of_one_lt_fst_positiveEndCoord_inf {z : ℝ × ℝ}
    (hz : 1 < (positiveEndCoord inf z).1) : 8 < ‖Complex.equivRealProdCLM.symm z‖ := by
  have hz0 : Complex.equivRealProdCLM.symm z ≠ 0 := by
    intro h
    rw [fst_positiveEndCoord, h, ← endCenter_inf, re_endCoord_endCenter, mul_zero] at hz
    linarith
  have h := (lt_fst_positiveEndCoord_inf_iff hz0).1 hz
  rw [mul_one] at h
  linarith [fourteen_le_two_mul_exp_two_pi]

/-- The second positive end coordinate is the signed angular coordinate `±t`. -/
theorem snd_positiveEndCoord (q : Puncture) (z : ℝ × ℝ) :
    (positiveEndCoord q z).2 = q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im := by
  simp [positiveEndCoord_apply]

/-- The positive end coordinates are measurable. -/
theorem measurable_positiveEndCoord (q : Puncture) : Measurable (positiveEndCoord q) := by
  have h : Measurable fun z : ℝ × ℝ ↦ q.endCoord (Complex.equivRealProdCLM.symm z) := by
    simp_rw [endCoord_def]
    exact ((Complex.measurable_log.comp ((Complex.equivRealProdCLM.symm.continuous.sub
      continuous_const).div_const _).measurable).neg.div_const _)
  have he : positiveEndCoord q =
      fun z ↦ q.endSign • Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)) :=
    funext (positiveEndCoord_apply q)
  rw [he]
  exact (Complex.equivRealProdCLM.continuous.measurable.comp h).const_smul q.endSign

/-- A `Cⁿ` function `F` on the cylinder of period one in the angular coordinate, read in the
positive end coordinates of the end `q`, is `Cⁿ` away from the center of the end. The angular
coordinate jumps by `1` across a ray, and periodicity removes the jump. -/
theorem contDiffAt_comp_positiveEndCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : Puncture) {n : WithTop ℕ∞} {F : ℝ × ℝ → E} (hF : ContDiff ℝ n F)
    (hFp : ∀ p, F (p + (0, 1)) = F p) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    ContDiffAt ℝ n (F ∘ positiveEndCoord q) z := by
  -- Read `F` as a function of the angular coordinate `t` and the longitudinal coordinate `s`.
  set f : ℝ → ℝ → E := fun t s ↦ F (q.endSign * s, q.endSign * t)
  have hf : Periodic f 1 := by
    intro t
    funext s
    rcases q.endSign_eq_one_or_eq_neg_one with hσ | hσ
    · simpa [f, hσ] using hFp (s, t)
    · have h := hFp (-s, -(t + 1))
      rw [Prod.mk_add_mk, add_zero, show -(t + 1) + 1 = -t by ring] at h
      simpa [f, hσ] using h.symm
  have hfs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (uncurry f) :=
    contMDiff_prod_modelWithCornersSelf_iff.2 (hF.comp ((contDiff_const.mul contDiff_snd).prodMk
      (contDiff_const.mul contDiff_fst))).contMDiff
  have hg : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℝ)) n
      (fun w : ℝ × ℝ ↦ (Complex.equivRealProdCLM.symm w,
        (q.endCoord (Complex.equivRealProdCLM.symm w)).re)) z :=
    Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.prodMk
      ((q.contDiffAt_re_endCoord hz).comp z
        Complex.equivRealProdCLM.symm.contDiff.contDiffAt).contMDiffAt
  have h := (q.contMDiffAt_comp_im_endCoord hf hfs hz _).comp z hg
  rw [contMDiffAt_iff_contDiffAt] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ ?_)
  simp [f, positiveEndCoord_apply]

/-- The longitudinal positive end coordinate is smooth away from the center of the end. -/
theorem contDiffAt_fst_positiveEndCoord (q : Puncture) {n : WithTop ℕ∞} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    ContDiffAt ℝ n (fun w ↦ (positiveEndCoord q w).1) z :=
  contDiffAt_comp_positiveEndCoord q contDiff_fst (fun _ ↦ by simp) hz

/-- The longitudinal positive end coordinate is continuous away from the center of the end. -/
theorem continuousAt_fst_positiveEndCoord (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    ContinuousAt (fun w ↦ (positiveEndCoord q w).1) z :=
  (contDiffAt_fst_positiveEndCoord q (n := 0) hz).continuousAt

/-- The longitudinal positive end coordinate is smooth on `S`. -/
theorem contDiffAt_fst_positiveEndCoord_of_mem (q : Puncture) {n : WithTop ℕ∞} {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) : ContDiffAt ℝ n (fun w ↦ (positiveEndCoord q w).1) z :=
  contDiffAt_fst_positiveEndCoord q (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)

/-- In real coordinates, a point lies in the truncation `S_T` exactly when it lies in `S` and its
longitudinal positive end coordinate on every end is at most `T`. -/
theorem mem_preimage_truncation_iff {T : ℝ} {z : ℝ × ℝ} :
    z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation T ↔
      z ∈ thricePuncturedSphereReal ∧ ∀ q, (positiveEndCoord q z).1 ≤ T := by
  simp only [mem_preimage, mem_truncation, mem_thricePuncturedSphereReal_iff, fst_positiveEndCoord,
    and_assoc]

/-- In real coordinates, a point lies in the truncation at heights `R` exactly when it lies in `S`
and its longitudinal positive end coordinate on every end `q` is at most `R q`. -/
theorem mem_preimage_truncationAt_iff {R : Puncture → ℝ} {z : ℝ × ℝ} :
    z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncationAt R ↔
      z ∈ thricePuncturedSphereReal ∧ ∀ q, (positiveEndCoord q z).1 ≤ R q := by
  simp only [mem_preimage, mem_truncationAt, mem_thricePuncturedSphereReal_iff,
    fst_positiveEndCoord, and_assoc]

/-- A point lies beyond `0` on at most one end. -/
theorem fst_positiveEndCoord_nonpos_of_ne {q r : Puncture} (hqr : q ≠ r) {z : ℝ × ℝ}
    (h : 0 < (positiveEndCoord q z).1) : (positiveEndCoord r z).1 ≤ 0 :=
  endSign_mul_re_endCoord_nonpos hqr h

/-- The truncation at heights `R` is compact in real coordinates. -/
theorem isCompact_preimage_truncationAt (R : Puncture → ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncationAt R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncationAt R)

/-- The truncation at heights `R`, in real coordinates, lies in `S`. -/
theorem preimage_truncationAt_subset_thricePuncturedSphereReal (R : Puncture → ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncationAt R ⊆ thricePuncturedSphereReal :=
  fun _ hz ↦ mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncationAt.1 hz).1,
    (mem_truncationAt.1 hz).2.1⟩

/-- In real coordinates, cutting the truncation `S_R` along the circle `±s = c` of the end `q`, for
`c ≤ R`, gives the truncation at the height `c` on `q` and `R` on the other two ends. -/
theorem preimage_truncation_inter_eq_preimage_truncationAt (q : Puncture) {c R : ℝ}
    (hcR : c ≤ R) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ c} =
      Complex.equivRealProdCLM.symm ⁻¹' truncationAt (Function.update (fun _ ↦ R) q c) := by
  rw [← truncation_inter_eq_truncationAt q hcR, preimage_inter,
    preimage_ofPred_eq (p := fun w ↦ q.endSign * (q.endCoord w).re ≤ c)]

/-- The truncation `S_R` is compact in real coordinates. -/
theorem isCompact_preimage_truncation (R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)

/-- The truncation `S_R`, in real coordinates, lies in `S`. -/
theorem preimage_truncation_subset_thricePuncturedSphereReal (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ thricePuncturedSphereReal :=
  fun _ hz ↦ mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1,
    (mem_truncation.1 hz).2.1⟩

/-- An open set on which the signed longitudinal coordinate `±s` of every end is at most `R`
lies in the truncation `S_R`, in real coordinates. -/
theorem subset_preimage_truncation_of_isOpen {U : Set (ℝ × ℝ)} (hU : IsOpen U) {R : ℝ}
    (h : ∀ z ∈ U, ∀ q : Puncture, (positiveEndCoord q z).1 ≤ R) :
    U ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R := by
  have hV := subset_truncation_of_isOpen (hU.preimage Complex.equivRealProdCLM.continuous)
    fun w hw q ↦ by
      simpa only [fst_positiveEndCoord, ContinuousLinearEquiv.symm_apply_apply] using h _ hw q
  exact fun z hz ↦ hV (by simpa using hz)

/-- A point of `S` outside the truncation `S_R` lies beyond `R` on some end. -/
theorem exists_lt_fst_positiveEndCoord_of_notMem_truncation {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (hzR : Complex.equivRealProdCLM.symm z ∉ truncation R) :
    ∃ q : Puncture, R < (positiveEndCoord q z).1 := by
  by_contra! h
  exact hzR (mem_truncation.2 ⟨(mem_thricePuncturedSphereReal_iff.1 hz).1,
    (mem_thricePuncturedSphereReal_iff.1 hz).2, h⟩)

/-- The integral over `S` of a function vanishing at every point of `S` beyond `R` on some end is
its integral over the truncation `S_R`. -/
theorem setIntegral_thricePuncturedSphereReal_eq_setIntegral_truncation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E} {R : ℝ}
    (hf : ∀ z ∈ thricePuncturedSphereReal, ∀ q : Puncture,
      R < (positiveEndCoord q z).1 → f z = 0) :
    ∫ z in thricePuncturedSphereReal, f z =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z := by
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    isOpen_thricePuncturedSphereReal.measurableSet
    (preimage_truncation_subset_thricePuncturedSphereReal R) fun z hz ↦ ?_
  obtain ⟨q, hq⟩ := exists_lt_fst_positiveEndCoord_of_notMem_truncation hz.1 hz.2
  exact hf z hz.1 q hq

/-- Almost every point of the plane lies in the pair of pants: the two punctures form a null set. -/
theorem ae_mem_thricePuncturedSphereReal : ∀ᵐ z : ℝ × ℝ, z ∈ thricePuncturedSphereReal := by
  refine measure_mono_null (t := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1})
    (fun z hz ↦ ?_) ?_
  · rcases not_and_or.1 (mem_thricePuncturedSphereReal_iff.not.1 hz) with h | h
    · exact Or.inl (by rw [← not_not.1 h, ContinuousLinearEquiv.apply_symm_apply])
    · exact Or.inr (by
        rw [Set.mem_singleton_iff, ← not_not.1 h, ContinuousLinearEquiv.apply_symm_apply])
  · rw [Measure.volume_eq_prod]
    exact (Set.toFinite _).measure_zero _

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

/-- In the real coordinates of `S`, the components of the pair-of-pants perturbation are `Cⁿ`
jointly on `S × V`, for `Cⁿ` Hamiltonians. -/
theorem contDiffOn_uncurry_pairOfPantsPerturbation {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ n (uncurry (H q))) (v : ℂ) :
    ContDiffOn ℝ n
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contDiffWithinAt

/-- In the real coordinates of `S`, the components of the pair-of-pants perturbation are
differentiable in the target point, for `C¹` Hamiltonians. -/
theorem differentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)
      x :=
  ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).differentiableAt
    one_ne_zero).comp _ ((differentiableAt_const _).prodMk differentiableAt_id)

section Manifold

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- A perturbation one-form `K` on `ℂ` which is `C¹` at every point of `S × M` has components
`(z, x) ↦ K(z, x)(v)`, in the real coordinates of `S`, that are `C¹` jointly on `S × M`. -/
theorem contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt
    {K : ℂ → M → ℂ →L[ℝ] ℝ}
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x)) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) 1
      (fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x) :=
    (Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
      contMDiffAt_snd
  exact (((hK ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (z, x) hφ).clm_apply
    contMDiffAt_const).contMDiffWithinAt

/-- In the real coordinates of `S`, the components of the pair-of-pants perturbation are `Cⁿ`
jointly in the domain point and the target point of a manifold, for `Cⁿ` Hamiltonians. -/
theorem contMDiffAt_uncurry_pairOfPantsPerturbation {H : Puncture → ℝ → M → ℝ} {n : ℕ∞}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v) (z, x) :=
  ((contMDiffAt_pairOfPantsPerturbation hH hHs ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp
    (z, x) ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.comp contMDiff_fst).prodMk
      contMDiff_snd).contMDiffAt).clm_apply contMDiffAt_const

/-- The components of the perturbation in real coordinates are differentiable in the domain
point, at points of `S`, for `C¹` Hamiltonians on a manifold. -/
theorem differentiableAt_pairOfPantsPerturbation_domain {H : Puncture → ℝ → M → ℝ}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ pairOfPantsPerturbation H w x)
      (Complex.equivRealProdCLM.symm z) :=
    (contMDiffAt_pairOfPantsPerturbation hH hHs
      ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (f := fun w : ℂ ↦ (w, x)) _
      (contMDiffAt_id.prodMk contMDiffAt_const)
  exact ((hK.contDiffAt.differentiableAt one_ne_zero).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

/-- The components of the perturbation are differentiable in the target point, at points
of `S`, for `C¹` Hamiltonians on a manifold. -/
theorem mdifferentiableAt_pairOfPantsPerturbation_target {H : Puncture → ℝ → M → ℝ}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  (((contMDiffAt_pairOfPantsPerturbation hH hHs
    ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp
      (f := fun y : M ↦ (Complex.equivRealProdCLM.symm z, y)) x
      (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply contMDiffAt_const).mdifferentiableAt
    one_ne_zero

end Manifold

/-- The end lift of `q`, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
noncomputable def endChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z))

theorem endChart_apply (q : Puncture) (z : ℝ × ℝ) :
    endChart q z =
      Complex.equivRealProdCLM (q.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) := (rfl)

/-- The end chart is the end lift read in the real coordinates. -/
theorem endChart_eq_realChart (q : Puncture) :
    endChart q = TauCeti.Complex.realChart q.cylindricalEndLift :=
  funext fun z ↦ (TauCeti.Complex.realChart_apply _ z).symm

/-- The end chart at a point `(s, t)` of the cylinder is the end lift at `s + i t`. -/
theorem endChart_mk (q : Puncture) (s t : ℝ) :
    endChart q (s, t) = Complex.equivRealProdCLM (q.cylindricalEndLift (↑s + ↑t * Complex.I)) := by
  simp [endChart_apply, Complex.equivRealProdCLM_symm_apply]

/-- The end chart is `1`-periodic in the angular coordinate. -/
theorem endChart_add_one (q : Puncture) (s t : ℝ) :
    endChart q (s, t + 1) = endChart q (s, t) := by
  rw [endChart_mk, endChart_mk]
  exact congrArg Complex.equivRealProdCLM (by exact_mod_cast q.periodic_cylindricalEndLift s t)

/-- A map read in the end chart is `1`-periodic in the angular coordinate. -/
theorem periodic_comp_endChart {α : Type*} (q : Puncture) (f : ℝ × ℝ → α) (s : ℝ) :
    Periodic (fun t ↦ (f ∘ endChart q) (s, t)) 1 := fun t ↦ by
  simp only [comp_apply, endChart_add_one]

/-- In complex coordinates the end chart is the end lift. -/
@[simp]
theorem equivRealProdCLM_symm_endChart (q : Puncture) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (endChart q z) =
      q.cylindricalEndLift (Complex.equivRealProdCLM.symm z) := by
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The end chart of `q` avoids the center of the end. -/
theorem equivRealProdCLM_symm_endChart_ne_endCenter (q : Puncture) (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (endChart q z) ≠ q.endCenter := by
  rw [equivRealProdCLM_symm_endChart]
  exact sub_ne_zero.1 (q.cylindricalEndLift_sub_endCenter_ne_zero _)

/-- The end chart of `0` lands in `ℂ ∖ {0}`. -/
theorem equivRealProdCLM_symm_endChart_zero_ne_zero (z : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (endChart .zero z) ≠ 0 := by
  simpa only [Puncture.endCenter_zero] using equivRealProdCLM_symm_endChart_ne_endCenter .zero z

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
    endStrip q = {s | 1 / 2 < q.endSign * s} ×ˢ Ico (-1 / 2) (1 / 2) := (rfl)

/-- A point lies in the strip of the end `q` when its signed longitudinal coordinate exceeds `1/2`
and its angular coordinate lies in `[-1/2, 1/2)`. -/
@[simp]
theorem mem_endStrip_iff {q : Puncture} {z : ℝ × ℝ} :
    z ∈ endStrip q ↔ 1 / 2 < q.endSign * z.1 ∧ z.2 ∈ Ico (-1 / 2) (1 / 2) := Iff.rfl

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

/-- The end charts are holomorphic: their derivatives are complex linear. -/
theorem isComplexLinearMap_fderiv_endChart (q : Puncture) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (endChart q) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, fderiv_endChart_apply,
    AlmostComplexStructure.product_apply]
  apply Prod.ext <;>
    simp [Complex.equivRealProdCLM_symm_apply, Complex.mul_re, Complex.mul_im] <;> ring

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

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the end chart sends `∂_t` to
`H_q(t)`. -/
theorem perturbationPullback_endChart_stdComplexLineImag_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) {ζ : ℝ × ℝ} (hζ : T₀ ≤ q.endSign * ζ.1) (x : X) :
    perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ x =
      H q ζ.2 x := by
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  rw [perturbationPullback_endChart_eq_cylindricalEndLift K, hI]
  beta_reduce
  obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift (Complex.equivRealProdCLM.symm ζ)
  have hre : (q.endCoord (q.cylindricalEndLift (Complex.equivRealProdCLM.symm ζ))).re = ζ.1 := by
    simp [hk]
  rw [hKH _ x (by rwa [hre]), smul_apply, endAngularForm_cylindricalEndLift,
    hk, smul_eq_mul, Complex.I_im, mul_one]
  simpa using congrFun (hH.int_mul k ζ.2) x

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the end chart sends `∂_s` to `0`. -/
theorem perturbationPullback_endChart_stdComplexLineReal_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {ζ : ℝ × ℝ} (hζ : T₀ ≤ q.endSign * ζ.1) (x : X) :
    perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ x =
      0 := by
  have h1 : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  rw [perturbationPullback_endChart_eq_cylindricalEndLift K, h1]
  beta_reduce
  have hre : (q.endCoord (q.cylindricalEndLift (Complex.equivRealProdCLM.symm ζ))).re = ζ.1 := by
    rw [re_endCoord_cylindricalEndLift]
    simp [Complex.equivRealProdCLM_symm_apply]
  rw [hKH _ x (by rwa [hre]), smul_apply, endAngularForm_cylindricalEndLift, Complex.one_im,
    smul_zero]

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

/-- Every point other than the center of the end `q` is the image under the end chart of its end
coordinate on `q`, in real coordinates. -/
theorem endChart_equivRealProdCLM_endCoord {q : Puncture} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    endChart q (Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z))) = z := by
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply, q.cylindricalEndLift_endCoord hz,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Every point of `S` where some end has signed longitudinal coordinate greater than `1/2` is the
image of a point of that end's strip. -/
theorem mem_image_endChart {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    {q : Puncture} (hq : 1 / 2 < (positiveEndCoord q z).1) :
    z ∈ endChart q '' endStrip q := by
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨by simpa [fst_positiveEndCoord] using hq, by simpa using q.im_endCoord_mem_Ico _⟩,
    endChart_equivRealProdCLM_endCoord (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)⟩

/-- Every point other than the center of the end `q` is the image under the end chart of the
point `(s, t)` whose longitudinal coordinate `s` is that of the end at the point and whose angular
coordinate `t` is the fractional part of the angular coordinate there, in `[0, 1)`. -/
theorem endChart_re_endCoord_fract_im_endCoord {q : Puncture} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    endChart q ((q.endCoord (Complex.equivRealProdCLM.symm z)).re,
      Int.fract (q.endCoord (Complex.equivRealProdCLM.symm z)).im) = z := by
  set w := q.endCoord (Complex.equivRealProdCLM.symm z)
  -- Move the angular coordinate into `[0, 1)` by an integer shift.
  have hper := (q.periodic_cylindricalEndLift w.re).sub_int_mul_eq (x := w.im) ⌊w.im⌋
  rw [mul_one] at hper
  rw [endChart_apply, Complex.equivRealProdCLM_symm_apply, Int.fract, hper, Complex.re_add_im,
    q.cylindricalEndLift_endCoord hz, ContinuousLinearEquiv.apply_symm_apply]

/-- The points of `S` at which the longitudinal coordinate of the end `q` lies in a set `P` of
positive signed values are exactly the images under the end chart of `P × [0, 1)`. -/
theorem image_endChart_prod_Ico {q : Puncture} {P : Set ℝ} (hP : ∀ s ∈ P, 0 < q.endSign * s) :
    endChart q '' (P ×ˢ Ico 0 1) =
      {z | z ∈ thricePuncturedSphereReal ∧
        (q.endCoord (Complex.equivRealProdCLM.symm z)).re ∈ P} := by
  ext z
  constructor
  · rintro ⟨ζ, ⟨hζ, -⟩, rfl⟩
    exact ⟨endChart_mem_thricePuncturedSphereReal (hP _ hζ), by rwa [re_endCoord_endChart]⟩
  · rintro ⟨hz, hzP⟩
    exact ⟨_, ⟨hzP, Int.fract_nonneg _, Int.fract_lt_one _⟩,
      endChart_re_endCoord_fract_im_endCoord
        (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)⟩

/-- Closing a band of angular width one does not change its image under the end chart: the
circles `t = 0` and `t = 1` have the same image. -/
theorem image_endChart_prod_Icc_zero_one (q : Puncture) (P : Set ℝ) :
    endChart q '' (P ×ˢ Icc 0 1) = endChart q '' (P ×ˢ Ico 0 1) := by
  refine Subset.antisymm ?_ (image_mono (prod_mono subset_rfl Ico_subset_Icc_self))
  rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
  rcases ht.2.eq_or_lt with rfl | ht₁
  · exact ⟨(s, 0), ⟨hs, left_mem_Ico.2 one_pos⟩, by simpa using (endChart_add_one q s 0).symm⟩
  · exact ⟨(s, t), ⟨hs, ht.1, ht₁⟩, rfl⟩

/-- A compact set of points other than the center of the end `q` lies in the image under the end
chart of a finite band `[-N, N] × [0, 1)`. -/
theorem exists_subset_image_endChart_Icc_prod_Ico {q : Puncture} {D : Set (ℝ × ℝ)}
    (hD : IsCompact D) (hDq : ∀ z ∈ D, Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    ∃ N, D ⊆ endChart q '' (Icc (-N) N ×ˢ Ico 0 1) := by
  have hre : ContinuousOn (fun z ↦ (q.endCoord (Complex.equivRealProdCLM.symm z)).re) D :=
    fun z hz ↦ ((q.contDiffAt_re_endCoord (hDq z hz) (n := 0)).continuousAt.comp
      Complex.equivRealProdCLM.symm.continuous.continuousAt).continuousWithinAt
  obtain ⟨N, hN⟩ := hD.exists_bound_of_continuousOn hre
  exact ⟨N, fun z hz ↦ ⟨_, ⟨abs_le.1 ((Real.norm_eq_abs _).symm.trans_le (hN z hz)),
    Int.fract_nonneg _, Int.fract_lt_one _⟩, endChart_re_endCoord_fract_im_endCoord (hDq z hz)⟩⟩

/-- A set of points other than the center of the end `q` is the image under the end chart of the
part of the band `ℝ × [0, 1)` lying over it. -/
theorem image_endChart_preimage_inter_univ_prod_Ico {q : Puncture} {Ω : Set (ℝ × ℝ)}
    (hΩ : ∀ z ∈ Ω, Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    endChart q '' (endChart q ⁻¹' Ω ∩ univ ×ˢ Ico 0 1) = Ω := by
  rw [image_preimage_inter, inter_eq_left]
  exact fun z hz ↦ ⟨_, ⟨mem_univ _, Int.fract_nonneg _, Int.fract_lt_one _⟩,
    endChart_re_endCoord_fract_im_endCoord (hΩ z hz)⟩

/-- For `0 ≤ c`, the part `±s > c` of the end `q` in the truncation `S_R` is the image under the
end chart of `c < ±s ≤ R`, `t ∈ [0, 1)`. -/
theorem preimage_truncation_inter_eq_image_endChart (q : Puncture) {c : ℝ} (hc : 0 ≤ c)
    (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | c < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re} =
      endChart q '' ({s : ℝ | c < q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico 0 1) := by
  rw [image_endChart_prod_Ico fun s hs ↦ by linarith [hs.1]]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_truncation, mem_ofPred_eq,
    mem_thricePuncturedSphereReal_iff]
  constructor
  · rintro ⟨⟨h₀, h₁, hR⟩, h⟩
    exact ⟨⟨h₀, h₁⟩, h, hR q⟩
  · rintro ⟨⟨h₀, h₁⟩, h, hR⟩
    refine ⟨⟨h₀, h₁, fun r ↦ ?_⟩, h⟩
    by_cases hr : q = r
    · exact hr ▸ hR
    · linarith [endSign_mul_re_endCoord_nonpos hr (by linarith : 0 < q.endSign *
        (q.endCoord (Complex.equivRealProdCLM.symm z)).re)]

/-- The strip of an end is measurable. -/
theorem measurableSet_endStrip (q : Puncture) : MeasurableSet (endStrip q) := by
  rw [endStrip_def]
  exact (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).prod
    measurableSet_Ico

/-- The end charts preserve orientation. -/
theorem det_fderiv_endChart_nonneg (q : Puncture) (ζ : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (endChart q) ζ).det := by
  rw [endChart_eq_realChart]
  exact TauCeti.Complex.det_fderiv_realChart_nonneg
    (q.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt

/-- The end charts are local diffeomorphisms: their Jacobian determinants are positive. -/
theorem det_fderiv_endChart_pos (q : Puncture) (ζ : ℝ × ℝ) :
    0 < (fderiv ℝ (endChart q) ζ).det := by
  rw [endChart_eq_realChart, TauCeti.Complex.det_fderiv_realChart
    (q.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt]
  exact Complex.normSq_pos.2 (q.deriv_cylindricalEndLift_ne_zero _)

/-- The Jacobian of the end chart of `q` at `z` is `4π² |φ_q(z) - c_q|²`. -/
theorem det_fderiv_endChart (q : Puncture) (z : ℝ × ℝ) :
    (fderiv ℝ (endChart q) z).det =
      4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm (endChart q z) - q.endCenter‖ ^ 2 := by
  rw [endChart_eq_realChart, TauCeti.Complex.det_fderiv_realChart
    (q.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt, deriv_cylindricalEndLift,
    ← endChart_eq_realChart, equivRealProdCLM_symm_endChart, Complex.normSq_eq_norm_sq]
  simp only [norm_neg, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, norm_eq_abs,
    abs_of_pos pi_pos]
  ring

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

/-! ### Positive end charts -/

/-- The end chart of `q` read as a positive end: `(s, t) ↦ φ_q(±s, ±t)`, with the sign `±` of the
end, so that `s → ∞` along every end. It is the end chart `TauCeti.Floer.endChart q` on the input
ends, and `(s, t) ↦ φ_∞(-s, -t)` on the output end. -/
noncomputable def positiveEndChart (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  endChart q (q.endSign • z)

theorem positiveEndChart_apply (q : Puncture) (z : ℝ × ℝ) :
    positiveEndChart q z = endChart q (q.endSign • z) := (rfl)

theorem positiveEndChart_mk (q : Puncture) (s t : ℝ) :
    positiveEndChart q (s, t) = endChart q (q.endSign * s, q.endSign * t) := by
  simp [positiveEndChart_apply]

/-- The end chart at `(±s, t)` is the positive end chart at `(s, ±t)`. -/
theorem endChart_eq_positiveEndChart (q : Puncture) (s t : ℝ) :
    endChart q (q.endSign * s, t) = positiveEndChart q (s, q.endSign * t) := by
  rw [positiveEndChart_mk, ← mul_assoc, endSign_mul_self, one_mul]

/-- The end loop `t ↦ u(φ_q(±s, t))` is the loop of `u ∘ φ'_q` at the height `s`, read with the
time `±t` of the end. -/
theorem comp_endChart_eq_comp_positiveEndChart {α : Type*} (u : ℝ × ℝ → α) (q : Puncture)
    (s : ℝ) :
    (fun t ↦ u (endChart q (q.endSign * s, t))) =
      (fun t ↦ (u ∘ positiveEndChart q) (s, t)) ∘ fun t ↦ q.endSign * t := by
  funext t
  simp only [comp_apply, endChart_eq_positiveEndChart]

/-- A family which is `J_q(t, u)` along the end `q` beyond `T₀` is `J_q(±t, u)` in the positive end
chart. -/
theorem eq_comp_positiveEndChart {α β : Type*} {u : ℝ × ℝ → α} {J : ℝ × ℝ → β}
    {Jq : ℝ → α → β} {q : Puncture} {T₀ : ℝ}
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {z : ℝ × ℝ} (hz : T₀ ≤ z.1) :
    J (positiveEndChart q z) = Jq (q.endSign * z.2) ((u ∘ positiveEndChart q) z) := by
  obtain ⟨s, t⟩ := z
  simp only [comp_apply, positiveEndChart_mk]
  exact hJ s _ hz

/-- If the end loops `t ↦ u(φ_q(±s, t))` converge uniformly to `y`, then the loops of `u ∘ φ'_q`
converge uniformly to `t ↦ y(±t)`. -/
theorem tendstoUniformly_comp_positiveEndChart {α : Type*} [UniformSpace α] {u : ℝ × ℝ → α}
    {q : Puncture} {y : ℝ → α} {l : Filter ℝ}
    (h : TendstoUniformly (fun s t ↦ u (endChart q (q.endSign * s, t))) y l) :
    TendstoUniformly (fun s t ↦ (u ∘ positiveEndChart q) (s, t)) (fun t ↦ y (q.endSign * t))
      l := by
  have hloop (s : ℝ) : (fun t ↦ (u ∘ positiveEndChart q) (s, t)) =
      (fun t ↦ u (endChart q (q.endSign * s, t))) ∘ fun t ↦ q.endSign * t := by
    rw [comp_endChart_eq_comp_positiveEndChart]
    funext t
    simp only [comp_apply, endSign_mul_endSign_mul]
  rw [funext hloop]
  exact h.comp _

/-- The positive end chart is `1`-periodic in the angular coordinate. -/
theorem positiveEndChart_add_one (q : Puncture) (s t : ℝ) :
    positiveEndChart q (s, t + 1) = positiveEndChart q (s, t) := by
  rw [positiveEndChart_mk, positiveEndChart_mk]
  rcases q.endSign_eq_one_or_eq_neg_one with h | h <;> simp only [h, one_mul, neg_one_mul]
  · exact endChart_add_one q s t
  · rw [← endChart_add_one q (-s) (-(t + 1)), neg_add, neg_add_cancel_right]

/-- The derivative of the positive end chart is the derivative of the end chart at the reflected
point, composed with the reflection `v ↦ ±v`. -/
theorem hasFDerivAt_positiveEndChart (q : Puncture) (z : ℝ × ℝ) :
    HasFDerivAt (positiveEndChart q)
      ((fderiv ℝ (endChart q) (q.endSign • z)).comp
        (q.endSign • ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
  ((contDiff_endChart q 1).differentiable one_ne_zero _).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul q.endSign)

theorem fderiv_positiveEndChart_apply (q : Puncture) (z v : ℝ × ℝ) :
    fderiv ℝ (positiveEndChart q) z v = q.endSign • fderiv ℝ (endChart q) (q.endSign • z) v := by
  simp [(hasFDerivAt_positiveEndChart q z).fderiv]

/-- The end chart is the positive end chart after the reflection `z ↦ ±z`, so a map read in the end
chart has, at `z`, the derivative of the map read in the positive end chart at `±z`, composed with
the reflection. -/
theorem fderiv_comp_endChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : Puncture)
    (u : ℝ × ℝ → E) (z : ℝ × ℝ) :
    fderiv ℝ (u ∘ endChart q) z =
      q.endSign • fderiv ℝ (u ∘ positiveEndChart q) (q.endSign • z) := by
  have h : u ∘ endChart q = fun z ↦ (u ∘ positiveEndChart q) (q.endSign • z) := by
    funext z
    simp [positiveEndChart_apply, smul_smul]
  rw [h, fderiv_comp_smul]

theorem contDiff_positiveEndChart (q : Puncture) (n : WithTop ℕ∞) :
    ContDiff ℝ n (positiveEndChart q) :=
  (contDiff_endChart q n).comp (contDiff_const_smul q.endSign)

/-- The derivative at `z` of the translate `z ↦ φ'_q(z + c)` of the positive end chart is the
derivative of the positive end chart at `z + c`. -/
theorem hasFDerivAt_positiveEndChart_add (q : Puncture) (c z : ℝ × ℝ) :
    HasFDerivAt (fun z ↦ positiveEndChart q (z + c)) (fderiv ℝ (positiveEndChart q) (z + c)) z :=
  ((contDiff_positiveEndChart q 1).differentiable one_ne_zero _).hasFDerivAt.comp z
    ((hasFDerivAt_id z).add_const c)

/-- The positive end charts are holomorphic. -/
theorem isComplexLinearMap_fderiv_positiveEndChart (q : Puncture) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (positiveEndChart q) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  have h := (isComplexLinearMap_iff_apply _ _ _).1 (isComplexLinearMap_fderiv_endChart q
    (q.endSign • z))
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, fderiv_positiveEndChart_apply] at h ⊢
  rw [h, map_smul]

/-- The Jacobian of the positive end chart at `ζ` is `4π² |φ'_q(ζ) - c_q|²`, where `c_q` is the
center of the end, as for the end chart at the reflected point. -/
theorem det_fderiv_positiveEndChart (q : Puncture) (ζ : ℝ × ℝ) :
    (fderiv ℝ (positiveEndChart q) ζ).det =
      4 * π ^ 2 * ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ ^ 2 := by
  have h : fderiv ℝ (positiveEndChart q) ζ = q.endSign • fderiv ℝ (endChart q) (q.endSign • ζ) :=
    ContinuousLinearMap.ext fun v ↦ fderiv_positiveEndChart_apply q ζ v
  rw [h, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
    Module.finrank_prod, Module.finrank_self, one_add_one_eq_two, sq, endSign_mul_self, one_mul,
    ← ContinuousLinearMap.det, det_fderiv_endChart, positiveEndChart_apply]

/-- The positive end charts preserve orientation strictly. -/
theorem det_fderiv_positiveEndChart_pos (q : Puncture) (z : ℝ × ℝ) :
    0 < (fderiv ℝ (positiveEndChart q) z).det := by
  rw [det_fderiv_positiveEndChart, positiveEndChart_apply]
  have := sub_ne_zero.2 (equivRealProdCLM_symm_endChart_ne_endCenter q (q.endSign • z))
  positivity

/-- The positive end chart of `q` avoids the center of the end. -/
theorem equivRealProdCLM_symm_positiveEndChart_ne_endCenter (q : Puncture) (ζ : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (positiveEndChart q ζ) ≠ q.endCenter := by
  rw [positiveEndChart_apply]
  exact equivRealProdCLM_symm_endChart_ne_endCenter q _

/-- The output end, read in the positive end chart `φ'_∞`, lies at the norm `2 exp (2πs)`. -/
theorem norm_equivRealProdCLM_symm_positiveEndChart_inf (s t : ℝ) :
    ‖Complex.equivRealProdCLM.symm (positiveEndChart inf (s, t))‖ = 2 * exp (2 * π * s) := by
  have h := norm_cylindricalEndLift_sub_endCenter inf
    (Complex.equivRealProdCLM.symm (inf.endSign • (s, t)))
  rw [positiveEndChart_apply, equivRealProdCLM_symm_endChart]
  simpa using h

/-- The **conformal scale** `2π |φ'_q(ζ) - c_q|` of the positive end chart `φ'_q` at `ζ`, where
`c_q` is the center of the end: the derivative of `φ'_q` at `ζ` is a rotation followed by
multiplication by this scale, whose square is the Jacobian (`sq_positiveEndChartScale`). -/
noncomputable def positiveEndChartScale (q : Puncture) (ζ : ℝ × ℝ) : ℝ :=
  2 * π * ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖

theorem positiveEndChartScale_apply (q : Puncture) (ζ : ℝ × ℝ) :
    positiveEndChartScale q ζ =
      2 * π * ‖Complex.equivRealProdCLM.symm (positiveEndChart q ζ) - q.endCenter‖ := (rfl)

theorem positiveEndChartScale_pos (q : Puncture) (ζ : ℝ × ℝ) : 0 < positiveEndChartScale q ζ := by
  have h := sub_ne_zero.2 (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ)
  rw [positiveEndChartScale_apply]
  positivity

/-- The square of the conformal scale of the positive end chart is its Jacobian. -/
theorem sq_positiveEndChartScale (q : Puncture) (ζ : ℝ × ℝ) :
    positiveEndChartScale q ζ ^ 2 = (fderiv ℝ (positiveEndChart q) ζ).det := by
  rw [det_fderiv_positiveEndChart, positiveEndChartScale_apply]
  ring

theorem continuous_positiveEndChartScale (q : Puncture) : Continuous (positiveEndChartScale q) := by
  have := (contDiff_positiveEndChart q 0).continuous
  unfold positiveEndChartScale
  fun_prop

/-- The derivative of the positive end chart is multiplication by a complex number: it sends
`(0, 1)` to the image of `(1, 0)` rotated by a quarter turn. -/
theorem fderiv_positiveEndChart_apply_zero_one (q : Puncture) (ζ : ℝ × ℝ) :
    fderiv ℝ (positiveEndChart q) ζ (0, 1) =
      (-(fderiv ℝ (positiveEndChart q) ζ (1, 0)).2,
        (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1) := by
  have h := (isComplexLinearMap_fderiv_positiveEndChart q ζ).apply_stdComplexLineImag_eq
  rwa [ContinuousLinearMap.coe_coe, stdComplexLineImag_eq, stdComplexLineReal_eq] at h

/-- The square of the conformal scale is the squared norm of the image of `(1, 0)` under the
derivative of the positive end chart. -/
theorem sq_positiveEndChartScale_eq_sq_add_sq (q : Puncture) (ζ : ℝ × ℝ) :
    positiveEndChartScale q ζ ^ 2 =
      (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 ^ 2 +
        (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 ^ 2 := by
  rw [sq_positiveEndChartScale, ContinuousLinearMap.det,
    (isComplexLinearMap_fderiv_positiveEndChart q ζ).det_eq_sq_add_sq, ContinuousLinearMap.coe_coe,
    stdComplexLineReal_eq]

/-- The derivative of the positive end chart vanishes nowhere. -/
theorem fderiv_positiveEndChart_ne_zero (q : Puncture) (ζ : ℝ × ℝ) :
    fderiv ℝ (positiveEndChart q) ζ ≠ 0 := fun h ↦
  (pow_pos (positiveEndChartScale_pos q ζ) 2).ne' <| by
    simpa [h] using sq_positiveEndChartScale_eq_sq_add_sq q ζ

/-- The first coordinate of the image of `(1, 0)` under the derivative of the positive end chart
is at most the conformal scale in absolute value. -/
theorem abs_fst_fderiv_positiveEndChart_le (q : Puncture) (ζ : ℝ × ℝ) :
    |(fderiv ℝ (positiveEndChart q) ζ (1, 0)).1| ≤ positiveEndChartScale q ζ := by
  refine abs_le_of_sq_le_sq ?_ (positiveEndChartScale_pos q ζ).le
  rw [sq_positiveEndChartScale_eq_sq_add_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The second coordinate of the image of `(1, 0)` under the derivative of the positive end chart
is at most the conformal scale in absolute value. -/
theorem abs_snd_fderiv_positiveEndChart_le (q : Puncture) (ζ : ℝ × ℝ) :
    |(fderiv ℝ (positiveEndChart q) ζ (1, 0)).2| ≤ positiveEndChartScale q ζ := by
  refine abs_le_of_sq_le_sq ?_ (positiveEndChartScale_pos q ζ).le
  rw [sq_positiveEndChartScale_eq_sq_add_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The point `±(ζ + (L, 0))` of `ℂ` is the point `±ζ` translated by `±L`. -/
private theorem equivRealProdCLM_symm_endSign_smul_add_fst (q : Puncture) (ζ : ℝ × ℝ) (L : ℝ) :
    Complex.equivRealProdCLM.symm (q.endSign • (ζ + (L, 0))) =
      Complex.equivRealProdCLM.symm (q.endSign • ζ) + ↑(q.endSign * L) := by
  apply Complex.ext <;> simp

/-- Translating the positive end chart of `q` by `L` along the end multiplies its derivative by
`e^{-2π (±L)}`, with the sign `±` of the end. -/
theorem fderiv_positiveEndChart_add_fst (q : Puncture) (ζ : ℝ × ℝ) (L : ℝ) :
    fderiv ℝ (positiveEndChart q) (ζ + (L, 0)) =
      Real.exp (-(2 * π * (q.endSign * L))) • fderiv ℝ (positiveEndChart q) ζ := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [smul_apply, fderiv_positiveEndChart_apply, fderiv_positiveEndChart_apply,
    fderiv_endChart_apply, fderiv_endChart_apply, equivRealProdCLM_symm_endSign_smul_add_fst,
    q.deriv_cylindricalEndLift_add_endSign_mul]
  simp only [← Complex.real_smul, smul_mul_assoc, map_smul]
  module

/-- Translating the positive end chart of `q` by `L` along the end multiplies its conformal scale
by `e^{-2π (±L)}`, with the sign `±` of the end. -/
theorem positiveEndChartScale_add_fst (q : Puncture) (ζ : ℝ × ℝ) (L : ℝ) :
    positiveEndChartScale q (ζ + (L, 0)) =
      Real.exp (-(2 * π * (q.endSign * L))) * positiveEndChartScale q ζ := by
  simp only [positiveEndChartScale_apply, positiveEndChart_apply, endChart_apply,
    ContinuousLinearEquiv.symm_apply_apply, equivRealProdCLM_symm_endSign_smul_add_fst,
    q.cylindricalEndLift_add_endSign_mul, q.endShift_apply, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  ring

/-- **The rotation of the positive end chart depends only on the angular coordinate.** The
derivative of `φ'_q` at `ζ`, divided by the conformal scale, is a rotation that does not change
when `ζ` moves along the end. -/
theorem positiveEndChartScale_inv_smul_fderiv_positiveEndChart_eq_of_snd_eq (q : Puncture)
    {ζ ζ' : ℝ × ℝ} (h : ζ.2 = ζ'.2) :
    (positiveEndChartScale q ζ)⁻¹ • fderiv ℝ (positiveEndChart q) ζ =
      (positiveEndChartScale q ζ')⁻¹ • fderiv ℝ (positiveEndChart q) ζ' := by
  have hζ' : ζ' = ζ + (ζ'.1 - ζ.1, 0) := Prod.ext (by simp) (by simp [h])
  rw [hζ', fderiv_positiveEndChart_add_fst, positiveEndChartScale_add_fst, smul_smul]
  congr 1
  field_simp

/-- The positive end chart sends the part `s > 0` of the end into `S`. -/
theorem positiveEndChart_mem_thricePuncturedSphereReal {q : Puncture} {z : ℝ × ℝ}
    (hz : 0 < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal := by
  refine endChart_mem_thricePuncturedSphereReal ?_
  simpa [← mul_assoc] using hz

/-- The positive end chart inverts the signed end coordinates `(±Re ζ_q, ±Im ζ_q)` at every point
`z` other than the center of the end `q`. -/
theorem positiveEndChart_endSign_mul_endCoord {q : Puncture} {z : ℝ × ℝ}
    (hw : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    positiveEndChart q (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im) = z := by
  rw [positiveEndChart_mk, endSign_mul_endSign_mul, endSign_mul_endSign_mul, endChart_mk,
    Complex.re_add_im, q.cylindricalEndLift_endCoord hw, ContinuousLinearEquiv.apply_symm_apply]

/-- The signed end coordinates of the image of `y` under the positive end chart are `y`, up to an
integer shift of the angular coordinate. -/
theorem exists_endCoord_positiveEndChart (q : Puncture) (y : ℝ × ℝ) :
    ∃ k : ℤ,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q y))).re = y.1 ∧
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q y))).im =
        y.2 + k := by
  obtain ⟨s, t⟩ := y
  obtain ⟨k, hk⟩ :=
    q.exists_endCoord_cylindricalEndLift (↑(q.endSign * s) + ↑(q.endSign * t) * Complex.I)
  rw [positiveEndChart_mk, endChart_mk, ContinuousLinearEquiv.symm_apply_apply, hk]
  rcases q.endSign_eq_one_or_eq_neg_one with h | h
  · exact ⟨k, by simp [h]⟩
  · exact ⟨-k, by simp [h, add_comm]⟩

/-- The positive end chart is an open map. -/
theorem isOpenMap_positiveEndChart (q : Puncture) : IsOpenMap (positiveEndChart q) := by
  convert ((Complex.equivRealProdCLM.toHomeomorph.isOpenMap.comp
    q.isOpenMap_cylindricalEndLift).comp Complex.equivRealProdCLM.symm.toHomeomorph.isOpenMap).comp
      (Homeomorph.smulOfNeZero _ q.endSign_ne_zero).isOpenMap using 1
  funext z
  simp [positiveEndChart_apply, endChart_apply]

/-- The longitudinal positive end coordinate at the image of a cylinder point under the end chart
is its signed longitudinal coordinate. -/
@[simp]
theorem fst_positiveEndCoord_endChart (q : Puncture) (ζ : ℝ × ℝ) :
    (positiveEndCoord q (endChart q ζ)).1 = q.endSign * ζ.1 := by
  rw [fst_positiveEndCoord, re_endCoord_endChart]

/-- The positive end chart is injective on every band `ℝ × [t₀, t₀ + 1)` of angular width one. -/
theorem injOn_positiveEndChart (q : Puncture) (t₀ : ℝ) :
    InjOn (positiveEndChart q) (univ ×ˢ Ico t₀ (t₀ + 1)) := by
  intro a ha b hb hab
  -- The reflection `v ↦ ±v` keeps the angular coordinates within distance one of each other, so
  -- both reflected points lie in the band of width one starting at the smaller of them.
  have hd : |q.endSign * a.2 - q.endSign * b.2| < 1 := by
    rw [← mul_sub, abs_mul, abs_endSign, one_mul, abs_sub_lt_iff]
    constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  obtain ⟨hab₁, hab₂⟩ := abs_sub_lt_iff.1 hd
  refine smul_right_injective _ q.endSign_ne_zero (injOn_endChart_univ_prod_Ico q
    (min (q.endSign * a.2) (q.endSign * b.2)) ⟨mem_univ _, ?_, ?_⟩ ⟨mem_univ _, ?_, ?_⟩ hab) <;>
    simp only [Prod.smul_snd, smul_eq_mul]
  · exact min_le_left _ _
  · rcases min_cases (q.endSign * a.2) (q.endSign * b.2) with h | h <;> linarith [h.1]
  · exact min_le_right _ _
  · rcases min_cases (q.endSign * a.2) (q.endSign * b.2) with h | h <;> linarith [h.1]

/-! ### The positive end coordinates invert the positive end chart -/

/-- Away from the center of the end, the positive end chart inverts the positive end coordinates. -/
theorem positiveEndChart_positiveEndCoord (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    positiveEndChart q (positiveEndCoord q z) = z := by
  rw [positiveEndChart_apply, positiveEndCoord_apply, smul_smul, endSign_mul_self, one_smul,
    endChart_apply, ContinuousLinearEquiv.symm_apply_apply, q.cylindricalEndLift_endCoord hz,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The positive end coordinates recover a point of the cylinder from its image under the positive
end chart, up to an integer shift of the angular coordinate. -/
theorem exists_positiveEndCoord_positiveEndChart (q : Puncture) (ζ : ℝ × ℝ) :
    ∃ k : ℤ, positiveEndCoord q (positiveEndChart q ζ) = ζ + (0, (k : ℝ)) := by
  obtain ⟨k, hk⟩ :=
    q.exists_endCoord_cylindricalEndLift (Complex.equivRealProdCLM.symm (q.endSign • ζ))
  -- The shift `k i` of the end coordinate becomes the shift `±k` of the positive coordinates.
  have h : positiveEndCoord q (positiveEndChart q ζ) = ζ + (0, q.endSign * k) := by
    rw [positiveEndCoord_apply, positiveEndChart_apply, equivRealProdCLM_symm_endChart, hk]
    ext <;> simp [Complex.equivRealProdCLM_symm_apply, mul_add, ← mul_assoc]
  rcases q.endSign_eq_one_or_eq_neg_one with hσ | hσ
  · exact ⟨k, by rw [h, hσ, one_mul]⟩
  · exact ⟨-k, by rw [h, hσ]; push_cast; ring_nf⟩

/-- The positive end coordinates recover the longitudinal coordinate of a point of the cylinder
from its image under the positive end chart. -/
@[simp]
theorem fst_positiveEndCoord_positiveEndChart (q : Puncture) (ζ : ℝ × ℝ) :
    (positiveEndCoord q (positiveEndChart q ζ)).1 = ζ.1 := by
  obtain ⟨k, hk⟩ := exists_positiveEndCoord_positiveEndChart q ζ
  simp [hk]

/-- A map of period one in the angular coordinate, read in the positive end coordinates of an end
and then in its positive end chart, is the map itself. -/
theorem comp_positiveEndCoord_positiveEndChart {α : Type*} {ξ : ℝ × ℝ → α}
    (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (q : Puncture) :
    (ξ ∘ positiveEndCoord q) ∘ positiveEndChart q = ξ := by
  funext ζ
  obtain ⟨k, hk⟩ := exists_positiveEndCoord_positiveEndChart q ζ
  rw [comp_apply, comp_apply, hk]
  simpa using (periodic_zero_prodMk_iff.2 hξp).zsmul k ζ

/-- The **band coordinates** of a point `z` in the positive end chart of `q`: its positive end
coordinates `(s, t)` (`TauCeti.Floer.positiveEndCoord`) with the angular coordinate reduced to
`[0, 1)`. Away from the center of the end they invert the positive end chart on the band
`ℝ × [0, 1)` (`positiveEndChart_endBandCoord`, `endBandCoord_positiveEndChart`). -/
noncomputable def endBandCoord (q : Puncture) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((positiveEndCoord q z).1, Int.fract (positiveEndCoord q z).2)

theorem endBandCoord_apply (q : Puncture) (z : ℝ × ℝ) :
    endBandCoord q z = ((positiveEndCoord q z).1, Int.fract (positiveEndCoord q z).2) := (rfl)

/-- The band coordinates lie in the band `ℝ × [0, 1)`. -/
theorem endBandCoord_mem (q : Puncture) (z : ℝ × ℝ) :
    endBandCoord q z ∈ (univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1 :=
  ⟨mem_univ _, Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The band coordinates are measurable. -/
theorem measurable_endBandCoord (q : Puncture) : Measurable (endBandCoord q) := by
  rw [funext (endBandCoord_apply q)]
  exact (measurable_positiveEndCoord q).fst.prodMk
    (measurable_fract.comp (measurable_positiveEndCoord q).snd)

/-- A map of period one in the angular coordinate takes the same value at the positive end
coordinates and at the band coordinates of a point. -/
theorem apply_positiveEndCoord_eq_apply_endBandCoord {α : Type*} {ξ : ℝ × ℝ → α}
    (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (q : Puncture) (z : ℝ × ℝ) :
    ξ (positiveEndCoord q z) = ξ (endBandCoord q z) := by
  have hper : Periodic (fun t ↦ ξ ((positiveEndCoord q z).1, t)) 1 := hξp _
  rw [endBandCoord_apply, Periodic.apply_fract hper, Prod.mk.eta]

/-- Away from the center of the end, the positive end chart inverts the band coordinates. -/
theorem positiveEndChart_endBandCoord (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) :
    positiveEndChart q (endBandCoord q z) = z := by
  rw [← apply_positiveEndCoord_eq_apply_endBandCoord (positiveEndChart_add_one q),
    positiveEndChart_positiveEndCoord q hz]

/-- The band coordinates invert the positive end chart on the band `ℝ × [0, 1)`. -/
theorem endBandCoord_positiveEndChart (q : Puncture) {ζ : ℝ × ℝ} (hζ : ζ.2 ∈ Ico (0 : ℝ) 1) :
    endBandCoord q (positiveEndChart q ζ) = ζ := by
  obtain ⟨k, hk⟩ := exists_positiveEndCoord_positiveEndChart q ζ
  rw [endBandCoord_apply, hk]
  ext
  · simp
  · simp [Int.fract_eq_self.2 hζ]

/-- The image of the band `ℝ × [0, 1)` under the positive end chart is the plane with the center
of the end removed. -/
theorem image_positiveEndChart_univ_prod_Ico (q : Puncture) :
    positiveEndChart q '' ((univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1) =
      {z | Complex.equivRealProdCLM.symm z ≠ q.endCenter} := by
  ext z
  constructor
  · rintro ⟨ζ, -, rfl⟩
    exact equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ
  · intro hz
    exact ⟨_, endBandCoord_mem q z, positiveEndChart_endBandCoord q hz⟩

/-- A point at distance more than `2` from `0` lies in the image of the band `(0, ∞) × [0, 1)`
under the positive end chart of the output end. -/
theorem mem_image_positiveEndChart_inf_of_two_lt_norm {v : ℝ × ℝ}
    (hv : 2 < ‖Complex.equivRealProdCLM.symm v‖) :
    v ∈ positiveEndChart inf '' (Ioi 0 ×ˢ Ico 0 1) := by
  have hv0 : Complex.equivRealProdCLM.symm v ≠ 0 := norm_pos_iff.1 (by linarith)
  refine ⟨endBandCoord inf v, ⟨?_, (endBandCoord_mem inf v).2⟩,
    positiveEndChart_endBandCoord inf (by rwa [endCenter_inf])⟩
  rw [endBandCoord_apply, mem_Ioi, lt_fst_positiveEndCoord_inf_iff hv0, mul_zero, exp_zero,
    mul_one]
  exact hv

/-- Every point of `S` lies in the truncation `S_T` or, for some end `q`, in the image under the
positive end chart `φ'_q` of the band `(T, ∞) × [0, 1)`. -/
theorem subset_preimage_truncation_union_iUnion_image_positiveEndChart (T : ℝ) :
    thricePuncturedSphereReal ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation T ∪
      ⋃ q, positiveEndChart q '' (Ioi T ×ˢ Ico 0 1) := by
  intro z hz
  by_cases hzT : Complex.equivRealProdCLM.symm z ∈ truncation T
  · exact Or.inl hzT
  obtain ⟨q, hq⟩ := exists_lt_fst_positiveEndCoord_of_notMem_truncation hz hzT
  set ζ := positiveEndCoord q z
  -- Move the angular coordinate into `[0, 1)` by an integer shift.
  have hper : Periodic (fun t ↦ positiveEndChart q (ζ.1, t)) 1 := positiveEndChart_add_one q ζ.1
  have h := hper.sub_int_mul_eq (x := ζ.2) ⌊ζ.2⌋
  rw [mul_one, ← Int.fract] at h
  refine Or.inr (mem_iUnion.2 ⟨q, (ζ.1, Int.fract ζ.2),
    ⟨hq, Int.fract_nonneg _, Int.fract_lt_one _⟩, h.trans ?_⟩)
  exact positiveEndChart_positiveEndCoord q
    (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)

/-- A function with compact support in `S` vanishes, in the positive end chart of `q`, near every
point beyond some height. -/
theorem exists_forall_comp_positiveEndChart_eventuallyEq_zero {M : Type*} [Zero M]
    {f : ℝ × ℝ → M} (hfc : HasCompactSupport f) (hfS : tsupport f ⊆ thricePuncturedSphereReal)
    (q : Puncture) :
    ∃ N, ∀ ζ : ℝ × ℝ, N < ζ.1 → f ∘ positiveEndChart q =ᶠ[nhds ζ] 0 := by
  -- The longitudinal positive end coordinate is bounded on the support of `f`.
  obtain ⟨N, hN⟩ :=
    hfc.isCompact.exists_bound_of_continuousOn (f := fun w ↦ (positiveEndCoord q w).1) fun z hz ↦
      (continuousAt_fst_positiveEndCoord q
        (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 (hfS hz)) q)).continuousWithinAt
  refine ⟨N, fun ζ hζ ↦ ?_⟩
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ] with ζ' hζ'
  rw [Pi.zero_apply, Function.comp_apply]
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  have := (Real.le_norm_self _).trans (hN _ h)
  rw [fst_positiveEndCoord_positiveEndChart] at this
  exact absurd hζ' (not_lt.2 this)

/-- The Hamiltonian of the end `q` in its positive end chart: `H'_q(t, x) = ±H_q(±t, x)` with the
sign of the end. It is `H_q` on the input ends and `(t, x) ↦ -H_∞(-t, x)` on the output end. -/
noncomputable def positiveEndHamiltonian {X : Type*} (H : Puncture → ℝ → X → ℝ) (q : Puncture)
    (t : ℝ) (x : X) : ℝ := q.endSign * H q (q.endSign * t) x

theorem positiveEndHamiltonian_apply {X : Type*} (H : Puncture → ℝ → X → ℝ) (q : Puncture)
    (t : ℝ) (x : X) : positiveEndHamiltonian H q t x = q.endSign * H q (q.endSign * t) x := (rfl)

/-- On an input end, the end Hamiltonian in the positive end chart is `H_q`. -/
theorem positiveEndHamiltonian_of_endSign_eq_one {X : Type*} (H : Puncture → ℝ → X → ℝ)
    {q : Puncture} (h : q.endSign = 1) : positiveEndHamiltonian H q = H q := by
  funext t x
  simp only [positiveEndHamiltonian_apply, h, one_mul]

/-- On the output end, the end Hamiltonian in the positive end chart is the reversed Hamiltonian
`(t, x) ↦ -H_q(-t, x)`. -/
theorem positiveEndHamiltonian_of_endSign_eq_neg_one {X : Type*} (H : Puncture → ℝ → X → ℝ)
    {q : Puncture} (h : q.endSign = -1) : positiveEndHamiltonian H q = fun t x ↦ -H q (-t) x := by
  funext t x
  simp only [positiveEndHamiltonian_apply, h, neg_one_mul]

/-- Passing to the positive end chart twice gives back the end Hamiltonian:
`(H'_q)'(t, x) = ±(±H_q(±(±t), x)) = H_q(t, x)`. -/
@[simp]
theorem positiveEndHamiltonian_positiveEndHamiltonian {X : Type*} (H : Puncture → ℝ → X → ℝ)
    (q : Puncture) : positiveEndHamiltonian (positiveEndHamiltonian H) q = H q := by
  funext t x
  simp only [positiveEndHamiltonian_apply, endSign_mul_endSign_mul]

theorem periodic_positiveEndHamiltonian {X : Type*} {H : Puncture → ℝ → X → ℝ} {q : Puncture}
    (hH : Periodic (H q) 1) : Periodic (positiveEndHamiltonian H q) 1 := by
  intro t
  funext x
  rcases q.endSign_eq_one_or_eq_neg_one with h | h <;>
    simp only [positiveEndHamiltonian_apply, h, mul_add, mul_one, one_mul, neg_one_mul,
      ← sub_eq_add_neg, hH.sub_eq, hH _]

theorem contDiff_uncurry_positiveEndHamiltonian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Puncture → ℝ → E → ℝ} {q : Puncture} {n : WithTop ℕ∞}
    (hH : ContDiff ℝ n (uncurry (H q))) : ContDiff ℝ n (uncurry (positiveEndHamiltonian H q)) :=
  contDiff_const.mul (hH.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd))

/-- The positive end Hamiltonian of a `Cⁿ` end Hamiltonian on a manifold is `Cⁿ`. -/
theorem contMDiff_uncurry_positiveEndHamiltonian {E G M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M]
    [ChartedSpace G M] {H : Puncture → ℝ → M → ℝ} {q : Puncture} {n : WithTop ℕ∞}
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry (H q))) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry (positiveEndHamiltonian H q)) :=
  contMDiff_uncurry_const_mul_comp_const_mul q.endSign hH

/-- A `1`-periodic loop read with the time `±t` of an end is `1`-periodic. -/
theorem periodic_comp_endSign_mul {α : Type*} {q : Puncture} {x : ℝ → α} (hx : Periodic x 1) :
    Periodic (fun t ↦ x (q.endSign * t)) 1 := by
  have h := hx.const_mul q.endSign
  rw [inv_endSign, mul_one] at h
  rcases q.endSign_eq_one_or_eq_neg_one with hσ | hσ
  · simpa only [hσ] using h
  · simpa only [hσ, neg_neg] using h.neg

/-- The pullback of a perturbation along the positive end chart is the pullback along the end
chart at the reflected point, multiplied by the sign of the end. -/
theorem perturbationPullback_positiveEndChart {X : Type*} {K : ℂ → X → ℂ →L[ℝ] ℝ} (q : Puncture)
    (v ζ : ℝ × ℝ) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v ζ x =
      q.endSign * perturbationPullback (endChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) v (q.endSign • ζ) x := by
  simp only [perturbationPullback_apply, fderiv_positiveEndChart_apply, positiveEndChart_apply,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the positive end chart sends `∂_s`
to `0`. -/
theorem perturbationPullback_positiveEndChart_stdComplexLineReal_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineReal ζ x =
      0 := by
  rw [perturbationPullback_positiveEndChart,
    perturbationPullback_endChart_stdComplexLineReal_of_le hKH (by simpa [← mul_assoc] using hζ),
    mul_zero]

/-- Where `K = H_q(t) dt` on the end `q`, its pullback along the positive end chart sends `∂_t`
to the end Hamiltonian `H'_q(t)` of the positive end. -/
theorem perturbationPullback_positiveEndChart_stdComplexLineImag_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ x =
      positiveEndHamiltonian H q ζ.2 x := by
  rw [perturbationPullback_positiveEndChart,
    perturbationPullback_endChart_stdComplexLineImag_of_le hKH hH
      (by simpa [← mul_assoc] using hζ), positiveEndHamiltonian_apply, Prod.smul_snd, smul_eq_mul]

/-- Where `K = H_q(t) dt` on the end `q`, each component of `K` at the point `φ'_q(ζ)` of the end is
a constant multiple of the end Hamiltonian `H_q(t₀)`, for the end coordinate `t₀` of the point. -/
theorem perturbation_positiveEndChart_eq_mul_of_le {X : Type*}
    {K : ℂ → X → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → X → ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (x : X) (v : ℂ) :
    K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v =
      q.endAngularForm (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) v *
        H q (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).im x := by
  have hre : T₀ ≤ q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  rw [hKH _ x hre, smul_apply, smul_eq_mul, mul_comm]

/-- Where `K = H_q(t) dt` on the end `q` and the Hamiltonians `H_q(t)` are differentiable, the
components of `K` at the point `φ'_q(ζ)` of the end are differentiable in the target point. -/
theorem differentiableAt_perturbation_positiveEndChart {K : ℂ → V → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    {q : Puncture} (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hHd : ∀ t, Differentiable ℝ (H q t)) {ζ : ℝ × ℝ} (hζ : T₀ ≤ ζ.1) (v : ℂ)
    (y : V) :
    DifferentiableAt ℝ (fun x ↦ K (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v)
      y := by
  simp only [perturbation_positiveEndChart_eq_mul_of_le hKH hζ]
  exact ((hHd _) y).const_mul _

end Floer

end TauCeti
