/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.PointwiseDecay
public import Mathlib.Topology.Compactification.OnePoint.Basic
import TauCeti.Analysis.Calculus.FDeriv.Puncture
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Puncture
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex

/-!
# Continuous removal of finite-energy punctures

A finite-energy solution of the Cauchy--Riemann equation on a punctured disc, with compact
image and a uniformly taming target structure, extends continuously across the puncture.
The extension takes values in the same compact set and is continuous on the entire original
disc. The target structure may vary with the image point. The original value of the map at
the puncture is unrestricted and is replaced by its limit using `Function.update`.

The same holds at the end of a plane. A finite-energy solution on the exterior `‖z‖ > R` of a
disc, with compact image, has a limit at infinity
(`SymplecticForm.exists_tendsto_cocompact_of_finite_energy`). The inverted map `w ↦ u w⁻¹` again
solves the Cauchy--Riemann equation on the punctured disc of radius `R⁻¹`, since the inversion is
holomorphic, and it again has finite energy: the Jacobian `‖w‖⁻⁴` of the inversion cancels the
square of its conformal factor `‖w‖⁻²`, up to the norm of the target structure, which is bounded
because the structure need only be tamed, not compatible. A finite-energy solution on the whole
plane therefore extends to a continuous map on the Riemann sphere `OnePoint ℂ`
(`SymplecticForm.exists_continuous_onePoint_elim_of_finite_energy`). This identifies the end at
infinity of a finite-energy plane with a point of a sphere, which is what turns a plane obtained by
rescaling at a bubbling point into a bubble sphere.

This is the continuous part of removal of singularities for pseudoholomorphic curves.
It does not assert differentiability at the puncture or the Cauchy--Riemann equation there;
those require elliptic regularity for the extended map.

The analytic inputs are
`SymplecticForm.exists_pos_integrableOn_deriv_radial` (finite radial length) and
`TauCeti.tendsto_norm_sub_mul_norm_fderiv_nhdsNE` (shrinking circle images).
`TauCeti.exists_continuousOn_update_of_integrableOn_radial_deriv_of_tendsto` combines them.
The real inner product is the caller's, identified with a fixed compatible symplectic metric;
no alternative norm or inner-product instance is installed.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c : ℝ} {W K : Set V}

open Classical in
/-- **Continuous removal of a finite-energy puncture.** A `C³` pseudoholomorphic curve on a
punctured disc with compact image, uniformly positive taming constant, and `C²`
target structure near its image has a limit at the puncture. Updating the map at that point yields a
continuous map on the original disc with image in the same compact set.

The fixed structure `J₀` identifies the given inner product with a symplectic metric. The
varying structure `J` need only be tamed, not compatible. No regularity at the puncture is
assumed or concluded beyond continuity. -/
theorem exists_continuousOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧
      ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  have hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M := fun z hz ↦ hM _ (huK hz)
  obtain ⟨ε, hε, hεR, hrad⟩ := ω.exists_pos_integrableOn_deriv_radial
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame hbound henergy
  have hsub : ball z₀ ε \ {z₀} ⊆ ball z₀ R \ {z₀} :=
    sdiff_subset_sdiff_left (ball_subset_ball hεR.le)
  have hdiff : DifferentiableOn ℝ u (ball z₀ ε \ {z₀}) :=
    (hu.mono hsub).differentiableOn (by norm_num)
  have hrad' : IntegrableOn (deriv (fun t : ℝ ↦ u (z₀ + (t : ℂ)))) (Ioo 0 ε) := by
    simpa only [Complex.real_smul, mul_one] using hrad (1 : ℂ) (by simp)
  obtain ⟨q, hlim, _⟩ :=
    exists_continuousOn_update_of_integrableOn_radial_deriv_of_tendsto hε hdiff hrad'
      (tendsto_norm_sub_mul_norm_fderiv_nhdsNE hW hJ hK hKW hJsq hR hu hCR huK henergy)
  have hqK : q ∈ K := hK.isClosed.mem_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds z₀ hR)] with z hz hzR
    exact huK ⟨hzR, hz⟩)
  -- The limit is local, but the original map is already continuous everywhere else in the disc.
  refine ⟨q, hqK, hlim, continuousOn_update_iff.mpr ⟨hu.continuousOn, fun _ ↦ ?_⟩, ?_⟩
  · exact hlim.mono_left (nhdsWithin_mono _ (sdiff_subset_compl _ _))
  · intro z hz
    by_cases hzz : z = z₀
    · subst z
      simpa using hqK
    · simpa [Function.update_of_ne hzz] using huK ⟨hz, hzz⟩

omit [FiniteDimensional ℝ V] in
/-- A real-linear map out of `ℂ` sending `i` to `A (L 1)` is determined by `L 1`:
`L a = re a • L 1 + im a • A (L 1)`. -/
private theorem apply_eq_re_smul_add_im_smul {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V}
    (hL : L I = A (L 1)) (a : ℂ) : L a = a.re • L 1 + a.im • A (L 1) := by
  conv_lhs => rw [show a = a.re • (1 : ℂ) + a.im • I by apply Complex.ext <;> simp]
  rw [map_add, map_smul, map_smul, hL]

omit [FiniteDimensional ℝ V] in
/-- The derivative of `w ↦ u w⁻¹` at `w ≠ 0` is the derivative of `u` at `w⁻¹` precomposed with
multiplication by `-(w ^ 2)⁻¹`. -/
private theorem fderiv_comp_inv_apply {w : ℂ} (hw : w ≠ 0) (hu : DifferentiableAt ℝ u w⁻¹)
    (h : ℂ) : fderiv ℝ (fun w ↦ u w⁻¹) w h = fderiv ℝ u w⁻¹ (-(w ^ 2)⁻¹ * h) := by
  have hinv : HasFDerivAt (fun w : ℂ ↦ w⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(w ^ 2)⁻¹)).restrictScalars ℝ) w :=
    (hasDerivAt_inv hw).hasFDerivAt.restrictScalars ℝ
  have hv : HasFDerivAt (fun w ↦ u w⁻¹) ((fderiv ℝ u w⁻¹).comp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(w ^ 2)⁻¹)).restrictScalars ℝ)) w :=
    hu.hasFDerivAt.comp w hinv
  rw [hv.fderiv]
  simp [mul_comm]

/-- The inversion maps the punctured disc of radius `R⁻¹` into the exterior of the closed disc of
radius `R`. -/
private theorem mapsTo_inv_ball_sdiff (hR : 0 < R) :
    MapsTo (·⁻¹) (ball (0 : ℂ) R⁻¹ \ {0}) (closedBall 0 R)ᶜ := by
  rintro w ⟨hw, hw0⟩
  simp only [mem_ball_zero_iff, mem_singleton_iff] at hw hw0
  simpa [norm_inv] using (lt_inv_comm₀ (norm_pos_iff.2 hw0) hR).1 hw

/-- **The energy near infinity is the energy of the inverted map near zero**, up to a constant:
for a solution of `∂ₜu = J(u) ∂ₛu` outside the disc of radius `R`, with `‖J‖ ≤ M` along it, the
map `w ↦ u w⁻¹` has integrable energy density on the disc of radius `R⁻¹` whenever `u` has
integrable energy density outside the disc of radius `R`. The Jacobian `‖w‖⁻⁴` of the inversion
cancels the square of its conformal factor `‖w‖⁻²`. -/
private theorem integrableOn_norm_fderiv_comp_inv_sq (hR : 0 < R) {M : ℝ}
    (hu : DifferentiableOn ℝ u (closedBall 0 R)ᶜ)
    (hCR : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hM : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (closedBall 0 R)ᶜ) :
    IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w 1‖ ^ 2) (ball 0 R⁻¹) := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  set D : Set ℂ := ball 0 R⁻¹ \ {0}
  have hDm : MeasurableSet D := measurableSet_ball.diff (measurableSet_singleton 0)
  have hdu (w : ℂ) (hw : w ∈ D) : DifferentiableAt ℝ u w⁻¹ :=
    hu.differentiableAt (isClosed_closedBall.isOpen_compl.mem_nhds (mapsTo_inv_ball_sdiff hR hw))
  -- The change of variables `z = w⁻¹`, whose real Jacobian is `‖w‖⁻⁴ = ‖-(w ^ 2)⁻¹‖ ^ 2`.
  set f' : ℂ → ℂ →L[ℝ] ℂ := fun w ↦
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(w ^ 2)⁻¹)).restrictScalars ℝ
  have hdet (w : ℂ) : |(f' w).det| = ‖-(w ^ 2)⁻¹‖ ^ 2 := by
    have : (f' w : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ (-(w ^ 2)⁻¹) := by
      ext h
      simp [f', mul_comm]
    rw [ContinuousLinearMap.det, this, ← Algebra.norm_apply, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  have hchange := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (f' := f') volume hDm
    (fun w hw ↦ ((hasDerivAt_inv hw.2).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    inv_injective.injOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2)).1
    (henergy.mono_set (mapsTo_inv_ball_sdiff hR).image_subset)
  -- Pointwise, `‖∂ₛ(u ∘ inv)‖ ≤ (1 + |M|) ‖w‖⁻² ‖∂ₛu‖` by the Cauchy--Riemann equation.
  have hbound (w : ℂ) (hw : w ∈ D) : ‖fderiv ℝ (fun w ↦ u w⁻¹) w 1‖ ^ 2 ≤
      (1 + |M|) ^ 2 * (|(f' w).det| * ‖fderiv ℝ u w⁻¹ 1‖ ^ 2) := by
    set b := -(w ^ 2)⁻¹
    set L := fderiv ℝ u w⁻¹
    have hJ : ‖J (u w⁻¹) (L 1)‖ ≤ |M| * ‖L 1‖ := ((J (u w⁻¹)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((hM _ (mapsTo_inv_ball_sdiff hR hw)).trans (le_abs_self M))
        (norm_nonneg _))
    have hle : ‖L b‖ ≤ (1 + |M|) * (‖b‖ * ‖L 1‖) := by
      rw [apply_eq_re_smul_add_im_smul (hCR _ (mapsTo_inv_ball_sdiff hR hw)) b]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h₁ := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm b) (norm_nonneg (L 1))
      have h₂ := mul_le_mul (Complex.abs_im_le_norm b) hJ (norm_nonneg _) (norm_nonneg b)
      nlinarith
    rw [fderiv_comp_inv_apply hw.2 (hdu w hw), mul_one, hdet]
    calc ‖L b‖ ^ 2 ≤ ((1 + |M|) * (‖b‖ * ‖L 1‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = (1 + |M|) ^ 2 * (‖b‖ ^ 2 * ‖L 1‖ ^ 2) := by ring
  have hD : IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w 1‖ ^ 2) D := by
    refine Integrable.mono' (hchange.const_mul ((1 + |M|) ^ 2))
      ((measurable_fderiv_apply_const ℝ _ 1).norm.pow_const 2).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hDm).2 (Eventually.of_forall fun w hw ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [smul_eq_mul] using hbound w hw
  exact hD.congr_set_ae (sdiff_null_ae_eq_self (measure_singleton 0)).symm

/-- **A finite-energy plane has a limit at infinity.** A `C³` pseudoholomorphic curve on the
exterior `‖z‖ > R` of a disc, with compact image, uniformly positive taming constant, `C²` target
structure near its image and integrable energy density, converges to a point of its image set as
`z → ∞`. -/
theorem exists_tendsto_cocompact_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (closedBall 0 R)ᶜ)
    (hCR : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (closedBall 0 R)ᶜ K)
    (htame : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (closedBall 0 R)ᶜ) :
    ∃ q ∈ K, Tendsto u (cocompact ℂ) (𝓝 q) := by
  have hDE := mapsTo_inv_ball_sdiff hR
  have hdu : DifferentiableOn ℝ u (closedBall 0 R)ᶜ := hu.differentiableOn (by norm_num)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  -- The inverted map `w ↦ u w⁻¹` is a finite-energy solution on the punctured disc of radius `R⁻¹`.
  have hCRv (w : ℂ) (hw : w ∈ ball 0 R⁻¹ \ {0}) : fderiv ℝ (fun w ↦ u w⁻¹) w I =
      J (u w⁻¹) (fderiv ℝ (fun w ↦ u w⁻¹) w 1) := by
    have hdw : DifferentiableAt ℝ u w⁻¹ :=
      hdu.differentiableAt (isClosed_closedBall.isOpen_compl.mem_nhds (hDE hw))
    have hL : fderiv ℝ u w⁻¹ I = J (u w⁻¹) (fderiv ℝ u w⁻¹ 1) := hCR _ (hDE hw)
    rw [fderiv_comp_inv_apply hw.2 hdw, fderiv_comp_inv_apply hw.2 hdw, mul_one,
      apply_eq_re_smul_add_im_smul hL (-(w ^ 2)⁻¹ * I),
      apply_eq_re_smul_add_im_smul hL (-(w ^ 2)⁻¹), map_add, map_smul, map_smul,
      hJsq _ (huK (hDE hw)), mul_I_re, mul_I_im, neg_smul, smul_neg]
    abel
  obtain ⟨q, hqK, hlim, -, -⟩ := ω.exists_continuousOn_update_of_finite_energy hg hc
    (inv_pos.2 hR) hW hJ hK hKW hJsq (hu.comp ((contDiffOn_inv ℝ).mono fun w hw ↦ hw.2) hDE)
    hCRv (huK.comp hDE) (fun w hw ↦ htame _ (hDE hw))
    (integrableOn_norm_fderiv_comp_inv_sq hR hdu hCR (fun z hz ↦ hM _ (huK hz)) henergy)
  refine ⟨q, hqK, ?_⟩
  rw [← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using hlim.comp tendsto_inv₀_cobounded'

/-- **A finite-energy plane extends to a sphere.** A `C³` pseudoholomorphic curve on the whole
plane, with compact image, uniformly positive taming constant, `C²` target structure near its image
and integrable energy density, extends continuously to the Riemann sphere `OnePoint ℂ`: sending
the point at infinity to the limit of the curve gives a continuous map with image in the same
compact set. -/
theorem exists_continuous_onePoint_elim_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hu : ContDiff ℝ 3 u)
    (hCR : ∀ z, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (huK : ∀ z, u z ∈ K)
    (htame : ∀ z v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : Integrable (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2)) :
    ∃ q ∈ K, Continuous (fun x : OnePoint ℂ ↦ x.elim q u) := by
  obtain ⟨q, hqK, hlim⟩ := ω.exists_tendsto_cocompact_of_finite_energy hg hc one_pos hW hJ hK
    hKW hJsq hu.contDiffOn (fun z _ ↦ hCR z) (fun z _ ↦ huK z) (fun z _ ↦ htame z)
    henergy.integrableOn
  refine ⟨q, hqK, (OnePoint.continuous_iff _).2 ⟨?_, hu.continuous⟩⟩
  rw [coclosedCompact_eq_cocompact]
  exact hlim

end TauCeti.SymplecticForm
