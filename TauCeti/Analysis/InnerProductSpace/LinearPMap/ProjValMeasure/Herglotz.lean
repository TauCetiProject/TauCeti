/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.HerglotzFinite
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# The Herglotz measure of a resolvent matrix element

Let `A` be a self-adjoint partial linear map on a complex Hilbert space and `v` a vector. In the
resolvent convention `(A - z)⁻¹ = -R(z)`, where `R(z) = (z - A)⁻¹` is `LinearPMap.resolvent`, the
function `F_v(z) = ⟪v, (A - z)⁻¹ v⟫` is the resolvent transform of the diagonal spectral measure
`μ_v` of `A` (`IsSelfAdjoint.neg_inner_resolvent_apply_eq_resolventTransform`). It has nonnegative
imaginary part on the upper half-plane and `y ‖F_v(i y)‖ ≤ μ_v(ℝ)`, so in every Herglotz
representation `F_v z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` the measure `ν` is finite
and `F_v` is its resolvent transform. By Stieltjes inversion the measure is then `μ_v`
(`IsSelfAdjoint.eq_spectralPVM_diag_of_eq_subtractedResolventKernel_add`).

## References

* TauCetiRoadmap, `AutomorphicSpectralTheory/README.md`, §0.5 (Herglotz representation, the
  resolvent case).
-/

public section

noncomputable section

open Complex MeasureTheory TauCeti Filter
open scoped InnerProductSpace

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- In the resolvent convention `(A - z)⁻¹ = -R(z)`, the diagonal matrix element
`⟪v, (A - z)⁻¹ v⟫` is the resolvent transform `∫ (s - z)⁻¹ dμ_v(s)` of the diagonal spectral
measure. -/
theorem _root_.IsSelfAdjoint.neg_inner_resolvent_apply_eq_resolventTransform
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z ∈ A.resolventSet) (v : H) :
    -⟪v, A.resolvent z v⟫_ℂ = resolventTransform ((A.spectralPVM hA).diag v) z := by
  rw [hA.inner_resolvent_apply_eq_integral hz, resolventTransform_apply, ← integral_neg]
  congr 1 with s
  rw [_root_.resolvent, Ring.inverse_eq_inv', ← inv_neg, neg_sub, Complex.coe_algebraMap]

/-- **The Herglotz measure of a resolvent matrix element is the spectral measure.** If
`⟪v, (A - z)⁻¹ v⟫ = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` on the upper half-plane, with
`ν` of finite weighted mass, then `ν` is the diagonal spectral measure `μ_v` of `A`. -/
theorem _root_.IsSelfAdjoint.eq_spectralPVM_diag_of_eq_subtractedResolventKernel_add
    (hA : IsSelfAdjoint A) (v : H) {a b : ℝ} {nu : Measure ℝ}
    (hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      -⟪v, A.resolvent z v⟫_ℂ = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu) :
    nu = (A.spectralPVM hA).diag v := by
  set μ := (A.spectralPVM hA).diag v
  have hF (z : ℂ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
      -⟪v, A.resolvent z v⟫_ℂ = resolventTransform μ z :=
    hA.neg_inner_resolvent_apply_eq_resolventTransform
      (hA.mem_resolventSet_of_im_ne_zero (ne_of_gt hz)) v
  have hbound : ∀ᶠ y : ℝ in atTop, y * ‖-⟪v, A.resolvent (y * I) v⟫_ℂ‖ ≤ μ.real Set.univ := by
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hz : ((y : ℂ) * I).im ≠ 0 := by simpa using hy.ne'
    rw [hF _ (by simpa using hy)]
    have := norm_resolventTransform_le (μ := μ) hz
    rw [show ((y : ℂ) * I).im = y by simp, abs_of_pos hy] at this
    calc y * ‖resolventTransform μ (y * I)‖ ≤ y * (y⁻¹ * μ.real Set.univ) := by gcongr
      _ = μ.real Set.univ := by field_simp
  have := isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hnu hrep hbound
  have hm := eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound hrep hbound
  exact Measure.ext_of_resolventTransform fun z hz ↦ (hm z hz).symm.trans (hF z hz)

end LinearPMap
