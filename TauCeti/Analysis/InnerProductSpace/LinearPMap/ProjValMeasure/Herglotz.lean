/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Herglotz.Finite
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# The Herglotz measure of a resolvent matrix element

Let `A` be a self-adjoint partial linear map on a complex Hilbert space and `v` a vector. In the
resolvent convention `(A - z)⁻¹ = -R(z)`, where `R(z) = (z - A)⁻¹` is `LinearPMap.resolvent`, the
function `F_v(z) = ⟪v, (A - z)⁻¹ v⟫` is the resolvent transform of the diagonal spectral measure
`μ_v` of `A` (`IsSelfAdjoint.neg_inner_resolvent_apply_eq_resolventTransform`). It has nonnegative
imaginary part on the upper half-plane and `y ‖F_v(i y)‖ ≤ μ_v(ℝ)`, so in every Herglotz
representation `F_v z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` with `ν` of finite
weighted mass `∫ (1 + t ^ 2)⁻¹ dν < ∞`, the measure `ν` is finite and `F_v` is its resolvent
transform. By Stieltjes inversion the measure is then `μ_v`
(`IsSelfAdjoint.eq_spectralPVM_diag_of_eq_subtractedResolventKernel_add`).

Polarization then reconstructs the whole spectral measure from these Herglotz measures: if `ν_v`
is the Herglotz measure of `F_v` for every `v`, then for every Borel set `B`
`⟪ψ, P_A(B) ξ⟫ = ¼ (ν_(ξ+ψ)(B) + i ν_(ξ+iψ)(B) - ν_(ξ-ψ)(B) - i ν_(ξ-iψ)(B))`
(`IsSelfAdjoint.inner_spectralPVM_proj_eq_of_eq_subtractedResolventKernel_add`).

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, §3.4, Theorem 3.20 and the discussion of
  spectral measures there.
* N. I. Akhiezer, *The Classical Moment Problem*, §3.1, for Stieltjes inversion.
-/

public section

noncomputable section

open Complex MeasureTheory TauCeti Filter
open scoped InnerProductSpace

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

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
    rw [hF _ (by simpa using hy)]
    exact mul_norm_resolventTransform_ofReal_mul_I_le hy
  have := isFiniteMeasure_of_eq_subtractedResolventKernel_add_of_bound hnu hrep
    (eventually_mul_abs_im_le_of_mul_norm_le hbound)
  have hm := eq_resolventTransform_of_eq_subtractedResolventKernel_add_of_bound hrep hbound
  exact Measure.ext_of_resolventTransform fun z hz ↦ (hm z hz).symm.trans (hF z hz)

/-- **Polarization reconstructs the spectral measure from the Herglotz measures.** If for every
vector `v` the resolvent matrix element `⟪v, (A - z)⁻¹ v⟫` has a Herglotz representation
`a v + b v z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν_v(t)` on the upper half-plane, with `ν_v` of
finite weighted mass, then every matrix element of the spectral projection `P_A(B)` is the
polarization `¼ (ν_(ξ+ψ)(B) + i ν_(ξ+iψ)(B) - ν_(ξ-ψ)(B) - i ν_(ξ-iψ)(B))`. -/
theorem _root_.IsSelfAdjoint.inner_spectralPVM_proj_eq_of_eq_subtractedResolventKernel_add
    (hA : IsSelfAdjoint A) {a b : H → ℝ} {nu : H → Measure ℝ}
    (hnu : ∀ v, ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu v < ⊤)
    (hrep : ∀ v, ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      -⟪v, A.resolvent z v⟫_ℂ = a v + b v * z + ∫ t, subtractedResolventKernel z t ∂nu v)
    (ψ ξ : H) {B : Set ℝ} (hB : MeasurableSet B) :
    ⟪ψ, (A.spectralPVM hA).proj B hB ξ⟫_ℂ =
      (1 / 4 : ℂ) * ((nu (ξ + ψ)).real B + I * (nu (ξ + I • ψ)).real B -
        (nu (ξ - ψ)).real B - I * (nu (ξ - I • ψ)).real B) := by
  have hdiag (v : H) : nu v = (A.spectralPVM hA).diag v :=
    hA.eq_spectralPVM_diag_of_eq_subtractedResolventKernel_add v (hnu v) (hrep v)
  set P := A.spectralPVM hA
  have hpol := LinearMap.inner_polarization (P.proj B hB) ψ ξ
  rw [ContinuousLinearMap.coe_coe, P.inner_proj B hB (ξ + ψ), P.inner_proj B hB (ξ + I • ψ),
    P.inner_proj B hB (ξ - ψ), P.inner_proj B hB (ξ - I • ψ)] at hpol
  rw [← hpol]
  simp only [hdiag, measureReal_def]

end LinearPMap
