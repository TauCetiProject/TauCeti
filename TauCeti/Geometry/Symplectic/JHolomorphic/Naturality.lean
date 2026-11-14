/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Linearization

/-!
# Naturality of the Cauchy–Riemann linearization

The local expression for the linearized Cauchy–Riemann operator transforms tensorially at a
pseudoholomorphic map. If a `C²` target map `Φ` intertwines the target endomorphism fields `J`
and `K` near `u x`, then its differential carries `D_u ξ` to
`D_(Φ ∘ u) (dΦ ∘ ξ)` at a zero of the Cauchy–Riemann defect. This is the overlap identity
needed to define the linearization independently of target coordinates.

We also retain the off-zero formula: the additional term is the second derivative of `Φ`
applied to the variation and the nonlinear defect. Thus tensorial transformation holds at
solutions without assuming that `J` is integrable or that the coordinate change is affine.
The endomorphisms need not square to minus one for these chain-rule identities.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (linearization and its independence of coordinates at a holomorphic map).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter
open scoped ContDiff Topology

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The nonlinear Cauchy–Riemann defect is natural under a differentiable target map whose
differential intertwines the target endomorphisms at the image point. -/
theorem cauchyRiemannOperator_comp
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (K : W → W →L[ℝ] W)
    (u : U → V) (Φ : V → W) (x : U)
    (hu : DifferentiableAt ℝ u x) (hΦ : DifferentiableAt ℝ Φ (u x))
    (hJK : (fderiv ℝ Φ (u x)).comp (J (u x)) =
      (K (Φ (u x))).comp (fderiv ℝ Φ (u x))) :
    cauchyRiemannOperator j K (Φ ∘ u) x =
      (fderiv ℝ Φ (u x)).comp (cauchyRiemannOperator j J u x) := by
  ext v
  have h := congrArg (fun L : V →L[ℝ] W ↦ L (fderiv ℝ u x v)) hJK
  simp only [comp_apply] at h
  simp only [cauchyRiemannOperator_apply, fderiv_comp x hΦ hu, comp_apply,
    Function.comp_apply, map_sub]
  rw [h]

/-- Under a `C²` target map intertwining `J` and `K` near the image, the linearization
transforms by the differential, with a second-derivative correction proportional to the
nonlinear Cauchy–Riemann defect; evaluated form. -/
theorem cauchyRiemannLinearization_comp_apply
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (K : W → W →L[ℝ] W)
    (u ξ : U → V) (Φ : V → W) (x v : U)
    (hu : DifferentiableAt ℝ u x) (hξ : DifferentiableAt ℝ ξ x)
    (hΦ : ContDiffAt ℝ 2 Φ (u x)) (hJ : DifferentiableAt ℝ J (u x))
    (hK : DifferentiableAt ℝ K (Φ (u x)))
    (hJK : ∀ᶠ y in 𝓝 (u x), (fderiv ℝ Φ y).comp (J y) =
      (K (Φ y)).comp (fderiv ℝ Φ y)) :
    cauchyRiemannLinearization j K (Φ ∘ u)
        (fun y ↦ fderiv ℝ Φ (u y) (ξ y)) x v =
      fderiv ℝ Φ (u x) (cauchyRiemannLinearization j J u ξ x v) +
        fderiv ℝ (fderiv ℝ Φ) (u x) (ξ x) (cauchyRiemannOperator j J u x v) := by
  have hdΦ := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hΦu := hΦ.differentiableAt (by norm_num)
  have hs := hΦ.isSymmSndFDerivAt (by norm_num)
  -- Differentiate the target intertwining identity in the variation direction.
  have hleft := (hdΦ.hasFDerivAt.clm_apply
    (hJ.hasFDerivAt.clm_apply (hasFDerivAt_const (x := u x) (fderiv ℝ u x v)))).fderiv
  have hright := ((hK.hasFDerivAt.comp (u x) hΦu.hasFDerivAt).clm_apply
    (hdΦ.hasFDerivAt.clm_apply (hasFDerivAt_const (x := u x) (fderiv ℝ u x v)))).fderiv
  have heq : (fun z ↦ fderiv ℝ Φ z (J z (fderiv ℝ u x v))) =ᶠ[𝓝 (u x)]
      (fun z ↦ K (Φ z) (fderiv ℝ Φ z (fderiv ℝ u x v))) := by
    filter_upwards [hJK] with z hz
    exact congrArg (fun L : V →L[ℝ] W ↦ L (fderiv ℝ u x v)) hz
  have ht := congrArg (fun L : V →L[ℝ] W ↦ L (ξ x))
    (hleft.symm.trans (heq.fderiv_eq.trans hright))
  simp only [add_apply, comp_apply, flip_apply, zero_apply, map_zero, zero_add,
    Function.comp_apply] at ht
  -- Expand the derivative of the pushed-forward variation; symmetry cancels its Hessian terms.
  have hpush := ((hdΦ.hasFDerivAt.comp x hu.hasFDerivAt).clm_apply hξ.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hpush
  have hbase := congrArg (fun L : V →L[ℝ] W ↦ L (fderiv ℝ ξ x v)) hJK.self_of_nhds
  simp only [comp_apply] at hbase
  simp only [cauchyRiemannLinearization_apply, cauchyRiemannOperator_apply,
    hpush, fderiv_comp x hΦu hu, add_apply, comp_apply, flip_apply, Function.comp_apply,
    map_add, map_sub]
  rw [hs (fderiv ℝ u x (j v)) (ξ x), hs (fderiv ℝ u x v) (ξ x)]
  rw [hbase]
  linear_combination (norm := module) ht

/-- Under a `C²` target map intertwining `J` and `K` near the image, the linearization
transforms by the differential, with a second-derivative correction proportional to the
nonlinear Cauchy–Riemann defect. -/
theorem cauchyRiemannLinearization_comp
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (K : W → W →L[ℝ] W)
    (u ξ : U → V) (Φ : V → W) (x : U)
    (hu : DifferentiableAt ℝ u x) (hξ : DifferentiableAt ℝ ξ x)
    (hΦ : ContDiffAt ℝ 2 Φ (u x)) (hJ : DifferentiableAt ℝ J (u x))
    (hK : DifferentiableAt ℝ K (Φ (u x)))
    (hJK : ∀ᶠ y in 𝓝 (u x), (fderiv ℝ Φ y).comp (J y) =
      (K (Φ y)).comp (fderiv ℝ Φ y)) :
    cauchyRiemannLinearization j K (Φ ∘ u)
        (fun y ↦ fderiv ℝ Φ (u y) (ξ y)) x =
      (fderiv ℝ Φ (u x)).comp (cauchyRiemannLinearization j J u ξ x) +
        (fderiv ℝ (fderiv ℝ Φ) (u x) (ξ x)).comp (cauchyRiemannOperator j J u x) := by
  ext v
  rw [cauchyRiemannLinearization_comp_apply j J K u ξ Φ x v hu hξ hΦ hJ hK hJK, add_apply,
    comp_apply, comp_apply]

/-- At a zero of the Cauchy–Riemann defect, the linearization is natural under a `C²`
target coordinate change. No integrability of the target structures is required. -/
theorem cauchyRiemannLinearization_comp_of_cauchyRiemannOperator_eq_zero
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (K : W → W →L[ℝ] W)
    (u ξ : U → V) (Φ : V → W) (x : U)
    (hu : DifferentiableAt ℝ u x) (hξ : DifferentiableAt ℝ ξ x)
    (hΦ : ContDiffAt ℝ 2 Φ (u x)) (hJ : DifferentiableAt ℝ J (u x))
    (hK : DifferentiableAt ℝ K (Φ (u x)))
    (hJK : ∀ᶠ y in 𝓝 (u x), (fderiv ℝ Φ y).comp (J y) =
      (K (Φ y)).comp (fderiv ℝ Φ y))
    (hhol : cauchyRiemannOperator j J u x = 0) :
    cauchyRiemannLinearization j K (Φ ∘ u)
        (fun y ↦ fderiv ℝ Φ (u y) (ξ y)) x =
      (fderiv ℝ Φ (u x)).comp (cauchyRiemannLinearization j J u ξ x) := by
  rw [cauchyRiemannLinearization_comp j J K u ξ Φ x hu hξ hΦ hJ hK hJK, hhol, comp_zero,
    add_zero]

end TauCeti
