/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.ConformalLaplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback

/-!
# Conformal covariance of the conformal Laplacian

For a smooth positive function `u` and `ĝ = u ^ (4 / (n - 2)) g`, the conformal Laplacian obeys

`L_ĝ v = u ^ (-(n + 2) / (n - 2)) L_g (u v)`.

The operators are evaluated on the distinct manifold copies `WithMetric ĝ` and `WithMetric g`.
The functions and evaluation points are transported by their tautological diffeomorphisms to
`M`; each copy carries only its selected metric.

The scalar-curvature formula already gives the identity on positive smooth functions by
comparing two successive rescalings with their product. Linearity extends it to every smooth
real function, including unbounded and sign-changing functions, without a compactness assumption.
This is the smooth operator identity; extensions to weak Sobolev domains require additional
analytic arguments.

## Main results

* `Bundle.ContMDiffRiemannianMetric.conformalLaplacian_rescale`: smooth operator covariance.
* `Bundle.ContMDiffRiemannianMetric.integral_mul_conformalLaplacian_rescale`: invariance of
  the bilinear operator pairing.
* `scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian_withMetric`:
  the scalar-curvature identity with the operator on its metric-indexed copy.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.

The central formal input is `TauCeti.Yamabe.scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian`.
Naturality of scalar curvature uses `Bundle.ContMDiffRiemannianMetric.scalarCurvature_pullback`.
-/

public section

open Bundle Module TauCeti TauCeti.Yamabe
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- The conformal scalar-curvature formula with the original operator evaluated on its
metric-indexed manifold copy. -/
theorem scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian_withMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hu_pos : ∀ x, 0 < u x) (x : M) :
    (g.rescale (fun y ↦ u y ^ (4 / ((finrank ℝ E : ℝ) - 2)))
      (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') _)
      (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _)).scalarCurvature x =
    u x ^ (-((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2)) *
      conformalLaplacian I (u ∘ WithMetric.ofWithMetric) (WithMetric.toWithMetric g x) := by
  have huc := hu.comp (WithMetric.contMDiff_ofWithMetric (g := g))
  have h := scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian
    (WithMetric.metric g) hn (fun y ↦ hu_pos y.ofWithMetric)
    (hf := huc.rpow_const_of_ne (fun y ↦ (hu_pos y.ofWithMetric).ne') _)
    (hf_pos := fun y ↦ Real.rpow_pos_of_pos (hu_pos y.ofWithMetric) _)
    (WithMetric.toWithMetric g x)
  have hpull := ContMDiffRiemannianMetric.pullback_rescale
    (g := g) (f := (WithMetric.ofWithMetric : WithMetric g → M))
    (hf := WithMetric.contMDiff_ofWithMetric)
    (hinj := fun y ↦ by
      rw [WithMetric.mfderiv_ofWithMetric]
      exact Function.injective_id)
    (fun y ↦ u y ^ (4 / ((finrank ℝ E : ℝ) - 2)))
    (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') _)
    (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _)
  -- Identify the rescaled pullback with the pullback of the rescaled metric.
  simp only [Function.comp_def] at hpull
  conv_lhs at h => rw [WithMetric.metric_def]
  rw [← hpull] at h
  rw [ContMDiffRiemannianMetric.scalarCurvature_pullback_of_isInvertible] at h
  · exact h
  · intro y
    rw [WithMetric.mfderiv_ofWithMetric]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩

/-- Covariance on positive smooth functions, obtained by comparing successive rescalings. -/
private theorem conformalLaplacian_rescale_pos
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hu_pos : ∀ x, 0 < u x) (hv : ContMDiff I 𝓘(ℝ) ∞ v) (hv_pos : ∀ x, 0 < v x)
    (x : M) :
    conformalLaplacian I (v ∘ WithMetric.ofWithMetric)
        (WithMetric.toWithMetric (g.rescale (fun y ↦ u y ^ (4 / ((finrank ℝ E : ℝ) - 2)))
          (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') _)
          (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _)) x) =
      u x ^ (-((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2)) *
        conformalLaplacian I ((u * v) ∘ WithMetric.ofWithMetric) (WithMetric.toWithMetric g x) := by
  let p : ℝ := 4 / ((finrank ℝ E : ℝ) - 2)
  let q : ℝ := -((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2)
  let ĝ := g.rescale (fun y ↦ u y ^ p)
    (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') p)
    (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) p)
  have heq : ĝ.rescale (fun y ↦ v y ^ p)
      (hv.rpow_const_of_ne (fun y ↦ (hv_pos y).ne') p)
      (fun y ↦ Real.rpow_pos_of_pos (hv_pos y) p) =
      g.rescale (fun y ↦ (u * v) y ^ p)
        ((hu.mul hv).rpow_const_of_ne (fun y ↦ (mul_pos (hu_pos y) (hv_pos y)).ne') p)
        (fun y ↦ Real.rpow_pos_of_pos (mul_pos (hu_pos y) (hv_pos y)) p) := by
    ext y a b
    simp only [ContMDiffRiemannianMetric.rescale_inner, ĝ, Pi.mul_apply,
      Real.mul_rpow (hu_pos y).le (hv_pos y).le]
    ring
  have h₁ := scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian_withMetric
    ĝ hn hv hv_pos x
  have h₂ := scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian_withMetric
    g hn (hu.mul hv) (fun y ↦ mul_pos (hu_pos y) (hv_pos y)) x
  have h : v x ^ q * conformalLaplacian I (v ∘ WithMetric.ofWithMetric)
      (WithMetric.toWithMetric ĝ x) =
      v x ^ q * (u x ^ q * conformalLaplacian I ((u * v) ∘ WithMetric.ofWithMetric)
        (WithMetric.toWithMetric g x)) := by
    rw [← h₁, heq, h₂, Pi.mul_apply, Real.mul_rpow (hu_pos x).le (hv_pos x).le]
    ring
  exact (mul_left_cancel₀ (Real.rpow_pos_of_pos (hv_pos x) q).ne') h

/-- **Conformal covariance of the conformal Laplacian.** For `ĝ = u^(4/(n-2)) g`,
`L_ĝ v = u^(-(n+2)/(n-2)) L_g (u v)` on all smooth real functions. The two operators act on
distinct metric-indexed copies, with functions and points transported from `M`. -/
theorem conformalLaplacian_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hu_pos : ∀ x, 0 < u x) (hv : ContMDiff I 𝓘(ℝ) ∞ v) (x : M) :
    conformalLaplacian I (v ∘ WithMetric.ofWithMetric)
        (WithMetric.toWithMetric (g.rescale (fun y ↦ u y ^ (4 / ((finrank ℝ E : ℝ) - 2)))
          (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') _)
          (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _)) x) =
      u x ^ (-((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2)) *
        conformalLaplacian I ((u * v) ∘ WithMetric.ofWithMetric) (WithMetric.toWithMetric g x) := by
  let ĝ := g.rescale (fun y ↦ u y ^ (4 / ((finrank ℝ E : ℝ) - 2)))
    (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') _)
    (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _)
  -- Every smooth real function is a difference of positive smooth functions, even when
  -- unbounded: `v = (v + exp (-v)) - exp (-v)`, since `exp (-v) ≥ 1 - v`.
  let w : M → ℝ := fun y ↦ Real.exp (-v y)
  have hw : ContMDiff I 𝓘(ℝ) ∞ w := Real.contDiff_exp.contMDiff.comp hv.neg
  have hw_pos (y : M) : 0 < w y := Real.exp_pos _
  have hvw_pos (y : M) : 0 < (v + w) y := by
    have h := Real.add_one_le_exp (-v y)
    dsimp only [Pi.add_apply, w]
    linarith
  have hsum := conformalLaplacian_rescale_pos g hn hu hu_pos (hv.add hw) hvw_pos x
  have hwcov := conformalLaplacian_rescale_pos g hn hu hu_pos hw hw_pos x
  have hleft : (v + w) ∘ (WithMetric.ofWithMetric : WithMetric ĝ → M) =
      v ∘ WithMetric.ofWithMetric + w ∘ WithMetric.ofWithMetric := rfl
  have hright : (u * (v + w)) ∘ (WithMetric.ofWithMetric : WithMetric g → M) =
      (u * v) ∘ WithMetric.ofWithMetric + (u * w) ∘ WithMetric.ofWithMetric := by
    ext y
    exact mul_add _ _ _
  rw [hleft, conformalLaplacian_add I (hv.comp WithMetric.contMDiff_ofWithMetric |>.of_le (by simp))
      (hw.comp WithMetric.contMDiff_ofWithMetric |>.of_le (by simp)),
    hright, conformalLaplacian_add I
      ((hu.mul hv).comp WithMetric.contMDiff_ofWithMetric |>.of_le (by simp))
      ((hu.mul hw).comp WithMetric.contMDiff_ofWithMetric |>.of_le (by simp)), hwcov] at hsum
  linarith

/-- **Conformal invariance of the smooth operator pairing.** Multiplication by the positive
conformal factor transports `∫ v L_ĝ w dV_ĝ` to `∫ (u v) L_g (u w) dV_g`. Only the function
acted on by the operator needs to be smooth. The identity also holds for the totalized Bochner
integrals when the integrands are not integrable. -/
theorem integral_mul_conformalLaplacian_rescale [LindelofSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u w : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hu_pos : ∀ x, 0 < u x) (hw : ContMDiff I 𝓘(ℝ) ∞ w) (v : M → ℝ) :
    ∫ x, v x.ofWithMetric * conformalLaplacian I (w ∘ WithMetric.ofWithMetric) x
        ∂riemannianVolume I (WithMetric (g.rescale
          (fun y ↦ u y ^ (4 / ((finrank ℝ E : ℝ) - 2)))
          (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') _)
          (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _))) =
      ∫ x, (u * v) x.ofWithMetric *
        conformalLaplacian I ((u * w) ∘ WithMetric.ofWithMetric) x
          ∂riemannianVolume I (WithMetric g) := by
  let ĝ := g.rescale (fun y ↦ u y ^ (4 / ((finrank ℝ E : ℝ) - 2)))
    (hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne') _)
    (fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _)
  have hvol := WithMetric.integral_riemannianVolume_rescale (g := g)
    (hf := hu.rpow_const_of_ne (fun y ↦ (hu_pos y).ne')
      (4 / ((finrank ℝ E : ℝ) - 2)))
    (hf_pos := fun y ↦ Real.rpow_pos_of_pos (hu_pos y) _)
    (fun y ↦ v y * conformalLaplacian I (w ∘ WithMetric.ofWithMetric)
      (WithMetric.toWithMetric ĝ y))
  simp only [WithMetric.toWithMetric_ofWithMetric] at hvol
  rw [hvol]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [smul_eq_mul, conformalLaplacian_rescale g hn hu hu_pos hw,
    ← Real.rpow_mul (hu_pos x.ofWithMetric).le]
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  have hexp : 4 / ((finrank ℝ E : ℝ) - 2) * ((finrank ℝ E : ℝ) / 2) +
      -((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2) = 1 := by
    field_simp
    ring
  rw [mul_left_comm (v x.ofWithMetric), ← mul_assoc, ← mul_assoc,
    ← Real.rpow_add (hu_pos x.ofWithMetric), hexp, Real.rpow_one]
  rfl

end Bundle.ContMDiffRiemannianMetric
