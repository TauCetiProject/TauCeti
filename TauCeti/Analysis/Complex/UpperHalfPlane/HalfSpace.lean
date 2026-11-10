/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The upper half-plane and half-space metrics

The coordinate map `x + iy ↦ (x, y)` identifies the Poincaré metric on the complex upper
half-plane with the two-dimensional upper half-space metric. The identification is a
Riemannian isometry: its differential preserves the Euclidean inner product and its base map
preserves height, so both tensors are the same Euclidean tensor divided by squared height.
Transporting the half-space curvature along this map proves that the Poincaré metric has
constant sectional curvature `−1`.

`TauCeti.UpperHalfPlane.upperHalfSpaceIsometry` gives this identification without changing
Mathlib's distance on the upper half-plane or installing a distance on the half-space.

The metric convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, second
edition, Chapter 3 (the upper half-space model).
-/

public section

open Bundle Manifold CovariantDerivative
open scoped ContDiff Manifold UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

private def coordinates : ℂ ≃L[ℝ] WithLp 2 (ℝ × ℝ) :=
  Complex.equivRealProdCLM.trans (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm

private theorem coordinates_apply (z : ℂ) :
    coordinates z = WithLp.toLp 2 (z.re, z.im) := rfl

private theorem coordinates_symm_im (p : WithLp 2 (ℝ × ℝ)) :
    (coordinates.symm p).im = p.snd := by
  simp [coordinates, Complex.equivRealProdCLM_symm_apply]

private def halfSpaceEquiv : ℍ ≃ UpperHalfSpace ℝ where
  toFun z := UpperHalfSpace.mk (coordinates z) (by simpa [coordinates_apply] using z.im_pos)
  invFun p := ⟨coordinates.symm p, by
    rw [coordinates_symm_im, UpperHalfSpace.snd_coe]
    exact UpperHalfSpace.height_pos p⟩
  left_inv z := by
    apply _root_.UpperHalfPlane.ext
    simpa only [UpperHalfSpace.coe_mk] using coordinates.symm_apply_apply (z : ℂ)
  right_inv p := by
    apply UpperHalfSpace.ext
    simpa only [UpperHalfSpace.coe_mk] using coordinates.apply_symm_apply
      (p : WithLp 2 (ℝ × ℝ))

private theorem coe_halfSpaceEquiv (z : ℍ) :
    (halfSpaceEquiv z : WithLp 2 (ℝ × ℝ)) = coordinates z :=
  UpperHalfSpace.coe_mk _ _

private theorem coe_halfSpaceEquiv_symm (p : UpperHalfSpace ℝ) :
    (halfSpaceEquiv.symm p : ℂ) = coordinates.symm p := rfl

private theorem contMDiff_halfSpaceEquiv :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) ∞ halfSpaceEquiv := by
  apply UpperHalfSpace.contMDiff_coe_comp_iff.mp
  have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ _root_.UpperHalfPlane.coe :=
    fun _ ↦ contMDiffAt_extChartAt
  simpa only [Function.comp_def, coe_halfSpaceEquiv] using
    coordinates.contDiff.contMDiff.comp hcoe

private theorem contMDiff_halfSpaceEquiv_symm :
    ContMDiff 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) 𝓘(ℝ, ℂ) ∞ halfSpaceEquiv.symm := by
  apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
  simpa only [Function.comp_def, coe_halfSpaceEquiv_symm] using
    coordinates.symm.contDiff.contMDiff.comp (UpperHalfSpace.contMDiff_coe.of_le le_top)

private theorem differential_halfSpaceEquiv (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (halfSpaceEquiv z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) halfSpaceEquiv z v) =
      coordinates (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  rw [(contMDiff_halfSpaceEquiv.mdifferentiableAt (by simp)).tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) z halfSpaceEquiv
      =ᶠ[nhds (z : ℂ)] coordinates := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds z.im_pos]
      with w hw
    have hchart (p : UpperHalfSpace ℝ) :
        extChartAt 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (halfSpaceEquiv z) p =
          (p : WithLp 2 (ℝ × ℝ)) := by simp [UpperHalfSpace.chartAt_apply]
    simp only [writtenInExtChartAt, Function.comp_apply, hchart, coe_halfSpaceEquiv]
    congr 1
    exact (extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw)
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, coordinates.hasFDerivAt.fderiv]
  rfl

/-- The coordinate identification `x + iy ↦ (x, y)` is a Riemannian isometry from the
Poincaré upper half-plane to the two-dimensional hyperbolic upper half-space. -/
def upperHalfSpaceIsometry :
    RiemannianIsometry 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) ℍ (UpperHalfSpace ℝ) where
  toEquiv := halfSpaceEquiv
  contMDiff_toFun := contMDiff_halfSpaceEquiv
  contMDiff_invFun := contMDiff_halfSpaceEquiv_symm
  inner_mfderiv' z v w := by
    -- The source inner product is the installed Poincaré tensor; the bundled map has
    -- underlying function `halfSpaceEquiv`, so its differential lemma applies here.
    change inner ℝ
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) halfSpaceEquiv z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) halfSpaceEquiv z w) =
      poincareRiemannianMetric.inner z v w
    rw [UpperHalfSpace.inner_def, differential_halfSpaceEquiv, differential_halfSpaceEquiv,
      _root_.UpperHalfPlane.poincareRiemannianMetric_inner]
    have hh : UpperHalfSpace.height (halfSpaceEquiv z) = z.im := by
      rw [← UpperHalfSpace.snd_coe, coe_halfSpaceEquiv, coordinates_apply]
      rfl
    simp [hh, coordinates_apply, WithLp.prod_inner_apply, Complex.inner]

/-- The identification with half-space sends a point to its real and imaginary coordinates. -/
@[simp]
theorem _root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply (z : ℍ) :
    (upperHalfSpaceIsometry z : WithLp 2 (ℝ × ℝ)) = WithLp.toLp 2 (z.re, z.im) :=
  coe_halfSpaceEquiv z

/-- The identification with half-space preserves height. -/
@[simp]
theorem _root_.UpperHalfPlane.height_upperHalfSpaceIsometry_apply (z : ℍ) :
    UpperHalfSpace.height (upperHalfSpaceIsometry z) = z.im := by
  rw [← UpperHalfSpace.snd_coe, z.coe_upperHalfSpaceIsometry_apply]
  rfl

/-- The inverse identification sends `(x, y)` to `x + iy`. -/
@[simp]
theorem coe_upperHalfSpaceIsometry_symm_apply (p : UpperHalfSpace ℝ) :
    (upperHalfSpaceIsometry.symm p : ℂ) =
      ((p : WithLp 2 (ℝ × ℝ)).fst : ℂ) + UpperHalfSpace.height p * Complex.I := by
  have h := congrArg UpperHalfSpace.coe (upperHalfSpaceIsometry.apply_symm_apply p)
  rw [_root_.UpperHalfPlane.coe_upperHalfSpaceIsometry_apply] at h
  apply Complex.ext
  · simpa using congrArg WithLp.fst h
  · simpa using congrArg WithLp.snd h

/-- The Poincaré metric on the upper half-plane has constant sectional curvature `−1`. -/
theorem hasConstantSectionalCurvature :
    (leviCivitaConnection 𝓘(ℝ, ℂ) ℍ).HasConstantSectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, ℂ)) (-1) :=
  (upperHalfSpaceIsometry.hasConstantSectionalCurvature_iff (-1)).mp
    UpperHalfSpace.hasConstantSectionalCurvature

end TauCeti.UpperHalfPlane
