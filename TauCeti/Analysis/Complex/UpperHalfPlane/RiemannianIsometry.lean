/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Manifold
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# `GL(2, ℝ)` acts by Riemannian isometries of the Poincaré metric

Mathlib's action `UpperHalfPlane.glAction` of `GL(2, ℝ)` on `ℍ` sends `z` to `(az + b)/(cz + d)`
when `det g > 0` and to `(a conj z + b)/(c conj z + d)` when `det g < 0`. Its real derivative at
`z` is Mathlib's `UpperHalfPlane.smulFDeriv g z`: multiplication by `det g/(cz + d)²`, followed by
complex conjugation when `det g < 0`. Its modulus `|det g|/|cz + d|²` is the ratio
`Im(g • z)/Im z` (`UpperHalfPlane.im_smul_eq_div_normSq`), so the derivative scales the
Euclidean inner product by `(Im(g • z)/Im z)²` (`UpperHalfPlane.inner_smulFDeriv`) and preserves
the Poincaré tensor `(Re v Re w + Im v Im w)/y²`. Hence every element of `GL(2, ℝ)`, including the
antiholomorphic elements of negative determinant, acts by a smooth Riemannian isometry of the
Poincaré metric, and so does every element of the quotients `PGL(2, ℝ)` and `PSL(2, ℝ)`.

## Main declarations

* `UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul`: in the inclusion chart, the differential of
  `z ↦ g • z` is `UpperHalfPlane.smulFDeriv g z`.
* `UpperHalfPlane.inner_smulFDeriv`: that derivative scales the Euclidean inner product by
  `(Im(g • z)/Im z)²`.
* `UpperHalfPlane.inner_mfderiv_smul`: the differential of `z ↦ g • z` preserves the Poincaré
  metric.
* `TauCeti.UpperHalfPlane.glToIsom`: the action of `GL(2, ℝ)` as a homomorphism to the Riemannian
  isometry group `TauCeti.Isom 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.pglToIsom` and `TauCeti.UpperHalfPlane.pslToIsom`: the injective
  homomorphisms from `PGL(2, ℝ)` and `PSL(2, ℝ)` to the Riemannian isometry group.

## References

* Svetlana Katok, *Fuchsian Groups*, §1.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 3 (the isometries of the upper half-plane model).
-/

public section

open Bundle UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups Topology

noncomputable section

namespace TauCeti.UpperHalfPlane

/-- In the inclusion chart, the differential of `z ↦ g • z` is Mathlib's real derivative
`UpperHalfPlane.smulFDeriv g z`. -/
theorem _root_.UpperHalfPlane.tangentSpaceCastModel_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (g • z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) =
      smulFDeriv g z (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v) := by
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : ℍ → ℍ) z :=
    (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) g z).mdifferentiableAt (by simp)
  rw [hmd.tangentSpaceCastModel_mfderiv_apply]
  -- In the inclusion chart the action is `w ↦ g • ofComplex w` near `z`.
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) z (g • · : ℍ → ℍ)
      =ᶠ[𝓝 (z : ℂ)] fun w ↦ ↑(g • ofComplex w) := by
    -- Both extended charts are the inclusion charts, read through the identity model.
    have h := comp_chartAt_symm_eventuallyEq (fun τ : ℍ ↦ ((g • τ : ℍ) : ℂ)) z
    simpa [writtenInExtChartAt, Function.comp_def] using h
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq, (hasStrictFDerivAt_smul g z).hasFDerivAt.fderiv]

/-- The real derivative of `z ↦ g • z` is conformal, scaling the Euclidean inner product by the
square of the ratio `Im(g • z)/Im z`. -/
theorem _root_.UpperHalfPlane.inner_smulFDeriv (g : GL (Fin 2) ℝ) (z : ℍ) (v w : ℂ) :
    inner ℝ (smulFDeriv g z v) (smulFDeriv g z w) = ((g • z).im / z.im) ^ 2 * inner ℝ v w := by
  have hσ (x y : ℂ) : inner ℝ (σ g x) (σ g y) = inner ℝ x y := by
    unfold σ
    split_ifs <;> simp [Complex.inner]
  have hmul (c x y : ℂ) : inner ℝ (x * c) (y * c) = Complex.normSq c * inner ℝ x y := by
    simp only [Complex.inner, map_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.normSq_apply]
    ring
  have happly (x : ℂ) :
      smulFDeriv g z x = σ g (x * ((g.det.val : ℂ) / denom g z ^ 2)) := by
    simp [smulFDeriv]
  rw [happly, happly, hσ, hmul, im_smul_eq_div_normSq]
  have hd := normSq_denom_pos g z.im_ne_zero
  simp only [map_div₀, map_pow, Complex.normSq_ofReal]
  field_simp
  rw [sq_abs]
  ring

/-- The differential of `z ↦ g • z` preserves the Poincaré metric: every element of `GL(2, ℝ)`
acts on the upper half-plane by a Riemannian isometry. -/
theorem _root_.UpperHalfPlane.inner_mfderiv_smul (g : GL (Fin 2) ℝ) (z : ℍ)
    (v w : TangentSpace 𝓘(ℝ, ℂ) z) :
    inner ℝ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) z w) =
      inner ℝ v w := by
  rw [UpperHalfPlane.inner_def, UpperHalfPlane.inner_def, tangentSpaceCastModel_mfderiv_smul,
    tangentSpaceCastModel_mfderiv_smul, inner_smulFDeriv]
  field_simp

/-- The action of `GL(2, ℝ)` on the upper half-plane, as a homomorphism to the group of
Riemannian isometries of the Poincaré metric. Scalar matrices act trivially, so it is not
injective. -/
def glToIsom : GL (Fin 2) ℝ →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom inner_mfderiv_smul

/-- The isometry `glToIsom g` is `z ↦ g • z`. -/
@[simp]
theorem glToIsom_apply (g : GL (Fin 2) ℝ) (z : ℍ) : glToIsom g z = g • z := by
  rw [glToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- The action of `PGL(2, ℝ)` on the upper half-plane, as a homomorphism to the group of
Riemannian isometries of the Poincaré metric. -/
def pglToIsom : PGL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  RiemannianIsometry.constSMulHom fun q ↦ by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    rw [show (Matrix.ProjGenLinGroup.mk g • · : ℍ → ℍ) = (g • ·) from funext (pglMk_smul g)]
    exact inner_mfderiv_smul g

/-- The isometry `pglToIsom q` is `z ↦ q • z`. -/
@[simp]
theorem pglToIsom_apply (q : PGL(2, ℝ)) (z : ℍ) : pglToIsom q z = q • z := by
  rw [pglToIsom, RiemannianIsometry.constSMulHom_apply, RiemannianIsometry.constSMul_apply]

/-- Distinct elements of `PGL(2, ℝ)` give distinct Riemannian isometries. -/
theorem pglToIsom_injective : Function.Injective pglToIsom :=
  RiemannianIsometry.constSMulHom_injective _

/-- The action of `PSL(2, ℝ)` on the upper half-plane, as a homomorphism to the group of
Riemannian isometries of the Poincaré metric. -/
def pslToIsom : PSL(2, ℝ) →* Isom 𝓘(ℝ, ℂ) ℍ :=
  pglToIsom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL

/-- The isometry `pslToIsom q` is `z ↦ q • z`. -/
@[simp]
theorem pslToIsom_apply (q : PSL(2, ℝ)) (z : ℍ) : pslToIsom q z = q • z := by
  rw [pslToIsom, MonoidHom.comp_apply, pglToIsom_apply, toPGL_smul]

/-- Distinct elements of `PSL(2, ℝ)` give distinct Riemannian isometries. -/
theorem pslToIsom_injective : Function.Injective pslToIsom :=
  pglToIsom_injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

end TauCeti.UpperHalfPlane
