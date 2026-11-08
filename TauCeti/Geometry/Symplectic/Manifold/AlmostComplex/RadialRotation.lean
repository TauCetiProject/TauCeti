/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Transport
public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Analysis.InnerProductSpace.NormPow
public import TauCeti.Analysis.SpecialFunctions.Pow.Regularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Almost complex structures with exactly finite regularity

In Euclidean complex dimension two, rotate the real coordinate plane through angle
`‖z‖^(ℓ+1/2)`, fixing its imaginary orthogonal complement, and conjugate multiplication by `i`.
This construction detects the strict distinction between successive finite regularity classes.
-/

public noncomputable section

open Complex Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.AlmostComplexStructure

local notation "V" => EuclideanSpace ℂ (Fin 2)

/-- The real plane spanned by the two real coordinate vectors in Euclidean complex dimension two.
The imaginary part of the source complex number parametrizes the second real coordinate. -/
def realPlaneEmbedding : ℂ →ₗᵢ[ℝ] V where
  toLinearMap :=
    ((Complex.reCLM.smulRight (EuclideanSpace.single 0 (1 : ℂ) : V)) +
      (Complex.imCLM.smulRight (EuclideanSpace.single 1 (1 : ℂ) : V))).toLinearMap
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, PiLp.single_apply,
      Complex.sq_norm, Complex.normSq_apply]

/-- First coordinate of the real plane embedding. -/
@[simp]
theorem realPlaneEmbedding_apply_zero (z : ℂ) : realPlaneEmbedding z 0 = (z.re : ℂ) := by
  simp [realPlaneEmbedding]

/-- Second coordinate of the real plane embedding. -/
@[simp]
theorem realPlaneEmbedding_apply_one (z : ℂ) : realPlaneEmbedding z 1 = (z.im : ℂ) := by
  simp [realPlaneEmbedding]

/-- The first real coordinate vector is the image of `1`. -/
@[simp]
theorem realPlaneEmbedding_one : realPlaneEmbedding 1 = EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp

/-- The second real coordinate vector is the image of `i` in the parametrizing plane. -/
@[simp]
theorem realPlaneEmbedding_I : realPlaneEmbedding I = EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp

/-- The imaginary coordinate vectors are orthogonal to the real coordinate plane. -/
theorem imaginary_single_mem_realPlane_orthogonal (i : Fin 2) :
    I • (EuclideanSpace.single i 1 : V) ∈ realPlaneEmbedding.rangeᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨z, rfl⟩
  fin_cases i <;>
    simp [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℂ,
      PiLp.single_apply]

/-- Rotate the real coordinate plane through the given angle and fix its orthogonal complement. -/
def realPlaneRotation (θ : ℝ) : V ≃ₗᵢ[ℝ] V :=
  realPlaneEmbedding.planeRotation (Circle.exp θ)

/-- Compare the specialized rotation with the native plane rotation. -/
theorem realPlaneRotation_eq (θ : ℝ) :
    realPlaneRotation θ = realPlaneEmbedding.planeRotation (Circle.exp θ) := by rfl

/-- Reversing the angle inverts the rotation. -/
@[simp]
theorem realPlaneRotation_neg (θ : ℝ) :
    realPlaneRotation (-θ) = (realPlaneRotation θ).symm := by
  simp only [realPlaneRotation, Circle.exp_neg, map_inv]
  rfl

/-- A zero angle gives the identity. -/
@[simp]
theorem realPlaneRotation_zero : realPlaneRotation 0 = LinearIsometryEquiv.refl ℝ V := by
  simp only [realPlaneRotation, Circle.exp_zero, map_one]
  rfl

/-- The imaginary coordinate vectors are fixed by every real-plane rotation. -/
@[simp]
theorem realPlaneRotation_imaginary_single (θ : ℝ) (i : Fin 2) :
    realPlaneRotation θ (I • (EuclideanSpace.single i 1 : V)) =
      I • (EuclideanSpace.single i 1 : V) := by
  rw [realPlaneRotation_eq]
  exact realPlaneEmbedding.planeRotation_apply_of_mem_orthogonal _
    (imaginary_single_mem_realPlane_orthogonal i)

/-- The first real coordinate vector rotates into the real coordinate plane. -/
theorem realPlaneRotation_single_zero (θ : ℝ) :
    realPlaneRotation θ (EuclideanSpace.single 0 1) =
      Real.cos θ • (EuclideanSpace.single 0 1 : V) +
        Real.sin θ • (EuclideanSpace.single 1 1 : V) := by
  rw [← realPlaneEmbedding_one, realPlaneRotation_eq,
    realPlaneEmbedding.planeRotation_apply_map]
  ext i
  fin_cases i <;> simp [Circle.coe_exp, Complex.exp_mul_I]

/-- The second real coordinate vector rotates into the real coordinate plane. -/
theorem realPlaneRotation_single_one (θ : ℝ) :
    realPlaneRotation θ (EuclideanSpace.single 1 1) =
      -Real.sin θ • (EuclideanSpace.single 0 1 : V) +
        Real.cos θ • (EuclideanSpace.single 1 1 : V) := by
  rw [← realPlaneEmbedding_I, realPlaneRotation_eq,
    realPlaneEmbedding.planeRotation_apply_map]
  ext i
  fin_cases i <;> simp [Circle.coe_exp, Complex.exp_mul_I]

/-- The rotation depends smoothly on its angle, as a continuous linear operator. -/
theorem contDiff_realPlaneRotation {n : ℕ∞ω} :
    ContDiff ℝ n
      (fun θ : ℝ ↦ (realPlaneRotation θ).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  rw [← contMDiff_iff_contDiff]
  -- The two inherited normed-space instances have the same pointwise real scalar action.
  convert! realPlaneEmbedding.contMDiff_planeRotation.comp
    (contMDiff_circleExp.prodMk (contMDiff_const (c := v))) using 1

/-- Conjugate the standard complex structure by the rotation of the real coordinate plane. -/
def planeRotated (θ : ℝ) : AlmostComplexStructure V :=
  (ofComplexModule V).transport (realPlaneRotation θ).toLinearEquiv

/-- The transported structure acts by conjugation of multiplication by `i`. -/
theorem planeRotated_apply (θ : ℝ) (v : V) :
    planeRotated θ v = realPlaneRotation θ (I • (realPlaneRotation θ).symm v) := by
  simp [planeRotated, ofComplexModule_apply]

/-- The coefficient which detects the rotation angle in the conjugated complex structure. -/
theorem planeRotated_imaginary_single_zero (θ : ℝ) :
    planeRotated θ (I • (EuclideanSpace.single 0 1 : V)) =
      -Real.cos θ • (EuclideanSpace.single 0 1 : V) -
        Real.sin θ • (EuclideanSpace.single 1 1 : V) := by
  rw [planeRotated_apply, ← realPlaneRotation_neg, realPlaneRotation_imaginary_single]
  simp [smul_smul, realPlaneRotation_single_zero, sub_eq_add_neg, add_comm]

/-- The continuous endomorphism underlying the rotated structure. -/
def planeRotatedEndomorphism (θ : ℝ) : V →L[ℝ] V :=
  (planeRotated θ).toLinearMap.toContinuousLinearMap

/-- Evaluate the continuous endomorphism through the transported structure. -/
@[simp]
theorem planeRotatedEndomorphism_apply (θ : ℝ) (v : V) :
    planeRotatedEndomorphism θ v = planeRotated θ v := by rfl

/-- The endomorphism is the composite of the two inverse rotations and multiplication by `i`. -/
theorem planeRotatedEndomorphism_eq (θ : ℝ) :
    planeRotatedEndomorphism θ =
      ((realPlaneRotation θ).toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((I • ContinuousLinearMap.id ℝ V).comp
          (realPlaneRotation (-θ)).toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext v
  simp [planeRotated_apply]

/-- Smooth dependence of the transported endomorphism on its rotation angle. -/
theorem contDiff_planeRotatedEndomorphism {n : ℕ∞ω} :
    ContDiff ℝ n planeRotatedEndomorphism := by
  rw [show planeRotatedEndomorphism = (fun θ : ℝ ↦
    ((realPlaneRotation θ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((I • ContinuousLinearMap.id ℝ V).comp
        (realPlaneRotation (-θ)).toContinuousLinearEquiv.toContinuousLinearMap)) from
    funext planeRotatedEndomorphism_eq]
  exact contDiff_realPlaneRotation.clm_comp
    (contDiff_const.clm_comp (contDiff_realPlaneRotation.comp contDiff_neg))

/-- The conjugated endomorphism retains the almost-complex square identity. -/
theorem planeRotatedEndomorphism_apply_apply (θ : ℝ) (v : V) :
    planeRotatedEndomorphism θ (planeRotatedEndomorphism θ v) = -v := by
  simp only [planeRotatedEndomorphism_apply]
  exact (planeRotated θ).apply_apply v

end TauCeti.AlmostComplexStructure

namespace TauCeti.ContMDiffAlmostComplexStructure

open AlmostComplexStructure

local notation "V" => EuclideanSpace ℂ (Fin 2)

/-- The radial angle used to separate the `ℓ`-th and `(ℓ+1)`-st regularity classes. -/
def radialAngle (ℓ : ℕ) (z : V) : ℝ := ‖z‖ ^ ((ℓ : ℝ) + 1 / 2)

/-- The angle is the specified Euclidean radial power at every point. -/
theorem radialAngle_def (ℓ : ℕ) (z : V) :
    radialAngle ℓ z = ‖z‖ ^ ((ℓ : ℝ) + 1 / 2) := by rfl

/-- The angle vanishes at the origin. -/
@[simp]
theorem radialAngle_zero (ℓ : ℕ) : radialAngle ℓ 0 = 0 := by
  rw [radialAngle_def, norm_zero]
  exact Real.zero_rpow (by positivity)

/-- Along the first real unit coordinate line, the angle is the specified absolute power. -/
theorem radialAngle_real_line (ℓ : ℕ) (t : ℝ) :
    radialAngle ℓ (t • (EuclideanSpace.single 0 1 : V)) = |t| ^ ((ℓ : ℝ) + 1 / 2) := by
  simp [radialAngle_def, norm_smul]

/-- The radial angle has the required finite regularity on the entire Euclidean space. -/
theorem contDiff_radialAngle (ℓ : ℕ) : ContDiff ℝ ℓ (radialAngle ℓ) :=
  contDiff_norm_rpow_of_lt (by linarith)

/-- The exact radial-rotation almost complex structure in Euclidean complex dimension two.
Its order is arbitrary finite `ℓ`, including zero. -/
def radialRotation (ℓ : ℕ) :
    ContMDiffAlmostComplexStructure 𝓘(ℝ, V) ℓ V :=
  ContMDiffAlmostComplexStructure.ofModel
    (fun z ↦ planeRotatedEndomorphism (radialAngle ℓ z))
    (contDiff_planeRotatedEndomorphism.comp (contDiff_radialAngle ℓ))
    (fun z v ↦ planeRotatedEndomorphism_apply_apply (radialAngle ℓ z) v)

/-- The native endomorphism section is the specified radial conjugation field. -/
@[simp]
theorem radialRotation_toEndomorphism (ℓ : ℕ) (z : V) :
    (show V →L[ℝ] V from (radialRotation ℓ).toEndomorphism z) =
      planeRotatedEndomorphism (radialAngle ℓ z) := by
  unfold radialRotation
  exact ContMDiffAlmostComplexStructure.ofModel_toEndomorphism_apply _ _ _ z

/-- Evaluate the finite-regularity structure through its actual conjugated field. -/
@[simp]
theorem radialRotation_apply (ℓ : ℕ) (z v : V) :
    radialRotation ℓ z v = planeRotated (radialAngle ℓ z) v := by
  have h := congrArg (fun L : V →L[ℝ] V ↦ L v) (radialRotation_toEndomorphism ℓ z)
  -- Evaluation of the native structure and of its model endomorphism differ only by
  -- the definitionally identical model tangent fibre and function-coercion wrappers.
  convert! h.trans (planeRotatedEndomorphism_apply _ v) using 1

/-- The stated coefficient and sign for the first imaginary coordinate vector. -/
theorem radialRotation_imaginary_single_zero (ℓ : ℕ) (z : V) :
    radialRotation ℓ z (I • (EuclideanSpace.single 0 1 : V)) =
      -Real.cos (radialAngle ℓ z) • (EuclideanSpace.single 0 1 : V) -
        Real.sin (radialAngle ℓ z) • (EuclideanSpace.single 1 1 : V) := by
  rw [radialRotation_apply, planeRotated_imaginary_single_zero]

/-- The radial angle fails to have the next finite order at the origin. -/
theorem not_contDiffAt_radialAngle (ℓ : ℕ) :
    ¬ ContDiffAt ℝ (ℓ + 1) (radialAngle ℓ) 0 := by
  intro h
  let v : V := EuclideanSpace.single 0 1
  have hline : ContDiff ℝ (ℓ + 1) (fun t : ℝ ↦ t • v) := contDiff_id.smul_const v
  have hh := (show ContDiffAt ℝ (ℓ + 1) (radialAngle ℓ)
    ((fun t : ℝ ↦ t • v) 0) by simpa only [zero_smul] using h).comp 0 hline.contDiffAt
  apply TauCeti.not_contDiffAt_abs_rpow (k := ℓ) (p := (ℓ : ℝ) + 1 / 2)
    (by linarith) (by linarith)
  simpa only [Function.comp_def, v, radialAngle_real_line] using hh

/-- The endomorphism field of the exact radial rotation fails to have order `ℓ+1` at zero. -/
theorem not_contDiffAt_radialRotation_field (ℓ : ℕ) :
    ¬ ContDiffAt ℝ (ℓ + 1)
      (fun z : V ↦ planeRotatedEndomorphism (radialAngle ℓ z)) 0 := by
  -- Recover the angle from its actual sine coefficient using arcsine near zero.
  intro h
  have heval := h.clm_apply (contDiffAt_const
    (c := I • (EuclideanSpace.single 0 1 : V)))
  have hcoord := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 2 ↦ ℂ) 1).contDiff.contDiffAt.comp
    (0 : V) heval
  have hre := Complex.reCLM.contDiff.contDiffAt.comp (0 : V) hcoord
  have hsin : ContDiffAt ℝ (ℓ + 1) (fun z : V ↦ Real.sin (radialAngle ℓ z)) 0 := by
    have heq : (fun z : V ↦ -((planeRotatedEndomorphism (radialAngle ℓ z)
        (I • (EuclideanSpace.single 0 1 : V))) 1).re) =
        fun z : V ↦ Real.sin (radialAngle ℓ z) := by
      funext z
      rw [planeRotatedEndomorphism_apply, planeRotated_imaginary_single_zero]
      simp [-Complex.ofReal_sin]
    rw [← heq]
    exact hre.neg
  have ha : ContDiffAt ℝ (ℓ + 1) Real.arcsin (Real.sin (radialAngle ℓ (0 : V))) := by
    simpa only [radialAngle_zero, Real.sin_zero] using
      (Real.contDiffAt_arcsin (x := 0) (by norm_num) (by norm_num) :
        ContDiffAt ℝ (ℓ + 1) Real.arcsin 0)
  have hasin := ha.comp (0 : V) hsin
  have hrange : Ioo (-(Real.pi / 2)) (Real.pi / 2) ∈ 𝓝 (radialAngle ℓ (0 : V)) := by
    rw [radialAngle_zero]
    exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsmall := (contDiff_radialAngle ℓ).continuous.continuousAt.preimage_mem_nhds hrange
  apply not_contDiffAt_radialAngle ℓ
  apply hasin.congr_of_eventuallyEq
  filter_upwards [hsmall] with z hz
  exact (Real.arcsin_sin hz.1.le hz.2.le).symm

/-- No structure of the next order has the same endomorphism field as this radial example. -/
theorem not_exists_radialRotation_successor (ℓ : ℕ) :
    ¬ ∃ K : ContMDiffAlmostComplexStructure 𝓘(ℝ, V) (ℓ + 1) V,
      ∀ z, (show V →L[ℝ] V from K.toEndomorphism z) =
        (show V →L[ℝ] V from (radialRotation ℓ).toEndomorphism z) := by
  rintro ⟨K, hK⟩
  apply not_contDiffAt_radialRotation_field ℓ
  apply K.contDiff_toEndomorphism.contDiffAt.congr_of_eventuallyEq
  filter_upwards [] with z
  exact ((hK z).trans (radialRotation_toEndomorphism ℓ z)).symm

end TauCeti.ContMDiffAlmostComplexStructure
