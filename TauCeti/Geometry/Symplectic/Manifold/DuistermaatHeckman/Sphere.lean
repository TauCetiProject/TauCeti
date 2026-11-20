/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# The Duistermaat–Heckman measure of the two-sphere

Let `S² ⊂ ℝ³` be the unit sphere with its area form `σ_x(v, w) = x ⬝ (v × w)`
(`TauCeti.sphereAreaForm`). The rotations about the vertical axis are the Hamiltonian flow of the
height `h(x) = x₃` (`TauCeti.mvfderiv_hamiltonianVectorField_sphereAreaForm`), so `h` is the moment
map of this circle action. This file computes its Duistermaat–Heckman measure, the pushforward of
the area measure `|σ|` along `h`:

`h_* |σ| = 2π · Lebesgue` on `[-1, 1]`

(`TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_height`). This is Archimedes' theorem that a
band of the sphere between two heights has the area of the band of the circumscribed cylinder
between the same heights. In particular the area of the sphere is `4π`
(`TauCeti.liouvilleMeasure_sphereAreaForm_univ`), and a constant moment map, such as that of the
trivial circle action, has Duistermaat–Heckman measure `4π δ_c`
(`TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_const`).

The computation uses longitude and height as coordinates. On the strip `(a, a + 2π) × (-1, 1)`
(`TauCeti.longitudeHeightStrip a`) the parametrization

`(θ, h) ↦ (√(1 - h²) cos θ, √(1 - h²) sin θ, h)`

(`TauCeti.sphereLongitudeHeight a`) is a smooth injective map into `S²`, and it pulls `σ` back to
`dθ ∧ dh` (`TauCeti.mpullback_sphereLongitudeHeight_sphereAreaForm`): its two partial derivatives
`∂_θ` and `∂_h` have triple product `1` with the point. So it carries Lebesgue measure on the strip
to the area measure on its image (`TauCeti.map_volume_sphereLongitudeHeight`). The image misses
only the meridian at longitude `a`, with both poles. That meridian is null: off the poles it lies
in the image of the strip starting at `a - π`, where it is the preimage of the segment `θ = a`,
and points are null for the Liouville measure
(`TauCeti.SmoothTwoForm.nullSingletonClass_liouvilleMeasure`).
Hence the area measure is the image of Lebesgue measure on `(0, 2π) × (-1, 1)`
(`TauCeti.liouvilleMeasure_sphereAreaForm`), and projecting to the height gives the
Duistermaat–Heckman measure.

## Main definitions

* `TauCeti.longitudeHeightStrip a`: the open strip `(a, a + 2π) × (-1, 1)` in `ℝ²`.
* `TauCeti.sphereLongitudeHeight a`: the longitude–height parametrization of `S²` on that strip.

## Main results

* `TauCeti.mpullback_sphereLongitudeHeight_sphereAreaForm`: in longitude–height coordinates the
  area form is `dθ ∧ dh`.
* `TauCeti.map_volume_sphereLongitudeHeight`: the parametrization carries Lebesgue measure to the
  area measure on its image.
* `TauCeti.liouvilleMeasure_sphereAreaForm`: the area measure of `S²` is the image of Lebesgue
  measure on `(0, 2π) × (-1, 1)`.
* `TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_height`: the Duistermaat–Heckman measure of the
  height is `2π` times Lebesgue measure on `[-1, 1]`.
* `TauCeti.liouvilleMeasure_sphereAreaForm_univ`: the area of `S²` is `4π`.
* `TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_const`: a constant moment map has
  Duistermaat–Heckman measure `4π δ_c`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 30.1 (the Duistermaat–Heckman measure, and the height function on `S²`).
* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* Archimedes, *On the Sphere and Cylinder*, Book I, Propositions 33 and 42–43.
-/

public section

noncomputable section

open Metric Module MeasureTheory Set Real Matrix
open scoped Manifold ContDiff ENNReal

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-! ### The longitude–height parametrization -/

/-- The longitude–height parametrization `(θ, h) ↦ (√(1 - h²) cos θ, √(1 - h²) sin θ, h)` as a map
to `ℝ³`. -/
private def lhVec (y : ℝ²) : ℝ³ :=
  WithLp.toLp 2 ![√(1 - y 1 ^ 2) * cos (y 0), √(1 - y 1 ^ 2) * sin (y 0), y 1]

private theorem lhVec_mem_sphere {y : ℝ²} (hy : y 1 ^ 2 ≤ 1) : lhVec y ∈ S² := by
  have h : ‖lhVec y‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [lhVec, Fin.sum_univ_three, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_pow,
      Real.sq_sqrt (sub_nonneg.2 hy)]
    linear_combination (1 - y 1 ^ 2) * sin_sq_add_cos_sq (y 0)
  rw [mem_sphere_zero_iff_norm]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

private theorem hasFDerivAt_lhRadius {y : ℝ²} (hy : y 1 ^ 2 < 1) :
    HasFDerivAt (fun x : ℝ² ↦ √(1 - x 1 ^ 2))
      ((-(y 1 / √(1 - y 1 ^ 2))) • (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ)) y := by
  convert (((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1).pow 2).const_sub 1).sqrt (sub_pos.2 hy).ne'
    using 1
  ext v
  have hs : √(1 - y 1 ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 (sub_pos.2 hy)
  simp only [neg_smul, neg_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp

private theorem contDiffAt_lhVec {y : ℝ²} (hy : y 1 ^ 2 < 1) : ContDiffAt ℝ ∞ lhVec y := by
  refine (contDiffAt_piLp 2).2 fun i ↦ ?_
  have hc (j : Fin 2) : ContDiffAt ℝ ∞ (fun x : ℝ² ↦ x j) y := contDiffAt_piLp_apply (p := 2)
  have hr : ContDiffAt ℝ ∞ (fun x : ℝ² ↦ √(1 - x 1 ^ 2)) y :=
    (contDiffAt_const.sub ((hc 1).pow 2)).sqrt (sub_pos.2 hy).ne'
  fin_cases i
  · exact hr.mul (Real.contDiff_cos.contDiffAt.comp y (hc 0))
  · exact hr.mul (Real.contDiff_sin.contDiffAt.comp y (hc 0))
  · exact hc 1

/-- The derivative of the longitude–height parametrization at a point with `|h| < 1`. -/
private theorem fderiv_lhVec_apply {y : ℝ²} (hy : y 1 ^ 2 < 1) (v : ℝ²) :
    fderiv ℝ lhVec y v = WithLp.toLp 2
      ![-(v 0 * √(1 - y 1 ^ 2) * sin (y 0)) - v 1 * (y 1 / √(1 - y 1 ^ 2)) * cos (y 0),
        v 0 * √(1 - y 1 ^ 2) * cos (y 0) - v 1 * (y 1 / √(1 - y 1 ^ 2)) * sin (y 0), v 1] := by
  have hd := ((contDiffAt_lhVec hy).differentiableAt (by simp)).hasFDerivAt
  have key (i : Fin 3) (D : ℝ² →L[ℝ] ℝ) (hD : HasFDerivAt (fun x ↦ lhVec x i) D y) :
      fderiv ℝ lhVec y v i = D v :=
    congrArg (· v) (((EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ).hasFDerivAt.comp y hd).unique hD)
  ext i
  fin_cases i
  · refine (key 0 _ ((hasFDerivAt_lhRadius hy).mul
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).cos)).trans ?_
    simp only [add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, Fin.zero_eta,
      Matrix.cons_val_zero]
    ring
  · refine (key 1 _ ((hasFDerivAt_lhRadius hy).mul
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).sin)).trans ?_
    simp only [add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · refine (key 2 _ (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1)).trans ?_
    simp

/-- The triple product of the parametrization with two of its derivatives is `dθ ∧ dh`. -/
private theorem dotProduct_cross_fderiv_lhVec {y : ℝ²} (hy : y 1 ^ 2 < 1) (v w : ℝ²) :
    (lhVec y).ofLp ⬝ᵥ (fderiv ℝ lhVec y v).ofLp ⨯₃ (fderiv ℝ lhVec y w).ofLp =
      v 0 * w 1 - v 1 * w 0 := by
  have hs : √(1 - y 1 ^ 2) ^ 2 = 1 - y 1 ^ 2 := Real.sq_sqrt (sub_pos.2 hy).le
  have hq : √(1 - y 1 ^ 2) * (y 1 / √(1 - y 1 ^ 2)) = y 1 :=
    mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 (sub_pos.2 hy))
  rw [fderiv_lhVec_apply hy, fderiv_lhVec_apply hy]
  simp only [lhVec, cross_apply, dotProduct, Fin.sum_univ_three, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (v 0 * w 1 - v 1 * w 0) * (sin (y 0) ^ 2 + cos (y 0) ^ 2) * hs +
    (v 0 * w 1 - v 1 * w 0) * y 1 * (sin (y 0) ^ 2 + cos (y 0) ^ 2) * hq +
    (v 0 * w 1 - v 1 * w 0) * sin_sq_add_cos_sq (y 0)

/-! ### The strip and the parametrization of the sphere -/

/-- The open strip `(a, a + 2π) × (-1, 1)` of longitudes `θ` and heights `h`. -/
def longitudeHeightStrip (a : ℝ) : TopologicalSpace.Opens ℝ² where
  carrier := {y | y 0 ∈ Ioo a (a + 2 * π) ∧ y 1 ∈ Ioo (-1) 1}
  is_open' :=
    (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous).inter
      (isOpen_Ioo.preimage (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)

/-- A point lies in the strip when its longitude is in `(a, a + 2π)` and its height in `(-1, 1)`. -/
@[simp]
theorem mem_longitudeHeightStrip {a : ℝ} {y : ℝ²} :
    y ∈ longitudeHeightStrip a ↔ y 0 ∈ Ioo a (a + 2 * π) ∧ y 1 ∈ Ioo (-1) 1 :=
  Iff.rfl

private theorem measurableEmbedding_subtype_val_longitudeHeightStrip (a : ℝ) :
    MeasurableEmbedding (Subtype.val : longitudeHeightStrip a → ℝ²) :=
  MeasurableEmbedding.subtypeVal (longitudeHeightStrip a).isOpen.measurableSet

private theorem sq_lt_one_of_mem_longitudeHeightStrip {a : ℝ} (y : longitudeHeightStrip a) :
    (y : ℝ²) 1 ^ 2 < 1 :=
  sq_lt_one_iff_abs_lt_one _ |>.2 (abs_lt.2 y.property.2)

/-- The **longitude–height parametrization** of the unit sphere,
`(θ, h) ↦ (√(1 - h²) cos θ, √(1 - h²) sin θ, h)`, on the strip `(a, a + 2π) × (-1, 1)`. It is
smooth and injective (`TauCeti.contMDiff_sphereLongitudeHeight`,
`TauCeti.sphereLongitudeHeight_injective`), and it pulls the area form back to `dθ ∧ dh`
(`TauCeti.mpullback_sphereLongitudeHeight_sphereAreaForm`). -/
def sphereLongitudeHeight (a : ℝ) : longitudeHeightStrip a → S² :=
  Set.codRestrict (fun y : longitudeHeightStrip a ↦ lhVec y) _ fun y ↦
    lhVec_mem_sphere (sq_lt_one_of_mem_longitudeHeightStrip y).le

/-- The longitude–height parametrization, read in `ℝ³`. -/
@[simp]
theorem coe_sphereLongitudeHeight (a : ℝ) (y : longitudeHeightStrip a) :
    (sphereLongitudeHeight a y : ℝ³) =
      WithLp.toLp 2 ![√(1 - (y : ℝ²) 1 ^ 2) * cos ((y : ℝ²) 0),
        √(1 - (y : ℝ²) 1 ^ 2) * sin ((y : ℝ²) 0), (y : ℝ²) 1] :=
  (rfl)

/-- The longitude–height parametrization is smooth. -/
theorem contMDiff_sphereLongitudeHeight (a : ℝ) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereLongitudeHeight a) := by
  refine ContMDiff.codRestrict_sphere (fun y ↦ ?_) _
  exact ((contDiffAt_lhVec (sq_lt_one_of_mem_longitudeHeightStrip y)).contMDiffAt).comp y
    contMDiff_subtypeVal.contMDiffAt

/-- The longitude–height parametrization is injective: on a strip of width `2π`, the longitude is
determined by its cosine and sine. -/
theorem sphereLongitudeHeight_injective (a : ℝ) : Function.Injective (sphereLongitudeHeight a) := by
  intro y z h
  have h' (i : Fin 3) := congrArg (fun x : S² ↦ (x : ℝ³) i) h
  simp only [coe_sphereLongitudeHeight, PiLp.toLp_apply] at h'
  have h1 : (y : ℝ²) 1 = (z : ℝ²) 1 := by simpa using h' 2
  have hr : 0 < √(1 - (y : ℝ²) 1 ^ 2) :=
    Real.sqrt_pos.2 (sub_pos.2 (sq_lt_one_of_mem_longitudeHeightStrip y))
  have hcos : cos ((y : ℝ²) 0) = cos ((z : ℝ²) 0) := by
    have := h' 0
    simp only [Matrix.cons_val_zero, ← h1] at this
    exact mul_left_cancel₀ hr.ne' this
  have hsin : sin ((y : ℝ²) 0) = sin ((z : ℝ²) 0) := by
    have := h' 1
    simp only [Matrix.cons_val_one, ← h1] at this
    exact mul_left_cancel₀ hr.ne' this
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hcos hsin)
  have hy := y.property.1
  have hz := z.property.1
  have hk0 : k = 0 := by
    have hlt : |(k : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [Real.pi_pos, hy.1, hy.2, hz.1, hz.2]
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast hlt)
  subst hk0
  refine Subtype.ext ?_
  ext i
  fin_cases i
  · exact sub_eq_zero.1 (by simpa using hk)
  · exact h1

/-- The parametrization is a measurable embedding of the strip into the sphere. -/
theorem measurableEmbedding_sphereLongitudeHeight (a : ℝ) :
    MeasurableEmbedding (sphereLongitudeHeight a) :=
  haveI := (longitudeHeightStrip a).isOpen.polishSpace
  (contMDiff_sphereLongitudeHeight a).continuous.measurableEmbedding
    (sphereLongitudeHeight_injective a)

/-- Read in `ℝ³`, the differential of the parametrization is the derivative of its formula. -/
private theorem mvfderiv_coe_mfderiv_sphereLongitudeHeight (a : ℝ) (y : longitudeHeightStrip a)
    (v : TangentSpace (𝓡 2) y) :
    mvfderiv (𝓡 2) ((↑) : S² → ℝ³) (sphereLongitudeHeight a y)
      (mfderiv (𝓡 2) (𝓡 2) (sphereLongitudeHeight a) y v) = fderiv ℝ lhVec y v := by
  have hd := (contDiffAt_lhVec (sq_lt_one_of_mem_longitudeHeightStrip y)).differentiableAt
    (by simp)
  rw [← mvfderiv_comp_apply y ((contMDiff_coe_sphere (n := 2) (m := 1) _).mdifferentiableAt
      one_ne_zero) ((contMDiff_sphereLongitudeHeight a y).mdifferentiableAt (by simp)) v]
  have hcomp : ((↑) : S² → ℝ³) ∘ sphereLongitudeHeight a = lhVec ∘ Subtype.val :=
    funext (Set.val_codRestrict_apply _ _ _)
  rw [hcomp, mvfderiv_comp_apply_of_differentiableAt hd
    (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero), mvfderiv_apply_eq_mfderiv_apply,
    Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_apply]

/-- **The area form in longitude–height coordinates is `dθ ∧ dh`.** The parametrization
`sphereLongitudeHeight a` pulls the area form of `S²` back to the restriction to the strip of the
standard area form `dθ ∧ dh` of the `(θ, h)`-plane, the determinant form of the standard basis. -/
theorem mpullback_sphereLongitudeHeight_sphereAreaForm (a : ℝ) :
    SmoothForm.mpullback (sphereLongitudeHeight a) (contMDiff_sphereLongitudeHeight a)
        sphereAreaForm =
      SmoothForm.mpullback (Subtype.val : longitudeHeightStrip a → ℝ²) contMDiff_subtypeVal
        (SmoothForm.const (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.continuousDet) := by
  refine Subtype.ext (funext fun y ↦ ?_)
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback, eval₂_sphereAreaForm,
    mvfderiv_coe_mfderiv_sphereLongitudeHeight, mvfderiv_coe_mfderiv_sphereLongitudeHeight]
  refine (dotProduct_cross_fderiv_lhVec (sq_lt_one_of_mem_longitudeHeightStrip y) _ _).trans ?_
  rw [SmoothBundleForm.eval₂_apply, SmoothForm.const_apply, Module.Basis.continuousDet_apply,
    Module.Basis.det_apply, Matrix.det_fin_two, Manifold.mfderiv_subtype_val]
  simp only [Module.Basis.toMatrix_apply, Fin.isValue, ContinuousLinearEquiv.coe_coe,
    Manifold.tangentSpaceOpenEquiv_apply, cons_val, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
  rw [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (y : ℝ²) (v 0),
    NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (y : ℝ²) (v 1)]
  ring

/-! ### The area measure in longitude–height coordinates -/

/-- **Lebesgue measure on the strip is the area measure of its image.** The parametrization
`sphereLongitudeHeight a` carries Lebesgue measure on the strip `(a, a + 2π) × (-1, 1)` to the
Liouville measure `|σ|` of the area form of the unit sphere, restricted to the image of the
strip. -/
theorem map_volume_sphereLongitudeHeight (a : ℝ) :
    (volume.comap ((↑) : longitudeHeightStrip a → ℝ²)).map (sphereLongitudeHeight a) =
      (sphereAreaForm.liouvilleMeasure 1).restrict (range (sphereLongitudeHeight a)) := by
  rw [← (measurableEmbedding_sphereLongitudeHeight a).map_liouvilleMeasure
    ((contMDiff_sphereLongitudeHeight a).mdifferentiable (by simp))
    (SmoothForm.coe_mpullback _ (contMDiff_sphereLongitudeHeight a) sphereAreaForm).symm,
    mpullback_sphereLongitudeHeight_sphereAreaForm,
    SmoothTwoForm.liouvilleMeasure_mpullback_subtypeVal,
    SmoothTwoForm.liouvilleMeasure_const_continuousDet, OrthonormalBasis.addHaar_eq_volume]

/-! ### The meridian is null -/

/-- A point of the sphere off the vertical axis is covered by one of the strips starting at
longitudes `0` and `-π`. -/
private theorem mem_range_sphereLongitudeHeight_of_ne (x : S²)
    (hx : (x : ℝ³) 0 ≠ 0 ∨ (x : ℝ³) 1 ≠ 0) :
    x ∈ range (sphereLongitudeHeight 0) ∪ range (sphereLongitudeHeight (-π)) := by
  set z : ℂ := ⟨(x : ℝ³) 0, (x : ℝ³) 1⟩
  have hz : z ≠ 0 := fun h ↦ by
    rcases hx with hx | hx
    · exact hx (congrArg Complex.re h)
    · exact hx (congrArg Complex.im h)
  have hnorm := EuclideanSpace.sq_add_sq_add_sq_of_mem_sphere x.property
  -- `‖z‖ = √(1 - h²)` for the height `h` of `x`.
  have hz2 : ‖z‖ = √(1 - (x : ℝ³) 2 ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    congr 1
    linear_combination hnorm
  have hh : (x : ℝ³) 2 ^ 2 < 1 := by
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [hz2, Real.sqrt_pos] at this
    linarith
  have hh' : (x : ℝ³) 2 ∈ Ioo (-1) 1 := by
    simpa [mem_Ioo, abs_lt] using (sq_lt_one_iff_abs_lt_one _).1 hh
  have hmk (a : ℝ) (hθ : z.arg ∈ Ioo a (a + 2 * π)) :
      x ∈ range (sphereLongitudeHeight a) := by
    refine ⟨⟨WithLp.toLp 2 ![z.arg, (x : ℝ³) 2], hθ, hh'⟩, Subtype.ext ?_⟩
    ext i
    fin_cases i
    · simp [← hz2, Complex.norm_mul_cos_arg, z]
    · simp [← hz2, Complex.norm_mul_sin_arg, z]
    · simp
  rcases (Complex.arg_le_pi z).eq_or_lt with h | h
  · exact Or.inl (hmk 0 ⟨h ▸ Real.pi_pos, by linarith [h, Real.pi_pos]⟩)
  · exact Or.inr (hmk (-π) ⟨Complex.neg_pi_lt_arg z, by linarith⟩)

/-- Off the meridian `θ = 0`, the strip starting at `-π` is covered by the strip starting at `0`. -/
private theorem mem_range_sphereLongitudeHeight_zero (y : longitudeHeightStrip (-π))
    (hy : (y : ℝ²) 0 ≠ 0) :
    sphereLongitudeHeight (-π) y ∈ range (sphereLongitudeHeight 0) := by
  have h0 := y.property.1
  have h1 := y.property.2
  rcases hy.lt_or_gt with hy | hy
  · refine ⟨⟨WithLp.toLp 2 ![(y : ℝ²) 0 + 2 * π, (y : ℝ²) 1],
      ⟨by simp only [cons_val_zero]; linarith [h0.1], by simp only [cons_val_zero]; linarith⟩, h1⟩,
      Subtype.ext ?_⟩
    ext i
    fin_cases i <;> simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  · refine ⟨⟨y, ⟨hy, by linarith [h0.2, Real.pi_pos]⟩, h1⟩, Subtype.ext ?_⟩
    simp [coe_sphereLongitudeHeight]

/-- The poles of the sphere are null for its area measure. -/
private theorem liouvilleMeasure_poles :
    sphereAreaForm.liouvilleMeasure 1 {x : S² | (x : ℝ³) 0 = 0 ∧ (x : ℝ³) 1 = 0} = 0 := by
  refine Set.Finite.measure_zero ?_ _
  refine Set.Finite.of_finite_image (f := fun x : S² ↦ (x : ℝ³) 2)
    ((Set.finite_singleton 1).insert (-1) |>.subset ?_) ?_
  · rintro _ ⟨x, ⟨h0, h1⟩, rfl⟩
    have hnorm := EuclideanSpace.sq_add_sq_add_sq_of_mem_sphere x.property
    rw [h0, h1] at hnorm
    have : ((x : ℝ³) 2 + 1) * ((x : ℝ³) 2 - 1) = 0 := by linear_combination hnorm
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by simp only [mem_singleton_iff]; linarith)
  · rintro x ⟨hx0, hx1⟩ x' ⟨hx0', hx1'⟩ h
    refine Subtype.ext ?_
    ext i
    fin_cases i
    · exact hx0.trans hx0'.symm
    · exact hx1.trans hx1'.symm
    · exact h

/-- The complement of the image of the strip starting at longitude `0`, the meridian through
`(1, 0, 0)` with both poles, is null for the area measure. -/
private theorem liouvilleMeasure_compl_range_sphereLongitudeHeight :
    sphereAreaForm.liouvilleMeasure 1 (range (sphereLongitudeHeight 0))ᶜ = 0 := by
  set μ := sphereAreaForm.liouvilleMeasure 1
  have hm (a : ℝ) := (measurableEmbedding_sphereLongitudeHeight a).measurableSet_range
  -- The strip starting at `-π` meets the meridian along the null segment `θ = 0`.
  have hM : μ (range (sphereLongitudeHeight (-π)) ∩ (range (sphereLongitudeHeight 0))ᶜ) = 0 := by
    rw [inter_comm, ← Measure.restrict_apply (hm 0).compl, ← map_volume_sphereLongitudeHeight,
      Measure.map_apply (measurableEmbedding_sphereLongitudeHeight _).measurable (hm 0).compl,
      (measurableEmbedding_subtype_val_longitudeHeightStrip _).comap_apply]
    have hker : (volume : Measure ℝ²) (LinearMap.ker (EuclideanSpace.proj (0 : Fin 2) :
        ℝ² →L[ℝ] ℝ).toLinearMap) = 0 := by
      refine Measure.addHaar_submodule _ _ fun h ↦ ?_
      have := (Submodule.eq_top_iff'.1 h) (EuclideanSpace.single 0 1)
      simp at this
    refine measure_mono_null ?_ hker
    rintro _ ⟨y, hy, rfl⟩
    by_contra h0
    exact hy (mem_range_sphereLongitudeHeight_zero y h0)
  refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null liouvilleMeasure_poles hM)
  by_cases h : (x : ℝ³) 0 = 0 ∧ (x : ℝ³) 1 = 0
  · exact Or.inl h
  · refine Or.inr ⟨?_, hx⟩
    rcases mem_range_sphereLongitudeHeight_of_ne x (by tauto) with h' | h'
    · exact absurd h' hx
    · exact h'

/-! ### The area measure and the Duistermaat–Heckman measure of the height -/

/-- **The area measure of `S²` in longitude–height coordinates.** The Liouville measure `|σ|` of
the area form of the unit sphere is the image of Lebesgue measure on the strip
`(0, 2π) × (-1, 1)` under the longitude–height parametrization: the meridian it misses is
null. -/
theorem liouvilleMeasure_sphereAreaForm :
    sphereAreaForm.liouvilleMeasure 1 =
      (volume.comap ((↑) : longitudeHeightStrip 0 → ℝ²)).map (sphereLongitudeHeight 0) := by
  rw [map_volume_sphereLongitudeHeight, Measure.restrict_eq_self_of_ae_mem]
  exact measure_eq_zero_iff_ae_notMem.1 liouvilleMeasure_compl_range_sphereLongitudeHeight
    |>.mono fun _ h ↦ not_not.1 h

/-- Projecting Lebesgue measure on the strip `(0, 2π) × (-1, 1)` to the height gives `2π` times
Lebesgue measure on `(-1, 1)`. -/
private theorem map_restrict_longitudeHeightStrip_zero :
    (volume.restrict (longitudeHeightStrip 0 : Set ℝ²)).map (fun y : ℝ² ↦ y 1) =
      ENNReal.ofReal (2 * π) • volume.restrict (Ioo (-1) 1) := by
  set e : ℝ² → ℝ × ℝ := fun y ↦ (y 0, y 1)
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hS : (longitudeHeightStrip 0 : Set ℝ²) = e ⁻¹' (Ioo 0 (0 + 2 * π) ×ˢ Ioo (-1) 1) := by
    ext y
    simp [e, mem_longitudeHeightStrip]
  have hsnd : (fun y : ℝ² ↦ y 1) = Prod.snd ∘ e := rfl
  rw [hS, hsnd, ← Measure.map_map measurable_snd he.measurable,
    (he.restrict_preimage (measurableSet_Ioo.prod measurableSet_Ioo)).map_eq,
    Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.map_snd_prod,
    Measure.restrict_apply_univ, Real.volume_Ioo, zero_add, sub_zero]

private theorem measurable_height : Measurable fun x : S² ↦ (x : ℝ³) 2 :=
  ((EuclideanSpace.proj (2 : Fin 3) : ℝ³ →L[ℝ] ℝ).continuous.comp continuous_subtypeVal).measurable

/-- **The Duistermaat–Heckman measure of the height on `S²` is `2π` times Lebesgue measure.** The
height `h(x) = x₃` generates the rotations of the unit sphere about the vertical axis with its area
form `σ`. Its Duistermaat–Heckman measure, the pushforward of the area measure `|σ|` along `h`, is
`2π` times Lebesgue measure on the interval `[-1, 1]` of heights. This is Archimedes' theorem that
the band of the sphere between two heights has the area of the corresponding band of the
circumscribed cylinder. -/
theorem duistermaatHeckmanMeasure_sphereAreaForm_height :
    sphereAreaForm.duistermaatHeckmanMeasure 1 (fun x : S² ↦ (x : ℝ³) 2) =
      ENNReal.ofReal (2 * π) • volume.restrict (Icc (-1) 1) := by
  have h1 : Measurable fun y : ℝ² ↦ y 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous.measurable
  have hcomp : (fun x : S² ↦ (x : ℝ³) 2) ∘ sphereLongitudeHeight 0 =
      (fun y : ℝ² ↦ y 1) ∘ Subtype.val :=
    funext fun y ↦ by simp [coe_sphereLongitudeHeight]
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_def, liouvilleMeasure_sphereAreaForm,
    Measure.map_map measurable_height (measurableEmbedding_sphereLongitudeHeight 0).measurable,
    hcomp, ← Measure.map_map h1 measurable_subtypeVal,
    (measurableEmbedding_subtype_val_longitudeHeightStrip 0).map_comap,
    Subtype.range_coe, map_restrict_longitudeHeightStrip_zero,
    Measure.restrict_congr_set Ioo_ae_eq_Icc]

/-- **The area of the unit sphere is `4π`**, as the total mass of its Liouville measure. -/
@[simp]
theorem liouvilleMeasure_sphereAreaForm_univ :
    sphereAreaForm.liouvilleMeasure 1 univ = ENNReal.ofReal (4 * π) := by
  rw [← SmoothTwoForm.duistermaatHeckmanMeasure_univ measurable_height,
    duistermaatHeckmanMeasure_sphereAreaForm_height, smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- **The Duistermaat–Heckman measure of a constant moment map on `S²`.** A constant map, such as
the moment map of the trivial circle action, pushes the area measure of the unit sphere forward to
the point mass `4π δ_c`. -/
theorem duistermaatHeckmanMeasure_sphereAreaForm_const {F : Type*} [MeasurableSpace F] (c : F) :
    sphereAreaForm.duistermaatHeckmanMeasure 1 (fun _ : S² ↦ c) =
      ENNReal.ofReal (4 * π) • Measure.dirac c := by
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_const, liouvilleMeasure_sphereAreaForm_univ]

end TauCeti
