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
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Geometry.Symplectic.Darboux.Basis

/-!
# The Duistermaat–Heckman measure of the height on the two-sphere

The rotations of the unit sphere `S² ⊂ ℝ³` about the vertical axis are the Hamiltonian flow of
the height `h(x) = x₃` for the area form `σ_x(v, w) = x ⬝ (v × w)`
(`TauCeti.sphereAreaForm`, `TauCeti.mvfderiv_hamiltonianVectorField_sphereAreaForm`), so `h` is
the moment map of this circle action. This file computes its Duistermaat–Heckman measure, the
pushforward `h_* |σ|` of the Liouville measure: it is `2π` times Lebesgue measure on `[-1, 1]`
(`TauCeti.duistermaatHeckmanMeasure_sphereAreaForm`). Its density `2π` is the period of the
rotation, and its total mass is the area `4π` of the sphere. Equivalently, the zone of the sphere
between two heights `-1 ≤ a ≤ b ≤ 1` has area `2π (b - a)`
(`TauCeti.liouvilleMeasure_sphereAreaForm_setOf_mem_Icc`): this is Archimedes' theorem that the
horizontal projection of the sphere onto its circumscribed cylinder preserves area.

The proof is Archimedes' argument. In cylindrical coordinates `(θ, h)` the map

`(θ, h) ↦ (√(1 - h²) cos θ, √(1 - h²) sin θ, h)`

pulls `σ` back to the constant form `dθ ∧ dh` on the strip `(a, a + 2π) × (-1, 1)`, whose
Liouville measure is Lebesgue measure. Since `σ` is the volume form of the sphere for the outward
normal, this is the triple product computation `x ⬝ (∂_θ x × ∂_h x) = 1`. The map is a smooth
embedding of the strip, so it carries Lebesgue measure on the strip to the Liouville measure of its
image (`MeasurableEmbedding.map_liouvilleMeasure`), and the height becomes the coordinate `h`.
For `a = -π` the image misses only the half-meridian `x₂ = 0`, `x₁ < 0` and the two poles. The
half-meridian is the image of the segment `θ = π` for `a = 0`, a Lebesgue-null set, and the
poles are null because the Liouville measure has no atoms
(`TauCeti.SmoothTwoForm.nullSingletonClass_liouvilleMeasure`).

Lean indexes the coordinates of `ℝ³ = EuclideanSpace ℝ (Fin 3)` by `0, 1, 2`, so the height is
`x 2`.

## Main results

* `TauCeti.duistermaatHeckmanMeasure_sphereAreaForm`: the Duistermaat–Heckman measure of the height
  on `S²` is `2π` times Lebesgue measure on `[-1, 1]`.
* `TauCeti.liouvilleMeasure_sphereAreaForm_setOf_mem_Icc`: **Archimedes' theorem**, the zone
  between the heights `a ≤ b` has area `2π (b - a)`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 30 (the Duistermaat–Heckman measure).
* Archimedes, *On the Sphere and Cylinder*, Book I (the area of a zone of the sphere).
-/

public section

noncomputable section

open Metric Module Matrix WithLp MeasureTheory Set Real
open scoped Manifold ContDiff EuclideanSpace

namespace TauCeti

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "S²" => sphere (0 : ℝ³) 1

/-! ### The area form of the plane -/

/-- The identification of `ℝ × ℝ` with the Euclidean plane, `(θ, h) ↦ (θ, h)`. -/
private def planeEquiv : (ℝ × ℝ) ≃ₗ[ℝ] ℝ² :=
  (LinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearEquiv

/-- The area form `dθ ∧ dh` of the Euclidean plane, the standard symplectic form of `ℝ × ℝ`. -/
private def planeAreaForm : SymplecticForm ℝ² :=
  (stdSymplecticForm (V := ℝ)).transport planeEquiv

private theorem planeAreaForm_apply (u v : ℝ²) : planeAreaForm u v = u 0 * v 1 - u 1 * v 0 := by
  simp [planeAreaForm, planeEquiv]
  ring

private instance : Fact (finrank ℝ ℝ² = 2 * 1) := ⟨by simp⟩

/-- The standard basis of the plane, indexed as a Darboux basis `(q₁, p₁)`. -/
private def planeBasis : Basis (Fin 1 × Fin 2) ℝ ℝ² :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.reindex
    ((finCongr (by norm_num : 2 = 1 * 2)).trans (finProdFinEquiv (m := 1) (n := 2)).symm)

private theorem isDarbouxBasis_planeBasis : planeAreaForm.IsDarbouxBasis planeBasis where
  apply_fst_fst i j := by
    fin_cases i; fin_cases j; simp
  apply_snd_snd i j := by
    fin_cases i; fin_cases j; simp
  apply_fst_snd i j := by
    fin_cases i; fin_cases j; simp [planeBasis, planeAreaForm_apply, finProdFinEquiv]

/-- The Liouville measure of `dθ ∧ dh` is Lebesgue measure. -/
private theorem liouvilleMeasure_planeAreaForm :
    planeAreaForm.constSmooth.liouvilleMeasure 1 = volume := by
  rw [SymplecticForm.liouvilleMeasure_constSmooth _ isDarbouxBasis_planeBasis, planeBasis,
    Basis.addHaar_reindex, OrthonormalBasis.addHaar_eq_volume]

/-! ### Cylindrical coordinates on the sphere -/

/-- The strip `(a, a + 2π) × (-1, 1)` of cylindrical coordinates `(θ, h)`. -/
private def strip (a : ℝ) : TopologicalSpace.Opens ℝ² :=
  ⟨{p | p 0 ∈ Ioo a (a + 2 * π) ∧ p 1 ∈ Ioo (-1) 1},
    (isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
      (isOpen_Ioo.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous)⟩

private theorem mem_strip {a : ℝ} {p : ℝ²} :
    p ∈ strip a ↔ p 0 ∈ Ioo a (a + 2 * π) ∧ p 1 ∈ Ioo (-1) 1 :=
  Iff.rfl

/-- Archimedes' cylindrical coordinates `(θ, h) ↦ (√(1 - h²) cos θ, √(1 - h²) sin θ, h)`, read
in `ℝ³`. -/
private def sphereCylinderCoord (p : ℝ²) : ℝ³ :=
  !₂[√(1 - p 1 ^ 2) * cos (p 0), √(1 - p 1 ^ 2) * sin (p 0), p 1]

private theorem norm_sphereCylinderCoord {p : ℝ²} (hp : |p 1| ≤ 1) :
    ‖sphereCylinderCoord p‖ = 1 := by
  have h : 0 ≤ 1 - p 1 ^ 2 := by nlinarith [abs_le.1 hp]
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three]
  simp only [sphereCylinderCoord, Real.norm_eq_abs, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [mul_pow, mul_pow, Real.sq_sqrt h]
  nlinarith [sin_sq_add_cos_sq (p 0)]

private theorem contDiffAt_sphereCylinderCoord {p : ℝ²} (hp : p 1 ∈ Ioo (-1) 1) :
    ContDiffAt ℝ ∞ sphereCylinderCoord p := by
  have h : 1 - p 1 ^ 2 ≠ 0 := by nlinarith [hp.1, hp.2]
  have h1 : ContDiff ℝ ∞ fun q : ℝ² ↦ q 1 := contDiff_piLp_apply 2
  have h0 : ContDiff ℝ ∞ fun q : ℝ² ↦ q 0 := contDiff_piLp_apply 2
  have hs : ContDiffAt ℝ ∞ (fun q : ℝ² ↦ √(1 - q 1 ^ 2)) p :=
    (Real.contDiffAt_sqrt h).comp p (contDiffAt_const.sub (h1.contDiffAt.pow 2))
  refine contDiffAt_piLp' 2 fun i ↦ ?_
  fin_cases i
  · exact hs.mul (Real.contDiff_cos.comp h0).contDiffAt
  · exact hs.mul (Real.contDiff_sin.comp h0).contDiffAt
  · exact h1.contDiffAt

/-- Archimedes' cylindrical coordinates on the strip `(a, a + 2π) × (-1, 1)`, as a map to the
sphere. -/
private def sphereCylinder (a : ℝ) : strip a → S² :=
  Set.codRestrict (fun p : strip a ↦ sphereCylinderCoord p) _ fun p ↦
    mem_sphere_zero_iff_norm.2 (norm_sphereCylinderCoord (abs_le.2 ⟨p.2.2.1.le, p.2.2.2.le⟩))

private theorem coe_sphereCylinder (a : ℝ) (p : strip a) :
    (sphereCylinder a p : ℝ³) = sphereCylinderCoord p :=
  rfl

private theorem contMDiff_sphereCylinder (a : ℝ) : ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereCylinder a) :=
  ContMDiff.codRestrict_sphere (fun p ↦
    (contDiffAt_sphereCylinderCoord p.2.2).contMDiffAt.comp p (contMDiff_subtype_val p)) _

/-- Cylindrical coordinates are injective on a strip of width `2π`. -/
private theorem injective_sphereCylinder (a : ℝ) : Function.Injective (sphereCylinder a) := by
  intro p q hpq
  have hpq' := congrArg (fun x : S² ↦ (x : ℝ³)) hpq
  simp only [coe_sphereCylinder, sphereCylinderCoord] at hpq'
  have h2 := congrArg (· 2) hpq'
  have h0 := congrArg (· 0) hpq'
  have h1 := congrArg (· 1) hpq'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hr : 0 < √(1 - (p : ℝ²) 1 ^ 2) := Real.sqrt_pos.2 (by nlinarith [p.2.2.1, p.2.2.2])
  rw [h2] at h0 h1 hr
  have hc := mul_left_cancel₀ hr.ne' h0
  have hs := mul_left_cancel₀ hr.ne' h1
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hc hs)
  have hp0 := p.2.1
  have hq0 := q.2.1
  have hk0 : k = 0 := by
    have hlt : |(k : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [hp0.1, hp0.2, hq0.1, hq0.2, Real.pi_pos]
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast hlt)
  rw [hk0, Int.cast_zero, mul_zero, sub_eq_zero] at hk
  refine Subtype.ext (PiLp.ext fun i ↦ ?_)
  fin_cases i
  · exact hk
  · exact h2

private theorem fderiv_sphereCylinderCoord_apply {p : ℝ²} (hp : p 1 ∈ Ioo (-1) 1) (u : ℝ²) :
    fderiv ℝ sphereCylinderCoord p u =
      !₂[-(√(1 - p 1 ^ 2) * sin (p 0)) * u 0 - p 1 / √(1 - p 1 ^ 2) * cos (p 0) * u 1,
        √(1 - p 1 ^ 2) * cos (p 0) * u 0 - p 1 / √(1 - p 1 ^ 2) * sin (p 0) * u 1, u 1] := by
  have h : 1 - p 1 ^ 2 ≠ 0 := by nlinarith [hp.1, hp.2]
  have hr : √(1 - p 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (by nlinarith [hp.1, hp.2])
    (Ne.symm h))).ne'
  have hd : HasFDerivAt sphereCylinderCoord (fderiv ℝ sphereCylinderCoord p) p :=
    ((contDiffAt_sphereCylinderCoord hp).differentiableAt (by simp)).hasFDerivAt
  have hcomp (i : Fin 3) := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (sphereCylinderCoord p) i).comp p hd
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (0 : Fin 2)
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (1 : Fin 2)
  have hs := ((h1.pow 2).const_sub 1).sqrt h
  refine PiLp.ext fun i ↦ ?_
  fin_cases i
  · have := (hcomp 0).unique (hs.mul h0.cos)
    have := congrArg (· u) this
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [show (fderiv ℝ sphereCylinderCoord p u) 0 = _ from this]
    simp
    field_simp
    ring
  · have := congrArg (· u) ((hcomp 1).unique (hs.mul h0.sin))
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show (fderiv ℝ sphereCylinderCoord p u) 1 = _ from this]
    simp
    field_simp
    ring
  · have := congrArg (· u) ((hcomp 2).unique h1)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [show (fderiv ℝ sphereCylinderCoord p u) 2 = _ from this]
    simp

/-- The triple product `x ⬝ (dx(u) × dx(w))` in cylindrical coordinates is `dθ ∧ dh (u, w)`. -/
private theorem dotProduct_cross_fderiv_sphereCylinderCoord {p : ℝ²} (hp : p 1 ∈ Ioo (-1) 1)
    (u w : ℝ²) :
    ofLp (sphereCylinderCoord p) ⬝ᵥ
        ofLp (fderiv ℝ sphereCylinderCoord p u) ⨯₃ ofLp (fderiv ℝ sphereCylinderCoord p w) =
      u 0 * w 1 - u 1 * w 0 := by
  have h : 0 < 1 - p 1 ^ 2 := by nlinarith [hp.1, hp.2]
  have hr2 := Real.sq_sqrt h.le
  rw [fderiv_sphereCylinderCoord_apply hp, fderiv_sphereCylinderCoord_apply hp]
  simp only [sphereCylinderCoord, cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  field_simp
  rw [hr2]
  linear_combination (1 - p 1 ^ 2) * (u 0 * w 1 - u 1 * w 0) * sin_sq_add_cos_sq (p 0)

/-- **Archimedes' map preserves area**: cylindrical coordinates pull the area form of the sphere
back to `dθ ∧ dh`. -/
private theorem mpullback_sphereCylinder_sphereAreaForm (a : ℝ) :
    SmoothForm.mpullback (sphereCylinder a) (contMDiff_sphereCylinder a) sphereAreaForm =
      SmoothForm.mpullback (Subtype.val : strip a → ℝ²) contMDiff_subtype_val
        planeAreaForm.constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  have hΦ : MDifferentiableAt (𝓡 2) (𝓡 2) (sphereCylinder a) x :=
    (contMDiff_sphereCylinder a).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³) ((↑) : S² → ℝ³) (sphereCylinder a x) :=
    (contMDiff_coe_sphere (n := 2)).mdifferentiableAt (n := 1) one_ne_zero
  have hd : DifferentiableAt ℝ sphereCylinderCoord (x : ℝ²) :=
    (contDiffAt_sphereCylinderCoord x.2.2).differentiableAt (by simp)
  have hval : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ²) (Subtype.val : strip a → ℝ²) x :=
    contMDiff_subtype_val.mdifferentiableAt (n := 1) one_ne_zero
  have key (u : TangentSpace (𝓡 2) x) :
      mvfderiv (𝓡 2) ((↑) : S² → ℝ³) (sphereCylinder a x)
        (mfderiv (𝓡 2) (𝓡 2) (sphereCylinder a) x u) = fderiv ℝ sphereCylinderCoord x u := by
    rw [← mvfderiv_comp_apply x hι hΦ]
    exact (mvfderiv_comp_apply_of_differentiableAt hd hval u).trans
      (congrArg _ (TauCeti.Manifold.mvfderiv_subtype_val_apply x u))
  rw [SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback, eval₂_sphereAreaForm,
    SymplecticForm.eval₂_constSmooth_mfderiv_eq, TauCeti.Manifold.mvfderiv_subtype_val_apply,
    TauCeti.Manifold.mvfderiv_subtype_val_apply, key, key, coe_sphereCylinder]
  exact (dotProduct_cross_fderiv_sphereCylinderCoord x.2.2 v w).trans (planeAreaForm_apply v w).symm

private theorem measurableEmbedding_sphereCylinder (a : ℝ) :
    MeasurableEmbedding (sphereCylinder a) := by
  have : PolishSpace (strip a) := (strip a).isOpen.polishSpace
  exact (contMDiff_sphereCylinder a).continuous.measurableEmbedding (injective_sphereCylinder a)

/-- Cylindrical coordinates carry Lebesgue measure on the strip to the area of their image. -/
private theorem map_comap_volume_sphereCylinder (a : ℝ) :
    ((volume : Measure ℝ²).comap Subtype.val).map (sphereCylinder a) =
      (sphereAreaForm.liouvilleMeasure 1).restrict (range (sphereCylinder a)) := by
  have h := (measurableEmbedding_sphereCylinder a).map_liouvilleMeasure (n := 1)
    ((contMDiff_sphereCylinder a).mdifferentiable (by simp))
    ((SmoothForm.coe_mpullback _ _ _).symm.trans
      (congrArg Subtype.val (mpullback_sphereCylinder_sphereAreaForm a)))
  rwa [SmoothTwoForm.liouvilleMeasure_mpullback_subtypeVal, liouvilleMeasure_planeAreaForm] at h

/-- The Lebesgue measure of a coordinate rectangle of the plane. -/
private theorem volume_setOf_apply_mem_and (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    volume {p : ℝ² | p 0 ∈ A ∧ p 1 ∈ B} = volume A * volume B := by
  have h : {p : ℝ² | p 0 ∈ A ∧ p 1 ∈ B} = ofLp ⁻¹' (univ.pi ![A, B]) := by
    ext p
    simp [Fin.forall_fin_two]
  rw [h, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun i ↦ by fin_cases i <;> simpa).nullMeasurableSet, volume_pi_pi,
    Fin.prod_univ_two]
  simp

/-- The area of the image of a measurable subset of the strip is its Lebesgue measure. -/
private theorem liouvilleMeasure_sphereCylinder_image (a : ℝ) {s : Set (strip a)}
    (hs : MeasurableSet s) :
    sphereAreaForm.liouvilleMeasure 1 (sphereCylinder a '' s) = volume (Subtype.val '' s) := by
  have hΦ := measurableEmbedding_sphereCylinder a
  have hv : MeasurableEmbedding (Subtype.val : strip a → ℝ²) :=
    MeasurableEmbedding.subtype_coe (strip a).isOpen.measurableSet
  have h := congrArg (· (sphereCylinder a '' s)) (map_comap_volume_sphereCylinder a)
  rw [Measure.restrict_apply (hΦ.measurableSet_image' hs),
    inter_eq_left.2 (image_subset_range _ _), hΦ.map_apply,
    preimage_image_eq _ (injective_sphereCylinder a), hv.comap_apply] at h
  exact h.symm

/-- A point of `S²` has coordinates with squares summing to `1`. -/
private theorem sq_add_sq_add_sq (x : S²) :
    (x : ℝ³) 0 ^ 2 + (x : ℝ³) 1 ^ 2 + (x : ℝ³) 2 ^ 2 = 1 := by
  have h := norm_eq_of_mem_sphere x
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- Off the poles and the half-meridian `x 1 = 0`, `x 0 < 0`, every point of the sphere has
cylindrical coordinates in the strip `(-π, π) × (-1, 1)`. -/
private theorem mem_range_sphereCylinder_of_ne (x : S²) (h2 : (x : ℝ³) 2 ∈ Ioo (-1) 1)
    (h01 : ¬((x : ℝ³) 1 = 0 ∧ (x : ℝ³) 0 < 0)) : x ∈ range (sphereCylinder (-π)) := by
  have hx := sq_add_sq_add_sq x
  set z : ℂ := ⟨(x : ℝ³) 0, (x : ℝ³) 1⟩
  have hz2 : ‖z‖ ^ 2 = 1 - (x : ℝ³) 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [z]
    linarith
  have hz : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz2
    nlinarith [h2.1, h2.2]
  have hr : √(1 - (x : ℝ³) 2 ^ 2) = ‖z‖ := by
    rw [← hz2, Real.sqrt_sq (norm_nonneg z)]
  have hπ : Complex.arg z ≠ π := by
    rw [Ne, Complex.arg_eq_pi_iff]
    exact fun h ↦ h01 ⟨h.2, h.1⟩
  refine ⟨⟨!₂[Complex.arg z, (x : ℝ³) 2], ⟨Complex.neg_pi_lt_arg z, ?_⟩, h2⟩, ?_⟩
  · simpa [two_mul] using lt_of_le_of_ne (Complex.arg_le_pi z) hπ
  refine Subtype.ext (PiLp.ext fun i ↦ ?_)
  rw [coe_sphereCylinder]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  fin_cases i
  · simp [sphereCylinderCoord, hr, Complex.cos_arg hz, z, mul_div_cancel₀ _ hn]
  · simp [sphereCylinderCoord, hr, Complex.sin_arg, z, mul_div_cancel₀ _ hn]
  · simp [sphereCylinderCoord]

/-- Each pole `x 2 = c`, `c = ±1`, of the sphere has area zero. -/
private theorem liouvilleMeasure_sphereAreaForm_setOf_apply_two_eq {c : ℝ} (hc : c ^ 2 = 1) :
    sphereAreaForm.liouvilleMeasure 1 {x : S² | (x : ℝ³) 2 = c} = 0 := by
  have hsub : {x : S² | (x : ℝ³) 2 = c}.Subsingleton := by
    -- A point at height `±1` has vanishing horizontal coordinates.
    have h01 {x : S²} (hx : (x : ℝ³) 2 = c) : (x : ℝ³) 0 = 0 ∧ (x : ℝ³) 1 = 0 := by
      have h := sq_add_sq_add_sq x
      rw [hx, hc] at h
      exact ⟨pow_eq_zero_iff two_ne_zero |>.1
          (by linarith [sq_nonneg ((x : ℝ³) 0), sq_nonneg ((x : ℝ³) 1)]),
        pow_eq_zero_iff two_ne_zero |>.1
          (by linarith [sq_nonneg ((x : ℝ³) 0), sq_nonneg ((x : ℝ³) 1)])⟩
    intro x hx y hy
    refine Subtype.ext (PiLp.ext fun i ↦ ?_)
    fin_cases i
    · exact (h01 hx).1.trans (h01 hy).1.symm
    · exact (h01 hx).2.trans (h01 hy).2.symm
    · exact (hx : (x : ℝ³) 2 = c).trans (hy : (y : ℝ³) 2 = c).symm
  exact hsub.induction_on (p := fun s ↦ sphereAreaForm.liouvilleMeasure 1 s = 0) measure_empty
    fun x ↦ measure_singleton x

/-- The half-meridian `x 1 = 0`, `x 0 < 0` off the poles is the image of the segment `θ = π` under
cylindrical coordinates on the strip `(0, 2π) × (-1, 1)`. -/
private theorem mem_image_sphereCylinder_of_apply_one_eq_zero (x : S²)
    (h2 : (x : ℝ³) 2 ∈ Ioo (-1) 1) (h1 : (x : ℝ³) 1 = 0) (h0 : (x : ℝ³) 0 < 0) :
    x ∈ sphereCylinder 0 '' {p | (p : ℝ²) 0 = π} := by
  have hsq := sq_add_sq_add_sq x
  rw [h1] at hsq
  have hr : √(1 - (x : ℝ³) 2 ^ 2) = -(x : ℝ³) 0 := by
    rw [show 1 - (x : ℝ³) 2 ^ 2 = (-(x : ℝ³) 0) ^ 2 by linarith, Real.sqrt_sq (by linarith)]
  refine ⟨⟨!₂[π, (x : ℝ³) 2], ⟨by simp [pi_pos], by simp [pi_pos]⟩, h2⟩, rfl, ?_⟩
  refine Subtype.ext (PiLp.ext fun i ↦ ?_)
  rw [coe_sphereCylinder]
  fin_cases i
  · simp [sphereCylinderCoord, hr]
  · simp [sphereCylinderCoord, h1]
  · simp [sphereCylinderCoord]

/-- The points of the sphere without cylindrical coordinates in `(-π, π) × (-1, 1)` have area
zero: they are the two poles and a half-meridian. -/
private theorem liouvilleMeasure_compl_range_sphereCylinder :
    sphereAreaForm.liouvilleMeasure 1 (range (sphereCylinder (-π)))ᶜ = 0 := by
  set T : Set (strip 0) := {p | (p : ℝ²) 0 = π}
  have hT : MeasurableSet T :=
    (measurableSet_singleton π).preimage ((PiLp.continuous_apply 2 _ 0).comp
      continuous_subtype_val).measurable
  -- The half-meridian is the image of a segment, which is Lebesgue-null.
  have hcut : sphereAreaForm.liouvilleMeasure 1 (sphereCylinder 0 '' T) = 0 := by
    rw [liouvilleMeasure_sphereCylinder_image 0 hT]
    refine measure_mono_null (t := {p : ℝ² | p 0 ∈ ({π} : Set ℝ) ∧ p 1 ∈ (univ : Set ℝ)}) ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨hp, mem_univ _⟩
    · rw [volume_setOf_apply_mem_and _ _ (measurableSet_singleton π) MeasurableSet.univ,
        Real.volume_singleton, zero_mul]
  refine measure_mono_null (t := {x : S² | (x : ℝ³) 2 = 1} ∪ {x : S² | (x : ℝ³) 2 = -1} ∪
    sphereCylinder 0 '' T) ?_ (measure_union_null (measure_union_null
      (liouvilleMeasure_sphereAreaForm_setOf_apply_two_eq (by norm_num))
      (liouvilleMeasure_sphereAreaForm_setOf_apply_two_eq (by norm_num))) hcut)
  intro x hx
  by_cases h2 : (x : ℝ³) 2 ∈ Ioo (-1) 1
  · by_cases h01 : (x : ℝ³) 1 = 0 ∧ (x : ℝ³) 0 < 0
    · exact Or.inr (mem_image_sphereCylinder_of_apply_one_eq_zero x h2 h01.1 h01.2)
    · exact absurd (mem_range_sphereCylinder_of_ne x h2 h01) hx
  · -- Off the open band the height is `±1`, since it lies in `[-1, 1]`.
    have h1 : (x : ℝ³) 2 ^ 2 ≤ 1 := by
      nlinarith [sq_add_sq_add_sq x, sq_nonneg ((x : ℝ³) 0), sq_nonneg ((x : ℝ³) 1)]
    rcases (show (x : ℝ³) 2 = 1 ∨ (x : ℝ³) 2 = -1 by
      by_contra hne
      push Not at hne
      exact h2 ⟨lt_of_le_of_ne (by nlinarith [h1]) (Ne.symm hne.2),
        lt_of_le_of_ne (by nlinarith [h1]) hne.1⟩) with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

/-! ### The Duistermaat–Heckman measure -/

/-- **The Duistermaat–Heckman measure of the height on the two-sphere.** The height `x ↦ x₃` is
the moment map of the rotations of `S²` about the vertical axis for the area form `σ`, and it
pushes the Liouville measure of `σ` forward to `2π` times Lebesgue measure on `[-1, 1]`. -/
theorem duistermaatHeckmanMeasure_sphereAreaForm :
    sphereAreaForm.duistermaatHeckmanMeasure 1 (fun x : S² ↦ (x : ℝ³) 2) =
      ENNReal.ofReal (2 * π) • volume.restrict (Icc (-1) 1) := by
  have hΦ := measurableEmbedding_sphereCylinder (-π)
  have hL : sphereAreaForm.liouvilleMeasure 1 =
      ((volume : Measure ℝ²).comap Subtype.val).map (sphereCylinder (-π)) := by
    rw [map_comap_volume_sphereCylinder, Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 liouvilleMeasure_compl_range_sphereCylinder
  have hh : Measurable fun x : S² ↦ (x : ℝ³) 2 :=
    ((continuous_apply 2).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)).measurable
  have hcomp : (fun x : S² ↦ (x : ℝ³) 2) ∘ sphereCylinder (-π) =
      (fun p : ℝ² ↦ p 1) ∘ Subtype.val := by
    funext p
    simp [coe_sphereCylinder, sphereCylinderCoord]
  have hv : MeasurableEmbedding (Subtype.val : strip (-π) → ℝ²) :=
    MeasurableEmbedding.subtype_coe (strip (-π)).isOpen.measurableSet
  have h1 : Measurable fun p : ℝ² ↦ p 1 := (PiLp.continuous_apply 2 _ 1).measurable
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_def, hL, Measure.map_map hh hΦ.measurable, hcomp,
    ← Measure.map_map h1 hv.measurable, hv.map_comap, Subtype.range_coe,
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
  ext s hs
  rw [Measure.map_apply h1 hs, Measure.restrict_apply (h1 hs), smul_apply,
    Measure.restrict_apply hs, smul_eq_mul]
  have hset : (fun p : ℝ² ↦ p 1) ⁻¹' s ∩ (strip (-π) : Set ℝ²) =
      {p : ℝ² | p 0 ∈ Ioo (-π) (-π + 2 * π) ∧ p 1 ∈ s ∩ Ioo (-1) 1} := by
    ext p
    simp only [mem_inter_iff, mem_preimage, SetLike.mem_coe, mem_strip, mem_ofPred_eq]
    tauto
  rw [hset, volume_setOf_apply_mem_and _ _ measurableSet_Ioo (hs.inter measurableSet_Ioo),
    Real.volume_Ioo]
  ring_nf

/-- **Archimedes' theorem.** The zone of the unit sphere between the heights `a` and `b`, with
`-1 ≤ a` and `b ≤ 1`, has area `2π (b - a)`. For `a = -1` and `b = 1` this is the area `4π` of the
sphere. -/
theorem liouvilleMeasure_sphereAreaForm_setOf_mem_Icc {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) :
    sphereAreaForm.liouvilleMeasure 1 {x : S² | (x : ℝ³) 2 ∈ Icc a b} =
      ENNReal.ofReal (2 * π * (b - a)) := by
  have hh : Measurable fun x : S² ↦ (x : ℝ³) 2 :=
    ((continuous_apply 2).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)).measurable
  have h := congrArg (· (Icc a b)) duistermaatHeckmanMeasure_sphereAreaForm
  simp only at h
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_def, Measure.map_apply hh measurableSet_Icc] at h
  have hset : {x : S² | (x : ℝ³) 2 ∈ Icc a b} = (fun x : S² ↦ (x : ℝ³) 2) ⁻¹' Icc a b := by
    ext x
    simp
  rw [hset, h,
    smul_apply, Measure.restrict_apply measurableSet_Icc,
    inter_eq_left.2 (Icc_subset_Icc ha hb), Real.volume_Icc, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity)]

end TauCeti
