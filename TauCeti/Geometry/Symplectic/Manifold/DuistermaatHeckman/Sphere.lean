/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.UnitSphere
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.MeasureTheory.Measure.Lebesgue.HalfSqRadius
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Duistermaat–Heckman measure of the height on the two-sphere

Let `S² ⊂ ℝ³` be the unit sphere with its area form `σ_x(v, w) = x ⬝ (v × w)`
(`TauCeti.sphereAreaForm`). The height `h(x) = x₃` is the Hamiltonian of the rotation about the
vertical axis: it is the component of the moment map `x ↦ ν_x` of the rotation action of `so(3)`
along the generator of that rotation (`TauCeti.isMomentMap_sphereRotationAction`). This file
computes its Duistermaat–Heckman measure, the pushforward along `h` of the Liouville measure of
`σ`:

`h_* |σ| = 2π · Lebesgue measure on [-1, 1]`

(`TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_height`). This is **Archimedes' theorem**: the
zone of the sphere between two heights `a ≤ b` in `[-1, 1]` has area `2π (b - a)`, the area of
the corresponding band of the circumscribed cylinder
(`TauCeti.liouvilleMeasure_sphereAreaForm_setOf_mem_Icc`). The total mass is the area `4π` of the
sphere (`TauCeti.liouvilleMeasure_sphereAreaForm_univ`), so for the trivial circle action, whose
moment map is constant, the Duistermaat–Heckman measure is `4π` times a Dirac mass
(`TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_const`). For the rotation the density `2π` is
constant on the interval of regular values, as the Duistermaat–Heckman theorem predicts for a
circle action on a surface: the reduced spaces are points, and `2π` is the period of the
rotation.

The computation goes through inverse stereographic projection from the south pole,
`q(x, y) = (2x, 2y, 1 - x² - y²) / (1 + x² + y²)` (`TauCeti.stereoSphere`). It pulls the
area form back to the density `4 / (1 + x² + y²)²` times Lebesgue measure, and it misses only the
south pole, which is null. So the Liouville measure of `S²` is the image of that weighted
Lebesgue measure (`TauCeti.liouvilleMeasure_sphereAreaForm`). In these coordinates both the
height and the density are functions of `s = (x² + y²) / 2`:

`h = (1 - 2s) / (1 + 2s)`,  density `= 4 / (1 + 2s)²`.

Half the squared radius pushes Lebesgue measure on the plane to `2π` times Lebesgue measure on
`[0, ∞)` (`TauCeti.map_volume_euclideanSpace_half_sq_norm`), and `s ↦ (1 - 2s) / (1 + 2s)` maps
`[0, ∞)` bijectively onto `(-1, 1]` with derivative `-4 / (1 + 2s)²`. The change of variables in
one dimension then turns the weighted measure into Lebesgue measure on `(-1, 1]`.

## Main results

* `TauCeti.liouvilleMeasure_sphereAreaForm`: the Liouville measure of `S²` in stereographic
  coordinates.
* `TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_height`: the Duistermaat–Heckman measure of
  the height is `2π` times Lebesgue measure on `[-1, 1]`.
* `TauCeti.liouvilleMeasure_sphereAreaForm_setOf_mem_Icc`: the zone between the heights `a` and
  `b` has area `2π (b - a)`.
* `TauCeti.liouvilleMeasure_sphereAreaForm_univ`: the Liouville measure of `S²` has total mass
  `4π`.
* `TauCeti.duistermaatHeckmanMeasure_sphereAreaForm_const`: the Duistermaat–Heckman measure of a
  constant moment map is `4π` times a Dirac mass.

## References

* Archimedes, *On the Sphere and Cylinder*, Book I, Propositions 33 and 42–43.
* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 30 (the Duistermaat–Heckman measure of the height on `S²`).
-/

public section

noncomputable section

open Metric Module MeasureTheory Set
open scoped Manifold ContDiff ENNReal Real

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-- The plane `ℝ²` has dimension `2 * 1`. This is the form of the dimension hypothesis under which
the Liouville measure `|σ¹ / 1!|` of a surface modelled on `ℝ²` is defined. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (finrank ℝ ℝ² = 2 * 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-! ### The Liouville measure in stereographic coordinates -/

/-- Inverse stereographic projection from the south pole is a measurable embedding. -/
theorem measurableEmbedding_stereoSphere : MeasurableEmbedding stereoSphere :=
  contMDiff_stereoSphere.continuous.measurable.measurableEmbedding
    injective_stereoSphere

/-- Inverse stereographic projection pulls the area form of `S²` back to a form on the plane whose
Liouville measure is Lebesgue measure with density `4 / (1 + x² + y²)²`. -/
private theorem liouvilleMeasure_mpullback_stereoSphere :
    SmoothTwoForm.liouvilleMeasure 1 (SmoothForm.mpullback stereoSphere
      contMDiff_stereoSphere sphereAreaForm) =
      volume.withDensity fun z : ℝ² ↦ ENNReal.ofReal (4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2) := by
  rw [SmoothTwoForm.liouvilleMeasure_def,
    RoughForm.measure_eq_withDensity_addHaar (k := 2 * 1) _
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    OrthonormalBasis.addHaar_eq_volume]
  congr 1
  funext z
  rw [SmoothTwoForm.volumeForm_apply, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  -- The basis vectors are tangent vectors of the model space, which `rw` does not identify with
  -- vectors of `ℝ²` at instance transparency.
  erw [ContinuousAlternatingMap.wedgePow_one_apply, SmoothForm.mpullback_apply]
  rw [sphereAreaForm_eq_sphereVolumeForm]
  -- `Fin.cast` along `2 * 1 = 2` is the identity, so the tangent vectors are those of the basis.
  refine (congrArg (fun t ↦ ENNReal.ofReal |t|)
    (sphereVolumeForm_mfderiv_stereoSphere z)).trans ?_
  rw [abs_of_pos (by positivity)]

/-- **The Liouville measure of `S²` in stereographic coordinates.** The Liouville measure of the
area form of `S²` is the image under inverse stereographic projection from the south pole of
Lebesgue measure on the plane with density `4 / (1 + x² + y²)²`. -/
theorem liouvilleMeasure_sphereAreaForm :
    sphereAreaForm.liouvilleMeasure 1 =
      (volume.withDensity fun z : ℝ² ↦ ENNReal.ofReal (4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2)).map
        stereoSphere := by
  -- The parametrization misses only the south pole, which is null.
  rw [← liouvilleMeasure_mpullback_stereoSphere,
    measurableEmbedding_stereoSphere.map_liouvilleMeasure
      (contMDiff_stereoSphere.mdifferentiable (by simp))
      (SmoothForm.coe_mpullback _ _ _).symm,
    range_stereoSphere, restrict_compl_singleton]

/-! ### The Duistermaat–Heckman measure of the height -/

/-- The map `s ↦ (1 - 2s) / (1 + 2s)`, the height on `S²` as a function of half the squared
stereographic radius, carries the measure `4 / (1 + 2s)² ds` on `[0, ∞)` to Lebesgue measure on
`(-1, 1]`. -/
private theorem map_withDensity_restrict_Ici :
    ((volume.restrict (Ici (0 : ℝ))).withDensity fun s ↦ ENNReal.ofReal (4 / (1 + 2 * s) ^ 2)).map
        (fun s : ℝ ↦ (1 - 2 * s) / (1 + 2 * s)) = volume.restrict (Ioc (-1) 1) := by
  set g : ℝ → ℝ := fun s ↦ (1 - 2 * s) / (1 + 2 * s)
  have hg : Measurable g := by fun_prop
  have hpos {s : ℝ} (hs : s ∈ Ici (0 : ℝ)) : 0 < 1 + 2 * s := by linarith [mem_Ici.1 hs]
  have himage : g '' Ici 0 = Ioc (-1) 1 := by
    ext y
    refine ⟨?_, fun hy ↦ ⟨(1 - y) / (2 * (1 + y)), ?_, ?_⟩⟩
    · rintro ⟨s, hs, rfl⟩
      have h := hpos hs
      constructor
      · rw [lt_div_iff₀ h]
        linarith
      · rw [div_le_iff₀ h]
        linarith [mem_Ici.1 hs]
    · have h1 : 0 < 1 + y := by linarith [hy.1]
      exact div_nonneg (by linarith [hy.2]) (by positivity)
    · have h1 : 0 < 1 + y := by linarith [hy.1]
      simp only [g]
      field_simp
      ring
  ext A hA
  rw [Measure.map_apply hg hA, withDensity_apply _ (hg hA), Measure.restrict_restrict (hg hA),
    Measure.restrict_apply hA]
  -- Change variables along `g`, which is injective on `[0, ∞)` with derivative `-4 / (1 + 2s)²`.
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul
    ((hg hA).inter (measurableSet_Ici (a := (0 : ℝ))))
    (f := g) (f' := fun s ↦ -4 / (1 + 2 * s) ^ 2) (fun s hs ↦ ?_) (fun s hs t ht hst ↦ ?_) 1
  · simp only [image_preimage_inter, himage, Pi.one_apply, mul_one] at hcv
    rw [← setLIntegral_one, hcv]
    refine setLIntegral_congr_fun ((hg hA).inter measurableSet_Ici) fun s hs ↦ ?_
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4),
      abs_of_pos (pow_pos (hpos hs.2) 2)]
  · have hd := ((hasDerivAt_id' s).const_mul 2 |>.const_sub 1).div
      ((hasDerivAt_id' s).const_mul 2 |>.const_add 1) (hpos hs.2).ne'
    refine (hd.congr_deriv ?_).hasDerivWithinAt
    ring
  · have h₁ := hpos hs.2
    have h₂ := hpos ht.2
    simp only [g] at hst
    field_simp at hst
    linarith

/-- **Archimedes' theorem: the Duistermaat–Heckman measure of the height on `S²`.** The height
`x ↦ x₃` pushes the Liouville measure of the area form of `S²` forward to `2π` times Lebesgue
measure on `[-1, 1]`. Equivalently, the zone of the sphere between two heights in `[-1, 1]` has
area `2π` times their difference (`TauCeti.liouvilleMeasure_sphereAreaForm_setOf_mem_Icc`). -/
theorem duistermaatHeckmanMeasure_sphereAreaForm_height :
    sphereAreaForm.duistermaatHeckmanMeasure 1 (fun x : S² ↦ (x : ℝ³) 2) =
      ENNReal.ofReal (2 * π) • volume.restrict (Icc (-1) 1) := by
  set q : ℝ² → ℝ := fun z ↦ ‖z‖ ^ 2 / 2
  set g : ℝ → ℝ := fun s ↦ (1 - 2 * s) / (1 + 2 * s)
  set D : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (4 / (1 + 2 * s) ^ 2)
  have hq : Measurable q := by fun_prop
  have hg : Measurable g := by fun_prop
  have hD : Measurable D := by fun_prop
  have hh : Measurable fun x : S² ↦ (x : ℝ³) 2 := by fun_prop
  have hnorm (z : ℝ²) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  -- In stereographic coordinates both the height and the area density are functions of `q`.
  have hheight : (fun x : S² ↦ (x : ℝ³) 2) ∘ stereoSphere = g ∘ q := by
    funext z
    have : 0 < 1 + z 0 ^ 2 + z 1 ^ 2 := by positivity
    simp only [Function.comp_apply, coe_stereoSphere, g, q, hnorm, Fin.isValue,
      Matrix.cons_val]
    field_simp
    ring
  have hdensity : (fun z : ℝ² ↦ ENNReal.ofReal (4 / (1 + z 0 ^ 2 + z 1 ^ 2) ^ 2)) = D ∘ q := by
    funext z
    simp only [Function.comp_apply, D, q, hnorm]
    ring_nf
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_def, liouvilleMeasure_sphereAreaForm,
    Measure.map_map hh measurableEmbedding_stereoSphere.measurable, hheight,
    ← Measure.map_map hg hq, hdensity, Measure.map_withDensity_comp hq hD,
    map_volume_euclideanSpace_half_sq_norm, withDensity_smul_measure,
    Measure.map_smul _ hg.aemeasurable, map_withDensity_restrict_Ici,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- **Archimedes' theorem on zones.** For `-1 ≤ a` and `b ≤ 1`, the zone of `S²` between the
heights `a` and `b` has area `2π (b - a)`. -/
theorem liouvilleMeasure_sphereAreaForm_setOf_mem_Icc {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) :
    sphereAreaForm.liouvilleMeasure 1 {x : S² | (x : ℝ³) 2 ∈ Icc a b} =
      ENNReal.ofReal (2 * π * (b - a)) := by
  have hh : Measurable fun x : S² ↦ (x : ℝ³) 2 := by fun_prop
  rw [← preimage_ofPred_eq (p := (· ∈ Icc a b)), ofPred_mem_eq,
    ← SmoothTwoForm.duistermaatHeckmanMeasure_apply hh measurableSet_Icc,
    duistermaatHeckmanMeasure_sphereAreaForm_height, smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, max_eq_left ha, min_eq_left hb,
    Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]

/-- **The area of `S²`.** The Liouville measure of the area form of `S²` has total mass `4π`. -/
theorem liouvilleMeasure_sphereAreaForm_univ :
    sphereAreaForm.liouvilleMeasure 1 univ = ENNReal.ofReal (4 * π) := by
  have hh : Measurable fun x : S² ↦ (x : ℝ³) 2 := by fun_prop
  rw [← SmoothTwoForm.duistermaatHeckmanMeasure_univ hh,
    duistermaatHeckmanMeasure_sphereAreaForm_height, smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

/-- **The Duistermaat–Heckman measure of the trivial action on `S²`.** A constant moment map
`x ↦ c` pushes the Liouville measure of the area form of `S²` forward to `4π` times the Dirac
mass at `c`. -/
theorem duistermaatHeckmanMeasure_sphereAreaForm_const {F : Type*} [MeasurableSpace F] (c : F) :
    sphereAreaForm.duistermaatHeckmanMeasure 1 (fun _ : S² ↦ c) =
      ENNReal.ofReal (4 * π) • Measure.dirac c := by
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_const, liouvilleMeasure_sphereAreaForm_univ]

end TauCeti
