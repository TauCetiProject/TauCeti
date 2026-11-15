/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Cube
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Oriented top-form integration on unit cubes and affine cube images

The closed unit cube `Icc (0 : ι → ℝ) 1` carries a canonical orientation
`TauCeti.unitCubeOrientation` determined by `Pi.basisFun ℝ ι`. More generally, for an injective
continuous linear map `M : (ι → ℝ) →L[ℝ] E`, a base point `q₀ : E`, and a sign `s : ℤˣ`, the
compact affine cube `(fun u ↦ q₀ + M u) '' Icc 0 1` carries the signed parameter orientation
`ContinuousLinearMap.unitCubeImageOrientation`.

Pulling an ambient `k`-form `ω` on `E` back along `Subtype.val` to `(fun u ↦ q₀ + M u) '' Icc 0 1`
produces a `C^r` form whenever `ω` is `C^r` on that compact image (in particular, a `C^0` form
whenever `ω` is continuous on the image, even if `ω` has singularities elsewhere in `E`). In top
degree `ι = Fin k`, `integralTopForm` against the `s`-signed parameter orientation equals `(s : ℝ)`
times the Lebesgue integral over `Icc (0 : Fin k → ℝ) 1` of `ω (q₀ + M u)` evaluated on the column
vectors `r ↦ M (Pi.single r 1)` unconditionally for any rough form `ω` (with both sides equal to
`0` when non-integrable).

## Main declarations

* `TauCeti.unitCubeOrientation`: the canonical coordinate orientation on `Icc (0 : ι → ℝ) 1`.
* `TauCeti.integrableTopForm_unitCube_iff`, `TauCeti.integralTopForm_unitCube`: coordinate
  integrability and Lebesgue integral formula on the closed unit cube.
* `ContinuousLinearMap.isSmoothForm_mpullback_unitCubeImage_of_contDiffOn`,
  `ContinuousLinearMap.isSmoothForm_mpullback_unitCubeImage_of_continuousOn`: regularity of forms
  pulled back to an injective affine cube image.
* `ContinuousLinearMap.unitCubeImageOrientation`: the `s`-signed parameter orientation on an
  injective affine cube image.
* `ContinuousLinearMap.integrableTopForm_mpullback_unitCubeImage_iff`,
  `ContinuousLinearMap.integralTopForm_mpullback_unitCubeImage`: integrability characterization and
  unconditional parameter-integral formula for pulled-back top forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 16.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped Manifold Topology

namespace TauCeti

section UnitCubeOrientation

variable (ι : Type*) [Fintype ι]

/-- The canonical orientation lift on the closed unit cube `Icc (0 : ι → ℝ) 1`, with model
orientation `(Pi.basisFun ℝ ι).orientation` and chart sign `1`. -/
def unitCubeOrientationLift :
    Manifold.OrientationLift (modelWithCornersUnitCube ι) (Icc (0 : ι → ℝ) 1) ι :=
  open scoped Classical in
  Manifold.OrientationLift.ofHasGroupoid (Pi.basisFun ℝ ι).orientation (by simp)

/-- The canonical coordinate orientation of the closed unit cube `Icc (0 : ι → ℝ) 1`. -/
def unitCubeOrientation :
    Manifold.Orientation (modelWithCornersUnitCube ι) (Icc (0 : ι → ℝ) 1) ι :=
  Manifold.Orientation.mk (unitCubeOrientationLift ι)

variable {ι}

@[simp]
theorem unitCubeOrientationLift_modelOrientation [DecidableEq ι] :
    (unitCubeOrientationLift ι).modelOrientation = (Pi.basisFun ℝ ι).orientation := by
  simp only [unitCubeOrientationLift, Manifold.OrientationLift.ofHasGroupoid_modelOrientation]
  congr!

@[simp]
theorem unitCubeOrientationLift_signAt (α x : Icc (0 : ι → ℝ) 1) :
    (unitCubeOrientationLift ι).signAt α x = 1 := by
  have hx : x ∈ (chartAt (Icc (0 : ι → ℝ) 1) α).source := by simp
  rw [Manifold.OrientationLift.signAt_of_mem _ hx, unitCubeOrientationLift,
    Manifold.OrientationLift.ofHasGroupoid_sign]

/-- At every point of the closed unit cube, including faces, edges, and corners, the canonical
tangent orientation read in the model space is `(Pi.basisFun ℝ ι).orientation`. -/
theorem map_orientationAt_unitCubeOrientation [DecidableEq ι] (x : Icc (0 : ι → ℝ) 1) :
    _root_.Orientation.map ι (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toLinearEquiv
      ((unitCubeOrientation ι).orientationAt x) = (Pi.basisFun ℝ ι).orientation := by
  rw [unitCubeOrientation, Manifold.Orientation.orientationAt_mk]
  change _root_.Orientation.map ι (LinearEquiv.refl ℝ (ι → ℝ))
    ((unitCubeOrientationLift ι).orientationAt x) = _
  rw [_root_.Orientation.map_refl, Manifold.OrientationLift.orientationAt_eq,
    Manifold.OrientationLift.chartOrientation_eq_ite, unitCubeOrientationLift_modelOrientation]
  have hs : (unitCubeOrientationLift ι).sign x ⟨x, mem_chart_source _ x⟩ = 1 := by
    rw [unitCubeOrientationLift,
      Manifold.OrientationLift.ofHasGroupoid_sign (I := modelWithCornersUnitCube ι)]
  rw [hs]
  rfl

end UnitCubeOrientation

private theorem eqOn_signedInChartAt_unitCube {k : ℕ}
    (φ : RoughForm (modelWithCornersUnitCube (Fin k)) (Icc (0 : Fin k → ℝ) 1) ℝ k)
    (α : Icc (0 : Fin k → ℝ) 1) :
    EqOn (fun u ↦ φ.inChartAt α u (Pi.basisFun ℝ (Fin k)))
      (φ.signedInChartAt (Pi.basisFun ℝ (Fin k)) α (fun _ ↦ 1))
      (Icc (0 : Fin k → ℝ) 1) := fun u hu ↦ by
  have hut : u ∈ (extChartAt (modelWithCornersUnitCube (Fin k)) α).target := by
    rwa [extChartAt_unitCube_target α]
  rw [RoughForm.signedInChartAt_apply, dite_eq_left hut]
  simp

/-- A rough top form on `Icc (0 : Fin k → ℝ) 1` is `IntegrableTopForm` if and only if its global
chart coefficient on `Pi.basisFun ℝ (Fin k)` is Lebesgue integrable on `Icc 0 1`. -/
theorem integrableTopForm_unitCube_iff {k : ℕ}
    (φ : RoughForm (modelWithCornersUnitCube (Fin k)) (Icc (0 : Fin k → ℝ) 1) ℝ k)
    (α : Icc (0 : Fin k → ℝ) 1) :
    IntegrableTopForm φ ↔
      IntegrableOn (fun u ↦ φ.inChartAt α u (Pi.basisFun ℝ (Fin k)))
        (Icc (0 : Fin k → ℝ) 1) := by
  let B := Pi.basisFun ℝ (Fin k)
  have hhaar : B.addHaar = (volume : Measure (Fin k → ℝ)) := Module.Basis.addHaar_basisFun (Fin k)
  have hm : MeasurableSet (Icc (0 : Fin k → ℝ) 1) := isClosed_Icc.measurableSet
  have heq := eqOn_signedInChartAt_unitCube φ α
  constructor
  · intro hi
    have hcoef : Integrable (φ.signedInChartAt B α (fun _ ↦ 1)) volume :=
      hhaar ▸ ((integrableTopForm_iff φ).mp hi).2.2 B α
    exact hcoef.integrableOn.congr_fun (fun u hu ↦ (heq hu).symm) hm
  · intro hg
    have himg : (extChartAt (modelWithCornersUnitCube (Fin k)) α) '' univ =
        Icc (0 : Fin k → ℝ) 1 := by
      rw [← extChartAt_unitCube_source α, (extChartAt _ α).image_source_eq_target,
        extChartAt_unitCube_target α]
    refine φ.integrableTopForm_of_open_cover (isClosed_tsupport _).isCompact B
      (fun _ : Unit ↦ α) (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ by simp)
      (fun x _ ↦ mem_iUnion.mpr ⟨(), mem_univ x⟩) fun _ ↦ ?_
    rw [himg, hhaar]
    exact hg.congr_fun heq hm

/-- On the closed unit cube `Icc (0 : Fin k → ℝ) 1`, `integralTopForm` against the canonical
coordinate orientation equals the Lebesgue integral over `Icc 0 1` of its chart coefficient on the
standard basis (for non-integrable forms both sides are `0`). -/
theorem integralTopForm_unitCube {k : ℕ}
    (φ : RoughForm (modelWithCornersUnitCube (Fin k)) (Icc (0 : Fin k → ℝ) 1) ℝ k)
    (α : Icc (0 : Fin k → ℝ) 1) :
    integralTopForm (unitCubeOrientation (Fin k)) φ =
      ∫ u in Icc (0 : Fin k → ℝ) 1, φ.inChartAt α u (Pi.basisFun ℝ (Fin k)) := by
  let B := Pi.basisFun ℝ (Fin k)
  let l := unitCubeOrientationLift (Fin k)
  by_cases hi : IntegrableTopForm φ
  · have hhaar : B.addHaar = (volume : Measure (Fin k → ℝ)) :=
      Module.Basis.addHaar_basisFun (Fin k)
    have heq := eqOn_signedInChartAt_unitCube φ α
    rw [unitCubeOrientation,
      integralTopForm_eq_chartIntegral l φ hi α
        (by rw [extChartAt_unitCube_source]; exact subset_univ _),
      l.chartIntegral_eq_const_mul_unsigned φ B α 1
        (fun x _ ↦ unitCubeOrientationLift_signAt α x),
      unitCubeOrientationLift_modelOrientation, _root_.Orientation.signBasis_orientation, hhaar]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0 : Fin k → ℝ) 1) fun u hu ↦ by
      have hut : u ∉ (extChartAt (modelWithCornersUnitCube (Fin k)) α).target := by
        rwa [extChartAt_unitCube_target α]
      rw [RoughForm.signedInChartAt_apply, dite_eq_right hut]]
    exact setIntegral_congr_fun isClosed_Icc.measurableSet fun u hu ↦ (heq hu).symm
  · have hni : ¬ IntegrableOn (fun u ↦ φ.inChartAt α u B) (Icc (0 : Fin k → ℝ) 1) :=
      mt (integrableTopForm_unitCube_iff φ α).mpr hi
    rw [integralTopForm_eq_zero_of_not_integrable _ _ hi, integral_undef hni]

end TauCeti

namespace ContinuousLinearMap

open TauCeti

section PullbackRegularity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] (M : (ι → ℝ) →L[ℝ] E) {k : ℕ}

/-- In the global affine chart on `(fun u ↦ q₀ + M u) '' Icc 0 1`, the pullback of an ambient
`k`-form `ω` along `Subtype.val` is the linear pullback of `ω (q₀ + M u)` by `M` at every
`u ∈ Icc 0 1`, including boundary and corner points. -/
theorem inChartAt_mpullback_unitCubeImage (hM : Injective M) (q₀ : E)
    (ω : RoughForm 𝓘(ℝ, E) E F k)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) {u : ι → ℝ} (hu : u ∈ Icc (0 : ι → ℝ) 1) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (mpullback (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
      (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω).inChartAt α u =
      (ω (q₀ + M u)).compContinuousLinearMap
        ((NormedSpace.fromTangentSpace (q₀ + M u)).symm.toContinuousLinearMap.comp M) := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  have htarget : u ∈ (extChartAt (modelWithCornersUnitCube ι) α).target := by
    rwa [M.extChartAt_unitCubeImage_target hM q₀ α]
  have hf : MDifferentiableAt (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
      (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E)
      ((extChartAt (modelWithCornersUnitCube ι) α).symm u) :=
    (M.contMDiff_subtypeVal_unitCubeImage hM q₀ (n := 1)).mdifferentiable one_ne_zero _
  rw [RoughForm.inChartAt_mpullback_modelSpace ω Subtype.val α htarget hf]
  have hsymm : ((extChartAt (modelWithCornersUnitCube ι) α).symm u : E) = q₀ + M u := by
    rw [M.extChartAt_unitCubeImage_symm_of_mem hM q₀ α hu]
  have hd : HasFDerivWithinAt
      (Subtype.val ∘ (extChartAt (modelWithCornersUnitCube ι) α).symm) M
      (range (modelWithCornersUnitCube ι)) u := by
    have haff : HasFDerivWithinAt (fun v : ι → ℝ ↦ q₀ + M v) M
        (range (modelWithCornersUnitCube ι)) u := by
      have hadd := ((hasFDerivAt_const q₀ u).add (M.hasFDerivAt (x := u))).hasFDerivWithinAt
        (s := range (modelWithCornersUnitCube ι))
      rwa [zero_add] at hadd
    exact haff.congr
      (fun v hv ↦ by
        simp only [Function.comp_apply]
        rw [M.extChartAt_unitCubeImage_symm_of_mem hM q₀ α
          (range_modelWithCornersUnitCube (ι := ι) ▸ hv)])
      (by simp only [Function.comp_apply, hsymm])
  have hfderiv : fderivWithin ℝ
      (Subtype.val ∘ (extChartAt (modelWithCornersUnitCube ι) α).symm)
      (range (modelWithCornersUnitCube ι)) u = M :=
    hd.fderivWithin ((modelWithCornersUnitCube ι).uniqueDiffOn u
      (by rwa [range_modelWithCornersUnitCube]))
  rw [hfderiv, hsymm]

/-- An ambient `k`-form that is `C^r` on `(fun u ↦ q₀ + M u) '' Icc 0 1` pulls back along
`Subtype.val` to a `C^r` form on that compact affine cube. -/
theorem isSmoothForm_mpullback_unitCubeImage_of_contDiffOn (hM : Injective M) (q₀ : E)
    {r : WithTop ℕ∞} {ω : RoughForm 𝓘(ℝ, E) E F k}
    (hω : ContDiffOn ℝ (E := E) (F := E [⋀^Fin k]→L[ℝ] F) r ω
      ((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
    IsSmoothForm (modelWithCornersUnitCube ι) r
      (mpullback (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
        (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω) := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
  intro x
  let C := ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin k) (F := F) M
  have hcomp : ContDiffOn ℝ r (fun u : ι → ℝ ↦ C (ω (q₀ + M u))) (Icc (0 : ι → ℝ) 1) :=
    C.contDiff.comp_contDiffOn
      (hω.comp (contDiff_const.add M.contDiff).contDiffOn (mapsTo_image _ _))
  have hx : extChartAt (modelWithCornersUnitCube ι) x x ∈ Icc (0 : ι → ℝ) 1 := by
    have hxt := mem_extChartAt_target (I := modelWithCornersUnitCube ι) x
    rwa [M.extChartAt_unitCubeImage_target hM q₀ x] at hxt
  rw [range_modelWithCornersUnitCube]
  refine (hcomp _ hx).congr (fun u hu ↦ ?_) ?_
  · rw [M.inChartAt_mpullback_unitCubeImage hM q₀ ω x hu]
    ext v
    rfl
  · rw [M.inChartAt_mpullback_unitCubeImage hM q₀ ω x hx]
    ext v
    rfl

/-- An ambient `k`-form that is continuous on `(fun u ↦ q₀ + M u) '' Icc 0 1` pulls back along
`Subtype.val` to a `C^0` form on that compact affine cube. -/
theorem isSmoothForm_mpullback_unitCubeImage_of_continuousOn (hM : Injective M) (q₀ : E)
    {ω : RoughForm 𝓘(ℝ, E) E F k}
    (hω : ContinuousOn (X := E) (Y := E [⋀^Fin k]→L[ℝ] F) ω
      ((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
    IsSmoothForm (modelWithCornersUnitCube ι) 0
      (mpullback (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
        (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω) :=
  M.isSmoothForm_mpullback_unitCubeImage_of_contDiffOn hM q₀ (contDiffOn_zero.mpr hω)

/-- A globally `C^r` ambient `k`-form pulls back along `Subtype.val` to a `C^r` form on an
injective affine cube image. -/
theorem isSmoothForm_mpullback_unitCubeImage (hM : Injective M) (q₀ : E)
    {r : WithTop ℕ∞} {ω : RoughForm 𝓘(ℝ, E) E F k} (hω : IsSmoothForm 𝓘(ℝ, E) r ω) :
    letI := M.unitCubeImageChartedSpace hM q₀
    letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
    IsSmoothForm (modelWithCornersUnitCube ι) r
      (mpullback (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
        (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω) :=
  M.isSmoothForm_mpullback_unitCubeImage_of_contDiffOn hM q₀
    (isSmoothForm_modelSpace_iff.mp hω).contDiffOn

end PullbackRegularity

section Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] (M : (ι → ℝ) →L[ℝ] E)

/-- The `s`-signed parameter orientation lift on `(fun u ↦ q₀ + M u) '' Icc 0 1`, with model
orientation `(Pi.basisFun ℝ ι).orientation` and constant chart sign `s : ℤˣ`. -/
def unitCubeImageOrientationLift (hM : Injective M) (q₀ : E) (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    Manifold.OrientationLift (modelWithCornersUnitCube ι)
      ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) ι :=
  letI := M.unitCubeImageChartedSpace hM q₀
  letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  letI := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  open scoped Classical in
  let l₀ := Manifold.OrientationLift.ofHasGroupoid
    (I := modelWithCornersUnitCube ι)
    (M := ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1))
    (Pi.basisFun ℝ ι).orientation (by simp)
  if s = 1 then l₀ else (-l₀).flip

/-- The `s`-signed parameter orientation on `(fun u ↦ q₀ + M u) '' Icc 0 1`. -/
def unitCubeImageOrientation (hM : Injective M) (q₀ : E) (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    Manifold.Orientation (modelWithCornersUnitCube ι)
      ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) ι :=
  letI := M.unitCubeImageChartedSpace hM q₀
  Manifold.Orientation.mk (M.unitCubeImageOrientationLift hM q₀ s)

theorem unitCubeImageOrientationLift_modelOrientation [DecidableEq ι] (hM : Injective M) (q₀ : E)
    (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (M.unitCubeImageOrientationLift hM q₀ s).modelOrientation = (Pi.basisFun ℝ ι).orientation := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  dsimp only [unitCubeImageOrientationLift]
  split_ifs
  · simp only [Manifold.OrientationLift.ofHasGroupoid_modelOrientation]
    congr!
  · simp only [Manifold.OrientationLift.flip_modelOrientation,
      Manifold.OrientationLift.neg_modelOrientation,
      Manifold.OrientationLift.ofHasGroupoid_modelOrientation]
    refine (_root_.neg_neg (G := _root_.Orientation ℝ (ι → ℝ) ι) _).trans ?_
    congr!

theorem unitCubeImageOrientationLift_sign (hM : Injective M) (q₀ : E) (s : ℤˣ)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1))
    (x : (letI := M.unitCubeImageChartedSpace hM q₀
      (chartAt (Icc (0 : ι → ℝ) 1) α).source)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (M.unitCubeImageOrientationLift hM q₀ s).sign α x = s := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  dsimp only [unitCubeImageOrientationLift]
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

theorem unitCubeImageOrientationLift_signAt (hM : Injective M) (q₀ : E) (s : ℤˣ)
    (α x : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (M.unitCubeImageOrientationLift hM q₀ s).signAt α x = s := by
  let := M.unitCubeImageChartedSpace hM q₀
  have hx : x ∈ (chartAt (Icc (0 : ι → ℝ) 1) α).source := by
    rw [M.chartAt_unitCubeImage_source hM q₀ α]
    exact mem_univ x
  rw [Manifold.OrientationLift.signAt_of_mem _ hx]
  exact M.unitCubeImageOrientationLift_sign hM q₀ s α ⟨x, hx⟩

theorem unitCubeImageOrientation_neg (hM : Injective M) (q₀ : E) (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    M.unitCubeImageOrientation hM q₀ (-s) = -(M.unitCubeImageOrientation hM q₀ s) := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  have h1 : M.unitCubeImageOrientation hM q₀ (-1) = -(M.unitCubeImageOrientation hM q₀ 1) := by
    dsimp only [unitCubeImageOrientation, unitCubeImageOrientationLift]
    have hn : (-1 : ℤˣ) ≠ 1 := by decide
    simp [hn, Manifold.Orientation.mk_eq_mk_iff (I := modelWithCornersUnitCube ι)]
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact h1
  · rw [_root_.neg_neg, h1, _root_.neg_neg]

/-- At every point of `(fun u ↦ q₀ + M u) '' Icc 0 1`, including faces, edges, and corners, the
tangent orientation of `M.unitCubeImageOrientation hM q₀ s` read in the model space `ι → ℝ` is
`(Pi.basisFun ℝ ι).orientation` when `s = 1` and its negation when `s = -1`. -/
theorem map_orientationAt_unitCubeImageOrientation [DecidableEq ι] (hM : Injective M) (q₀ : E)
    (s : ℤˣ) (x : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
    _root_.Orientation.map ι (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toLinearEquiv
      ((M.unitCubeImageOrientation hM q₀ s).orientationAt x) =
      if s = 1 then (Pi.basisFun ℝ ι).orientation else -(Pi.basisFun ℝ ι).orientation := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  rw [unitCubeImageOrientation, Manifold.Orientation.orientationAt_mk]
  change _root_.Orientation.map ι (LinearEquiv.refl ℝ (ι → ℝ))
    ((M.unitCubeImageOrientationLift hM q₀ s).orientationAt x) = _
  rw [_root_.Orientation.map_refl, Manifold.OrientationLift.orientationAt_eq,
    Manifold.OrientationLift.chartOrientation_eq_ite,
    M.unitCubeImageOrientationLift_sign hM q₀ s x ⟨x, mem_chart_source _ x⟩,
    M.unitCubeImageOrientationLift_modelOrientation hM q₀ s]
  rfl

end Orientation

section Integration

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : ℕ} (M : (Fin k → ℝ) →L[ℝ] E)

private theorem eqOn_signedInChartAt_mpullback_unitCubeImage (hM : Injective M) (q₀ : E)
    (ω : RoughForm 𝓘(ℝ, E) E ℝ k)
    (α : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    EqOn (fun u : Fin k → ℝ ↦ ω (q₀ + M u)
        (fun r ↦ (NormedSpace.fromTangentSpace (q₀ + M u)).symm (M (Pi.single r 1))))
      ((mpullback (modelWithCornersUnitCube (Fin k)) 𝓘(ℝ, E)
        (Subtype.val : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω).signedInChartAt
          (Pi.basisFun ℝ (Fin k)) α (fun _ ↦ 1))
      (Icc (0 : Fin k → ℝ) 1) := by
  let := M.unitCubeImageChartedSpace hM q₀
  intro u hu
  have hut : u ∈ (extChartAt (modelWithCornersUnitCube (Fin k)) α).target := by
    rwa [M.extChartAt_unitCubeImage_target hM q₀ α]
  rw [RoughForm.signedInChartAt_apply, dite_eq_left hut]
  simp only [Units.val_one, Int.cast_one, one_mul]
  rw [M.inChartAt_mpullback_unitCubeImage hM q₀ ω α hu,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext r
  simp [Pi.basisFun_apply]

/-- The pullback of an ambient rough `k`-form `ω` to `(fun u ↦ q₀ + M u) '' Icc 0 1` is
`IntegrableTopForm` if and only if the column evaluation `u ↦ ω (q₀ + M u) (r ↦ M (eᵣ))` is
Lebesgue integrable on `Icc (0 : Fin k → ℝ) 1`. -/
theorem integrableTopForm_mpullback_unitCubeImage_iff (hM : Injective M) (q₀ : E)
    (ω : RoughForm 𝓘(ℝ, E) E ℝ k) :
    letI := M.unitCubeImageChartedSpace hM q₀
    IntegrableTopForm (mpullback (modelWithCornersUnitCube (Fin k)) 𝓘(ℝ, E)
      (Subtype.val : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω) ↔
      IntegrableOn
        (fun u : Fin k → ℝ ↦ ω (q₀ + M u)
          (fun r ↦ (NormedSpace.fromTangentSpace (q₀ + M u)).symm (M (Pi.single r 1))))
        (Icc (0 : Fin k → ℝ) 1) := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let : CompactSpace ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.image (continuous_const.add M.continuous))
  let α : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) :=
    ⟨q₀ + M 0, mem_image_of_mem _ ⟨le_rfl, zero_le_one⟩⟩
  let φ := mpullback (modelWithCornersUnitCube (Fin k)) 𝓘(ℝ, E)
    (Subtype.val : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω
  let B := Pi.basisFun ℝ (Fin k)
  have hhaar : B.addHaar = (volume : Measure (Fin k → ℝ)) := Module.Basis.addHaar_basisFun (Fin k)
  have hm : MeasurableSet (Icc (0 : Fin k → ℝ) 1) := isClosed_Icc.measurableSet
  have heq := M.eqOn_signedInChartAt_mpullback_unitCubeImage hM q₀ ω α
  constructor
  · intro hi
    have hcoef : Integrable (φ.signedInChartAt B α (fun _ ↦ 1)) volume :=
      hhaar ▸ ((integrableTopForm_iff φ).mp hi).2.2 B α
    exact hcoef.integrableOn.congr_fun (fun u hu ↦ (heq hu).symm) hm
  · intro hg
    have himg : (extChartAt (modelWithCornersUnitCube (Fin k)) α) '' univ =
        Icc (0 : Fin k → ℝ) 1 := by
      rw [← M.extChartAt_unitCubeImage_source hM q₀ α, (extChartAt _ α).image_source_eq_target,
        M.extChartAt_unitCubeImage_target hM q₀ α]
    refine φ.integrableTopForm_of_open_cover (isClosed_tsupport _).isCompact B
      (fun _ : Unit ↦ α) (fun _ ↦ univ) (fun _ ↦ isOpen_univ)
      (fun _ ↦ by rw [M.chartAt_unitCubeImage_source hM q₀ α])
      (fun x _ ↦ mem_iUnion.mpr ⟨(), mem_univ x⟩) fun _ ↦ ?_
    rw [himg, hhaar]
    exact hg.congr_fun heq hm

/-- For any ambient rough `k`-form `ω`, `integralTopForm` of its pullback to
`(fun u ↦ q₀ + M u) '' Icc 0 1` against the `s`-signed parameter orientation equals `(s : ℝ)` times
the Lebesgue integral over `Icc (0 : Fin k → ℝ) 1` of `ω (q₀ + M u)` evaluated on the columns of
`M` (for non-integrable forms both sides are `0`). -/
theorem integralTopForm_mpullback_unitCubeImage (hM : Injective M) (q₀ : E) (s : ℤˣ)
    (ω : RoughForm 𝓘(ℝ, E) E ℝ k) :
    letI := M.unitCubeImageChartedSpace hM q₀
    integralTopForm (M.unitCubeImageOrientation hM q₀ s)
      (mpullback (modelWithCornersUnitCube (Fin k)) 𝓘(ℝ, E)
        (Subtype.val : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω) =
      (s : ℝ) * ∫ u in Icc (0 : Fin k → ℝ) 1,
        ω (q₀ + M u)
          (fun r ↦ (NormedSpace.fromTangentSpace (q₀ + M u)).symm (M (Pi.single r 1))) := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let φ := mpullback (modelWithCornersUnitCube (Fin k)) 𝓘(ℝ, E)
    (Subtype.val : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω
  let g := fun u : Fin k → ℝ ↦ ω (q₀ + M u)
    (fun r ↦ (NormedSpace.fromTangentSpace (q₀ + M u)).symm (M (Pi.single r 1)))
  by_cases hi : IntegrableTopForm φ
  · let α : ↥((fun u : Fin k → ℝ ↦ q₀ + M u) '' Icc 0 1) :=
      ⟨q₀ + M 0, mem_image_of_mem _ ⟨le_rfl, zero_le_one⟩⟩
    let B := Pi.basisFun ℝ (Fin k)
    let l := M.unitCubeImageOrientationLift hM q₀ s
    have hhaar : B.addHaar = (volume : Measure (Fin k → ℝ)) :=
      Module.Basis.addHaar_basisFun (Fin k)
    have heq := M.eqOn_signedInChartAt_mpullback_unitCubeImage hM q₀ ω α
    rw [unitCubeImageOrientation,
      integralTopForm_eq_chartIntegral l φ hi α
        (by rw [M.extChartAt_unitCubeImage_source hM q₀ α]; exact subset_univ _),
      l.chartIntegral_eq_const_mul_unsigned φ B α s
        (fun x _ ↦ M.unitCubeImageOrientationLift_signAt hM q₀ s α x),
      M.unitCubeImageOrientationLift_modelOrientation hM q₀ s,
      _root_.Orientation.signBasis_orientation, hhaar]
    simp only [Units.val_one, Int.cast_one, one_mul]
    congr 1
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0 : Fin k → ℝ) 1) fun u hu ↦ by
      have hut : u ∉ (extChartAt (modelWithCornersUnitCube (Fin k)) α).target := by
        rwa [M.extChartAt_unitCubeImage_target hM q₀ α]
      rw [RoughForm.signedInChartAt_apply, dite_eq_right hut]]
    exact setIntegral_congr_fun isClosed_Icc.measurableSet fun u hu ↦ (heq hu).symm
  · have hni : ¬ IntegrableOn g (Icc (0 : Fin k → ℝ) 1) :=
      mt (M.integrableTopForm_mpullback_unitCubeImage_iff hM q₀ ω).mpr hi
    rw [integralTopForm_eq_zero_of_not_integrable _ _ hi, integral_undef hni, mul_zero]

end Integration

end ContinuousLinearMap

end
