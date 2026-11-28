/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Cube
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Oriented top-form integration on unit cubes and affine cube images

Pulling an ambient `k`-form `ω` on `E` back along `Subtype.val` to an injective affine cube image
`(fun u ↦ q₀ + M u) '' Icc 0 1` produces a `C^r` form whenever `ω` is `C^r` on that compact image
(in particular, a `C^0` form whenever `ω` is continuous on the image, even if `ω` has singularities
elsewhere in `E`). In top degree `ι = Fin k`, `integralTopForm` against
`ContinuousLinearMap.unitCubeImageOrientation` with sign `s : ℤˣ` equals `(s : ℝ)` times the
Lebesgue integral over `Icc (0 : Fin k → ℝ) 1` of `ω (q₀ + M u)` evaluated on the column vectors
`r ↦ M (Pi.single r 1)` unconditionally for any rough form `ω` (with both sides `0` when
non-integrable).

## Main declarations

* `TauCeti.integrableTopForm_unitCube_iff`, `TauCeti.integralTopForm_unitCube`: coordinate
  integrability and Lebesgue integral formula on the closed unit cube.
* `ContinuousLinearMap.isSmoothForm_mpullback_unitCubeImage_of_contDiffOn`,
  `ContinuousLinearMap.isSmoothForm_mpullback_unitCubeImage_of_continuousOn`: regularity of forms
  pulled back to an injective affine cube image.
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

private theorem eqOn_signedInChartAt_unitCube {k : ℕ}
    (φ : RoughForm (modelWithCornersUnitCube (Fin k)) (Icc (0 : Fin k → ℝ) 1) ℝ k)
    (α : Icc (0 : Fin k → ℝ) 1) :
    EqOn (fun u ↦ φ.inChartAt α u (Pi.basisFun ℝ (Fin k)))
      (φ.signedInChartAt (Pi.basisFun ℝ (Fin k)) α (fun _ ↦ 1))
      (Icc (0 : Fin k → ℝ) 1) := fun u hu ↦ by
  rw [RoughForm.signedInChartAt_apply, dite_eq_left (by rwa [extChartAt_unitCube_target α])]
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
  rw [φ.integrableTopForm_iff_of_tsupport_subset_chart B α (isClosed_tsupport _).isCompact
      (by simp), Module.Basis.addHaar_basisFun (Fin k),
    ← integrableOn_iff_integrable_of_support_subset
      ((φ.support_signedInChartAt_subset_target B α (fun _ ↦ 1)).trans_eq
        (extChartAt_unitCube_target α))]
  exact integrableOn_congr_fun (eqOn_signedInChartAt_unitCube φ α).symm isClosed_Icc.measurableSet

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
  · rw [unitCubeOrientation_eq_mk,
      integralTopForm_eq_chartIntegral l φ hi α
        (by rw [extChartAt_unitCube_source]; exact subset_univ _),
      l.chartIntegral_eq_const_mul_unsigned φ B α 1 (fun x _ ↦ unitCubeOrientationLift_signAt α x),
      unitCubeOrientationLift_modelOrientation, _root_.Orientation.signBasis_orientation,
      Module.Basis.addHaar_basisFun (Fin k)]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0 : Fin k → ℝ) 1) fun u hu ↦ by
      rw [RoughForm.signedInChartAt_apply, dite_eq_right (by rwa [extChartAt_unitCube_target α])]]
    exact setIntegral_congr_fun isClosed_Icc.measurableSet
      fun u hu ↦ (eqOn_signedInChartAt_unitCube φ α hu).symm
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
  have hsymm {v : ι → ℝ} (hv : v ∈ Icc (0 : ι → ℝ) 1) :
      ((extChartAt (modelWithCornersUnitCube ι) α).symm v : E) = q₀ + M v :=
    congrArg Subtype.val (M.extChartAt_unitCubeImage_symm_of_mem hM q₀ α hv)
  have hd := (((M.hasFDerivAt (x := u)).const_add q₀).hasFDerivWithinAt
    (s := range (modelWithCornersUnitCube ι))).congr
    (f₁ := Subtype.val ∘ (extChartAt (modelWithCornersUnitCube ι) α).symm)
    (fun v hv ↦ hsymm (range_modelWithCornersUnitCube (ι := ι) ▸ hv)) (hsymm hu)
  rw [hd.fderivWithin ((modelWithCornersUnitCube ι).uniqueDiffOn u
    (by rwa [range_modelWithCornersUnitCube])), hsymm hu]

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
  have heq : ∀ u ∈ Icc (0 : ι → ℝ) 1,
      (mpullback (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
        (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω).inChartAt x u =
        C (ω (q₀ + M u)) := fun u hu ↦ by
    rw [M.inChartAt_mpullback_unitCubeImage hM q₀ ω x hu]; ext v
    exact congrArg (ω (q₀ + M u)) <|
      funext fun i ↦ NormedSpace.fromTangentSpace_symm_apply (q₀ + M u) (M (v i))
  exact (hcomp _ hx).congr heq (heq _ hx)

/-- An ambient `k`-form that is continuous on `(fun u ↦ q₀ + M u) '' Icc 0 1` pulls back along
`Subtype.val` to a `C^0` form on that compact affine cube. -/
theorem isSmoothForm_mpullback_unitCubeImage_of_continuousOn (hM : Injective M) (q₀ : E)
    {ω : RoughForm 𝓘(ℝ, E) E F k} (hω : ContinuousOn (X := E) (Y := E [⋀^Fin k]→L[ℝ] F) ω
      ((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
    IsSmoothForm (modelWithCornersUnitCube ι) 0 (mpullback (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
      (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω) :=
  M.isSmoothForm_mpullback_unitCubeImage_of_contDiffOn hM q₀ (contDiffOn_zero.mpr hω)

/-- A globally `C^r` ambient `k`-form pulls back along `Subtype.val` to a `C^r` form on an
injective affine cube image. -/
theorem isSmoothForm_mpullback_unitCubeImage (hM : Injective M) (q₀ : E)
    {r : WithTop ℕ∞} {ω : RoughForm 𝓘(ℝ, E) E F k} (hω : IsSmoothForm 𝓘(ℝ, E) r ω) :
    letI := M.unitCubeImageChartedSpace hM q₀
    letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
    IsSmoothForm (modelWithCornersUnitCube ι) r (mpullback (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
      (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) ω) :=
  M.isSmoothForm_mpullback_unitCubeImage_of_contDiffOn hM q₀
    (isSmoothForm_modelSpace_iff.mp hω).contDiffOn

end PullbackRegularity

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
  rw [RoughForm.signedInChartAt_apply,
    dite_eq_left (by rwa [M.extChartAt_unitCubeImage_target hM q₀ α]),
    M.inChartAt_mpullback_unitCubeImage hM q₀ ω α hu]
  simp only [Units.val_one, Int.cast_one, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    one_mul]
  congr 1; ext r; simp [Pi.basisFun_apply]

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
  rw [φ.integrableTopForm_iff_of_tsupport_subset_chart B α (isClosed_tsupport _).isCompact
      (by rw [M.chartAt_unitCubeImage_source hM q₀ α]; exact subset_univ _),
    Module.Basis.addHaar_basisFun (Fin k),
    ← integrableOn_iff_integrable_of_support_subset
      ((φ.support_signedInChartAt_subset_target B α (fun _ ↦ 1)).trans_eq
        (M.extChartAt_unitCubeImage_target hM q₀ α))]
  exact integrableOn_congr_fun (M.eqOn_signedInChartAt_mpullback_unitCubeImage hM q₀ ω α).symm
    isClosed_Icc.measurableSet

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
    rw [M.unitCubeImageOrientation_eq_mk hM q₀ s,
      integralTopForm_eq_chartIntegral l φ hi α
        (by rw [M.extChartAt_unitCubeImage_source hM q₀ α]; exact subset_univ _),
      l.chartIntegral_eq_const_mul_unsigned φ B α s
        (fun x _ ↦ M.unitCubeImageOrientationLift_signAt hM q₀ s α x),
      M.unitCubeImageOrientationLift_modelOrientation hM q₀ s,
      _root_.Orientation.signBasis_orientation, Module.Basis.addHaar_basisFun (Fin k)]
    simp only [Units.val_one, Int.cast_one, one_mul]
    congr 1
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0 : Fin k → ℝ) 1) fun u hu ↦ by
      rw [RoughForm.signedInChartAt_apply,
        dite_eq_right (by rwa [M.extChartAt_unitCubeImage_target hM q₀ α])]]
    exact setIntegral_congr_fun isClosed_Icc.measurableSet
      fun u hu ↦ (M.eqOn_signedInChartAt_mpullback_unitCubeImage hM q₀ ω α hu).symm
  · have hni : ¬ IntegrableOn g (Icc (0 : Fin k → ℝ) 1) :=
      mt (M.integrableTopForm_mpullback_unitCubeImage_iff hM q₀ ω).mpr hi
    rw [integralTopForm_eq_zero_of_not_integrable _ _ hi, integral_undef hni, mul_zero]

end Integration

end ContinuousLinearMap

end
