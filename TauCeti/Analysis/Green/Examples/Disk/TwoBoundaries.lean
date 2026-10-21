/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.Disk.Basic
public import TauCeti.Analysis.Green.Comparison.Boundary.Components
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Two genuine components in the manifold boundary comparison

The disjoint union of two actual disk-boundary manifolds has two disjoint positive closed
parametrizations. Their area-form integrals add to `2π` through the finite-family comparison.
-/

public section
noncomputable section

open Set Metric MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti.Green

attribute [local instance] finrank_real_complex_fact'

local notation "D" => closedBall (0 : ℂ) 1
local notation "B" => ModelWithCorners.boundary (I := (𝓡∂ (1 + 1))) D
local notation "E₁" => EuclideanSpace ℝ (Fin 1)

local instance : IsManifold (𝓡 1) ω B := isManifold_boundary (n := 1) D (by simp)

local instance : CompactSpace B :=
  isCompact_iff_compactSpace.mp
    ((𝓡∂ (1 + 1)).isClosed_boundary (M := D) (by simp : (ω : ℕ∞ω) ≠ 0)).isCompact

private def foldBoundary : B ⊕ B → B := Sum.elim id id

private theorem foldBoundary_mem_chart_source {a : B ⊕ B} {x : B ⊕ B}
    (hx : x ∈ (chartAt E₁ a).source) :
    foldBoundary x ∈ (chartAt E₁ (foldBoundary a)).source := by
  cases a <;> cases x <;>
    simp_all [foldBoundary, ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr,
      OpenPartialHomeomorph.lift_openEmbedding_source]

private def doubleBoundaryLift (l : Manifold.OrientationLift (𝓡 1) B (Fin 1)) :
    Manifold.OrientationLift (𝓡 1) (B ⊕ B) (Fin 1) where
  modelOrientation := l.modelOrientation
  card_eq := l.card_eq
  sign a x := l.sign (foldBoundary a) ⟨foldBoundary x.val, foldBoundary_mem_chart_source x.property⟩
  locallyConstant_sign a := (l.locallyConstant_sign (foldBoundary a)).comp_continuous
    ((continuous_id.sumElim continuous_id).comp continuous_subtype_val |>.subtype_mk _)
  compatible a b x ha hb := by
    cases a <;> cases b <;> cases x
    all_goals
      simp only [ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr,
        OpenPartialHomeomorph.lift_openEmbedding_source] at ha hb
      simp only [mem_image, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
        exists_eq_right, and_false, exists_false] at ha hb
    all_goals
      convert l.compatible _ _ _ ha hb using 1
      simp [foldBoundary, extChartAt, Function.comp_def, ChartedSpace.sum_chartAt_inl,
        ChartedSpace.sum_chartAt_inr, Sum.inl_injective.extend_apply,
        Sum.inr_injective.extend_apply]

private def diskOrientationLift : Manifold.OrientationLift (𝓡∂ 2) D (Fin 2) :=
  (Manifold.Orientation.closedBall (n := 2) Complex.basisOneI.orientation).exists_lift.choose

private theorem diskOrientationLift_mk :
    Manifold.Orientation.mk diskOrientationLift =
      Manifold.Orientation.closedBall (n := 2) Complex.basisOneI.orientation :=
  (Manifold.Orientation.closedBall (n := 2) Complex.basisOneI.orientation).exists_lift.choose_spec

/-- The disjoint union of two disk boundaries, each with its actual outward-first orientation. -/
def twoDiskBoundaryOrientation : Manifold.Orientation (𝓡 1) (B ⊕ B) (Fin 1) :=
  Manifold.Orientation.mk (doubleBoundaryLift diskOrientationLift.boundary)

private def componentInclusion (i : Bool) : B → B ⊕ B :=
  if i then Sum.inr else Sum.inl

/-- The actual tangent map of either disjoint-sum inclusion, between the common model fibers. -/
private def componentTangentEquiv (i : Bool) (x : B) :
    TangentSpace (𝓡 1) x ≃L[ℝ] TangentSpace (𝓡 1) (componentInclusion i x) :=
  ContinuousLinearEquiv.refl ℝ E₁

private theorem componentTangentEquiv_eq_mfderiv (i : Bool) (x : B) :
    (componentTangentEquiv i x).toContinuousLinearMap =
      mfderiv (𝓡 1) (𝓡 1) (componentInclusion i) x := by
  cases i
  · -- The left sum inclusion has the identity derivative on its component's model fiber.
    change ContinuousLinearMap.id ℝ E₁ = mfderiv (𝓡 1) (𝓡 1) (Sum.inl : B → B ⊕ B) x
    exact mfderiv_sumInl.symm
  · -- The right sum inclusion has the same identity model derivative.
    change ContinuousLinearMap.id ℝ E₁ = mfderiv (𝓡 1) (𝓡 1) (Sum.inr : B → B ⊕ B) x
    exact mfderiv_sumInr.symm

private theorem componentTangentEquiv_apply (i : Bool) (x : B) (v : E₁) :
    componentTangentEquiv i x v = v := rfl

private theorem continuous_componentInclusion (i : Bool) : Continuous (componentInclusion i) := by
  cases i
  · exact continuous_inl
  · exact continuous_inr

private theorem doubleBoundaryLift_orientationAt (l : Manifold.OrientationLift (𝓡 1) B (Fin 1))
    (i : Bool) (x : B) :
    (doubleBoundaryLift l).orientationAt (componentInclusion i x) =
      -- Both summands use this same tangent model; only their base points differ.
      (show Orientation ℝ E₁ (Fin 1) from l.orientationAt x) := by
  rw [Manifold.OrientationLift.orientationAt_eq,
    Manifold.OrientationLift.chartOrientation_eq_ite,
    Manifold.OrientationLift.orientationAt_eq,
    Manifold.OrientationLift.chartOrientation_eq_ite]
  cases i <;> rfl

/-- At either summand, the chosen orientation is the disk's actual induced boundary
orientation. The disjoint-union charts identify the corresponding tangent model spaces. -/
theorem orientationAt_twoDiskBoundaryOrientation (x : B ⊕ B) :
    twoDiskBoundaryOrientation.orientationAt x =
      -- Both summands use this same tangent model; only their base points differ.
      (show Orientation ℝ E₁ (Fin 1) from
        (boundaryOrientation (Manifold.Orientation.closedBall (n := 2)
          Complex.basisOneI.orientation)).orientationAt (Sum.elim id id x)) := by
  -- Unfold the chosen orientation lift before applying its summand orientation identity.
  change (Manifold.Orientation.mk
    (doubleBoundaryLift diskOrientationLift.boundary)).orientationAt x = _
  rw [← diskOrientationLift_mk, boundaryOrientation_mk,
    Manifold.Orientation.orientationAt_mk, Manifold.Orientation.orientationAt_mk]
  cases x with
  | inl x => exact doubleBoundaryLift_orientationAt diskOrientationLift.boundary false x
  | inr x => exact doubleBoundaryLift_orientationAt diskOrientationLift.boundary true x

/-- The canonical integral over two actual disk-boundary components is the sum of their
counterclockwise curve integrals. Their planar maps agree, so the sum is twice either integral. -/
theorem integralTopForm_twoDiskBoundaries (P Q : ℂ → ℝ) (hP : Continuous P) (hQ : Continuous Q) :
    let f : B ⊕ B → ℂ := Sum.elim (fun x : B ↦ x.val.val) (fun x : B ↦ x.val.val)
    IntegrableTopForm (mpullback (𝓡 1) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) ∧
      CurveIntegrable (oneForm P Q)
        (unitDiskBoundaryLoop.map (continuous_subtype_val.comp continuous_subtype_val)) ∧
      integralTopForm twoDiskBoundaryOrientation
        (mpullback (𝓡 1) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) =
        2 * curveIntegral (oneForm P Q)
          (unitDiskBoundaryLoop.map (continuous_subtype_val.comp continuous_subtype_val)) := by
  classical
  let l := diskOrientationLift.boundary
  let f : B ⊕ B → ℂ := Sum.elim (fun x : B ↦ x.val.val) (fun x : B ↦ x.val.val)
  let q := fun i ↦ unitDiskBoundaryLoop.map (continuous_componentInclusion i)
  let p := fun i ↦ componentInclusion i
    (sphereDiffeomorphBoundaryClosedBall (n := 1) (Circle.exp (-Real.pi)))
  have hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) 1 f := by
    have h := (contMDiff_subtypeVal_closedBall (n := 2) (k := 1)).comp
      (isSmoothEmbedding_subtypeVal_boundary (n := 1) D
        (by simp : (1 : ℕ∞ω) ≠ 0)).contMDiff
    exact h.sumElim h
  have hqext (i : Bool) (t : ℝ) : (q i).extend t =
      componentInclusion i (unitDiskBoundaryLoop.extend t) := rfl
  have himage : (⋃ i, (q i).extend '' Ioo (0 : ℝ) 1) = (range p)ᶜ := by
    have hi (i : Bool) : (q i).extend '' Ioo (0 : ℝ) 1 =
        componentInclusion i '' {(sphereDiffeomorphBoundaryClosedBall (n := 1)
          (Circle.exp (-Real.pi)))}ᶜ := by
      -- Expose composition of the mapped path extension before transporting its image.
      change (componentInclusion i ∘ unitDiskBoundaryLoop.extend) '' Ioo (0 : ℝ) 1 = _
      rw [image_comp, unitDiskBoundaryLoop_image]
    simp only [hi]
    ext x
    cases x
    all_goals
      rename_i x
      have h : (∃ y : B, y ≠ sphereDiffeomorphBoundaryClosedBall (n := 1)
          (Circle.exp (-Real.pi)) ∧ y = x) ↔
          x ≠ sphereDiffeomorphBoundaryClosedBall (n := 1) (Circle.exp (-Real.pi)) := by
        simp only [exists_eq_right]
      simp only [Subtype.exists] at h
      simpa [componentInclusion, p] using h
  have hdisj : Pairwise (fun i j : Bool ↦ Disjoint
      ((q i).extend '' Ioo (0 : ℝ) 1) ((q j).extend '' Ioo (0 : ℝ) 1)) := by
    intro i j hij
    cases i <;> cases j <;> try contradiction
    all_goals
      rw [Set.disjoint_left]
      rintro x ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
      contradiction
  have hinj (i : Bool) : InjOn (q i).extend (Ioo (0 : ℝ) 1) := by
    intro s hs t ht he
    apply unitDiskBoundaryLoop_injOn hs ht
    cases i
    · exact Sum.inl_injective he
    · exact Sum.inr_injective he
  have he (i : Bool) (z : E₁) : ∃ e : E₁ ≃L[ℝ] TangentSpace (𝓡 1) ((q i).extend (z 0)),
      ∀ hz : z 0 ∈ Ioo (0 : ℝ) 1,
      HasMFDerivAt (𝓡 1) (𝓡 1) (fun w : E₁ ↦ (q i).extend (w 0)) z
        (e.toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap) ∧
      Orientation.map (Fin 1) e.toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
        (doubleBoundaryLift l).orientationAt ((q i).extend (z 0)) := by
    by_cases hz : z 0 ∈ Ioo (0 : ℝ) 1
    · obtain ⟨e, hd, ho⟩ := exists_unitDiskBoundaryLoop_positive_tangentEquiv
        (Manifold.Orientation.closedBall (n := 2) Complex.basisOneI.orientation)
        (Manifold.Orientation.map_orientationAt_closedBall (n := 2)
          Complex.basisOneI.orientation) z hz
      let ecomp := e.trans (componentTangentEquiv i (unitDiskBoundaryLoop.extend (z 0)))
      refine ⟨ecomp, fun _ ↦ ?_⟩
      constructor
      · have hinc : HasMFDerivAt (𝓡 1) (𝓡 1) (componentInclusion i)
            (unitDiskBoundaryLoop.extend (z 0))
            (componentTangentEquiv i
              (unitDiskBoundaryLoop.extend (z 0))).toContinuousLinearMap := by
          rw [componentTangentEquiv_eq_mfderiv]
          cases i
          · exact (hasMFDerivAt_inl (I := 𝓡 1)).mdifferentiableAt.hasMFDerivAt
          · exact (hasMFDerivAt_inr (I := 𝓡 1)).mdifferentiableAt.hasMFDerivAt
        -- Normalize the mapped path base point before comparing the composed tangent maps.
        have hcomposition := hinc.comp z hd
        convert! hcomposition using 1
      · rw [hqext, doubleBoundaryLift_orientationAt]
        -- The inclusion tangent equivalence is the identity on the shared Euclidean model.
        have hecomp : ecomp.toLinearEquiv = e.toLinearEquiv := by
          apply LinearEquiv.ext
          intro v
          exact componentTangentEquiv_apply i _ (e v)
        rw [hecomp]
        rw [← diskOrientationLift_mk, boundaryOrientation_mk,
          Manifold.Orientation.orientationAt_mk] at ho
        exact ho
    · exact ⟨(tangentSpaceCastModel (𝓡 1) ((q i).extend (z 0))).symm,
        fun h ↦ (hz h).elim⟩
  choose e he using he
  have hr := integralTopForm_mpullback_eq_sum_curveIntegral
    (Manifold.Orientation.mk (doubleBoundaryLift l)) p p q
    f hf P Q univ isOpen_univ (subset_univ _) hP.continuousOn hQ.continuousOn
    (range p) (finite_range p) himage hdisj hinj e
    (fun i z hz ↦ (he i z hz).1) (fun i z hz ↦ by
      simpa only [Manifold.Orientation.orientationAt_mk] using (he i z hz).2)
  have hmap (i : Bool) : curveIntegral (oneForm P Q) ((q i).map hf.continuous) =
      curveIntegral (oneForm P Q)
        (unitDiskBoundaryLoop.map (continuous_subtype_val.comp continuous_subtype_val)) := by
    cases i <;> rfl
  refine ⟨hr.1, ?_, ?_⟩
  · convert! hr.2.1 false using 1
  · -- Unfold the chosen lift and folding map to match the finite-component integral theorem.
    change integralTopForm (Manifold.Orientation.mk (doubleBoundaryLift l))
      (mpullback (𝓡 1) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) = _
    rw [hr.2.2, Fintype.sum_bool, hmap, hmap, two_mul]

/-- Each genuine boundary component contributes `π`, so the two-component canonical integral
of the area form is nonzero and equals `2π`. -/
theorem integralTopForm_twoDiskBoundaries_area :
    integralTopForm twoDiskBoundaryOrientation
      (mpullback (𝓡 1) 𝓘(ℝ, ℂ)
        (Sum.elim (fun x : B ↦ x.val.val) (fun x : B ↦ x.val.val))
        (manifoldOneForm Examples.areaP Examples.areaQ)) = 2 * Real.pi := by
  rw [(integralTopForm_twoDiskBoundaries Examples.areaP Examples.areaQ
    (Examples.contDiff_areaP (n := 1)).continuous
    (Examples.contDiff_areaQ (n := 1)).continuous).2.2,
    curveIntegral_unitDisk_area]

end TauCeti.Green
