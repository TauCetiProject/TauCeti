/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.LocallySymmetric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Differentiating curvature along a curve

The covariant product rule for curvature applies to arbitrary differentiable tangent fields
along a differentiable curve, including within parameter sets with unique derivatives.
In particular, when the curvature is parallel, applying curvature to three parallel fields
again gives a parallel field. For a metric connection its pairing with a fourth parallel
field is constant.

The connection need not be torsion free. The Riemannian bundle supplies fibre norms for the
smooth hom-bundle representation of curvature; compatibility is needed only for the final
scalar conservation law.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (covariant differentiation of curvature and local symmetry).
* `CovariantDerivative.derivCurvatureTensor` and `curvatureTensorCLM` supply the
  pointwise derivative and smooth curvature tensor used here. The coordinate calculation
  follows the hom-bundle reading in `CovariantDerivative.eventually_norm_curvatureTensor_le`.
-/

public section

open Bundle ContinuousLinearMap FiberBundle Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
  {U V W : ∀ r, TangentSpace I (γ r)}

/-- Simultaneous coordinate regularity and the covariant curvature product rule. -/
private theorem curvatureTensor_alongCurveWithin_aux
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ U (γ t)) s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    DifferentiableWithinAt ℝ (sectionCoord (F := E) γ
      (fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r)) (γ t)) s t ∧
      ∀ (_hu : UniqueDiffWithinAt ℝ s t),
      alongCurveWithin cov γ (fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r)) s t =
      cov.derivCurvatureTensor cov (γ t) (curveVelocityWithin I γ s t) (U t) (V t) (W t) +
        cov.curvatureTensor (γ t) (alongCurveWithin cov γ U s t) (V t) (W t) +
        cov.curvatureTensor (γ t) (U t) (alongCurveWithin cov γ V s t) (W t) +
        cov.curvatureTensor (γ t) (U t) (V t) (alongCurveWithin cov γ W s t) := by
  -- Cache the iterated operator-space instances, as in the smooth curvature API.
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  let _ : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  let _ : ∀ x : M, NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  let _ : ∀ x : M, NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  let _ : ∀ x : M, AddCommMonoid
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ (inferInstance : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)).toAddCommMonoid
  let e := trivializationAt E (TangentSpace I) (γ t)
  have he : γ t ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  let A : M → E →L[ℝ] E →L[ℝ] E →L[ℝ] E := fun x ↦
    inCoordinates E (TangentSpace I) (E →L[ℝ] E →L[ℝ] E)
      (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
      (γ t) x (γ t) x (cov.curvatureTensorCLM (V := TangentSpace I)
        (fiberNorm := fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x))) x)
  have hR := contMDiff_curvatureTensorCLM (F := E) (V := fun x : M ↦ TangentSpace I x)
    (fiberNorm := fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x))) cov
  have hA : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] E) A (γ t) :=
    ((mdifferentiableAt_hom_bundle _).1 (hR.mdifferentiableAt (by simp))).2
  have hAγ : DifferentiableWithinAt ℝ (fun r ↦ A (γ r)) s t :=
    (hA.comp_mdifferentiableWithinAt t hγ).differentiableWithinAt
  have hread (x : M) (hx : x ∈ e.baseSet) (a b c : TangentSpace I x) :
      e.continuousLinearMapAt ℝ x (cov.curvatureTensor x a b c) =
        A x (e.continuousLinearMapAt ℝ x a) (e.continuousLinearMapAt ℝ x b)
          (e.continuousLinearMapAt ℝ x c) := by
    have hx' : x ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet := hx
    dsimp only [A]
    rw [inCoordinates_apply_eq₂ (F₁ := E) (E₁ := TangentSpace I)
      (F₂ := E) (E₂ := TangentSpace I) (F₃ := E →L[ℝ] E)
      (E₃ := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) hx' hx'
      (by rw [hom_trivializationAt_baseSet]; exact ⟨hx', hx'⟩),
      Trivialization.linearMapAt_def_of_mem _ (by
        rw [hom_trivializationAt_baseSet]; exact ⟨hx', hx'⟩)]
    simp [hom_trivializationAt_apply, inCoordinates,
      (trivializationAt E (TangentSpace I) (γ t)).symmL_apply hx']
    simp only [e, Trivialization.symm_linearMapAt _ hx']
  have hsmooth : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ
      (fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r)) (γ t)) s t := by
    refine (((hAγ.clm_apply hU).clm_apply hV).clm_apply hW).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hγ.continuousWithinAt.preimage_mem_nhdsWithin
        (e.open_baseSet.mem_nhds he)] with r hr
      simpa only [sectionCoord_apply] using hread (γ r) hr (U r) (V r) (W r)
    · simpa only [sectionCoord_apply] using hread (γ t) he (U t) (V t) (W t)
  refine ⟨hsmooth, fun hu ↦ ?_⟩
  let C := e.continuousLinearMapAt ℝ (γ t)
  have hreadT (a b c : TangentSpace I (γ t)) :
      C (cov.curvatureTensor (γ t) a b c) = A (γ t) (C a) (C b) (C c) :=
    hread (γ t) he a b c
  let G := christoffelMap (Module.finBasis ℝ E)
    (cov.isCovariantDerivativeOn (s := e.baseSet)) (γ t)
  let z := derivWithin (extChartAt I (γ t) ∘ γ) s t
  have hD (Q : ∀ r, TangentSpace I (γ r)) :
      C (alongCurveWithin cov γ Q s t) =
        derivWithin (sectionCoord (F := E) γ Q (γ t)) s t + G (C (Q t)) z := by
    rw [alongCurveWithin_apply, e.continuousLinearMapAt_symmL he,
      alongCurveInChartWithin_apply, sectionCoord_apply]
  -- The ordinary product rule in the fixed model fibre differentiates arbitrary input fields.
  have hDR (Q₁ Q₂ Q₃ : ∀ r, TangentSpace I (γ r))
      (h₁ : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Q₁ (γ t)) s t)
      (h₂ : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Q₂ (γ t)) s t)
      (h₃ : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Q₃ (γ t)) s t) :
      C (alongCurveWithin cov γ
          (fun r ↦ cov.curvatureTensor (γ r) (Q₁ r) (Q₂ r) (Q₃ r)) s t) =
        derivWithin (fun r ↦ A (γ r)) s t (C (Q₁ t)) (C (Q₂ t)) (C (Q₃ t)) +
          A (γ t) (C (Q₁ t)) (C (Q₂ t))
            (derivWithin (sectionCoord (F := E) γ Q₃ (γ t)) s t) +
          A (γ t) (C (Q₁ t))
            (derivWithin (sectionCoord (F := E) γ Q₂ (γ t)) s t) (C (Q₃ t)) +
          A (γ t) (derivWithin (sectionCoord (F := E) γ Q₁ (γ t)) s t)
            (C (Q₂ t)) (C (Q₃ t)) +
          G (A (γ t) (C (Q₁ t)) (C (Q₂ t)) (C (Q₃ t))) z := by
    have h := ((hAγ.hasDerivWithinAt.clm_apply h₁.hasDerivWithinAt).clm_apply
      h₂.hasDerivWithinAt).clm_apply h₃.hasDerivWithinAt
    have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
      hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds he)
    have hEq : (fun r ↦ A (γ r) (sectionCoord (F := E) γ Q₁ (γ t) r)
        (sectionCoord (F := E) γ Q₂ (γ t) r) (sectionCoord (F := E) γ Q₃ (γ t) r)) =ᶠ[𝓝[s] t]
        sectionCoord (F := E) γ
          (fun r ↦ cov.curvatureTensor (γ r) (Q₁ r) (Q₂ r) (Q₃ r)) (γ t) := by
      filter_upwards [hnear] with r hr
      simpa only [sectionCoord_apply] using (hread (γ r) hr (Q₁ r) (Q₂ r) (Q₃ r)).symm
    have hpoint : sectionCoord (F := E) γ
        (fun r ↦ cov.curvatureTensor (γ r) (Q₁ r) (Q₂ r) (Q₃ r)) (γ t) t =
        A (γ t) (sectionCoord (F := E) γ Q₁ (γ t) t)
          (sectionCoord (F := E) γ Q₂ (γ t) t) (sectionCoord (F := E) γ Q₃ (γ t) t) := by
      simpa only [sectionCoord_apply] using hread (γ t) he (Q₁ t) (Q₂ t) (Q₃ t)
    have hd := (h.congr_of_eventuallyEq hEq.symm hpoint).derivWithin hu
    rw [hD, hd, hread (γ t) he]
    simp only [sectionCoord_apply, add_apply, C]
    abel
  -- Smooth ambient extensions identify the model-fibre coefficient with the native ∇R.
  obtain ⟨X, hX, hXt⟩ := exists_contMDiff_section_eq I E ∞ (U t)
  obtain ⟨Y, hY, hYt⟩ := exists_contMDiff_section_eq I E ∞ (V t)
  obtain ⟨Z, hZ, hZt⟩ := exists_contMDiff_section_eq I E ∞ (W t)
  have hcoord (Q : Π x : M, TangentSpace I x) (hQ : CMDiff ∞ (T% Q)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (fun r ↦ Q (γ r)) (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ _
      ((hQ.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t hγ) he
  have hpull (Q : Π x : M, TangentSpace I x) (hQ : CMDiff ∞ (T% Q)) :
      cov Q (γ t) (curveVelocityWithin I γ s t) =
        alongCurveWithin cov γ (fun r ↦ Q (γ r)) s t :=
    (alongCurveWithin_pullback_curveVelocityWithin cov γ Q hu hγ
      (hQ.mdifferentiableAt (by simp))).symm
  have hn := congrArg C (cov.derivCurvatureTensor_apply (covT := cov) (γ t)
    (curveVelocityWithin I γ s t) hX hY hZ)
  rw [hpull _ (cov.contMDiff_curvatureOperator hX hY hZ)] at hn
  have heq : curvatureOperator cov X Y Z =
      fun x ↦ cov.curvatureTensor x (X x) (Y x) (Z x) :=
    funext fun x ↦ (cov.curvatureTensor_apply x hX hY hZ).symm
  simp only [heq, map_sub] at hn
  rw [hDR _ _ _ (hcoord X hX) (hcoord Y hY) (hcoord Z hZ)] at hn
  simp only [hpull X hX, hpull Y hY, hpull Z hZ, hreadT, hD,
    hXt, hYt, hZt, map_add, add_apply] at hn
  apply Function.LeftInverse.injective (f := C) (g := e.symmL ℝ (γ t))
    (e.symmL_continuousLinearMapAt he)
  rw [hDR U V W hU hV hW]
  simp only [map_add, hreadT, hD]
  rw [hn]
  simp only [add_apply]
  abel

/-- Curvature applied to three fields with differentiable coordinate readings again has
a differentiable coordinate reading. No unique-derivative hypothesis is needed here. -/
theorem differentiableWithinAt_sectionCoord_curvatureTensor
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ U (γ t)) s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    DifferentiableWithinAt ℝ (sectionCoord (F := E) γ
      (fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r)) (γ t)) s t :=
  (curvatureTensor_alongCurveWithin_aux cov hγ hU hV hW).1

/-- The covariant product rule for curvature along a differentiable curve:
`D(R(U,V)W) = (∇_γ' R)(U,V)W + R(DU,V)W + R(U,DV)W + R(U,V)DW`.
Only differentiability within the parameter set at the tested parameter is required. -/
theorem alongCurveWithin_curvatureTensor
    (hu : UniqueDiffWithinAt ℝ s t) (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ U (γ t)) s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    alongCurveWithin cov γ (fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r)) s t =
      cov.derivCurvatureTensor cov (γ t) (curveVelocityWithin I γ s t) (U t) (V t) (W t) +
        cov.curvatureTensor (γ t) (alongCurveWithin cov γ U s t) (V t) (W t) +
        cov.curvatureTensor (γ t) (U t) (alongCurveWithin cov γ V s t) (W t) +
        cov.curvatureTensor (γ t) (U t) (V t) (alongCurveWithin cov γ W s t) :=
  (curvatureTensor_alongCurveWithin_aux cov hγ hU hV hW).2 hu

/-- Parallel curvature maps three parallel fields along a curve to a parallel field.
No metric compatibility or torsion assumption is needed. -/
theorem HasParallelCurvature.alongCurveWithin_curvatureTensor_eq_zero
    (h : cov.HasParallelCurvature)
    (hu : UniqueDiffWithinAt ℝ s t) (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hU : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ U (γ t)) s t)
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hU₀ : alongCurveWithin cov γ U s t = 0)
    (hV₀ : alongCurveWithin cov γ V s t = 0)
    (hW₀ : alongCurveWithin cov γ W s t = 0) :
    alongCurveWithin cov γ (fun r ↦ cov.curvatureTensor (γ r) (U r) (V r) (W r)) s t = 0 := by
  simp [cov.alongCurveWithin_curvatureTensor hu hγ hU hV hW,
    (cov.hasParallelCurvature_iff.mp h) (γ t), hU₀, hV₀, hW₀]

/-- For a metric connection with parallel curvature, the curvature pairing of four
parallel fields is constant on every preconnected parameter set with unique derivatives. -/
theorem HasParallelCurvature.inner_curvatureTensor_eq_of_alongCurveWithin_eq_zero
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (h : cov.HasParallelCurvature)
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hs : UniqueDiffOn ℝ s) (hconn : IsPreconnected s)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s) {Z : ∀ r, TangentSpace I (γ r)}
    (hU : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ U (γ t)) s t)
    (hV : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hZ : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ Z (γ t)) s t)
    (hU₀ : ∀ t ∈ s, alongCurveWithin cov γ U s t = 0)
    (hV₀ : ∀ t ∈ s, alongCurveWithin cov γ V s t = 0)
    (hW₀ : ∀ t ∈ s, alongCurveWithin cov γ W s t = 0)
    (hZ₀ : ∀ t ∈ s, alongCurveWithin cov γ Z s t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    inner ℝ (cov.curvatureTensor (γ a) (U a) (V a) (W a)) (Z a) =
      inner ℝ (cov.curvatureTensor (γ b) (U b) (V b) (W b)) (Z b) := by
  exact hcov.inner_eq_of_alongCurveWithin_eq_zero hs hconn hγ
    (fun t ht ↦ cov.differentiableWithinAt_sectionCoord_curvatureTensor (hγ t ht)
      (hU t ht) (hV t ht) (hW t ht)) hZ
    (fun t ht ↦ h.alongCurveWithin_curvatureTensor_eq_zero cov (hs t ht) (hγ t ht)
      (hU t ht) (hV t ht) (hW t ht) (hU₀ t ht) (hV₀ t ht) (hW₀ t ht)) hZ₀ ha hb

end CovariantDerivative
