/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Operations
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Integrating against the Riemannian volume form

On an oriented manifold `M` with a continuous Riemannian metric there are two ways to integrate a
function `f`: as the top form `f dV` against the orientation (`TauCeti.integralTopForm`), where
`dV` is the Riemannian volume form `TauCeti.riemannianVolumeForm`, and against the Riemannian
volume measure `TauCeti.riemannianVolume`, which uses no orientation. This file proves that they
agree on continuous compactly supported functions:

`∫_M f dV = ∫ f d(vol_g)`.

Integral identities proved for forms, such as Stokes' theorem or the pairing of closed forms with
de Rham classes, thereby become statements about integrals against the Riemannian measure. The
Riemannian measure is also the measure `|dV|` of the volume form
(`TauCeti.measure_riemannianVolumeForm`).

In the chart at `α`, with model basis `b` the standard basis `Module.finBasis` reindexed, the
coefficient `dV(∂₁, …, ∂ₙ)` of the volume form is `±√(det g)`, the chart volume density
`TauCeti.chartVolumeDensity` up to sign (`TauCeti.abs_inChartAt_riemannianVolumeForm`). The
integral of `f dV` is a sum of chart integrals of these coefficients times `f`, each multiplied by
the chart sign of the orientation; the signs cancel against the sign of the coefficient
(`TauCeti.signBasis_mul_signAt_mul_riemannianVolumeForm_chartLocalFrame`), so each such signed
integrand is `f √(det g)`, which is the integrand of the Riemannian measure in that chart. This
holds in every dimension, including dimension `0`.

## Main results

* `TauCeti.abs_inChartAt_riemannianVolumeForm`: the coefficient of the volume form in a chart is
  the chart volume density up to sign.
* `TauCeti.measure_riemannianVolumeForm`: the measure `|dV|` of the volume form is the Riemannian
  volume measure.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm`: `∫_M f dV = ∫ f d(vol_g)` for continuous
  compactly supported `f`.
* `TauCeti.integralTopForm_riemannianVolumeForm`: on a compact manifold, `∫_M dV` is the total
  Riemannian volume.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44 and the Riemannian density following it.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16
  (integration of top forms and densities, and the Riemannian density).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {m : ℕ}

/-- In the chart at `α`, the coefficient of the Riemannian volume form on the reindexed standard
model basis is the volume form on the coordinate frame. -/
private theorem inChartAt_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m))
    (σ : Fin (finrank ℝ E) ≃ Fin m) (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    (riemannianVolumeForm o).inChartAt α y ((finBasis ℝ E).reindex σ) =
      riemannianVolumeForm o ((extChartAt I α).symm y)
        (fun i ↦ Riemannian.Tensor.chartLocalFrame (I := I) α (σ.symm i)
          ((extChartAt I α).symm y)) := by
  have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  -- The derivative of the inverse chart sends the model basis to the coordinate frame.
  have hframe : (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y
      ((finBasis ℝ E).reindex σ i)) =
      fun i ↦
        Riemannian.Tensor.chartLocalFrame (I := I) α (σ.symm i) ((extChartAt I α).symm y) := by
    funext i
    rw [Riemannian.Tensor.chartLocalFrame_eq_symmL, TangentBundle.symmL_trivializationAt hx,
      (extChartAt I α).right_inv hy, Module.Basis.reindex_apply]
    -- The two sides differ only in the base point named in the type of the tangent space.
    rfl
  rw [RoughForm.inChartAt_apply, hframe]

/-- **The volume form in a chart.** In the chart at `α` and the reindexed standard model basis,
the coefficient of the Riemannian volume form is `±√(det g)`: its absolute value is the chart
volume density. -/
theorem abs_inChartAt_riemannianVolumeForm (o : Manifold.Orientation I M (Fin m))
    (σ : Fin (finrank ℝ E) ≃ Fin m) (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    |(riemannianVolumeForm o).inChartAt α y ((finBasis ℝ E).reindex σ)| =
      chartVolumeDensity (I := I) α ((extChartAt I α).symm y) := by
  rw [inChartAt_riemannianVolumeForm o σ α hy]
  exact abs_riemannianVolumeForm_chartLocalFrame o σ
    (by simpa only [extChartAt_source] using (extChartAt I α).map_target hy)

/-- The chart integrand of `f dV`: in the chart at `α`, the signed coefficient of `f dV`, with the
sign of the model basis, is `√(det g) f`, the integrand of the Riemannian measure in that chart. -/
private theorem signBasis_mul_signedInChartAt_smul_riemannianVolumeForm
    (l : Manifold.OrientationLift I M (Fin m)) (σ : Fin (finrank ℝ E) ≃ Fin m) (f : M → ℝ)
    (α : M) {x : M} (hx : x ∈ (extChartAt I α).source) :
    (Orientation.signBasis l.modelOrientation ((finBasis ℝ E).reindex σ) : ℝ) *
        RoughForm.signedInChartAt
          (fun z ↦ f z • riemannianVolumeForm (Manifold.Orientation.mk l) z)
          ((finBasis ℝ E).reindex σ) α (fun z ↦ l.signAt α z) (extChartAt I α x) =
      chartVolumeDensity (I := I) α x * f x := by
  rw [RoughForm.signedInChartAt_fun_smul, (extChartAt I α).left_inv hx,
    RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx,
    inChartAt_riemannianVolumeForm _ σ α ((extChartAt I α).map_source hx),
    (extChartAt I α).left_inv hx,
    ← signBasis_mul_signAt_mul_riemannianVolumeForm_chartLocalFrame l σ
      (by simpa only [extChartAt_source] using hx)]
  ring

section Integral

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **The Riemannian measure is the measure of the volume form.** The measure `|dV|` of the
Riemannian volume form of any orientation is the Riemannian volume measure. -/
@[simp]
theorem measure_riemannianVolumeForm [Fact (finrank ℝ E = m)]
    (o : Manifold.Orientation I M (Fin m)) :
    (riemannianVolumeForm o).measure = riemannianVolume I M := by
  refine (RoughForm.eq_measure_iff.2 fun α s hs hsub ↦ ?_).symm
  rw [riemannianVolume_apply_of_subset (by simpa only [extChartAt_source] using hsub),
    chartRiemannianVolume_apply α hs, inter_eq_left.2 hsub, finBasisOfFinrankEq,
    Basis.addHaar_reindex]
  refine setLIntegral_congr_fun (hs.image_extChartAt α hsub) ?_
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  rw [abs_inChartAt_riemannianVolumeForm o _ α ((extChartAt I α).map_source (hsub hx))]

/-- **Integration against the Riemannian volume form is integration against the Riemannian
measure.** On an oriented manifold of any dimension with a continuous Riemannian metric, the
integral of the top form `f dV`, for the Riemannian volume form `dV` of the orientation and a
continuous compactly supported function `f`, is the integral of `f` against the Riemannian volume
measure: `∫_M f dV = ∫ f d(vol_g)`. -/
theorem integralTopForm_smul_riemannianVolumeForm
    (o : Manifold.Orientation I M (Fin m)) {f : M → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) =
      ∫ x, f x ∂riemannianVolume I M := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨l, rfl⟩ := o.exists_lift
  have hm : finrank ℝ E = m := by simpa using l.card_eq.symm
  set σ : Fin (finrank ℝ E) ≃ Fin m := finCongr hm
  set b := (finBasis ℝ E).reindex σ
  set φ : RoughForm I M ℝ m := fun x ↦ f x • riemannianVolumeForm (Manifold.Orientation.mk l) x
  -- `f dV` is a continuous top form supported in the support of `f`.
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have hφ : IsSmoothForm I 0 φ :=
    (isSmoothForm_riemannianVolumeForm _).fun_smul (contMDiff_zero_iff.2 hf)
  have hsupp : _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) φ ⊆ tsupport f :=
    -- `simp` leaves the zero of the fibre at `x` against the value at `x` of the zero form.
    closure_mono fun x hx ↦ Function.mem_support.2 fun h ↦ hx (by simp [φ, h]; rfl)
  have hi : IntegrableTopForm φ :=
    hφ.integrableTopForm (hc.of_isClosed_subset isClosed_closure hsupp) b
  -- Compute both integrals on the disjointed pieces of a chart cover of the support of `f`.
  obtain ⟨n, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  have hpiece (i : Fin n) : disjointed u i ⊆ (extChartAt I (α i)).source :=
    (disjointed_subset u i).trans (hu i).2.1
  have hmeas (i : Fin n) : MeasurableSet (disjointed u i) := by
    rw [disjointed_apply, Finset.sup_set_eq_biUnion]
    exact (hu i).1.measurableSet.diff
      (Finset.measurableSet_biUnion _ fun j _ ↦ (hu j).1.measurableSet)
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hu i).1)
    (fun i ↦ (hu i).2.1) (hsupp.trans hcover), Finset.mul_sum,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ⋃ i, disjointed u i) fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (by rw [iUnion_disjointed]; exact hcover h),
    integral_iUnion_fintype hmeas (disjoint_disjointed u)
      fun i ↦ (hf.integrable_of_hasCompactSupport hc).integrableOn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [setIntegral_riemannianVolume_of_subset (by simpa only [extChartAt_source] using hpiece i)
    (hmeas i), ← integral_const_mul, Basis.addHaar_reindex]
  refine setIntegral_congr_fun ((hmeas i).image_extChartAt (α i) (hpiece i)) ?_
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  rw [(extChartAt I (α i)).left_inv (hpiece i hx), smul_eq_mul]
  exact signBasis_mul_signedInChartAt_smul_riemannianVolumeForm l σ f (α i) (hpiece i hx)

omit [LindelofSpace M] in
/-- **The integral of the volume form is the total volume.** On a compact oriented manifold with a
continuous Riemannian metric, the integral of the Riemannian volume form is the total Riemannian
volume: `∫_M dV = vol_g(M)`. -/
theorem integralTopForm_riemannianVolumeForm [CompactSpace M]
    (o : Manifold.Orientation I M (Fin m)) :
    integralTopForm o (riemannianVolumeForm o) = riemannianTotalVolume I M := by
  have h := integralTopForm_smul_riemannianVolumeForm o (f := fun _ ↦ (1 : ℝ)) continuous_const
    (HasCompactSupport.of_compactSpace _)
  simp only [one_smul, integral_const, smul_eq_mul, mul_one] at h
  rw [h, riemannianTotalVolume_def]

end Integral

end TauCeti
