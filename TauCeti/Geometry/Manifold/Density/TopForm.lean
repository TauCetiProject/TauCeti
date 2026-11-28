/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Integral
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm

/-!
# Comparison of oriented top-form and density integration

On an oriented manifold, a top form `φ` defines the rough density `φ.toDensity o`. Its chart
coefficients match the signed chart coefficients of `φ` up to the relative basis sign of the
orientation lift (`TauCeti.RoughDensity.inChartAt_toDensity`), so `φ.toDensity o` is integrable
iff `φ` is (`TauCeti.integrableDensity_toDensity_iff`), and the oriented integral of `φ` equals
the orientation-free density integral (`TauCeti.integralTopForm_eq_integralDensity`).
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {m : ℕ}

/-- In a preferred chart, the coefficient of the density of a top form is its signed coefficient
against an orientation lift, weighted by the relative sign of the model basis. -/
theorem RoughDensity.inChartAt_toDensity (l : Manifold.OrientationLift I M (Fin m))
    (φ : RoughForm I M ℝ m) (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    (φ.toDensity (Manifold.Orientation.mk l)).inChartAt b α y =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun x ↦ l.signAt α x) y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [← (extChartAt I α).right_inv hy]
    set x := (extChartAt I α).symm y
    have hx : x ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    have hα : x ∈ (chartAt H α).source := by rwa [extChartAt_source] at hx
    have hxx : x ∈ (chartAt H x).source := mem_chart_source H x
    let D := fderivWithin ℝ (extChartAt I x ∘ (extChartAt I α).symm) (range I)
      (extChartAt I α x)
    -- The orientation lift relates the chart signs at `x` through the transition determinant.
    have hdet : (l.signAt α x : ℝ) * D.toLinearMap.det =
        |D.toLinearMap.det| * (l.signAt x x : ℝ) := by
      simpa only [l.signAt_of_mem hα, l.signAt_of_mem hxx] using l.sign_mul_det α x x hα hxx
    -- The value of the density at `x` on the model basis.
    have hval : (φ.toDensity (Manifold.Orientation.mk l)) x b =
        (Orientation.signBasis l.modelOrientation b : ℝ) * l.signAt x x * φ x b := by
      have hs := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : ℝ)) (l.signBasis_orientationAt b x)
      simp only [Units.val_mul, Int.cast_mul] at hs
      rw [← hs, ← Manifold.Orientation.orientationAt_mk]
      exact φ.toDensity_apply_basis _ x b
    -- The form coefficient changes to the chart at `x` with the signed determinant.
    have hcoef := φ.inChartAt_apply_basis_eq_det_mul b ((extChartAt I α).map_source hx)
      (x := x) (by rw [(extChartAt I α).left_inv hx]; exact mem_extChartAt_source x)
    rw [(extChartAt I α).left_inv hx, RoughForm.inChartAt_extChartAt_self] at hcoef
    rw [RoughDensity.inChartAt_changeChart _ b hx (mem_extChartAt_source x),
      RoughDensity.inChartAt_self, hval, RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx,
      hcoef]
    linear_combination (-((Orientation.signBasis l.modelOrientation b : ℝ) * φ x b)) * hdet
  · rw [RoughDensity.inChartAt_of_notMem_target _ b α hy, RoughForm.signedInChartAt_apply,
      dite_eq_right hy, mul_zero]

/-- On an oriented manifold, a top form is integrable exactly when its density is. -/
@[simp]
theorem integrableDensity_toDensity_iff (o : Manifold.Orientation I M (Fin m))
    (φ : RoughForm I M ℝ m) : IntegrableDensity (φ.toDensity o) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  rw [integrableDensity_iff, integrableTopForm_iff, RoughForm.tsupport_toDensity]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun b ↦ forall_congr' fun α ↦ ?_))
  have heq : (φ.toDensity (Manifold.Orientation.mk l)).inChartAt b α = fun y ↦
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun x ↦ l.signAt α x) y :=
    funext (RoughDensity.inChartAt_toDensity l φ b α)
  have hu : IsUnit ((Orientation.signBasis l.modelOrientation b : ℤ) : ℝ) :=
    isUnit_iff_ne_zero.mpr (abs_pos.mp (by rw [abs_unit_intCast]; exact one_pos))
  rw [heq, integrable_const_mul_iff hu]
  apply φ.integrable_signedInChartAt_iff_unsigned b α (fun x ↦ l.signAt α x) ?_ b.addHaar
  apply continuousOn_iff_continuous_domRestrict.mp
  simpa only [extChartAt_source] using l.continuousOn_signAt α

/-- On an oriented manifold, the integral of a top form is the integral of its density. -/
theorem integralTopForm_eq_integralDensity (o : Manifold.Orientation I M (Fin m))
    (φ : RoughForm I M ℝ m) : integralTopForm o φ = integralDensity (φ.toDensity o) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  by_cases hi : IntegrableTopForm φ
  · have hd := (integrableDensity_toDensity_iff o φ).mpr hi
    obtain ⟨l, rfl⟩ := o.exists_lift
    let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
    obtain ⟨n, α, u, _, hp, hc⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
    rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hp i).1)
        (fun i ↦ (hp i).2.1) hc,
      integralDensity_eq_sum_disjointed_chart_integrals hd b α u
        (fun i ↦ (hp i).1.isChartMeasurable) (fun i ↦ (hp i).2.1)
        (fun x hx ↦ hc (by rw [← RoughForm.tsupport_toDensity]; exact subset_closure hx)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦
      (RoughDensity.inChartAt_toDensity l φ b (α i) y).symm)
  · rw [integralTopForm_eq_zero_of_not_integrable o φ hi,
      integralDensity_eq_zero_of_not_integrable (mt (integrableDensity_toDensity_iff o φ).mp hi)]

end TauCeti
