/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Integration
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Agreement of oriented top-form integration with orientation-free density integration

On an oriented `C¹` manifold `M` (possibly non-Hausdorff and possibly with boundary or corners), a
rough top form `φ : RoughForm I M ℝ k` determines the rough density `φ.toDensity o`. This file
proves that `φ.toDensity o` is integrable as a density if and only if `φ` is integrable as a top
form (`TauCeti.integrableDensity_toDensity_iff`), and that the oriented integral of `φ` equals the
orientation-free density integral of `φ.toDensity o` unconditionally for every rough top form
(`TauCeti.integralTopForm_eq_integralDensity`).

Without choosing any orientation on `M`, every top-degree rough form `φ` also defines the
nonnegative absolute density `φ.absDensity` (`x ↦ v ↦ |φ x v|`). Whenever `φ` is integrable as a
top form (in particular for every compactly supported continuous top form, even on a nonorientable
manifold), `φ.absDensity` is integrable (`TauCeti.IntegrableTopForm.integrableDensity_absDensity`,
`TauCeti.IsSmoothForm.integrableDensity_absDensity`), and on an oriented manifold its density
integral bounds `|integralTopForm o φ|` unconditionally
(`TauCeti.abs_integralTopForm_le_integralDensity`) and equals `integralTopForm o φ` when `φ` is
nonnegative on positively oriented tangent bases
(`TauCeti.integralTopForm_eq_integralDensity_absDensity`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities
  (Proposition 16.41).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] {k : ℕ}

/-! ### Oriented top forms via `RoughForm.toDensity` -/

section Oriented

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- On an oriented `C¹` manifold, `φ.toDensity o` is integrable as a rough density if and only if
`φ` is integrable as a top form. -/
@[simp]
theorem integrableDensity_toDensity_iff (o : Manifold.Orientation I M (Fin k))
    (φ : RoughForm I M ℝ k) :
    IntegrableDensity (φ.toDensity o) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  rw [integrableDensity_iff, integrableTopForm_iff, RoughForm.tsupport_toDensity]
  refine and_congr Iff.rfl (and_congr Iff.rfl <| forall_congr' fun b ↦ forall_congr' fun α ↦ ?_)
  have hcongr : IntegrableOn
      (fun y ↦ ((φ.toDensity (Manifold.Orientation.mk l)).inChartAt α y) b)
      (extChartAt I α).target b.addHaar ↔
    IntegrableOn
      (fun y ↦ (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun z ↦ l.signAt α z) y)
      (extChartAt I α).target b.addHaar :=
    integrableOn_congr_fun (fun y hy ↦ RoughForm.toDensity_inChartAt_apply l φ b α hy)
      (measurableSet_extChartAt_target α)
  have hsne : (Orientation.signBasis l.modelOrientation b : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Units.ne_zero _)
  have hσ : Continuous fun z : {z : M // z ∈ (extChartAt I α).source} ↦ l.signAt α z := by
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt α
  rw [hcongr, IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hsne),
    ← IntegrableOn,
    integrableOn_iff_integrable_of_support_subset (φ.support_signedInChartAt_subset_target b α _),
    φ.integrable_signedInChartAt_iff_unsigned b α _ hσ b.addHaar]

/-- **Oriented top-form integration as density integration** (Lee, Proposition 16.41): on any
oriented `C¹` manifold (possibly non-Hausdorff and possibly with boundary or corners), the oriented
integral of any rough top form `φ` equals the orientation-free density integral of
`φ.toDensity o`. Holds unconditionally, including when `φ` is not integrable. -/
theorem integralTopForm_eq_integralDensity (o : Manifold.Orientation I M (Fin k))
    (φ : RoughForm I M ℝ k) :
    integralTopForm o φ = integralDensity (φ.toDensity o) := by
  by_cases hi : IntegrableTopForm φ
  · have hi' : IntegrableDensity (φ.toDensity o) := (integrableDensity_toDensity_iff o φ).mpr hi
    let : MeasurableSpace E := borel E
    let : BorelSpace E := ⟨rfl⟩
    let : LocallyCompactSpace H := I.locallyCompactSpace
    obtain ⟨l, rfl⟩ := o.exists_lift
    let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
    obtain ⟨m, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
    have hcover' : _root_.tsupport (α := Density E k) (φ.toDensity (Manifold.Orientation.mk l)) ⊆
        ⋃ i, u i := by
      rwa [RoughForm.tsupport_toDensity]
    rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hu i).1)
        (fun i ↦ (hu i).2.1) hcover, Finset.mul_sum,
      integralDensity_eq_sum_disjointed_chart_integrals _ hi' b α u (fun i ↦ (hu i).1)
        (fun i ↦ (hu i).2.1) hcover']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_const_mul]
    have hm : MeasurableSet ((extChartAt I (α i)) '' disjointed u i) :=
      (isChartMeasurable_disjointed (fun j ↦ (hu j).1) i).image_extChartAt (α i)
        ((disjointed_subset u i).trans (hu i).2.1)
    have hsub : (extChartAt I (α i)) '' disjointed u i ⊆ (extChartAt I (α i)).target :=
      (image_mono ((disjointed_subset u i).trans (hu i).2.1)).trans
        (extChartAt I (α i)).image_source_eq_target.subset
    exact setIntegral_congr_fun hm fun y hy ↦
      (RoughForm.toDensity_inChartAt_apply l φ b (α i) (hsub hy)).symm
  · have hi' : ¬IntegrableDensity (φ.toDensity o) := by
      rwa [integrableDensity_toDensity_iff]
    rw [integralTopForm_eq_zero_of_not_integrable o φ hi,
      integralDensity_eq_zero_of_not_integrable _ hi']

end Oriented

/-! ### Orientation-free absolute density `RoughForm.absDensity` -/

section AbsDensity

variable [Fact (Module.finrank ℝ E = k)]

/-- Every integrable top form has integrable orientation-free absolute density `φ.absDensity`,
without requiring an orientation on `M`. -/
theorem IntegrableTopForm.integrableDensity_absDensity {φ : RoughForm I M ℝ k}
    (hi : IntegrableTopForm φ) : IntegrableDensity φ.absDensity := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableTopForm_iff] at hi
  rw [integrableDensity_iff, RoughForm.tsupport_absDensity]
  refine ⟨hi.1, hi.2.1, fun b α ↦ ?_⟩
  have hnorm : IntegrableOn (fun y ↦ |φ.signedInChartAt b α (fun _ ↦ 1) y|)
      (extChartAt I α).target b.addHaar := by
    simpa only [Real.norm_eq_abs] using (hi.2.2 b α).norm.integrableOn
  exact hnorm.congr_fun (fun y hy ↦ (RoughForm.absDensity_inChartAt_apply φ b α hy).symm)
    (measurableSet_extChartAt_target α)

/-- The integral of `φ.absDensity` is always nonnegative. -/
theorem integralDensity_absDensity_nonneg (φ : RoughForm I M ℝ k) :
    0 ≤ integralDensity φ.absDensity :=
  integralDensity_nonneg φ.absDensity_nonneg

variable [FiniteDimensional ℝ E]

/-- Every compactly supported `C^n` top form on a `C¹` manifold (orientable or not) has integrable
absolute density `φ.absDensity`. -/
theorem IsSmoothForm.integrableDensity_absDensity [IsManifold I 1 M] {n : WithTop ℕ∞}
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I n φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ)) :
    IntegrableDensity φ.absDensity :=
  (hφ.integrableTopForm hc (Module.finBasisOfFinrankEq ℝ E Fact.out)).integrableDensity_absDensity

/-- The magnitude of an oriented top-form integral is bounded above by the orientation-free
integral of `φ.absDensity`, unconditionally for every rough top form `φ`. -/
theorem abs_integralTopForm_le_integralDensity [IsManifold I 1 M]
    (o : Manifold.Orientation I M (Fin k)) (φ : RoughForm I M ℝ k) :
    |integralTopForm o φ| ≤ integralDensity φ.absDensity := by
  by_cases hi : IntegrableTopForm φ
  · rw [integralTopForm_eq_integralDensity o φ]
    exact abs_integralDensity_le_of_integrable ((integrableDensity_toDensity_iff o φ).mpr hi)
      hi.integrableDensity_absDensity fun x v ↦ by
        rw [RoughForm.abs_toDensity_apply, RoughForm.absDensity_apply]
  · rw [integralTopForm_eq_zero_of_not_integrable o φ hi, abs_zero]
    exact integralDensity_absDensity_nonneg φ

/-- On an oriented manifold of positive dimension, a top form that is nonnegative on every
positively oriented tangent basis satisfies `φ.toDensity o = φ.absDensity`. -/
theorem RoughForm.toDensity_eq_absDensity [IsManifold I 1 M] [NeZero k]
    (o : Manifold.Orientation I M (Fin k)) {φ : RoughForm I M ℝ k}
    (hφ : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 ≤ φ x c) :
    φ.toDensity o = φ.absDensity := by
  funext x
  have hfin : Module.finrank ℝ (TangentSpace I x) = k :=
    (TauCeti.finrank_tangentSpace (I := I) x).trans Fact.out
  let c : Module.Basis (Fin k) ℝ (TangentSpace I x) :=
    (Module.finBasisOfFinrankEq ℝ (TangentSpace I x) hfin).adjustToOrientation (o.orientationAt x)
  have hc : c.orientation = o.orientationAt x :=
    Module.Basis.orientation_adjustToOrientation _ _
  apply c.density_ext
  rw [RoughForm.toDensity_apply_of_orientation_eq φ hc, RoughForm.absDensity_apply,
    abs_of_nonneg (hφ x c hc)]

/-- On an oriented manifold of positive dimension, the oriented integral of a top form that is
nonnegative on positively oriented tangent bases equals the orientation-free integral of
`φ.absDensity`. -/
theorem integralTopForm_eq_integralDensity_absDensity [IsManifold I 1 M] [NeZero k]
    (o : Manifold.Orientation I M (Fin k)) {φ : RoughForm I M ℝ k}
    (hφ : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 ≤ φ x c) :
    integralTopForm o φ = integralDensity φ.absDensity := by
  rw [integralTopForm_eq_integralDensity o φ, RoughForm.toDensity_eq_absDensity o hφ]

end AbsDensity

end TauCeti
