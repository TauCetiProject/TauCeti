/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Direct integration of zero-dimensional forms

A zero-dimensional chart contains one point. Its normalized basis Haar measure has mass one,
so the actual oriented chart integral is the value at that point times its orientation sign.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A `0`-form on a zero-dimensional manifold is integrable if and only if its topological support
is compact. -/
theorem integrableTopForm_iff_isCompact_tsupport_zeroDim (φ : RoughForm I M ℝ 0) :
    IntegrableTopForm φ ↔ IsCompact (_root_.tsupport (α := E [⋀^Fin 0]→L[ℝ] ℝ) φ) :=
  ⟨IntegrableTopForm.isCompact, fun hc ↦ (isSmoothForm_zeroDim (n := 0) φ).integrableTopForm hc
    (Module.finBasisOfFinrankEq ℝ E (Module.finrank_zero_iff.mpr inferInstance))⟩

/-- A function supported in a singleton integrates to its value at that point multiplied by
the tangent orientation sign. Singleton support also supplies compactness. -/
theorem integralTopForm_ofFunction_zeroDim (o : Manifold.Orientation I M (Fin 0))
    (b : Module.Basis (Fin 0) ℝ E) (g : M → ℝ) (x : M)
    (hs : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (RoughForm.ofFunction I g)) ⊆ {x}) :
    integralTopForm o (RoughForm.ofFunction I g) =
      (Orientation.signBasis (o.orientationAt x) b : ℝ) * g x := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  have hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ)
      (RoughForm.ofFunction I g)) :=
    isCompact_singleton.of_isClosed_subset (_root_.isClosed_tsupport _) hs
  have hi := (integrableTopForm_iff_isCompact_tsupport_zeroDim _).2 hc
  rw [integralTopForm_eq_chartIntegral l _ hi x
    (by simpa only [extChartAt_source_zeroDim] using hs), l.chartIntegral_eq_integral _ b x]
  -- the chart integral is the evaluation at `0`, which is the chart image of `x`
  rw [Module.Basis.addHaar_eq_dirac, integral_dirac,
    Subsingleton.elim (0 : E) (extChartAt I x x),
    RoughForm.signedInChartAt_apply_of_mem_source _ b x _ (mem_extChartAt_source x),
    RoughForm.inChartAt_ofFunction]
  -- split the tangent orientation sign at `x` into the model sign and the lift sign
  dsimp only
  rw [Manifold.Orientation.orientationAt_mk, Manifold.OrientationLift.signBasis_orientationAt,
    (extChartAt I x).left_inv (mem_extChartAt_source x)]
  simp only [ContinuousAlternatingMap.constOfIsEmpty_apply, Units.val_mul, Int.cast_mul]
  ring

/-- On a finite zero-dimensional manifold the actual integral is the signed sum of values.
The signs come from its tangent orientations, and the point masses are normalized to one. -/
theorem integralTopForm_ofFunction_finite_zeroDim [Fintype M]
    (o : Manifold.Orientation I M (Fin 0)) (b : Module.Basis (Fin 0) ℝ E) (g : M → ℝ) :
    integralTopForm o (RoughForm.ofFunction I g) =
      ∑ x : M, (Orientation.signBasis (o.orientationAt x) b : ℝ) * g x := by
  classical
  have : T1Space M := I.t1Space M
  let δ : M → RoughForm I M ℝ 0 := fun x ↦
    RoughForm.ofFunction I (fun y ↦ if y = x then g x else 0)
  have hs (x : M) : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (δ x)) ⊆ {x} := by
    apply closure_minimal _ isClosed_singleton
    intro y hy
    by_contra hn
    have hne : y ≠ x := by simpa only [mem_singleton_iff] using hn
    apply hy
    ext v
    simp [δ, RoughForm.ofFunction_apply, hne]
    rfl
  have hc (x : M) : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (δ x)) :=
    isCompact_singleton.of_isClosed_subset
    (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) _) (hs x)
  have hi (x : M) : IntegrableTopForm (δ x) :=
    (integrableTopForm_iff_isCompact_tsupport_zeroDim _).2 (hc x)
  have he : RoughForm.ofFunction I g = ∑ x : M, δ x := by
    ext y v
    simp [δ, RoughForm.ofFunction_apply, Finset.sum_apply,
      ContinuousAlternatingMap.sum_apply]
  rw [he, integralTopForm_sum o δ Finset.univ (fun x _ ↦ hi x)]
  apply Finset.sum_congr rfl
  intro x _
  have h := integralTopForm_ofFunction_zeroDim o b
    (fun y ↦ if y = x then g x else 0) x (hs x)
  simpa only [δ, ite_true] using h

/-- On a finite zero-dimensional manifold, the top-form integral of any `0`-form is the signed sum
of its values on the empty tangent frame. -/
theorem integralTopForm_finite_zeroDim [Fintype M]
    (o : Manifold.Orientation I M (Fin 0)) (b : Module.Basis (Fin 0) ℝ E) (φ : RoughForm I M ℝ 0) :
    integralTopForm o φ =
      ∑ x : M, (Orientation.signBasis (o.orientationAt x) b : ℝ) * φ x ![] := by
  conv_lhs => rw [φ.eq_ofFunction]
  rw [integralTopForm_ofFunction_finite_zeroDim o b]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Subsingleton.elim (0 : Fin 0 → TangentSpace I x) ![]]

end TauCeti
