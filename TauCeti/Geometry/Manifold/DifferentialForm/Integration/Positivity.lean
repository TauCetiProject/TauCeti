/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Order.Disjointed

/-!
# Positivity of the integral of top forms

A top form on an oriented manifold is nonnegative when it takes nonnegative values on the
positively oriented bases of every tangent space. The integral of such a form is nonnegative
(`TauCeti.integralTopForm_nonneg`), and it is positive as soon as the form is continuous,
compactly supported and positive at one point (`TauCeti.integralTopForm_pos`). The manifold may
have boundary or corners, and it need not be Hausdorff.

Both statements need positive degree. A zero-dimensional tangent space has a unique basis, and its
orientation may be the opposite of the given one; the hypothesis on positively oriented bases is
then vacuous at that point, where the form contributes its value with a negative sign.

## Main results

* `TauCeti.integralTopForm_nonneg`: the integral of a nonnegative top form is nonnegative.
* `TauCeti.integralTopForm_pos`: the integral of a continuous, compactly supported, nonnegative
  top form that is positive somewhere is positive.

## Implementation notes

In a preferred chart of an orientation lift, the signed coordinate coefficient of a top form is a
positive multiple of the form's value on a positively oriented tangent basis, so every chart
integral computing `TauCeti.integralTopForm` has a nonnegative integrand. In the chart at a point
where the form is positive, that integrand is positive on a nonempty open subset of the chart
target, which has positive Haar measure even when the point lies on the boundary.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 16.6.
-/

public section

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k : ℕ}

/-- In a preferred chart, the signed coefficient of a top form at the chart image of `x`, with the
sign of the model basis, is a positive multiple of the form's value on any positively oriented
basis of the tangent space at `x`. -/
private theorem exists_pos_signBasis_mul_signedInChartAt_eq
    (l : Manifold.OrientationLift I M (Fin k)) (φ : RoughForm I M ℝ k)
    (b : Module.Basis (Fin k) ℝ E) {α x : M} (hx : x ∈ (extChartAt I α).source)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I x)) (hc : c.orientation = l.orientationAt x) :
    ∃ r : ℝ, 0 < r ∧
      (Orientation.signBasis l.modelOrientation b : ℝ) *
          φ.signedInChartAt b α (fun z ↦ l.signAt α z) (extChartAt I α x) = r * φ x c := by
  have hα : x ∈ (chartAt H α).source := by rwa [extChartAt_source] at hx
  have hxx : x ∈ (chartAt H x).source := mem_chart_source H x
  let D := fderivWithin ℝ (extChartAt I x ∘ (extChartAt I α).symm) (range I) (extChartAt I α x)
  -- The chart signs compensate the sign of the transition Jacobian to the chart at `x`.
  have hD : 0 < (l.signAt α x : ℝ) * (l.signAt x x : ℝ) * D.toLinearMap.det := by
    rw [l.signAt_of_mem hα, l.signAt_of_mem hxx]
    exact l.compatible α x x hα hxx
  refine ⟨(l.signAt α x : ℝ) * (l.signAt x x : ℝ) * D.toLinearMap.det * |c.det b|,
    mul_pos hD (abs_pos.mpr (c.isUnit_det b).ne_zero), ?_⟩
  have hcoef := φ.inChartAt_apply_basis_eq_det_mul b ((extChartAt I α).map_source hx)
    (x := x) (by rw [(extChartAt I α).left_inv hx]; exact mem_extChartAt_source x)
  rw [(extChartAt I α).left_inv hx,
    RoughForm.inChartAt_chart_apply φ x (mem_extChartAt_source x)] at hcoef
  simp only [tangentCoordChange_self (mem_extChartAt_source x)] at hcoef
  -- The value on the model basis, signed against the tangent orientation, is the value on `c`
  -- times the absolute change-of-basis determinant.
  have key : (Orientation.signBasis (l.orientationAt x) b : ℝ) * φ x b = |c.det b| * φ x c := by
    have h := (φ x).toAlternatingMap.signBasis_mul_apply_eq_abs_det_mul c b
    rw [hc] at h
    -- `h` reads the model basis `b` as a basis of the tangent space `TangentSpace I x = E`;
    -- the statement elaborates it over `E`, which `rw` cannot match up to that unfolding.
    exact h
  rw [l.signBasis_orientationAt b x, Units.val_mul, Int.cast_mul] at key
  have hsq : (l.signAt x x : ℝ) * l.signAt x x = 1 := by
    exact_mod_cast Int.isUnit_mul_self (l.signAt x x).isUnit
  rw [RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx, hcoef, mul_assoc _ |c.det b|,
    ← key]
  linear_combination
    -((Orientation.signBasis l.modelOrientation b : ℝ) * l.signAt α x * D.toLinearMap.det *
      φ x b) * hsq

/-- Every chart integrand computing the integral of a nonnegative top form is nonnegative. -/
private theorem signBasis_mul_signedInChartAt_nonneg [NeZero k]
    (l : Manifold.OrientationLift I M (Fin k)) {φ : RoughForm I M ℝ k}
    (hφ : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = l.orientationAt x → 0 ≤ φ x c)
    (b : Module.Basis (Fin k) ℝ E) (α : M) (y : E) :
    0 ≤ (Orientation.signBasis l.modelOrientation b : ℝ) *
      φ.signedInChartAt b α (fun z ↦ l.signAt α z) y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [← (extChartAt I α).right_inv hy]
    -- In positive degree, a positively oriented tangent basis exists.
    let x := (extChartAt I α).symm y
    let c : Module.Basis (Fin k) ℝ (TangentSpace I x) := b.adjustToOrientation (l.orientationAt x)
    have hc : c.orientation = l.orientationAt x := b.orientation_adjustToOrientation _
    obtain ⟨r, hr, h⟩ := exists_pos_signBasis_mul_signedInChartAt_eq l φ b
      ((extChartAt I α).map_target hy) c hc
    rw [h]
    exact mul_nonneg hr.le (hφ x c hc)
  · rw [RoughForm.signedInChartAt_apply, dite_eq_right hy, mul_zero]

/-- The integral over a chart target of the chart integrand of a continuous, compactly supported,
nonnegative top form is positive when the form is positive at a point of the chart source. -/
private theorem setIntegral_signBasis_mul_signedInChartAt_pos [NeZero k] [MeasurableSpace E]
    [BorelSpace E] (l : Manifold.OrientationLift I M (Fin k)) {φ : RoughForm I M ℝ k}
    (hφ : IsSmoothForm I 0 φ) (hi : IntegrableTopForm φ)
    (hnn : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = l.orientationAt x → 0 ≤ φ x c)
    (b : Module.Basis (Fin k) ℝ E) {α x₀ : M} (hx₀ : x₀ ∈ (extChartAt I α).source)
    (c₀ : Module.Basis (Fin k) ℝ (TangentSpace I x₀)) (hc₀ : c₀.orientation = l.orientationAt x₀)
    (hφ₀ : 0 < φ x₀ c₀) :
    0 < ∫ y in (extChartAt I α).target, (Orientation.signBasis l.modelOrientation b : ℝ) *
      φ.signedInChartAt b α (fun z ↦ l.signAt α z) y ∂b.addHaar := by
  -- The chart integrand `g` is nonnegative, integrable and continuous on the target, and positive
  -- at the chart image of `x₀`.
  let g : E → ℝ := fun y ↦ (Orientation.signBasis l.modelOrientation b : ℝ) *
    φ.signedInChartAt b α (fun z ↦ l.signAt α z) y
  have hσ : Continuous (fun z : {z : M // z ∈ (extChartAt I α).source} ↦ l.signAt α z) := by
    apply continuousOn_iff_continuous_domRestrict.mp
    simpa only [extChartAt_source] using l.continuousOn_signAt α
  have hint : Integrable g b.addHaar :=
    ((φ.integrable_signedInChartAt_iff_unsigned b α _ hσ b.addHaar).mpr
      (((integrableTopForm_iff φ).mp hi).2.2 b α)).const_mul _
  have hcont : ContinuousOn g (extChartAt I α).target :=
    continuousOn_const.mul (φ.continuousOn_signedInChartAt b α _ hσ (hφ.continuousOn_inChartAt α))
  have hy₀ := (extChartAt I α).map_source hx₀
  have hg₀ : 0 < g (extChartAt I α x₀) := by
    obtain ⟨r, hr, h⟩ := exists_pos_signBasis_mul_signedInChartAt_eq l φ b hx₀ c₀ hc₀
    simp only [g, h]
    exact mul_pos hr hφ₀
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y ↦ signBasis_mul_signedInChartAt_nonneg l hnn b α y)
    hint.integrableOn]
  -- `g` is positive on a nonempty open subset of the interior of the target, which has positive
  -- Haar measure even when `x₀` is a boundary point.
  let V := interior (extChartAt I α).target ∩ g ⁻¹' Ioi 0
  have hV : IsOpen V :=
    (hcont.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_Ioi
  obtain ⟨U, hUo, hxU, hUg⟩ := mem_nhdsWithin.mp
    ((hcont.continuousWithinAt hy₀).eventually (lt_mem_nhds hg₀))
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp
    (extChartAt_target_subset_closure_interior hy₀) U hUo hxU
  have hVne : V.Nonempty := ⟨z, hz, hUg ⟨hzU, interior_subset hz⟩⟩
  refine (hV.measure_pos b.addHaar hVne).trans_le (measure_mono fun y hy ↦ ?_)
  exact ⟨(ne_of_gt hy.2 : g y ≠ 0), interior_subset hy.1⟩

/-- **Nonnegativity of integration.** On an oriented manifold of positive dimension, a top form
that is nonnegative on every positively oriented tangent basis has nonnegative integral. No
regularity or support condition is needed, since the integral is zero for nonintegrable forms. -/
theorem integralTopForm_nonneg [NeZero k] (o : Manifold.Orientation I M (Fin k))
    {φ : RoughForm I M ℝ k}
    (hφ : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 ≤ φ x c) :
    0 ≤ integralTopForm o φ := by
  by_cases hi : IntegrableTopForm φ
  swap
  · rw [integralTopForm_eq_zero_of_not_integrable o φ hi]
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨l, rfl⟩ := o.exists_lift
  simp only [Manifold.Orientation.orientationAt_mk] at hφ
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  obtain ⟨m, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hu i).1)
    (fun i ↦ (hu i).2.1) hcover, Finset.mul_sum]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [← integral_const_mul]
  exact integral_nonneg fun y ↦ signBasis_mul_signedInChartAt_nonneg l hφ b (α i) y

/-- **Positivity of integration** [Lee, Prop. 16.6]. On an oriented manifold of positive
dimension, a continuous, compactly supported top form that is nonnegative on every positively
oriented tangent basis, and positive on one, has positive integral. -/
theorem integralTopForm_pos [NeZero k] (o : Manifold.Orientation I M (Fin k))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ))
    (hnn : ∀ x (c : Module.Basis (Fin k) ℝ (TangentSpace I x)),
      c.orientation = o.orientationAt x → 0 ≤ φ x c)
    (hpos : ∃ x, ∃ c : Module.Basis (Fin k) ℝ (TangentSpace I x),
      c.orientation = o.orientationAt x ∧ 0 < φ x c) :
    0 < integralTopForm o φ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨l, rfl⟩ := o.exists_lift
  simp only [Manifold.Orientation.orientationAt_mk] at hnn hpos
  obtain ⟨x₀, c₀, hc₀, hφ₀⟩ := hpos
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  have hi := hφ.integrableTopForm hc b
  -- Compute the integral on a chart cover whose first chart is the chart at `x₀`, so that the
  -- first disjointed piece is that chart's whole source.
  obtain ⟨m, α, u, _, hu, hcover⟩ := exists_finite_precompact_chart_cover (I := I) hc
  let α' : Fin (m + 1) → M := Fin.cons x₀ α
  let u' : Fin (m + 1) → Set M := Fin.cons (extChartAt I x₀).source u
  have hu' : ∀ i, IsOpen (u' i) ∧ u' i ⊆ (extChartAt I (α' i)).source := by
    refine Fin.cases ?_ fun i ↦ ?_
    · simpa [α', u'] using isOpen_extChartAt_source (I := I) x₀
    · simpa [α', u'] using And.intro (hu i).1 (hu i).2.1
  have hcover' : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ ⋃ i, u' i :=
    hcover.trans (iUnion_subset fun i ↦ by simpa [u'] using subset_iUnion u' i.succ)
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α' u' (fun i ↦ (hu' i).1)
    (fun i ↦ (hu' i).2) hcover', Finset.mul_sum, Fin.sum_univ_succ]
  refine add_pos_of_pos_of_nonneg ?_ (Finset.sum_nonneg fun i _ ↦ ?_)
  swap
  · rw [← integral_const_mul]
    exact integral_nonneg fun y ↦ signBasis_mul_signedInChartAt_nonneg l hnn b (α' i.succ) y
  have hpiece : (extChartAt I (α' 0)) '' disjointed u' 0 = (extChartAt I (α' 0)).target := by
    rw [← bot_eq_zero, disjointed_bot, bot_eq_zero]
    simp only [α', u', Fin.cons_zero]
    exact (extChartAt I x₀).image_source_eq_target
  rw [hpiece, ← integral_const_mul]
  exact setIntegral_signBasis_mul_signedInChartAt_pos l hφ hi hnn b
    (by simp [α']) c₀ hc₀ hφ₀

end TauCeti
