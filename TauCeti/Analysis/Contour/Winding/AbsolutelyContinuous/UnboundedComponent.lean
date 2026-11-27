/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ConstantSpeed
public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.LocallyConstant
public import TauCeti.Topology.FilledHull
import TauCeti.Analysis.Contour.Winding.UnboundedComponent
import TauCeti.MeasureTheory.Function.MetricDerivative.ConstantSpeed

/-!
# Winding numbers of absolutely continuous curves on unbounded components

A closed absolutely continuous curve has winding number zero sufficiently far from its trace
(`AbsolutelyContinuousOnInterval.windingNumber_eventually_zero_cocompact`, in
`TauCeti/Analysis/Contour/Winding/Vanishing.lean`).
Local constancy then gives vanishing on every unbounded connected component of the complement, and
hence outside the filled hull of the trace (both directly for closed AC curves and for the
arclength parametrization of rectifiable closed curves). A ray from a point to infinity that misses
the curve exhibits such a component, and a curve in a set without holes is null-homologous there.

## Main results

* `AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component` — the winding
  number vanishes on every unbounded component of the complement of the trace.
* `AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_ray` — it vanishes at a point joined to
  infinity by a ray off the curve.
* `AbsolutelyContinuousOnInterval.isNullHomologous_of_filledHull_subset` — a closed curve in a set
  without holes is null-homologous there.
-/

public section

open Bornology Complex MeasureTheory Set

namespace TauCeti.Contour

/-- The winding number of a closed absolutely continuous curve vanishes on every unbounded
component of the complement of its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) {z : ℂ}
    (hz : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) z)) :
    windingNumber γ a b z = 0 := by
  exact hγ.continuousOn.windingNumber_eq_zero_of_unbounded_component_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hw ↦ hγ.exists_int_windingNumber hclosed hw) hz

/-- **The winding number of a closed absolutely continuous curve vanishes outside its filled
hull.** -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_notMem_filledHull
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hz : z ∉ filledHull (γ '' uIcc a b)) :
    windingNumber γ a b z = 0 :=
  hγ.windingNumber_eq_zero_of_unbounded_component hclosed (mt mem_filledHull_iff.mpr hz)

/-- **Outside the filled hull of a continuous closed curve, the winding number of its natural
parametrization vanishes.** Here `naturalParameterization γ (Icc a b) a` runs over
`[0, (eVariationOn γ (Icc a b)).toReal]`. If `γ` has bounded variation and `a ≤ b`, this is the
arclength parametrization; otherwise the parameter interval is `[0, 0]` and the winding number is
`0`. -/
theorem _root_.ContinuousOn.windingNumber_naturalParameterization_eq_zero_of_notMem_filledHull
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hz : z ∉ filledHull (γ '' Icc a b)) :
    windingNumber (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal z = 0 := by
  by_cases hγ : BoundedVariationOn γ (Icc a b)
  swap
  · -- infinite variation: the parameter interval is degenerate
    have htop : eVariationOn γ (Icc a b) = ⊤ := by
      by_contra h
      exact hγ h
    rw [htop, ENNReal.toReal_top, windingNumber_same]
  rcases le_or_gt a b with hab | hab
  swap
  · rw [Icc_eq_empty (not_le.mpr hab), eVariationOn.subsingleton _ subsingleton_empty]
    simp
  have hz' : z ∉ filledHull (naturalParameterization γ (Icc a b) a ''
      uIcc 0 (eVariationOn γ (Icc a b)).toReal) := by
    rwa [uIcc_of_le ENNReal.toReal_nonneg, hγ.image_naturalParameterization_Icc hcont hab]
  exact (hγ.absolutelyContinuousOnInterval_naturalParameterization hcont
      hab).windingNumber_eq_zero_of_notMem_filledHull
    (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab hclosed) hz'

/-- **The winding number vanishes at a point joined to infinity by a ray off the curve.** If the
ray `c ↦ w + c · v` (`0 ≤ c`, `v ≠ 0`) misses the closed absolutely continuous curve, then `w`
lies in an unbounded component of the complement and the winding number about `w` is zero.

This is the form callers can actually discharge: exhibiting one escape ray is elementary, whereas
`AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_unbounded_component` asks for the
component itself. Any
point outside a bounded region the curve encloses -- outside a disc containing the curve, or on the
far side of a line the curve does not cross -- has such a ray. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_ray
    {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) {w v : ℂ} (hv : v ≠ 0)
    (hray : ∀ c : ℝ, 0 ≤ c → w + (c : ℂ) * v ∉ γ '' uIcc a b) :
    windingNumber γ a b w = 0 := by
  have hAconn : IsPreconnected ((fun c : ℝ => w + (c : ℂ) * v) '' Ici 0) :=
    isPreconnected_Ici.image (fun c : ℝ => w + (c : ℂ) * v)
      (Continuous.continuousOn (by fun_prop))
  have hzero : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have hAmem : w ∈ (fun c : ℝ => w + (c : ℂ) * v) '' Ici 0 := ⟨0, hzero, by simp⟩
  have hAsub : (fun c : ℝ => w + (c : ℂ) * v) '' Ici 0 ⊆ (γ '' uIcc a b)ᶜ := by
    rintro _ ⟨c, hc, rfl⟩
    exact hray c hc
  refine hγ.windingNumber_eq_zero_of_unbounded_component hclosed fun hbdd => ?_
  have hsub := hAconn.subset_connectedComponentIn hAmem hAsub
  obtain ⟨r, hr⟩ := (hbdd.subset hsub).subset_closedBall 0
  have hwr : ‖w‖ ≤ r := by simpa using Metric.mem_closedBall.mp (hr ⟨0, hzero, by simp⟩)
  have hrnn : (0 : ℝ) ≤ r := le_trans (norm_nonneg w) hwr
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- Far enough along the ray the norm exceeds `r`, so the ray escapes the ball.
  set c : ℝ := (r + ‖w‖ + 1) / ‖v‖ with hc_def
  have hcnn : 0 ≤ c := by positivity
  have hnorm : ‖(c : ℂ) * v‖ = r + ‖w‖ + 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcnn, hc_def]
    field_simp [hvpos.ne']
  have hle : ‖w + (c : ℂ) * v‖ ≤ r := by
    simpa using Metric.mem_closedBall.mp (hr ⟨c, hcnn, rfl⟩)
  have hge : ‖(c : ℂ) * v‖ ≤ ‖w + (c : ℂ) * v‖ + ‖w‖ := by
    simpa using norm_sub_le (w + (c : ℂ) * v) w
  rw [hnorm] at hge
  linarith

/-- **A closed curve in a set without holes is null-homologous there.** If `filledHull U ⊆ U`,
that is, if every connected component of `ℂ \ U` is unbounded, then every closed absolutely
continuous curve in `U` has winding number zero about every point outside `U`. For open `U`, the
hypothesis is the plane form of the connectedness of the complement of `U` in the Riemann
sphere. -/
theorem _root_.AbsolutelyContinuousOnInterval.isNullHomologous_of_filledHull_subset
    {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b)
    (hγU : MapsTo γ (uIcc a b) U)
    (hU : filledHull U ⊆ U) : IsNullHomologous γ a b U := by
  rw [isNullHomologous_iff]
  intro w hw
  refine hγ.windingNumber_eq_zero_of_unbounded_component hclosed fun hbdd => hw (hU ?_)
  refine (mem_filledHull_iff (K := U)).2 (hbdd.subset (connectedComponentIn_mono w ?_))
  rintro _ hx ⟨t, ht, rfl⟩
  exact hx (hγU ht)

end TauCeti.Contour
