/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-!
# Integral curves on open forward rays

An integral curve defined on an open ray containing zero is a restriction of the maximal
integral curve with the same initial value. These comparisons allow asymptotic results about
maximal curves to be applied to a prescribed forward trajectory, after moving its time origin
into the interior of its domain.
-/

public section

open Set
open scoped ContDiff Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {a : ℝ} {x : M}

/-- A curve on an open forward ray containing zero supplies existence on that whole ray. -/
theorem IsMIntegralCurveOn.Ioi_subset_maximalIntegralCurveInterval
    (hγ : IsMIntegralCurveOn γ v (Ioi a)) (ha : a < 0) (hx : γ 0 = x) :
    Ioi a ⊆ maximalIntegralCurveInterval v x := by
  intro t ht
  have hcurve : IsMIntegralCurveOn γ v (Ioo a (max t 0 + 1)) := hγ.mono fun _ h ↦ h.1
  exact hcurve.subset_maximalIntegralCurveInterval
    ⟨ha, by linarith [le_max_right t 0]⟩ hx ⟨ht, by linarith [le_max_left t 0]⟩

/-- On an open forward ray containing zero, a prescribed integral curve agrees with the maximal
curve with the same initial value. -/
theorem IsMIntegralCurveOn.eqOn_maximalIntegralCurve_Ioi [T2Space M] [IsManifold I 1 M]
    [BoundarylessManifold I M]
    (hγ : IsMIntegralCurveOn γ v (Ioi a))
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ha : a < 0) (hx : γ 0 = x) :
    EqOn (maximalIntegralCurve v x) γ (Ioi a) := by
  intro t ht
  have hcurve : IsMIntegralCurveOn γ v (Ioo a (max t 0 + 1)) := hγ.mono fun _ h ↦ h.1
  exact hcurve.eqOn_maximalIntegralCurve hv
    ⟨ha, by linarith [le_max_right t 0]⟩ hx ⟨ht, by linarith [le_max_left t 0]⟩
