/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Jet
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Family
import TauCeti.Analysis.Calculus.ContDiff.BilinearJet

/-!
# Scalar curvature of smooth metric families

The scalar curvature of a jointly smooth family of native Riemannian metrics is jointly
continuous in time and space. This follows from the native coordinate two-jet formula.
It provides the closed-slab continuity needed by scalar Ricci-flow comparison.

## References

* P. Topping, *Lectures on the Ricci Flow*, Section 2.3.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Native scalar curvature is jointly continuous for a smooth positive metric family.
No compactness, connectedness, or flow equation is required. -/
theorem continuous_scalarCurvature
    (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
    (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric) :
    Continuous (fun q : ℝ × M ↦ (r q.1).scalarCurvature q.2) := by
  classical
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  let b := Module.finBasis ℝ E
  let V : Set (ℝ × E) := univ ×ˢ (extChartAt I x).target
  have hV : IsOpen V := isOpen_univ.prod (isOpen_extChartAt_target x)
  have hmem : (t, extChartAt I x x) ∈ V := ⟨mem_univ _, mem_extChartAt_target x⟩
  have hmetric : ContDiffOn ℝ ∞
      (fun q : ℝ × E ↦ (g.metric q.1).chartMetric x q.2) V := by
    intro q hq
    have hint : q.2 ∈ interior (range I) := by
      rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ]
      trivial
    have h := g.contMDiffAt_chartMetric x hq.2 hint
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt.contDiffWithinAt
  let F (i j : Fin (Module.finrank ℝ E)) : ℝ × E → ℝ :=
    fun q ↦ (g.metric q.1).chartMetric x q.2 (b i) (b j)
  have hF (i j) : ContDiffOn ℝ 2 (F i j) V :=
    ((hmetric.clm_apply contDiffOn_const).clm_apply contDiffOn_const).of_le (by simp)
  obtain ⟨h₀, h₁, h₂⟩ := b.continuousAt_jets_of_eqOn_contDiffOn
    (fun s z ↦ (r s).toNondegenerateMetric.chartMetric x z) F hV hmem hF
    (fun q _ i j ↦ by simp only [F, hr])
  apply continuousAt_scalarCurvature_of_continuousAt_chartMetric b r _ h₀ h₁ h₂
  rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ]
  trivial

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily
