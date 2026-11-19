/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Dimension-zero check for relative volume density

The relative density of any two metrics is one in dimension zero, so both parameter
derivatives vanish for every family of metrics.
-/

public noncomputable section

open Bundle Manifold
open scoped ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω}

/- Both parameter derivatives of relative density vanish in dimension zero, for any family
of metrics. -/
example
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (G : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 0) (x : M) (t : ℝ) :
    deriv (fun s ↦ relativeVolumeDensity g (G s) x) t = 0 ∧
      deriv (deriv (fun s ↦ relativeVolumeDensity g (G s) x)) t = 0 := by
  simp [hE]

end Bundle.ContMDiffRiemannianMetric
