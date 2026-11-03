/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius

/-! # Bounds and partial sums of formal multilinear series

Taking partial sums of a formal multilinear series commutes with continuous linear maps.
This allows coefficientwise linear operations to pass through finite approximations.
A geometric bound on coefficient norms also gives a comparison of convergence radii, even when
the two series are defined over different normed fields.
-/

public section

section PartialSum

variable {𝕜 E F G : Type*} [Semiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousConstSMul 𝕜 F] [AddCommMonoid G] [Module 𝕜 G]
  [TopologicalSpace G] [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]

/-- A partial sum of the composed series is the image of the original partial sum. -/
@[simp]
theorem ContinuousLinearMap.compFormalMultilinearSeries_partialSum (f : F →L[𝕜] G)
    (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) :
    (f.compFormalMultilinearSeries p).partialSum n x = f (p.partialSum n x) := by
  simp [FormalMultilinearSeries.partialSum]

end PartialSum

namespace FormalMultilinearSeries

open scoped NNReal ENNReal

variable {𝕜 𝕜' E E' F F' : Type*} [NontriviallyNormedField 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜' F']

/-- If the coefficient norms of `q` are bounded by those of `p` times `c ^ n`, every radius
whose product with `c` lies below the radius of `p` is a lower bound for the radius of `q`.
The series may have different scalar fields and different source and target spaces. -/
theorem le_radius_of_norm_le_mul_pow {p : FormalMultilinearSeries 𝕜 E F}
    {q : FormalMultilinearSeries 𝕜' E' F'} {c r : ℝ≥0}
    (h : ∀ n, ‖q n‖ ≤ (c : ℝ) ^ n * ‖p n‖)
    (hr : ((c * r : ℝ≥0) : ℝ≥0∞) < p.radius) : (r : ℝ≥0∞) ≤ q.radius := by
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  refine le_radius_of_bound _ C fun n ↦ ?_
  calc
    ‖q n‖ * (r : ℝ) ^ n ≤ (c : ℝ) ^ n * ‖p n‖ * (r : ℝ) ^ n := by gcongr; exact h n
    _ = ‖p n‖ * ((c * r : ℝ≥0) : ℝ) ^ n := by push_cast; ring
    _ ≤ C := hC n

end FormalMultilinearSeries
