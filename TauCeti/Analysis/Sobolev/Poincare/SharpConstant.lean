/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# Sharp Poincaré constants from extremal functions

Let `S` be a set of Sobolev classes on which the Poincaré inequality `k² ‖u‖² ≤ ‖∇u‖²` holds. If
some `u ∈ S` with `‖u‖ ≠ 0` attains it, `‖∇u‖² = k² ‖u‖²`, then the constant is sharp in both of
its usual forms: `k²` is the greatest `C` with `C ‖u‖² ≤ ‖∇u‖²` on `S`
(`TauCeti.W1p.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_of_eq`), and for `k > 0`, `k⁻¹` is
the least `C ≥ 0` with `‖u‖ ≤ C ‖∇u‖` on `S`
(`TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_eq`).

These turn an inequality together with an explicit extremal function into an optimality
statement, for instance for the one-endpoint Poincaré–Friedrichs constant of an interval
(`TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_singleton_left`).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti.W1p

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [OpensMeasurableSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- If `k² ‖u‖² ≤ ‖∇u‖²` on a set `S` of Sobolev classes and some `u ∈ S` with `‖u‖ ≠ 0` has
`‖∇u‖² = k² ‖u‖²`, then `k²` is the best constant `C` in `C ‖u‖² ≤ ‖∇u‖²` on `S`. -/
theorem isGreatest_mul_norm_value_sq_le_norm_gradient_sq_of_eq {S : Set (W1p mu Omega p)}
    {k : ℝ} (hS : ∀ u ∈ S, k ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2)
    {u : W1p mu Omega p} (hu : u ∈ S) (hu0 : 0 < ‖value u‖ ^ 2)
    (hgu : ‖gradient u‖ ^ 2 = k ^ 2 * ‖value u‖ ^ 2) :
    IsGreatest {C : ℝ | ∀ u ∈ S, C * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2} (k ^ 2) :=
  ⟨hS, fun _ hC ↦ le_of_mul_le_mul_right ((hC u hu).trans hgu.le) hu0⟩

/-- If `k² ‖u‖² ≤ ‖∇u‖²` on a set `S` of Sobolev classes, `k > 0`, and some `u ∈ S` with
`‖u‖ ≠ 0` has `‖∇u‖² = k² ‖u‖²`, then `k⁻¹` is the least constant `C ≥ 0` with `‖u‖ ≤ C ‖∇u‖`
on `S`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_of_eq {S : Set (W1p mu Omega p)} {k : ℝ}
    (hk : 0 < k) (hS : ∀ u ∈ S, k ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2)
    {u : W1p mu Omega p} (hu : u ∈ S) (hu0 : 0 < ‖value u‖ ^ 2)
    (hgu : ‖gradient u‖ ^ 2 = k ^ 2 * ‖value u‖ ^ 2) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ S, ‖value u‖ ≤ C * ‖gradient u‖} k⁻¹ := by
  refine ⟨⟨inv_nonneg.2 hk.le, fun v hv ↦ ?_⟩, fun C hC ↦ ?_⟩
  · rw [inv_mul_eq_div, le_div_iff₀ hk]
    have := hS v hv
    nlinarith [norm_nonneg (value v), norm_nonneg (gradient v)]
  · have hg : ‖gradient u‖ = k * ‖value u‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hk.le (norm_nonneg _)), hgu, mul_pow]
    have h1 := hC.2 u hu
    rw [hg] at h1
    have hpos : 0 < ‖value u‖ := by nlinarith [norm_nonneg (value u)]
    rw [inv_le_iff_one_le_mul₀ hk]
    nlinarith

end TauCeti.W1p
