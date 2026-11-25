/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable
public import TauCeti.Dynamics.Billiard.ClosedCylinder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Chords and exit points of a convex table

Let `γ` be a convex table with unit tangent `τ`. A ball leaving `γ(s)` at the angle `δ ∈ (0, π)`
from `τ(s)` travels along the ray `{γ(s) + r exp(iδ) τ(s) : r > 0}`, which meets the curve again in
exactly one point `γ(s₁)` with `s < s₁ < s + ℓ`. This file defines the exit parameter
`s₁ = TauCeti.ConvexTable.exitParam T s δ` and proves:

* `TauCeti.ConvexTable.exitParam_mem_Ioo`: `s < s₁ < s + ℓ`;
* `TauCeti.ConvexTable.apply_exitParam_sub`: `γ(s₁) − γ(s) = r exp(iδ) τ(s)` with
  `r = ‖γ(s₁) − γ(s)‖ > 0`;
* `TauCeti.ConvexTable.eq_exitParam`: uniqueness, every `t ∈ (s, s + ℓ)` with `γ(t)` on the ray
  is `s₁`;
* `TauCeti.ConvexTable.continuousOn_exitParam`: `s₁` is continuous in `(s, δ)` on the closed strip
  `ℝ × [0, π]`, where it is extended by `s₁ = s` at `δ = 0` and `s₁ = s + ℓ` at `δ = π`
  (`exitParam_zero`, `exitParam_pi`), so `s₁ → s` as `δ → 0` and `s₁ → s + ℓ` as `δ → π`,
  locally uniformly in `s` (`tendsto_exitParam_zero`, `tendsto_exitParam_pi`);
* `TauCeti.ConvexTable.strictMonoOn_exitParam`: `s₁` is strictly increasing in `δ ∈ [0, π]`.

The exit parameter is the next collision parameter `TauCeti.StrictConvexBilliardTable.nextParam`
of the billiard table `T.toStrictConvexBilliardTable` at the tangential component `cos δ`, extended
to the closed strip (`TauCeti.StrictConvexBilliardTable.closedNextParam`); the outgoing direction
`cos δ τ + sin δ i τ` of that table is `exp(iδ) τ`.

## References

* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Complex
open scoped ComplexConjugate

namespace TauCeti

namespace ConvexTable

attribute [local instance] Complex.finrank_real_complex_fact

variable {k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (T : ConvexTable k ℓ)

/-- The **exit parameter** `s₁` of the chord leaving `γ(s)` at the angle `δ` from the unit tangent:
for `δ ∈ (0, π)`, the unique `s₁ ∈ (s, s + ℓ)` with `γ(s₁)` on the ray from `γ(s)` in the direction
`exp(iδ) τ(s)` (`TauCeti.ConvexTable.eq_exitParam`). It is `s` at `δ = 0` and `s + ℓ` at `δ = π`,
the continuous extension (`TauCeti.ConvexTable.continuousOn_exitParam`). -/
def exitParam (s δ : ℝ) : ℝ := T.toStrictConvexBilliardTable.closedNextParam s (Real.cos δ)

theorem exitParam_def (s δ : ℝ) :
    T.exitParam s δ = T.toStrictConvexBilliardTable.closedNextParam s (Real.cos δ) := (rfl)

private theorem cos_mem_Ioo {δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) : Real.cos δ ∈ Ioo (-1) 1 := by
  rw [← Real.cos_pi, ← Real.cos_zero]
  exact ⟨Real.strictAntiOn_cos ⟨hδ.1.le, hδ.2.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hδ.2,
    Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hδ.1.le, hδ.2.le⟩ hδ.1⟩

theorem exitParam_eq_nextParam {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    T.exitParam s δ = T.toStrictConvexBilliardTable.nextParam s (Real.cos δ) :=
  T.toStrictConvexBilliardTable.closedNextParam_of_mem_Ioo (cos_mem_Ioo hδ)

@[simp]
theorem exitParam_zero (s : ℝ) : T.exitParam s 0 = s := by
  simp [exitParam_def]

@[simp]
theorem exitParam_pi (s : ℝ) : T.exitParam s Real.pi = s + ℓ := by
  simp [exitParam_def]

/-- The exit parameter lies strictly between `s` and `s + ℓ`. -/
theorem exitParam_mem_Ioo {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    T.exitParam s δ ∈ Ioo s (s + ℓ) := by
  rw [exitParam_eq_nextParam T hδ]
  simpa using T.toStrictConvexBilliardTable.nextParam_mem_Ioo (s := s) (cos_mem_Ioo hδ)

/-- The outgoing direction of the billiard table at the tangential component `cos δ`,
`0 ≤ δ ≤ π`, is `exp(iδ) τ(s)`. -/
theorem outgoingDir_cos {s δ : ℝ} (hδ : δ ∈ Icc 0 Real.pi) :
    T.toStrictConvexBilliardTable.outgoingDir s (Real.cos δ) = exp (δ * I) * deriv T s := by
  rw [StrictConvexBilliardTable.outgoingDir_def, ← Real.sin_eq_sqrt_one_sub_cos_sq hδ.1 hδ.2,
    Complex.rightAngleRotation, coe_toStrictConvexBilliardTable, exp_mul_I, real_smul,
    real_smul, ← ofReal_cos, ← ofReal_sin]
  ring

/-- **The chord lies on the ray.** For `0 < δ < π`, `γ(s₁) − γ(s) = r exp(iδ) τ(s)` with
`r = ‖γ(s₁) − γ(s)‖ > 0`. -/
theorem apply_exitParam_sub {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    T (T.exitParam s δ) - T s = ‖T (T.exitParam s δ) - T s‖ • (exp (δ * I) * deriv T s) := by
  rw [← outgoingDir_cos T ⟨hδ.1.le, hδ.2.le⟩, exitParam_eq_nextParam T hδ]
  simpa using T.toStrictConvexBilliardTable.sub_eq_norm_smul_outgoingDir (s := s) (cos_mem_Ioo hδ)

theorem apply_exitParam_ne {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) : T (T.exitParam s δ) ≠ T s := by
  rw [exitParam_eq_nextParam T hδ]
  simpa using T.toStrictConvexBilliardTable.apply_nextParam_ne (s := s) (cos_mem_Ioo hδ)

/-- **Uniqueness of the exit point.** For `0 < δ < π`, a parameter `t ∈ (s, s + ℓ)` whose point
`γ(t)` lies on the line through `γ(s)` in the direction `exp(iδ) τ(s)` is the exit parameter. -/
theorem eq_exitParam {s δ t r : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) (ht : t ∈ Ioo s (s + ℓ))
    (h : T t = T s + r • (exp (δ * I) * deriv T s)) : t = T.exitParam s δ := by
  rw [exitParam_eq_nextParam T hδ]
  refine T.toStrictConvexBilliardTable.eq_nextParam_of_areaForm_eq_zero (cos_mem_Ioo hδ)
    (by simpa using ht) ?_
  rw [outgoingDir_cos T ⟨hδ.1.le, hδ.2.le⟩, coe_toStrictConvexBilliardTable, h,
    add_sub_cancel_left, map_smul, Orientation.areaForm_apply_self, smul_zero]

/-- **Continuity of the exit parameter** on the closed strip `ℝ × [0, π]`. -/
theorem continuousOn_exitParam :
    ContinuousOn (fun p : ℝ × ℝ => T.exitParam p.1 p.2) (univ ×ˢ Icc 0 Real.pi) := by
  refine T.toStrictConvexBilliardTable.continuousOn_closedNextParam.comp
    (continuous_fst.prodMk (Real.continuous_cos.comp continuous_snd)).continuousOn ?_
  rintro ⟨s, δ⟩ -
  refine ⟨mem_univ _, ?_⟩
  exact ⟨Real.neg_one_le_cos δ, Real.cos_le_one δ⟩

/-- **The exit parameter is strictly increasing in the angle** on `[0, π]`. -/
theorem strictMonoOn_exitParam (s : ℝ) : StrictMonoOn (T.exitParam s) (Icc 0 Real.pi) :=
  fun _ ha _ hb hab => T.toStrictConvexBilliardTable.strictAntiOn_closedNextParam s
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    (Real.strictAntiOn_cos ha hb hab)

/-- As `δ → 0` the exit parameter tends to `s`, locally uniformly in `s`: jointly in `(s, δ)`. -/
theorem tendsto_exitParam_zero (s : ℝ) :
    Tendsto (fun p : ℝ × ℝ => T.exitParam p.1 p.2) (𝓝[univ ×ˢ Icc 0 Real.pi] (s, 0)) (𝓝 s) := by
  simpa using (T.continuousOn_exitParam (s, 0) ⟨mem_univ _, le_rfl, Real.pi_pos.le⟩).tendsto

/-- As `δ → π` the exit parameter tends to `s + ℓ`, locally uniformly in `s`: jointly in
`(s, δ)`. -/
theorem tendsto_exitParam_pi (s : ℝ) :
    Tendsto (fun p : ℝ × ℝ => T.exitParam p.1 p.2) (𝓝[univ ×ˢ Icc 0 Real.pi] (s, Real.pi))
      (𝓝 (s + ℓ)) := by
  simpa using
    (T.continuousOn_exitParam (s, Real.pi) ⟨mem_univ _, Real.pi_pos.le, le_rfl⟩).tendsto

/-- On the circle of radius `R` the exit parameter is `s + 2Rδ`: the chord leaving at the angle
`δ` subtends the arc `2δ`. -/
theorem exitParam_circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] (s : ℝ) {δ : ℝ}
    (hδ : δ ∈ Icc 0 Real.pi) : (circle R).exitParam s δ = s + 2 * R * δ := by
  rcases eq_or_lt_of_le hδ.1 with rfl | h0
  · simp
  rcases eq_or_lt_of_le hδ.2 with rfl | hπ
  · rw [exitParam_pi]
    ring
  rw [exitParam_eq_nextParam _ ⟨h0, hπ⟩, toStrictConvexBilliardTable_circle,
    StrictConvexBilliardTable.nextParam_circle (cos_mem_Ioo ⟨h0, hπ⟩),
    Real.arccos_cos hδ.1 hδ.2]

end ConvexTable

end TauCeti
