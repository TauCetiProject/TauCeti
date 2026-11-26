/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable
public import TauCeti.Dynamics.Billiard.ClosedCylinder
public import TauCeti.Dynamics.Billiard.ConvexTable.Region
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Chords and exit points of a convex table

Let `γ` be a convex table with unit tangent `τ`. A ball leaving `γ(s)` at the angle `δ ∈ (0, π)`
from `τ(s)` travels along the ray `{γ(s) + r exp(iδ) τ(s) : r > 0}`, which meets the curve again in
exactly one point `γ(s₁)` with `s < s₁ < s + ℓ`. This file defines the exit parameter
`s₁ = TauCeti.ConvexTable.exitParam T s δ` and proves:

* `TauCeti.ConvexTable.exitParam_mem_Ioo`: `s < s₁ < s + ℓ`;
* `TauCeti.ConvexTable.apply_exitParam_sub_eq_norm_smul`: `γ(s₁) − γ(s) = r exp(iδ) τ(s)` with
  `r = ‖γ(s₁) − γ(s)‖ > 0`;
* `TauCeti.ConvexTable.eq_exitParam`: uniqueness, every `t ∈ (s, s + ℓ)` with `γ(t)` on the ray
  is `s₁`;
* `TauCeti.ConvexTable.setOf_mem_range_ray_eq`: the open ray meets the image of `γ` exactly at
  `γ(s₁)`;
* `TauCeti.ConvexTable.openSegment_exitParam_subset_interior_region`: the open chord between
  `γ(s)` and `γ(s₁)` lies in the interior of the region `Ω` bounded by `γ`, so the ray points into
  the interior (`TauCeti.ConvexTable.eventually_add_smul_mem_interior_region`);
* `TauCeti.ConvexTable.continuous_exitParam`: `s₁` is continuous in `(s, δ)`, where it is
  extended by `s₁ = s` at `δ = 0` and `s₁ = s + ℓ` at `δ = π` (`exitParam_zero`, `exitParam_pi`),
  so `s₁ → s` as `δ → 0` and `s₁ → s + ℓ` as `δ → π`, locally uniformly in `s`
  (`tendsto_exitParam_zero`, `tendsto_exitParam_pi`);
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
the continuous extension (`TauCeti.ConvexTable.continuous_exitParam`). -/
def exitParam (s δ : ℝ) : ℝ := T.toStrictConvexBilliardTable.closedNextParam s (Real.cos δ)

theorem exitParam_def (s δ : ℝ) :
    T.exitParam s δ = T.toStrictConvexBilliardTable.closedNextParam s (Real.cos δ) := (rfl)

theorem exitParam_eq_nextParam {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    T.exitParam s δ = T.toStrictConvexBilliardTable.nextParam s (Real.cos δ) :=
  T.toStrictConvexBilliardTable.closedNextParam_of_mem_Ioo (Real.mapsTo_cos_Ioo hδ)

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
  simpa using T.toStrictConvexBilliardTable.nextParam_mem_Ioo (s := s) (Real.mapsTo_cos_Ioo hδ)

/-- The outgoing direction of the billiard table at the tangential component `cos δ`,
`0 ≤ δ ≤ π`, is `exp(iδ) τ(s)`. -/
theorem toStrictConvexBilliardTable_outgoingDir_cos {s δ : ℝ} (hδ : δ ∈ Icc 0 Real.pi) :
    T.toStrictConvexBilliardTable.outgoingDir s (Real.cos δ) = exp (δ * I) * deriv T s := by
  rw [StrictConvexBilliardTable.outgoingDir_def, ← Real.sin_eq_sqrt_one_sub_cos_sq hδ.1 hδ.2,
    Complex.rightAngleRotation, coe_toStrictConvexBilliardTable, exp_mul_I, real_smul,
    real_smul, ← ofReal_cos, ← ofReal_sin]
  ring

/-- **The chord lies on the ray.** For `0 < δ < π`, `γ(s₁) − γ(s) = r exp(iδ) τ(s)` with
`r = ‖γ(s₁) − γ(s)‖ > 0`. -/
theorem apply_exitParam_sub_eq_norm_smul {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    T (T.exitParam s δ) - T s = ‖T (T.exitParam s δ) - T s‖ • (exp (δ * I) * deriv T s) := by
  rw [← toStrictConvexBilliardTable_outgoingDir_cos T ⟨hδ.1.le, hδ.2.le⟩,
    exitParam_eq_nextParam T hδ]
  simpa using
    T.toStrictConvexBilliardTable.sub_eq_norm_smul_outgoingDir (s := s) (Real.mapsTo_cos_Ioo hδ)

theorem apply_exitParam_ne {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) : T (T.exitParam s δ) ≠ T s := by
  rw [exitParam_eq_nextParam T hδ]
  simpa using T.toStrictConvexBilliardTable.apply_nextParam_ne (s := s) (Real.mapsTo_cos_Ioo hδ)

/-- **Uniqueness of the exit point.** For `0 < δ < π`, a parameter `t ∈ (s, s + ℓ)` whose point
`γ(t)` lies on the line through `γ(s)` in the direction `exp(iδ) τ(s)` is the exit parameter. -/
theorem eq_exitParam {s δ t r : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) (ht : t ∈ Ioo s (s + ℓ))
    (h : T t = T s + r • (exp (δ * I) * deriv T s)) : t = T.exitParam s δ := by
  rw [exitParam_eq_nextParam T hδ]
  refine T.toStrictConvexBilliardTable.eq_nextParam_of_areaForm_eq_zero (Real.mapsTo_cos_Ioo hδ)
    (by simpa using ht) ?_
  rw [toStrictConvexBilliardTable_outgoingDir_cos T ⟨hδ.1.le, hδ.2.le⟩,
    coe_toStrictConvexBilliardTable, h, add_sub_cancel_left, map_smul,
    Orientation.areaForm_apply_self, smul_zero]

/-- **The ray meets the curve exactly once.** For `0 < δ < π`, the open ray
`{γ(s) + r exp(iδ) τ(s) : r > 0}` meets the image of `γ` exactly at the exit point `γ(s₁)`. -/
theorem setOf_mem_range_ray_eq {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    {z | z ∈ range T ∧ ∃ r : ℝ, 0 < r ∧ z = T s + r • (exp (δ * I) * deriv T s)} =
      {T (T.exitParam s δ)} := by
  ext z
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨⟨t, rfl⟩, r, hr, hz⟩
    -- The representative `t' ∈ (s, s + ℓ]` of `t` is not `s + ℓ`, since `γ(t) ≠ γ(s)`.
    set t' := toIocMod (Fact.out : 0 < ℓ) s t with ht'_def
    have ht' : T t' = T t := by
      rw [ht'_def, ← self_sub_toIocDiv_zsmul]
      exact T.periodic.sub_zsmul_eq _
    have hne : T t ≠ T s := by
      rw [hz, Ne, add_eq_left, smul_eq_zero, not_or]
      exact ⟨hr.ne', mul_ne_zero (exp_ne_zero _) (T.deriv_ne_zero s)⟩
    have hmem := toIocMod_mem_Ioc (Fact.out : 0 < ℓ) s t
    have hlt : t' < s + ℓ := hmem.2.lt_of_ne fun h => hne <| by
      rw [← ht', ht'_def, h, apply_add_period]
    rw [← ht', ← T.eq_exitParam hδ ⟨hmem.1, hlt⟩ (ht'.trans hz)]
  · rintro rfl
    refine ⟨mem_range_self _, _,
      norm_pos_iff.2 (sub_ne_zero.2 (T.apply_exitParam_ne (s := s) hδ)), ?_⟩
    rw [← T.apply_exitParam_sub_eq_norm_smul hδ, add_sub_cancel]

/-- **The open chord lies in the interior of the region.** For `0 < δ < π`, the open segment
between `γ(s)` and the exit point `γ(s₁)` lies in the interior of the region `Ω` bounded by `γ`. -/
theorem openSegment_exitParam_subset_interior_region {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    openSegment ℝ (T s) (T (T.exitParam s δ)) ⊆ interior T.region :=
  T.strictConvex_region.openSegment_subset (T.apply_mem_region s) (T.apply_mem_region _)
    (T.apply_exitParam_ne hδ).symm

/-- **The ray points into the interior of the region.** For `0 < δ < π`, the points
`γ(s) + r exp(iδ) τ(s)` with `r > 0` small lie in the interior of `Ω`. -/
theorem eventually_add_smul_mem_interior_region {s δ : ℝ} (hδ : δ ∈ Ioo 0 Real.pi) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), T s + r • (exp (δ * I) * deriv T s) ∈ interior T.region := by
  set d := ‖T (T.exitParam s δ) - T s‖
  have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 (T.apply_exitParam_ne (s := s) hδ))
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr
  have hmem := (openSegment_subset_iff ℝ).1
    (T.openSegment_exitParam_subset_interior_region (s := s) hδ)
    (1 - r / d) (r / d) (sub_pos.2 ((div_lt_one hd).2 hr.2)) (div_pos hr.1 hd) (sub_add_cancel _ _)
  convert hmem using 1
  rw [eq_add_of_sub_eq' (T.apply_exitParam_sub_eq_norm_smul (s := s) hδ), smul_add, smul_smul,
    div_mul_cancel₀ _ hd.ne']
  module

/-- **Continuity of the exit parameter** in `(s, δ)`. -/
theorem continuous_exitParam : Continuous (fun p : ℝ × ℝ => T.exitParam p.1 p.2) :=
  T.toStrictConvexBilliardTable.continuousOn_closedNextParam.comp_continuous
    (continuous_fst.prodMk (Real.continuous_cos.comp continuous_snd))
    fun _ => ⟨mem_univ _, Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- **The exit parameter is strictly increasing in the angle** on `[0, π]`. -/
theorem strictMonoOn_exitParam (s : ℝ) : StrictMonoOn (T.exitParam s) (Icc 0 Real.pi) :=
  fun _ ha _ hb hab => T.toStrictConvexBilliardTable.strictAntiOn_closedNextParam s
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    (Real.strictAntiOn_cos ha hb hab)

/-- As `δ → 0` the exit parameter tends to `s`, locally uniformly in `s`: jointly in `(s, δ)`. -/
theorem tendsto_exitParam_zero (s : ℝ) :
    Tendsto (fun p : ℝ × ℝ => T.exitParam p.1 p.2) (𝓝 (s, 0)) (𝓝 s) := by
  simpa using T.continuous_exitParam.tendsto (s, 0)

/-- As `δ → π` the exit parameter tends to `s + ℓ`, locally uniformly in `s`: jointly in
`(s, δ)`. -/
theorem tendsto_exitParam_pi (s : ℝ) :
    Tendsto (fun p : ℝ × ℝ => T.exitParam p.1 p.2) (𝓝 (s, Real.pi)) (𝓝 (s + ℓ)) := by
  simpa using T.continuous_exitParam.tendsto (s, Real.pi)

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
    StrictConvexBilliardTable.nextParam_circle (Real.mapsTo_cos_Ioo ⟨h0, hπ⟩),
    Real.arccos_cos hδ.1 hδ.2]

end ConvexTable

end TauCeti
