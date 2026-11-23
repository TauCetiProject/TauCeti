/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The exterior of a closed ball is path-connected

In a real normed space of dimension at least two the complement of a closed ball is path-connected:
it is the image of the product of the unit sphere with the ray `(r, ∞)` of radii exceeding the
ball's under the polar-coordinate map `(u, t) ↦ x + t • u`. By Hahn–Banach separation, every point
outside the union of two closed balls can be pushed along a ray staying in two closed half-spaces
avoiding both balls into the exterior of a larger ball containing them, so the complement of the
union of two closed balls is also path-connected.

Every unbounded complementary component of a bounded set meets the exterior of any closed ball
containing that set. Connectedness of the exterior therefore forces all such components to
coincide. This uniqueness result and the corresponding filled-hull alternative are proved in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

## Main results

* `TauCeti.isPathConnected_compl_closedBall` — the exterior of a closed ball is path-connected in
  a real normed space of dimension at least two.
* `TauCeti.isPathConnected_compl_union_closedBall` — the exterior of a union of two closed balls
  is path-connected in a real normed space of dimension at least two.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The exterior of a closed ball is path-connected** in a real normed space of dimension at
least two. -/
theorem isPathConnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPathConnected (closedBall x r)ᶜ := by
  rcases lt_or_ge r 0 with hr | hr
  · simpa [closedBall_eq_empty.mpr hr] using isPathConnected_univ
  have hIoi : IsPathConnected (Ioi r) := (convex_Ioi r).isPathConnected nonempty_Ioi
  convert ((isPathConnected_sphere h 0 zero_le_one).prod hIoi).image
    (f := fun p : E × ℝ => x + p.2 • p.1) (by fun_prop)
  ext w
  simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le, mem_image, mem_prod,
    mem_sphere_zero_iff_norm, mem_Ioi, Prod.exists]
  refine ⟨fun hw => ?_, ?_⟩
  · have hw' : w - x ≠ 0 := norm_pos_iff.mp (hr.trans_lt hw)
    exact ⟨‖w - x‖⁻¹ • (w - x), ‖w - x‖, ⟨by simp [norm_smul, hw'], hw⟩,
      by simp [smul_smul, hw']⟩
  · rintro ⟨u, t, ⟨hu, ht⟩, rfl⟩
    simpa [norm_smul, hu, abs_of_nonneg (hr.trans ht.le)] using ht

/-- **The exterior of a union of two closed balls is path-connected** in a real normed space of
dimension at least two. -/
theorem isPathConnected_compl_union_closedBall (h : 1 < Module.rank ℝ E) (x₁ x₂ : E) (r₁ r₂ : ℝ) :
    IsPathConnected (closedBall x₁ r₁ ∪ closedBall x₂ r₂)ᶜ := by
  rcases lt_or_ge r₁ 0 with hr₁ | hr₁
  · simpa [closedBall_eq_empty.mpr hr₁] using isPathConnected_compl_closedBall h x₂ r₂
  rcases lt_or_ge r₂ 0 with hr₂ | _hr₂
  · simpa [closedBall_eq_empty.mpr hr₂] using isPathConnected_compl_closedBall h x₁ r₁
  have : Nontrivial E := rank_pos_iff_nontrivial.mp (zero_lt_one.trans h)
  let U : Set E := (closedBall x₁ r₁ ∪ closedBall x₂ r₂)ᶜ
  let R : ℝ := max (‖x₁‖ + r₁) (‖x₂‖ + r₂)
  have hR_nonneg : 0 ≤ R := le_trans (add_nonneg (norm_nonneg x₁) hr₁) (le_max_left _ _)
  have hRU : (closedBall (0 : E) R)ᶜ ⊆ U := by
    intro w hw
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le] at hw
    rw [mem_compl_iff, mem_union, not_or, mem_closedBall, mem_closedBall, not_le, not_le]
    refine ⟨?_, ?_⟩
    · have := (le_max_left (‖x₁‖ + r₁) (‖x₂‖ + r₂)).trans_lt hw
      have htri := norm_le_norm_add_norm_sub' w x₁
      rw [← dist_eq_norm] at htri
      linarith
    · have := (le_max_right (‖x₁‖ + r₁) (‖x₂‖ + r₂)).trans_lt hw
      have htri := norm_le_norm_add_norm_sub' w x₂
      rw [← dist_eq_norm] at htri
      linarith
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : E)
  let p₀ : E := ((R + 1) / ‖u₀‖) • u₀
  have hp₀R : p₀ ∈ (closedBall (0 : E) R)ᶜ := by
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le, norm_smul,
      Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu₀)]
    linarith
  refine ⟨p₀, hRU hp₀R, fun z hz => ?_⟩
  rw [mem_compl_iff, mem_union, not_or] at hz
  obtain ⟨f₁, c₁, hfz₁, hfc₁⟩ := geometric_hahn_banach_point_closed (convex_closedBall x₁ r₁)
    isClosed_closedBall hz.1
  obtain ⟨f₂, c₂, hfz₂, hfc₂⟩ := geometric_hahn_banach_point_closed (convex_closedBall x₂ r₂)
    isClosed_closedBall hz.2
  -- Find a nonzero vector `v₀` in `ker f₁`, then orient `v = ±v₀` so `f₂ v ≤ 0`.
  obtain ⟨v₀, hv₀_ne, hv₀_f₁⟩ : ∃ v₀ : E, v₀ ≠ 0 ∧ f₁ v₀ = 0 := by
    by_cases hne : ∃ u : E, f₁ u ≠ 0
    · obtain ⟨u, hu⟩ := hne
      have htop : Submodule.span ℝ ({u} : Set E) ≠ ⊤ := by
        intro hspan
        have hrank : Module.rank ℝ E ≤ 1 := by
          rw [← rank_top ℝ E, ← hspan]
          exact (rank_span_le ({u} : Set E)).trans (by simp)
        exact h.not_ge hrank
      obtain ⟨w, hw⟩ := not_forall.mp (mt Submodule.eq_top_iff'.mpr htop)
      refine ⟨w - (f₁ w / f₁ u) • u, ?_, ?_⟩
      · intro h0
        apply hw
        rw [sub_eq_zero.mp h0]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
      · simp [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu]
    · push Not at hne
      exact ⟨u₀, hu₀, hne u₀⟩
  obtain ⟨v, hv_ne, hv_f₁, hv_f₂⟩ : ∃ v : E, v ≠ 0 ∧ f₁ v ≤ 0 ∧ f₂ v ≤ 0 := by
    rcases le_total (f₂ v₀) 0 with h2 | h2
    · exact ⟨v₀, hv₀_ne, hv₀_f₁.le, h2⟩
    · exact ⟨-v₀, neg_ne_zero.mpr hv₀_ne, by simp [hv₀_f₁], by simpa using h2⟩
  let T : ℝ := (R + ‖z‖ + 1) / ‖v‖
  have hT_pos : 0 < T := div_pos (by linarith [hR_nonneg, norm_nonneg z]) (norm_pos_iff.mpr hv_ne)
  have hzT_R : z + T • v ∈ (closedBall (0 : E) R)ᶜ := by
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]
    have hnorm : T * ‖v‖ = R + ‖z‖ + 1 := by
      dsimp only [T]
      exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv_ne)
    have htri := norm_le_norm_add_norm_sub' (T • v) (-z)
    rw [sub_neg_eq_add, add_comm (T • v) z, norm_smul, Real.norm_of_nonneg hT_pos.le,
      norm_neg, hnorm] at htri
    linarith
  have hjoin_ray : JoinedIn U z (z + T • v) := by
    refine ⟨{ toFun := fun t => z + ((t : ℝ) * T) • v
              continuous_toFun := by fun_prop
              source' := by simp
              target' := by simp }, fun t => ?_⟩
    have ht0 : 0 ≤ (t : ℝ) * T := mul_nonneg t.property.1 hT_pos.le
    rw [mem_compl_iff, mem_union, not_or]
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · have hc := hfc₁ _ h1
      have hf_ray : f₁ (z + ((t : ℝ) * T) • v) < c₁ := by
        calc f₁ (z + ((t : ℝ) * T) • v) = f₁ z + ((t : ℝ) * T) * f₁ v := by simp [smul_eq_mul]
          _ ≤ f₁ z := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht0 hv_f₁)
          _ < c₁ := hfz₁
      change f₁ (z + ((t : ℝ) * T) • v) < c₁ at hf_ray
      change c₁ < f₁ (z + ((t : ℝ) * T) • v) at hc
      linarith
    · have hc := hfc₂ _ h2
      have hf_ray : f₂ (z + ((t : ℝ) * T) • v) < c₂ := by
        calc f₂ (z + ((t : ℝ) * T) • v) = f₂ z + ((t : ℝ) * T) * f₂ v := by simp [smul_eq_mul]
          _ ≤ f₂ z := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht0 hv_f₂)
          _ < c₂ := hfz₂
      change f₂ (z + ((t : ℝ) * T) • v) < c₂ at hf_ray
      change c₂ < f₂ (z + ((t : ℝ) * T) • v) at hc
      linarith
  exact ((hjoin_ray.trans ((isPathConnected_compl_closedBall h 0 R).joinedIn
    (z + T • v) hzT_R p₀ hp₀R |>.mono hRU)).symm)

end TauCeti
