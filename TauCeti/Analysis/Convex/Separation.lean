/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
-- Proof-only: strict separation of a point from an open convex set, and the Riesz representation.
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Separation of points from open convex sets by heights

In a real Hilbert space, a point outside a nonempty open convex set `W` is strictly separated from
`W` by a continuous linear functional (`geometric_hahn_banach_open_point`). By the Riesz
representation, such a functional is a positive multiple of the height `x ↦ ⟪u, x⟫` along a unit
vector `u`. Hence a set whose heights along every unit vector are heights of points of `W` is
contained in `W`.

## Main results

* `Convex.subset_of_image_inner_subset`: a set whose heights along every unit vector are heights
  of points of a nonempty open convex set `W` is contained in `W`.
-/

public section

open Set
open scoped RealInnerProductSpace

/-- **Containment in an open convex set from directional images.** If the heights `⟪u, x⟫` of the
points of `U` along every unit vector `u` are heights of points of a nonempty open convex set `W`,
then `U ⊆ W`: a point outside `W` is strictly separated from it by a continuous linear functional,
which is a positive multiple of the height along a unit vector. -/
theorem Convex.subset_of_image_inner_subset {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {U W : Set E} (hW : Convex ℝ W) (hWo : IsOpen W)
    (hWn : W.Nonempty)
    (hUW : ∀ u : E, ‖u‖ = 1 → (fun x ↦ ⟪u, x⟫) '' U ⊆ (fun x ↦ ⟪u, x⟫) '' W) : U ⊆ W := by
  intro x hx
  by_contra hxW
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hW hWo hxW
  set w := (InnerProductSpace.toDual ℝ E).symm f
  have hfw (y : E) : f y = ⟪w, y⟫ := InnerProductSpace.toDual_symm_apply.symm
  have hw : w ≠ 0 := by
    rintro hw
    obtain ⟨a, ha⟩ := hWn
    simpa [hfw, hw] using hf a ha
  obtain ⟨a, ha, hax⟩ : ⟪‖w‖⁻¹ • w, x⟫ ∈ (fun y ↦ ⟪‖w‖⁻¹ • w, y⟫) '' W :=
    hUW _ (norm_smul_inv_norm (𝕜 := ℝ) hw) (mem_image_of_mem _ hx)
  simp only [real_inner_smul_left] at hax
  have := hf a ha
  rw [hfw, hfw, ← mul_left_cancel₀ (inv_ne_zero (norm_ne_zero_iff.2 hw)) hax] at this
  exact lt_irrefl _ this
