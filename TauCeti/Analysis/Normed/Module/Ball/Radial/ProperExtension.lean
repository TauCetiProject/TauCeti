/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Proper radial extension of a map from a closed ball

Let `f : E → F` be continuous on the closed ball of radius `r > 0` about `x₀` in a proper real
normed space `E`, and suppose that on the sphere of radius `r` it stays at distance at least
`δ > 0` from `f x₀`. Extending `f` radially, linearly in the distance from `x₀` along each ray,

`g x = f x₀ + (dist x x₀ / r) • (f y - f x₀)` for `dist x x₀ ≥ r`,

where `y = TauCeti.centeredRadialRetraction x₀ r x` is the point of the sphere on the ray through
`x`, gives a proper map `g : E → F` which agrees with `f` on the closed ball and stays at distance
at least `δ` from `f x₀` outside the open ball. The growth of `g` along the rays makes it proper.

This is how a map defined near a point is replaced by a proper map with the same local behaviour,
so that a degree, a sum of local indices over a fibre, is defined for it.

## Main results

* `ContinuousOn.exists_isProperMap_eqOn_closedBall`: the proper radial extension.
-/

public section

open Metric Set TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Proper radial extension.** If `f` is continuous on the closed ball of radius `r > 0` about
`x₀` and stays at distance at least `δ > 0` from `f x₀` on its boundary sphere, then `f` agrees on
the closed ball with a proper continuous map `g` which stays at distance at least `δ` from `f x₀`
outside the open ball. Explicitly, `g x = f x₀ + (dist x x₀ / r) • (f y - f x₀)` outside the ball,
where `y` is the radial retraction of `x` onto the closed ball. -/
theorem ContinuousOn.exists_isProperMap_eqOn_closedBall {f : E → F} {x₀ : E} {r δ : ℝ}
    (hf : ContinuousOn f (closedBall x₀ r)) (hr : 0 < r) (hδ : 0 < δ)
    (hfδ : ∀ x ∈ sphere x₀ r, δ ≤ ‖f x - f x₀‖) :
    ∃ g : C(E, F), IsProperMap g ∧ EqOn g f (closedBall x₀ r) ∧
      ∀ x, r ≤ dist x x₀ → δ ≤ ‖g x - f x₀‖ := by
  set s : E → ℝ := fun x ↦ max 1 (dist x x₀ / r) with hs
  have hs1 (x : E) : 1 ≤ s x := le_max_left _ _
  have hsc : Continuous s :=
    continuous_const.max ((continuous_id.dist continuous_const).div_const r)
  have hfρ : Continuous fun x ↦ f (centeredRadialRetraction x₀ r x) :=
    hf.comp_continuous (lipschitzWith_centeredRadialRetraction hr.le).continuous
      (centeredRadialRetraction_mem_closedBall hr.le)
  let g : C(E, F) :=
    ⟨fun x ↦ f x₀ + s x • (f (centeredRadialRetraction x₀ r x) - f x₀),
      continuous_const.add (hsc.smul (hfρ.sub continuous_const))⟩
  have hg (x : E) : g x = f x₀ + s x • (f (centeredRadialRetraction x₀ r x) - f x₀) := rfl
  -- Outside the open ball, `g x - f x₀` is `s x` times the value of `f - f x₀` at the point of the
  -- sphere on the ray through `x`.
  have hout (x : E) (hx : r ≤ dist x x₀) : s x * δ ≤ ‖g x - f x₀‖ := by
    have hmem : centeredRadialRetraction x₀ r x ∈ sphere x₀ r := by
      rw [mem_sphere, dist_centeredRadialRetraction hr.le, min_eq_right hx]
    rw [hg, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (zero_le_one.trans (hs1 x))]
    exact mul_le_mul_of_nonneg_left (hfδ _ hmem) (zero_le_one.trans (hs1 x))
  refine ⟨g, ?_, fun x hx ↦ ?_, fun x hx ↦
    (le_mul_of_one_le_left hδ.le (hs1 x)).trans (hout x hx)⟩
  · -- The preimage of a compact set is closed and, by `hout`, bounded.
    refine isProperMap_iff_isCompact_preimage.2 ⟨g.continuous, fun K hK ↦ ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (f x₀)
    refine isCompact_of_isClosed_isBounded (hK.isClosed.preimage g.continuous)
      ((isBounded_closedBall (x := x₀) (r := max r (R * r / δ))).subset fun x hx ↦ ?_)
    rw [mem_closedBall]
    by_cases hxr : r ≤ dist x x₀
    · have h1 := (hout x hxr).trans (by simpa [dist_eq_norm] using hR hx)
      have hsx : s x = dist x x₀ / r := max_eq_right ((one_le_div hr).2 hxr)
      rw [hsx, div_mul_eq_mul_div, div_le_iff₀ hr] at h1
      exact le_max_of_le_right ((le_div_iff₀ hδ).2 (by nlinarith))
    · exact le_max_of_le_left (not_le.1 hxr).le
  · have hsx : s x = 1 := max_eq_left ((div_le_one hr).2 (mem_closedBall.1 hx))
    rw [hg, hsx, centeredRadialRetraction_of_mem_closedBall hx, one_smul, add_sub_cancel]

end
