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

Let `E` be a proper real seminormed space, `F` a real normed space, and `f : E → F` a map
continuous on the closed ball of radius `r ≥ 0` about `x₀`. Suppose that on the sphere of radius
`r` about `x₀` it stays at distance at least `δ > 0` from a point `y₀ : F`. Extending `f` radially
about `y₀`, linearly in the distance from `x₀` along each ray,

`g x = y₀ + (dist x x₀ - r + 1) • (f y - y₀)` for `dist x x₀ ≥ r`,

where `y = TauCeti.centeredRadialRetraction x₀ r x` is the point of the sphere chosen by the radial
retraction: the point of the sphere on the ray from `x₀` through `x` when `dist x x₀ > 0`, and `x₀`
when `dist x x₀ = 0` (which here forces `r = 0`). This gives a proper map `g : E → F` which
agrees with `f` on the closed ball and stays at distance at least `δ` from `y₀` outside the open
ball. The growth of `g` along the rays makes it proper.
For `r = 0` the closed ball and the sphere both consist of the points at distance zero from `x₀`
(just `{x₀}` when `E` is normed), `y` is always `x₀`, and
`g x = y₀ + (dist x x₀ + 1) • (f x₀ - y₀)` runs out along the ray from `y₀` through `f x₀`.

For `r > 0` the closed ball is a neighbourhood of `x₀`, so `g` agrees with `f` near `x₀`. This is
how a map defined near a point is replaced by a proper map with the same local behaviour there:
when `E` and `F` are normed, oriented and of the same finite dimension, the proper map `g` has a
degree, which can be computed by summing local indices over any finite fibre. For `r = 0` the
theorem only says that `g` agrees with `f` at the points at distance zero from `x₀`.

## Main results

* `ContinuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub`: the proper radial extension.
-/

public section

open Metric Set TauCeti

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Proper radial extension.** If `f` is continuous on the closed ball of radius `r ≥ 0` about
`x₀` and stays at distance at least `δ > 0` from `y₀` on the sphere of radius `r` about `x₀`, then
`f` agrees on the closed ball with a proper continuous map `g` which stays at distance at least `δ`
from `y₀` outside the open ball. -/
theorem ContinuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub {f : E → F} {x₀ : E}
    {y₀ : F} {r δ : ℝ} (hf : ContinuousOn f (closedBall x₀ r)) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hfδ : ∀ x ∈ sphere x₀ r, δ ≤ ‖f x - y₀‖) :
    ∃ g : C(E, F), IsProperMap g ∧ EqOn g f (closedBall x₀ r) ∧
      ∀ x, r ≤ dist x x₀ → δ ≤ ‖g x - y₀‖ := by
  -- The scaling factor is `1` on the closed ball and grows linearly with the distance outside it.
  set s : E → ℝ := fun x ↦ max 1 (dist x x₀ - r + 1)
  have hs1 (x : E) : 1 ≤ s x := le_max_left _ _
  have hsc : Continuous s :=
    continuous_const.max (((continuous_id.dist continuous_const).sub continuous_const).add
      continuous_const)
  have hfρ : Continuous fun x ↦ f (TauCeti.centeredRadialRetraction x₀ r x) :=
    hf.comp_continuous (lipschitzWith_centeredRadialRetraction hr).continuous
      (centeredRadialRetraction_mem_closedBall hr)
  let g : C(E, F) :=
    ⟨fun x ↦ y₀ + s x • (f (TauCeti.centeredRadialRetraction x₀ r x) - y₀),
      continuous_const.add (hsc.smul (hfρ.sub continuous_const))⟩
  have hg (x : E) : g x = y₀ + s x • (f (TauCeti.centeredRadialRetraction x₀ r x) - y₀) := rfl
  -- Outside the open ball, `g x - y₀` is `s x` times the value of `f - y₀` at the point of the
  -- sphere on the ray through `x`.
  have hout (x : E) (hx : r ≤ dist x x₀) : s x * δ ≤ ‖g x - y₀‖ := by
    have hmem : TauCeti.centeredRadialRetraction x₀ r x ∈ sphere x₀ r := by
      rw [mem_sphere, dist_centeredRadialRetraction hr, min_eq_right hx]
    rw [hg, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (zero_le_one.trans (hs1 x))]
    exact mul_le_mul_of_nonneg_left (hfδ _ hmem) (zero_le_one.trans (hs1 x))
  refine ⟨g, ?_, fun x hx ↦ ?_, fun x hx ↦
    (le_mul_of_one_le_left hδ.le (hs1 x)).trans (hout x hx)⟩
  · -- The preimage of a compact set is closed and, by `hout`, bounded.
    refine isProperMap_iff_isCompact_preimage.2 ⟨g.continuous, fun K hK ↦ ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall y₀
    refine isCompact_of_isClosed_isBounded (hK.isClosed.preimage g.continuous)
      ((isBounded_closedBall (x := x₀) (r := r + R / δ)).subset fun x hx ↦ ?_)
    rw [mem_closedBall]
    have hRx : ‖g x - y₀‖ ≤ R := by simpa [dist_eq_norm] using hR hx
    by_cases hxr : r ≤ dist x x₀
    · -- `(dist x x₀ - r + 1) * δ ≤ s x * δ ≤ ‖g x - y₀‖ ≤ R`
      have h1 := (mul_le_mul_of_nonneg_right (le_max_right 1 (dist x x₀ - r + 1)) hδ.le).trans
        ((hout x hxr).trans hRx)
      rw [← sub_le_iff_le_add', le_div_iff₀ hδ]
      linarith
    · have hRδ : 0 ≤ R / δ := div_nonneg ((norm_nonneg _).trans hRx) hδ.le
      linarith
  · -- On the closed ball the scaling factor is `1`, and the retraction fixes the points at
    -- positive distance from `x₀` and sends the others to `x₀`.
    have hsx : s x = 1 := max_eq_left (by linarith [mem_closedBall.1 hx])
    rw [hg, hsx, one_smul, add_sub_cancel]
    rcases (dist_nonneg (x := x) (y := x₀)).eq_or_lt with h0 | hpos
    · -- At distance zero `x₀` and `x` are inseparable points of the closed ball, so `f`, being
      -- continuous there, takes the same value at both.
      rw [centeredRadialRetraction_of_dist_eq_zero h0.symm]
      have hins : Inseparable (⟨x₀, mem_closedBall_self hr⟩ : closedBall x₀ r) ⟨x, hx⟩ :=
        Metric.inseparable_iff.2 (by rw [Subtype.dist_eq, dist_comm, ← h0])
      exact (hins.map hf.domRestrict).eq
    · rw [centeredRadialRetraction_of_dist_pos_of_dist_le hpos (mem_closedBall.1 hx)]

end
