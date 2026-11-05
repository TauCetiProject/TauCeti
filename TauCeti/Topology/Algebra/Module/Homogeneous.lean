/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousOn

/-!
# Injectivity of a positively homogeneous germ

Let `L : E → F` be positively homogeneous (`L (c • v) = c • L v` for `c ≥ 0`), and suppose that
near a point `x` a map `f` is given by `f y = f x + L (y - x)`. If `f` is injective on a
neighbourhood of `x`, then `L` is injective: two vectors with the same image under `L` can be
scaled down by a common positive factor until both are read by `f` near `x`.

The main example is the conical germ of a piecewise-linear map
(`TauCeti.IsPLWithinAt.exists_eventually_eq_add_homogeneous`).

## Main results

* `TauCeti.injective_of_eventually_eq_add`: injectivity passes from `f` near `x` to its positively
  homogeneous germ `L`.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] [AddCommGroup F] [Module ℝ F]
  {f : E → F} {x : E}

/-- **Injectivity passes to the conical germ.** If `f y = f x + L (y - x)` for all `y` near `x`,
where `L` is positively homogeneous, and `f` is injective on a neighbourhood of `x`, then `L` is
injective: two vectors with the same image under `L` are scaled down until they are read by `f`
near `x`. -/
theorem injective_of_eventually_eq_add {L : E → F}
    (hL : ∀ c : ℝ, 0 ≤ c → ∀ v, L (c • v) = c • L v)
    (hfL : ∀ᶠ y in 𝓝 x, f y = f x + L (y - x)) {D : Set E} (hD : D ∈ 𝓝 x) (hinj : InjOn f D) :
    Function.Injective L := by
  intro v w hvw
  have hev (u : E) : ∀ᶠ c in 𝓝[>] (0 : ℝ), x + c • u ∈ D ∧ f (x + c • u) = f x + L (c • u) := by
    have hlim : Tendsto (fun c : ℝ => x + c • u) (𝓝 0) (𝓝 x) :=
      (by fun_prop : Continuous fun c : ℝ => x + c • u).tendsto' 0 x (by simp)
    refine (hlim.eventually ((eventually_mem_set.2 hD).and hfL)).filter_mono
      nhdsWithin_le_nhds |>.mono fun c h => ⟨h.1, ?_⟩
    simpa using h.2
  obtain ⟨c, ⟨hvD, hv⟩, ⟨hwD, hw⟩, hc⟩ :=
    ((hev v).and ((hev w).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ))))).exists
  have hcvw : x + c • v = x + c • w :=
    hinj hvD hwD (by rw [hv, hw, hL c (le_of_lt hc), hL c (le_of_lt hc), hvw])
  exact smul_right_injective E (ne_of_gt hc) (add_left_cancel hcvw)

end TauCeti
