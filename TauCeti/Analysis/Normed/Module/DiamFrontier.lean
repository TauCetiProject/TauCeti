/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Topology.Frontier

/-!
# A bounded set is exactly as wide as its frontier

In a real normed space a bounded set `V` and its frontier have the same diameter:
`TauCeti.diam_frontier`. One inequality is trivial, `frontier V` being contained in `closure V`.
The other says that the frontier already realises every distance realised inside `V`, and it is
the geometric content: a set cannot be wide and have a narrow boundary.

The mechanism is that a ray leaving a bounded set has to cross the frontier, and crossing it only
*later* than it passes through a given point of the set. Precisely
(`TauCeti.exists_mem_frontier_dist_le`), for `x ∈ V` and any base point `y ≠ x` the ray
`t ↦ y + t • (x - y)`, followed from `t = 1` outwards, eventually leaves the bounded set `V`, and
the segment it traces is connected, so `IsPreconnected.inter_frontier_nonempty` produces a
frontier point `p = y + t • (x - y)` with `t ≥ 1`, whence `dist y p = t * dist y x ≥ dist y x`.

Applying this twice turns a pair of points of `V` into a pair of frontier points at least as far
apart: first push `x` away from `y` to a frontier point `p`, then push `y` away from `p` to a
frontier point `q`, and `dist x y ≤ dist y p ≤ dist p q`. Boundedness is essential and not merely
a convenience of `Metric.diam`, which vanishes on unbounded sets: in `ℝ` the unbounded set
`Metric.ball 0 1 ∪ Set.Ici 2` has frontier `{-1, 1, 2}` of diameter `3`.

Nothing here needs `V` to be open, connected, or measurable, and the ambient space is an arbitrary
real normed space: only the segment and the norm are used.

The intended consumer is Carathéodory's boundary correspondence. There the piece of a domain that
a crosscut cuts off has to be shown small, and what is small is its boundary — the crosscut itself
together with the arc of the domain boundary it separates; `TauCeti.diam_frontier` is what converts
that into a bound on the piece. `TauCeti/Analysis/Complex/Conformal/CutDiameter.lean` carries out
that conversion.

## Main results

* `Bornology.IsBounded.exists_add_smul_mem_frontier` — a ray from a point of a bounded set meets
  its frontier.
* `TauCeti.exists_mem_frontier_dist_le` — from a point of a bounded set, the ray away from any other
  base point reaches the frontier no sooner than it reaches that point.
* `TauCeti.diam_le_diam_frontier` and `TauCeti.diam_frontier` — a bounded set is exactly as wide as
  its frontier.
* `TauCeti.diam_le_diam_of_frontier_subset` — hence a bounded set is no wider than any bounded set
  containing its frontier, which is the form a boundary estimate is spent in.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} {x y : E}

/-- **A ray leaving a bounded set crosses its frontier.** For `x` in a bounded set `V` and any
nonzero direction `v`, the ray `s ↦ x + s • v`, `s ≥ 0`, meets `frontier V`. -/
theorem _root_.Bornology.IsBounded.exists_add_smul_mem_frontier (hV : IsBounded V) (hx : x ∈ V)
    {v : E} (hv : v ≠ 0) :
    ∃ s : ℝ, 0 ≤ s ∧ x + s • v ∈ frontier V := by
  obtain ⟨R, hR⟩ := hV.subset_closedBall x
  have hR0 : 0 ≤ R := dist_nonneg.trans (mem_closedBall.1 (hR hx))
  set γ : ℝ → E := fun s => x + s • v
  set T : ℝ := (R + 1) / ‖v‖
  have hT : 0 ≤ T := by positivity
  have hTV : γ T ∉ V := fun hmem => by
    have := mem_closedBall.1 (hR hmem)
    rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg hT,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv)] at this
    linarith
  obtain ⟨_, ⟨s, hs, rfl⟩, hpf⟩ :=
    (isPreconnected_Icc.image γ (by fun_prop : Continuous γ).continuousOn).inter_frontier_nonempty
      ⟨x, ⟨0, ⟨le_rfl, hT⟩, by simp [γ]⟩, hx⟩ ⟨γ T, ⟨T, ⟨hT, le_rfl⟩, rfl⟩, hTV⟩
  exact ⟨s, hs.1, hpf⟩

/-- **A ray leaving a bounded set crosses its frontier, and does so no sooner than it passes
through a given point of the set.** For `x` in a bounded set `V` and any base point `y ≠ x`, the
ray from `y` through `x` meets `frontier V` at a point `p` with `dist y x ≤ dist y p`. -/
theorem exists_mem_frontier_dist_le (hV : IsBounded V) (hx : x ∈ V) (hne : y ≠ x) :
    ∃ p ∈ frontier V, dist y x ≤ dist y p := by
  obtain ⟨s, hs, hp⟩ := hV.exists_add_smul_mem_frontier hx (sub_ne_zero.2 hne.symm)
  refine ⟨_, hp, ?_⟩
  have hsub : x + s • (x - y) - y = (1 + s) • (x - y) := by
    rw [add_smul, one_smul]
    abel
  have hdist : dist y (x + s • (x - y)) = (1 + s) * ‖x - y‖ := by
    rw [dist_eq_norm', hsub, norm_smul, Real.norm_of_nonneg (by linarith)]
  rw [hdist, dist_eq_norm']
  nlinarith [norm_nonneg (x - y)]

/-- **A bounded set is no wider than its frontier.** Every distance realised between two points of
a bounded set `V` is already realised between two points of `frontier V`: push the first point away
from the second to the frontier, then the second away from the resulting frontier point. -/
theorem diam_le_diam_frontier (hV : IsBounded V) : diam V ≤ diam (frontier V) := by
  have hfb : IsBounded (frontier V) := hV.closure.subset frontier_subset_closure
  refine diam_le_of_forall_dist_le diam_nonneg fun a ha b hb => ?_
  rcases eq_or_ne a b with rfl | hab
  · simpa using diam_nonneg
  obtain ⟨p, hp, hple⟩ := exists_mem_frontier_dist_le hV ha hab.symm
  have hpb : p ≠ b := by
    rintro rfl
    exact hab (dist_le_zero.mp (le_trans hple (by simp))).symm
  obtain ⟨q, hq, hqle⟩ := exists_mem_frontier_dist_le hV hb hpb
  calc dist a b = dist b a := dist_comm a b
    _ ≤ dist b p := hple
    _ = dist p b := dist_comm b p
    _ ≤ dist p q := hqle
    _ ≤ diam (frontier V) := dist_le_diam_of_mem hfb hp hq

/-- **The diameter of a bounded set is the diameter of its frontier.** The frontier is contained in
the closure, which gives one inequality, and `TauCeti.diam_le_diam_frontier` gives the other.

Boundedness cannot be dropped: `Metric.diam` is `0` on an unbounded set, while the frontier of
`Metric.ball 0 1 ∪ Set.Ici 2` in `ℝ` is `{-1, 1, 2}`. -/
theorem diam_frontier (hV : IsBounded V) : diam (frontier V) = diam V := by
  refine le_antisymm ?_ (diam_le_diam_frontier hV)
  calc diam (frontier V) ≤ diam (closure V) := diam_mono frontier_subset_closure hV.closure
    _ = diam V := diam_closure V

/-- **A bounded set is no wider than anything bounded that contains its frontier.** Enclosing
`frontier V` in a bounded set `W` bounds `diam V` by `diam W`, since by `TauCeti.diam_frontier` the
set and its frontier have the same diameter.

This is the form in which a boundary estimate is spent: what a geometric argument produces is a
*cover* of the boundary of a piece — for a crosscut, the image of the cut together with the arc of
the domain boundary it separates — and what is wanted is the width of the piece itself.
Boundedness of `W` is what `Metric.diam_mono` needs and is not automatic from that of `V`, `W`
being unconstrained apart from the inclusion. -/
theorem diam_le_diam_of_frontier_subset {W : Set E} (hV : IsBounded V) (hW : IsBounded W)
    (hVW : frontier V ⊆ W) : diam V ≤ diam W := by
  rw [← diam_frontier hV]
  exact diam_mono hVW hW

end TauCeti
