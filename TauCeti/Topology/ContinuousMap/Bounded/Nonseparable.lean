/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded functions on an infinite discrete space are not separable

For an infinite discrete space `X` and a nontrivial normed group `E`, the space `X →ᵇ E` is not
separable: for `c ≠ 0`, the functions `s.indicator (fun _ ↦ c)`, for `s : Set X`, are
uncountably many elements at mutual distance at least `‖c‖`. For `X = ℕ` and `E = ℂ` this is the
non-separability of `ℓ∞`.

## Main statements

* `BoundedContinuousFunction.not_separableSpace_of_infinite`: `X →ᵇ E` is not separable.
-/

public section

open TopologicalSpace
open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

/-- **Bounded functions on an infinite discrete space are not separable**: for `c ≠ 0` in `E`,
the indicator functions with value `c` of the subsets of `X` are uncountably many elements of
`X →ᵇ E` at mutual distance at least `‖c‖`. For `X = ℕ`, `E = ℂ` this says that `ℓ∞` is not
separable. -/
theorem not_separableSpace_of_infinite {X E : Type*} [TopologicalSpace X] [DiscreteTopology X]
    [Infinite X] [NormedAddCommGroup E] [Nontrivial E] : ¬ SeparableSpace (X →ᵇ E) := by
  intro _
  obtain ⟨c, hc⟩ := exists_ne (0 : E)
  let f : Set X → X →ᵇ E := fun s ↦
    mkOfDiscrete (s.indicator fun _ ↦ c) ‖c‖ fun x y ↦ by
      by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp [hx, hy]
  have hsep {s t : Set X} (hst : s ≠ t) : ‖c‖ ≤ dist (f s) (f t) := by
    obtain ⟨x, hx⟩ := Set.symmDiff_nonempty.2 hst
    refine le_trans ?_ (dist_coe_le_dist x)
    rcases hx with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> simp [f, hs, ht]
  have hcount : Countable (Set X) :=
    Pairwise.countable_of_isOpen_disjoint (s := fun s ↦ Metric.ball (f s) (‖c‖ / 2))
      (fun s t hst ↦ Metric.ball_disjoint_ball (by linarith [hsep hst]))
      (fun _ ↦ Metric.isOpen_ball)
      (fun _ ↦ ⟨_, Metric.mem_ball_self (half_pos (norm_pos_iff.2 hc))⟩)
  have := Cardinal.mk_le_aleph0_iff.2 hcount
  rw [Cardinal.mk_set] at this
  exact ((Cardinal.aleph0_le_mk X).trans_lt (Cardinal.cantor _)).not_ge this

end BoundedContinuousFunction
