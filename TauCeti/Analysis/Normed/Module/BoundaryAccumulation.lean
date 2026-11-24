/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Relatively discrete sets accumulating in every boundary branch

Let `Ω` be an open subset of a proper normed group. This file constructs a set `E ⊆ Ω` which is
closed and discrete relative to `Ω` (`Eᶜ ∈ codiscreteWithin Ω`) and yet comes close to every point
of `Ω` at the scale of its distance to the complement: every `x ∈ Ω` has a point `y ∈ E` with
`dist x y < dist x ξ` for all `ξ ∉ Ω`
(`IsOpen.exists_compl_mem_codiscreteWithin_forall_exists_dist_lt`). The construction covers the
shells of the filled exhaustion `TauCeti.filledExhaustion Ω n` by finite nets whose mesh
`(n + 1)⁻¹` is at most the distance of the `n`th stage to `Ωᶜ`.

In a real normed space, such a set accumulates at every point `ξ ∉ Ω` from within every local
branch of `Ω` at `ξ`: if `U` is a neighbourhood of `ξ` and `ξ` lies in the closure of a connected
component `C` of `U ∩ Ω`, then points of `E ∩ C` accumulate at `ξ`
(`TauCeti.frequently_mem_inter_connectedComponentIn_of_forall_exists_dist_lt`).

Such a set is the zero set used to build, on an open `Ω ⊆ ℂ`, a holomorphic function admitting no
meromorphic continuation across any local boundary branch: a continuation would have zeros
accumulating at an interior point of its domain. For a connected open `D` meeting both `Ω`
and its complement, `IsPreconnected.exists_mem_inter_closure_connectedComponentIn_sdiff` supplies a
point of `D \ Ω` in the closure of any given component of `D ∩ Ω`, to which the accumulation
statement applies with `U = D`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 15.5.
-/

public section

open Filter Metric Set Topology

open TauCeti in
/-- **A relatively discrete net at the scale of the boundary distance.** An open set `Ω` in a
proper normed group contains a set `E`, closed and discrete relative to `Ω`, such that every
`x ∈ Ω` has a point `y ∈ E` closer to `x` than every point outside `Ω`. -/
theorem IsOpen.exists_compl_mem_codiscreteWithin_forall_exists_dist_lt {V : Type*}
    [NormedAddCommGroup V] [ProperSpace V] {Ω : Set V} (hΩ : IsOpen Ω) :
    ∃ E ⊆ Ω, Eᶜ ∈ codiscreteWithin Ω ∧ ∀ x ∈ Ω, ∃ y ∈ E, ∀ ξ ∉ Ω, dist x y < dist x ξ := by
  -- The `n`th shell: the `n`th stage minus the interiors of all earlier stages.
  set S : ℕ → Set V := fun n ↦
    filledExhaustion Ω n \ ⋃ m ∈ Finset.range n, interior (filledExhaustion Ω m)
  have hnet (n : ℕ) : ∃ t ⊆ S n, t.Finite ∧ S n ⊆ ⋃ y ∈ t, ball y (n + 1 : ℝ)⁻¹ :=
    finite_approx_of_totallyBounded ((isCompact_filledExhaustion Ω n).diff
      (isOpen_biUnion fun _ _ ↦ isOpen_interior)).totallyBounded _ (by positivity)
  choose F hFS hFfin hFcov using hnet
  refine ⟨⋃ n, F n, iUnion_subset fun n ↦ (hFS n).trans (sdiff_subset.trans
    (filledExhaustion_subset Ω n)), ?_, fun x hx ↦ ?_⟩
  · -- A point of the `N`th stage has the interior of the next stage as a neighbourhood, which
    -- misses every later shell.
    rw [codiscreteWithin_iff_locallyFiniteComplementWithin]
    intro z hz
    obtain ⟨N, hN⟩ := mem_iUnion.mp (hΩ.iUnion_filledExhaustion.symm ▸ hz)
    refine ⟨interior (filledExhaustion Ω (N + 1)),
      isOpen_interior.mem_nhds (filledExhaustion_subset_interior_succ Ω N hN), ?_⟩
    refine ((finite_le_nat (N + 1)).biUnion fun n _ ↦ hFfin n).subset ?_
    rintro w ⟨hwN, -, hwE⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (not_not.mp hwE)
    refine mem_biUnion (x := n) ?_ hn
    exact not_lt.mp fun hlt ↦ (hFS n hn).2 (mem_biUnion (Finset.mem_range.mpr hlt) hwN)
  · -- A point lies in the shell of the first stage containing it, whose net has mesh at most its
    -- distance to `Ωᶜ`.
    have hex : ∃ n, x ∈ filledExhaustion Ω n :=
      mem_iUnion.mp (hΩ.iUnion_filledExhaustion.symm ▸ hx)
    classical
    have hxS : x ∈ S (Nat.find hex) := ⟨Nat.find_spec hex, fun h ↦ by
      obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp h
      exact Nat.find_min hex (Finset.mem_range.mp hm) (interior_subset hxm)⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hFcov _ hxS)
    exact ⟨y, mem_iUnion.mpr ⟨_, hy⟩, fun ξ hξ ↦
      (mem_ball.mp hxy).trans_le (le_dist_of_mem_filledExhaustion (Nat.find_spec hex) hξ)⟩

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Accumulation in every boundary branch.** Let `E` come closer to each point `x ∈ Ω` than every
point outside `Ω` does. If `ξ ∉ Ω` lies in the closure of a connected component `C` of `U ∩ Ω`,
where `U` is a neighbourhood of `ξ`, then points of `E ∩ C` accumulate at `ξ`. -/
theorem frequently_mem_inter_connectedComponentIn_of_forall_exists_dist_lt {Ω E U : Set V}
    (hE : ∀ x ∈ Ω, ∃ y ∈ E, ∀ ξ ∉ Ω, dist x y < dist x ξ) {ξ z : V} (hξ : ξ ∉ Ω) (hU : U ∈ 𝓝 ξ)
    (hz : ξ ∈ closure (connectedComponentIn (U ∩ Ω) z)) :
    ∃ᶠ w in 𝓝[≠] ξ, w ∈ E ∩ connectedComponentIn (U ∩ Ω) z := by
  rw [nhdsWithin_basis_ball.frequently_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨x, hxC, hξx⟩ := Metric.mem_closure_iff.mp hz (min ε ρ / 2) (by positivity)
  obtain ⟨y, hyE, hy⟩ := hE x (connectedComponentIn_subset _ _ hxC).2
  have hxy := hy ξ hξ
  have hmin : 2 * dist x ξ < min ε ρ := by rw [dist_comm]; linarith
  -- The segment from `x` to `y` stays in `Ω`, since `y` is closer to `x` than `Ωᶜ` is, and in the
  -- ball of radius `ρ` about `ξ`; so it joins `x` to `y` inside `C`.
  have hseg : segment ℝ x y ⊆ U ∩ Ω := fun w hw ↦ by
    have hwx : dist w x ≤ dist x y := segment_subset_closedBall_left x y hw
    refine ⟨hρU (mem_ball.mpr ?_), by_contra fun hwΩ ↦ ?_⟩
    · linarith [dist_triangle w x ξ, min_le_right ε ρ]
    · linarith [hy w hwΩ, dist_comm x w]
  have hyC : y ∈ connectedComponentIn (U ∩ Ω) z := by
    rw [connectedComponentIn_eq hxC]
    exact (convex_segment x y).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ x y) hseg (right_mem_segment ℝ x y)
  have hyΩ : y ∈ Ω := (hseg (right_mem_segment ℝ x y)).2
  refine ⟨y, ⟨mem_ball.mpr ?_, fun hyξ ↦ hξ (hyξ ▸ hyΩ)⟩, hyE, hyC⟩
  linarith [dist_triangle y x ξ, dist_comm x y, min_le_left ε ρ]

end TauCeti
