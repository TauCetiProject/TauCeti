/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.LusternikSchnirelmann
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.CupLength
import TauCeti.Dynamics.Flow.Basic

/-!
# Rest points of flows with a Lyapunov function and the Lusternik–Schnirelmann category

Let `ϕ` be a flow of `ℝ` on a compact locally contractible space `α`, such as a compact manifold,
and let `W : α → ℝ` be a continuous function which strictly decreases along every nonconstant orbit
of `ϕ`. This file shows that `ϕ` has at least as many rest points as the unnormalized
Lusternik–Schnirelmann count of `α` (`Flow.lsCategoryCount_univ_le_encard`), and hence, for
nonempty `α`, at least `cl + 1` rest points, where `cl` is the cup length of the singular cohomology
of `α` with coefficients in any commutative ring (`Flow.lsCupLength_add_one_le_encard`). For
instance, such a flow on an `n`-torus has at least `n + 1` rest points.

Both follow from the abstract bound `Flow.index_univ_le_encard`, applied to the index
`TauCeti.lsCategoryCount α`: it is monotone and subadditive, the time-`t` map of the flow is
homotopic to the identity so it does not increase the count, and local contractibility gives every
point an open neighbourhood of count at most `1`. Without local contractibility the last property
can fail.

## Main results

* `Flow.lsCategoryCount_univ_le_encard`: the Lusternik–Schnirelmann count of `α` is at most the
  number of rest points.
* `Flow.lsCupLength_add_one_le_encard`: on a nonempty space, the cup length plus one is at most
  the number of rest points.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, AMS, 2003, Chapter 1.
-/

public section

open Set TauCeti Topology

namespace Flow

universe u

variable {α : Type u} [TopologicalSpace α] [CompactSpace α] {ϕ : Flow ℝ α} {W : α → ℝ}

/-- **The Lusternik–Schnirelmann theorem for flows.** On a compact locally contractible space, a
flow with a continuous function `W` strictly decreasing along every nonconstant orbit has at least
as many rest points as the Lusternik–Schnirelmann count of the space. -/
theorem lsCategoryCount_univ_le_encard (hX : LocallyContractibleSpace α) (hWc : Continuous W)
    (hW : ∀ x t, 0 < t → ϕ t x ≠ x → W (ϕ t x) < W x) :
    lsCategoryCount α univ ≤ {x | ∀ t, ϕ t x = x}.encard := by
  refine index_univ_le_encard hWc hW (fun _ _ ↦ lsCategoryCount_mono) lsCategoryCount_empty
    (fun _ _ ↦ lsCategoryCount_union_le) (fun t _ A ↦ ?_) fun x _ ↦ ?_
  · -- The time-`t` map is homotopic to the identity through the time-`u t` maps, `u ∈ [0, 1]`.
    refine lsCategoryCount_le_of_homotopic_id ⟨ϕ t, ϕ.continuous_toFun t⟩ ?_ fun x hx ↦ hx
    exact ϕ.homotopic_of_eq_apply Topology.IsEmbedding.id continuous_id continuous_const
      continuous_const (τ₀ := fun _ ↦ t) (τ₁ := fun _ ↦ 0) (fun _ ↦ rfl)
      (fun x ↦ (map_zero_apply ϕ x).symm) fun x u _ ↦ mem_range_self _
  · obtain ⟨U, hUo, hxU, hU⟩ := exists_isOpen_mem_lsCategoryCount_le_one hX x
    exact ⟨U, hUo.mem_nhds hxU, hU⟩

/-- **The cup-length bound for flows.** On a nonempty compact locally contractible space, a flow
with a continuous function `W` strictly decreasing along every nonconstant orbit has at least
`cl + 1` rest points, where `cl` is the cup length of the singular cohomology of the space with
coefficients in the commutative ring `R`. -/
theorem lsCupLength_add_one_le_encard [Nonempty α] (R : Type u) [CommRing R]
    (hX : LocallyContractibleSpace α) (hWc : Continuous W)
    (hW : ∀ x t, 0 < t → ϕ t x ≠ x → W (ϕ t x) < W x) :
    lsCupLength α R + 1 ≤ {x | ∀ t, ϕ t x = x}.encard :=
  (lsCupLength_add_one_le_lsCategoryCount_univ (X := α) (R := R)).trans
    (lsCategoryCount_univ_le_encard hX hWc hW)

end Flow
