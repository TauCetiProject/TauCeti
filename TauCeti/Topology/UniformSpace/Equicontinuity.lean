/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuity of a sequence from equicontinuity of a tail

Equicontinuity at a point is insensitive to finitely many members of a family, provided each of
them is continuous there (`equicontinuousAt_finite`). For a sequence `F : ℕ → X → α` this means
that equicontinuity at `x₀` of a tail `n ↦ F (n + N)` and continuity at `x₀` of the first `N`
members give equicontinuity at `x₀` of the whole sequence
(`TauCeti.equicontinuousAt_of_equicontinuousAt_add`). Local arguments often control a sequence
only from some index on, with the index depending on the point; this lemma assembles such local
control into equicontinuity of the original sequence.

Equicontinuity within a neighbourhood of `x₀` is equicontinuity at `x₀`
(`EquicontinuousWithinAt.equicontinuousAt`), as for continuity.
-/

public section

open Filter Topology

variable {ι X α : Type*} [TopologicalSpace X] [UniformSpace α]

/-- A family equicontinuous at `x₀` within a neighbourhood of `x₀` is equicontinuous at `x₀`. -/
theorem EquicontinuousWithinAt.equicontinuousAt {F : ι → X → α} {S : Set X} {x₀ : X}
    (hF : EquicontinuousWithinAt F S x₀) (hS : S ∈ 𝓝 x₀) : EquicontinuousAt F x₀ := by
  rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.2 hS] at hF

namespace TauCeti

/-- A sequence of functions is equicontinuous at `x₀` if one of its tails `n ↦ F (n + N)` is,
and its first `N` members are continuous at `x₀`. -/
theorem equicontinuousAt_of_equicontinuousAt_add {F : ℕ → X → α} {x₀ : X} (N : ℕ)
    (hF : EquicontinuousAt (fun n ↦ F (n + N)) x₀) (hc : ∀ n < N, ContinuousAt (F n) x₀) :
    EquicontinuousAt F x₀ := by
  intro U hU
  have hfin : EquicontinuousAt (fun n : Fin N ↦ F n) x₀ :=
    equicontinuousAt_finite.2 fun n ↦ hc n n.isLt
  filter_upwards [hF U hU, hfin U hU] with x htail hhead n
  rcases lt_or_ge n N with hn | hn
  · exact hhead ⟨n, hn⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact htail k

end TauCeti
