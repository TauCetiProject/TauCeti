/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Topology.Order.Interval

/-!
# Nested partitions recovering total variation

Every function on a compact real interval admits nested finite partitions with prescribed
positive gap bounds whose variation sums converge to its full extended variation. In particular,
choosing bounds tending to zero gives arbitrarily small gaps. No continuity or bounded-variation
hypothesis is needed, and the limit may be infinite. The sequence is chosen depending on the
function; convergence along every fine partition sequence is not asserted.

Partitions are represented by finite sets containing both endpoints. Their variation sums are
`eVariationOn f` on those finite sets: Mathlib's `eVariationOn.image_range_of_monotone`
identifies these with sums of successive distances in an increasing enumeration. Refinement
increases these sums by `eVariationOn.mono`.

We use `eVariationOn.exists_monotone_finset_tendsto` to adjoin finite ball covers to nested
variation approximants. These partitions provide pathwise approximations for finite-variation
integration.
-/

public section

open Set Filter Topology

namespace TauCeti

/-- For every function on `[a,b]` and every sequence of positive bounds `ε n`, choose nested
finite partitions with gaps at most `ε n` whose successive-distance sums tend to the full
extended variation. Taking `ε n = 1 / (n + 1)` gives vanishing mesh. No regularity is required
of the function, and infinite variation is included. -/
theorem exists_nested_partitions_tendsto_eVariationOn
    {E : Type*} [TopologicalSpace E] [WeakPseudoEMetricSpace E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ p : ℕ → Finset ℝ, Monotone p ∧
      (∀ n, (p n : Set ℝ) ⊆ Icc a b ∧ a ∈ p n ∧ b ∈ p n) ∧
      (∀ n, ∀ x ∈ p n, ∀ y ∈ p n, x < y →
        (∀ z ∈ p n, x < z → y ≤ z) → y - x ≤ ε n) ∧
      Tendsto (fun n => eVariationOn f (p n : Set ℝ)) atTop
        (𝓝 (eVariationOn f (Icc a b))) := by
  classical
  choose q hq hqa hqb hqgap using fun n : ℕ =>
    exists_finset_Icc_gap_le hab (hε n)
  obtain ⟨p, hp, hps, hqp, hlim⟩ :=
    eVariationOn.exists_monotone_finset_tendsto f (Icc a b) q hq
  exact ⟨p, hp, fun n => ⟨hps n, hqp n (hqa n), hqp n (hqb n)⟩,
    fun n => consecutive_gap_le_of_subset (hqp n) (hps n) (hqa n) (hqb n) (hqgap n), hlim⟩

end TauCeti
