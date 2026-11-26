/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UrysohnsLemma

/-!
# Continuous maps agreeing with a map continuous on an open set

In a normal space, a map into a topological real module that is continuous on an open set `Ω`
agrees on each closed subset `K ⊆ Ω` with a map continuous everywhere
(`ContinuousOn.exists_continuous_eqOn_of_isClosed`): multiply it by a Urysohn cutoff equal to `1`
on `K` and to `0` off an open `W ⊇ K` with `closure W ⊆ Ω`.
-/

public section

open Set

/-- A map continuous on an open set `Ω` of a normal space agrees on each closed subset `K ⊆ Ω` with
a map continuous everywhere, namely its product with a Urysohn cutoff equal to `1` on `K` and to `0`
near `Ωᶜ`. -/
theorem ContinuousOn.exists_continuous_eqOn_of_isClosed {X E : Type*} [TopologicalSpace X]
    [NormalSpace X] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [ContinuousSMul ℝ E]
    {u : X → E} {Ω K : Set X} (hu : ContinuousOn u Ω) (hΩ : IsOpen Ω) (hK : IsClosed K)
    (hKΩ : K ⊆ Ω) : ∃ g : X → E, Continuous g ∧ EqOn g u K := by
  -- The cutoff `χ` is `1` on `K` and `0` off an open `W ⊇ K` with `closure W ⊆ Ω`.
  obtain ⟨W, hW, hKW, hWΩ⟩ := normal_exists_closure_subset hK hΩ hKΩ
  obtain ⟨χ, hχW, hχK, -⟩ := exists_continuous_zero_one_of_isClosed hW.isClosed_compl hK
    (disjoint_compl_left_iff_subset.2 hKW)
  have hχ : Function.support χ ⊆ W := fun x hx ↦ by_contra fun h ↦ hx (hχW h)
  -- The product is continuous on `Ω` and supported in `closure W ⊆ Ω`.
  exact ⟨fun x ↦ χ x • u x, (χ.continuous.continuousOn.smul hu).continuous_of_tsupport_subset hΩ
    (((tsupport_smul_subset_left _ _).trans (closure_mono hχ)).trans hWΩ),
    fun x hx ↦ by simp [hχK hx]⟩
