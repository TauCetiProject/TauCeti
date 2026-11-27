/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Urysohn cutoffs of continuous maps

In a normal space, a map into a topological real module that is continuous on an open set `Ω`
agrees on each closed subset `K ⊆ Ω` with a map continuous everywhere
(`ContinuousOn.exists_continuous_eqOn_of_isClosed`): multiply it by a Urysohn cutoff equal to `1`
on `K` and to `0` off an open `W ⊇ K` with `closure W ⊆ Ω`.

In a locally compact regular space, a continuous map `ψ` into a real normed space tending to `0`
at infinity is uniformly approximated by continuous compactly supported maps `χ • ψ` of no larger
norm (`Continuous.exists_hasCompactSupport_norm_sub_le`), where `0 ≤ χ ≤ 1` is a compactly
supported Urysohn cutoff equal to `1` on a compact set outside which `‖ψ‖ < ε`.
-/

public section

open Set Filter Topology

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

/-- **Compactly supported approximation of maps vanishing at infinity.** In a locally compact
regular space, a continuous map `ψ` into a real normed space tending to `0` at infinity is
uniformly within `ε` of a continuous compactly supported map `ψ'` with `‖ψ' x‖ ≤ ‖ψ x‖`. It is
`χ • ψ` for a continuous compactly supported cutoff `0 ≤ χ ≤ 1` equal to `1` on a compact set
outside which `‖ψ‖ < ε`. -/
theorem Continuous.exists_hasCompactSupport_norm_sub_le {X E : Type*} [TopologicalSpace X]
    [RegularSpace X] [LocallyCompactSpace X] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : X → E} (hψ : Continuous ψ) (hψ0 : Tendsto ψ (cocompact X) (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ' : X → E, Continuous ψ' ∧ HasCompactSupport ψ' ∧ (∀ x, ‖ψ' x‖ ≤ ‖ψ x‖) ∧
      ∀ x, ‖ψ x - ψ' x‖ ≤ ε := by
  obtain ⟨K, hKc, hK⟩ := mem_cocompact.1 (hψ0 (Metric.ball_mem_nhds (0 : E) hε))
  obtain ⟨χ, hχ1, -, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact hKc isClosed_empty
    (disjoint_empty _)
  refine ⟨fun x ↦ χ x • ψ x, χ.continuous.smul hψ, hχc.smul_right, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (hχI x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχI x).2
  · by_cases hx : x ∈ K
    · simp [hχ1 hx, hε.le]
    · rw [show ψ x - χ x • ψ x = (1 - χ x) • ψ x by rw [sub_smul, one_smul], norm_smul,
        Real.norm_of_nonneg (sub_nonneg.2 (hχI x).2)]
      refine (mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hχI x).1])).trans ?_
      exact (mem_ball_zero_iff.1 (hK hx)).le
