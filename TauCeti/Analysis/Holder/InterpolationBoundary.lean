/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Interpolation
public import TauCeti.Analysis.InnerProductSpace.GraphPatch

/-!
# Interpolation up to the boundary of a bounded domain with Lipschitz boundary

Let `Ω` be a bounded set in a proper real inner product space which near each frontier point is
the region above a Lipschitz graph. Its closure satisfies a uniform interior cone condition
(`TauCeti.exists_forall_closedBall_add_smul_subset`), so the interpolation inequalities under an
interior cone condition
(`HolderOnWith.norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_forall_closedBall_add_smul_subset`)
hold on `closure Ω` with constants depending only on `Ω`: at every small scale `ε`, every `u`
that is `C²` near `closure Ω` satisfies

`‖Du‖, ‖D²u‖ ≤ 9 (c ε)⁻² sup ‖u‖ + 5 ε^α [D²u]_α` on `closure Ω`.

These are the bounds used to absorb the lower-order norms in the global Schauder estimate.

## Main declarations

* `TauCeti.exists_forall_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded`: the
  interpolation inequalities up to the boundary of `Ω`, at every small scale `ε`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.8 (interpolation inequalities).
-/

public section

open Metric Set
open scoped NNReal InnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Interpolation up to the boundary of a bounded domain with Lipschitz boundary.** Let `Ω` be
a bounded set that near each frontier point `x` is the region above a Lipschitz graph:
`ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` for a unit vector `ν`, a radius `r > 0` and a
function `γ` invariant along `ν` and Lipschitz on `ball x r`, as in
`TauCeti.exists_forall_closedBall_add_smul_subset`. There are a scale `ε₀ > 0` and a constant
`0 < c ≤ 1`, depending only on `Ω`, such that at every scale `0 < ε ≤ ε₀` and for every exponent
`α`, every `u` that is `C²` on an open set containing `closure Ω`, with `‖u‖ ≤ N` and `D²u`
`α`-Hölder with constant `H` on `closure Ω`, has `‖Du‖` and `‖D²u‖` at most
`9 (c ε)⁻² N + 5 H ε^α` on `closure Ω` (Gilbarg–Trudinger, Section 6.8). -/
theorem exists_forall_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_isBounded {Ω : Set E}
    (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      LipschitzOnWith G γ (ball x r) ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) :
    ∃ ε₀ > 0, ∃ c > 0, c ≤ 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {α : ℝ≥0} {U : Set E} {u : E → F} {N H : ℝ≥0}, IsOpen U → closure Ω ⊆ U →
      ContDiffOn ℝ 2 u U → (∀ z ∈ closure Ω, ‖u z‖ ≤ N) →
      HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω) → ∀ z ∈ closure Ω,
        ‖fderiv ℝ u z‖ ≤ 9 / (c * ε) ^ 2 * N + 5 * H * ε ^ (α : ℝ) ∧
        ‖iteratedFDeriv ℝ 2 u z‖ ≤ 9 / (c * ε) ^ 2 * N + 5 * H * ε ^ (α : ℝ) := by
  -- The closure of `Ω` satisfies a uniform interior cone condition.
  obtain ⟨h₀, hh₀, c, hc, hc1, hcone⟩ :=
    exists_forall_closedBall_add_smul_subset hΩ.isCompact_closure hbdry
  have hcone' : ∀ z ∈ closure Ω, ∃ v : E, ‖v‖ = 1 ∧
      ∀ t, 0 < t → t ≤ h₀ → closedBall (z + t • v) (c * t) ⊆ closure Ω := fun z hz => by
    obtain ⟨v, hv, hb⟩ := hcone z hz
    exact ⟨v, hv, fun t ht hth => (hb t ht hth).trans subset_closure⟩
  refine ⟨min h₀ 1, lt_min hh₀ one_pos, c, hc, hc1,
    fun ε hε hεε₀ {α U u N H} hU hΩU hu hN hH z hz => ?_⟩
  have hε1 : ε ≤ 1 := hεε₀.trans (min_le_right _ _)
  obtain ⟨h1, h2⟩ :=
    hH.norm_fderiv_le_and_norm_iteratedFDeriv_two_le_of_forall_closedBall_add_smul_subset hU hu
      hΩU hN hc hc1 hcone' hε (hεε₀.trans (min_le_left _ _))
  have hHε : 0 ≤ (H : ℝ) * ε ^ (α : ℝ) := by positivity
  refine ⟨(h1 z hz).trans ?_, (h2 z hz).trans ?_⟩
  · have hpow : ε ^ (1 + (α : ℝ)) ≤ ε ^ (α : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
    have h9 : 9 * (N : ℝ) / (c ^ 2 * ε) ≤ 9 / (c * ε) ^ 2 * N := by
      rw [div_mul_eq_mul_div, mul_comm 9]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    nlinarith [H.coe_nonneg]
  · have h8 : 8 * (N : ℝ) / (c * ε) ^ 2 ≤ 9 / (c * ε) ^ 2 * N := by
      rw [div_mul_eq_mul_div, mul_comm 9]
      exact div_le_div_of_nonneg_right (by nlinarith [N.coe_nonneg]) (by positivity)
    nlinarith

end TauCeti
