/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Uniform approximation of finite sums by differentiable functions

If each summand `f i : E → F` (`i ∈ s`) is uniformly approximable on `K ⊆ E` to arbitrary accuracy
by functions `𝕜`-differentiable on `Ω ⊆ E`, then the finite sum `∑ i ∈ s, f i` is likewise
uniformly approximable on `K` by functions `𝕜`-differentiable on `Ω`
(`TauCeti.exists_differentiableOn_norm_sum_sub_lt`).
-/

public section

namespace TauCeti

/-- If each function `f i : E → F` (`i ∈ s`) is uniformly approximable on `K` by functions
`𝕜`-differentiable on `Ω`, then the finite sum `∑ i ∈ s, f i` is uniformly approximable on `K` by a
function `𝕜`-differentiable on `Ω`. -/
theorem exists_differentiableOn_norm_sum_sub_lt {𝕜 E F ι : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {Ω K : Set E} (s : Finset ι) {f : ι → E → F} {ε : ℝ} (hε : 0 < ε)
    (happrox : ∀ i ∈ s, ∀ δ > 0, ∃ g : E → F, DifferentiableOn 𝕜 g Ω ∧
      ∀ z ∈ K, ‖f i z - g z‖ < δ) :
    ∃ g : E → F, DifferentiableOn 𝕜 g Ω ∧ ∀ z ∈ K, ‖(∑ i ∈ s, f i z) - g z‖ < ε := by
  classical
  have hpos : 0 < (s.card : ℝ) + 1 := Nat.cast_add_one_pos s.card
  have hδ : 0 < ε / ((s.card : ℝ) + 1) := div_pos hε hpos
  have hall : ∀ i : ι, ∃ g : E → F, DifferentiableOn 𝕜 g Ω ∧
      (i ∈ s → ∀ z ∈ K, ‖f i z - g z‖ < ε / ((s.card : ℝ) + 1)) := fun i => by
    by_cases hi : i ∈ s
    · obtain ⟨g, hg, hb⟩ := happrox i hi _ hδ
      exact ⟨g, hg, fun _ => hb⟩
    · exact ⟨0, differentiableOn_const 0, fun h => False.elim (hi h)⟩
  choose g hg hbound using hall
  refine ⟨fun z => ∑ i ∈ s, g i z, DifferentiableOn.fun_sum fun i _ => hg i, fun z hz => ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine lt_of_le_of_lt (norm_sum_le s _) ?_
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i hi => (hbound i hi z hz).le) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_div_left_comm]
  exact mul_lt_of_lt_one_right hε ((div_lt_one hpos).mpr (lt_add_one (s.card : ℝ)))

end TauCeti
