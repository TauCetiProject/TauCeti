/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Differentiability of sums and of linear families of functions

If each summand `f i : E → F` (`i ∈ s`) is uniformly approximable on `K ⊆ E` to arbitrary accuracy
by functions `𝕜`-differentiable on `Ω ⊆ E`, then the finite sum `∑ i ∈ s, f i` is likewise
uniformly approximable on `K` by functions `𝕜`-differentiable on `Ω`
(`TauCeti.exists_differentiableOn_norm_sum_sub_lt`).

For a linear family of functions `P : Λ →ₗ[R] E → F`, moving the parameter from `p` to
`p + s • q` subtracts `s • P q` from `g - P p` (`LinearMap.sub_map_add_smul`), and so subtracts
`s • d(P q)_x` from the differential of `g - P p` at `x` (`LinearMap.fderiv_sub_map_add_smul`).

The derivative of a point `u + μ • (u' - u)` of the segment between two differentiable maps is the
corresponding point of the segment between their derivatives
(`TauCeti.fderiv_add_smul_sub_apply`).
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

/-- The derivative at `z` of a point `u + μ • (u' - u)` of the segment between two maps
differentiable at `z`. -/
theorem fderiv_add_smul_sub_apply {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u u' : E → F} {z : E} (hu : DifferentiableAt 𝕜 u z) (hu' : DifferentiableAt 𝕜 u' z) (μ : 𝕜)
    (v : E) :
    fderiv 𝕜 (u + μ • (u' - u)) z v = fderiv 𝕜 u z v + μ • (fderiv 𝕜 u' z v - fderiv 𝕜 u z v) := by
  rw [(hu.hasFDerivAt.add ((hu'.hasFDerivAt.sub hu.hasFDerivAt).const_smul μ)).fderiv]
  simp

end TauCeti

namespace LinearMap

/-- Moving the parameter of a linear family of functions `P` from `p` to `p + s • q` subtracts
`s • P q` from `g - P p`. -/
theorem sub_map_add_smul {R Λ E F : Type*} [Semiring R] [AddCommMonoid Λ] [Module R Λ]
    [AddCommGroup F] [Module R F] (P : Λ →ₗ[R] E → F) (g : E → F) (p q : Λ) (s : R) :
    (fun y ↦ g y - P (p + s • q) y) = (fun y ↦ g y - P p y) - s • P q := by
  ext y
  simp [sub_add_eq_sub_sub]

/-- Moving the parameter of a linear family of functions `P` from `p` to `p + s • q` subtracts
`s • d(P q)_x` from the differential at `x` of `g - P p`. -/
theorem fderiv_sub_map_add_smul {𝕜 Λ E F : Type*} [NontriviallyNormedField 𝕜] [AddCommMonoid Λ]
    [Module 𝕜 Λ] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (P : Λ →ₗ[𝕜] E → F) {g : E → F} {p q : Λ} {x : E}
    (hg : DifferentiableAt 𝕜 (fun y ↦ g y - P p y) x) (hq : DifferentiableAt 𝕜 (P q) x) (s : 𝕜) :
    fderiv 𝕜 (fun y ↦ g y - P (p + s • q) y) x =
      fderiv 𝕜 (fun y ↦ g y - P p y) x - s • fderiv 𝕜 (P q) x := by
  rw [P.sub_map_add_smul g p q s, fderiv_sub hg (hq.const_smul s), fderiv_const_smul hq]

end LinearMap
