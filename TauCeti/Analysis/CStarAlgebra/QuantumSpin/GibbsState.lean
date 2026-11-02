/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Gibbs
public import TauCeti.Analysis.CStarAlgebra.QuantumSpin.LocalAlgebra

/-!
# Gibbs states of the local algebras of a quantum spin system

Over a topological coefficient ring the inclusion `QuantumSpin.inclusion : A_Λ → A_Λ'` of local
algebras, `x ↦ x ⊗ 1`, is continuous, `QuantumSpin.continuous_inclusion`. Over `ℝ` or `ℂ` it
therefore commutes with the exponential, `exp (x ⊗ 1) = exp x ⊗ 1`, `QuantumSpin.exp_inclusion`.

For a Hermitian matrix `K` of `A_Λ`, the Gibbs state `Tr (exp (-βK) ·) / Tr (exp (-βK))`
evaluated on the normalized partial trace `QuantumSpin.expectation : A_Λ' → A_Λ` is the Gibbs
state of the included matrix `K ⊗ 1`, `QuantumSpin.gibbsState_expectation`. So extending the
Gibbs state of `K` to the larger region by the normalized trace on the added sites gives the
Gibbs state of `K ⊗ 1`.
-/

public section

noncomputable section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace TauCeti.QuantumSpin

variable {L S : Type*} [DecidableEq L] [Fintype S] [DecidableEq S] {Λ Λ' : Finset L}

/-- The inclusion of local algebras is continuous. -/
theorem continuous_inclusion {R : Type*} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    (h : Λ ⊆ Λ') : Continuous (inclusion (S := S) (R := R) h) :=
  continuous_matrix fun σ τ => by
    simp_rw [inclusion_apply]
    split_ifs
    · exact continuous_id.matrix_elem _ _
    · exact continuous_const

/-- The inclusion of local algebras commutes with the exponential: `exp (x ⊗ 1) = exp x ⊗ 1`. -/
theorem exp_inclusion {𝕜 : Type*} [RCLike 𝕜] (h : Λ ⊆ Λ') (x : Matrix (Λ → S) (Λ → S) 𝕜) :
    exp (inclusion h x) = inclusion h (exp x) :=
  (map_exp_of_mem_ball (𝕂 := 𝕜) _ (continuous_inclusion h) x
    (by simp [expSeries_radius_eq_top])).symm

/-- **The Gibbs state of `K` on the normalized partial trace is the Gibbs state of `K ⊗ 1`.** For
a Hermitian matrix `K` of the local algebra of `Λ ⊆ Λ'`, composing its Gibbs state with the
normalized partial trace `A_Λ' → A_Λ` gives the Gibbs state of the included matrix. -/
theorem gibbsState_expectation [Nonempty S] (h : Λ ⊆ Λ') {K : Matrix (Λ → S) (Λ → S) ℂ}
    (hK : K.IsHermitian) (β : ℝ) (X : Matrix (Λ' → S) (Λ' → S) ℂ) :
    gibbsState K hK β (expectation h X) =
      gibbsState (inclusion h K) (hK.isSelfAdjoint.map (inclusion h)).isHermitian β X := by
  -- tracing a weight `ρ` against the normalized partial trace is tracing `ρ ⊗ 1`, up to the
  -- number `c` of configurations of the sites of `Λ'` outside `Λ`
  set c : ℂ := (Fintype.card ({i : Λ' // (i : L) ∉ Λ} → S) : ℂ)
  have htr (ρ : Matrix (Λ → S) (Λ → S) ℂ) (X : Matrix (Λ' → S) (Λ' → S) ℂ) :
      (ρ * expectation h X).trace = c⁻¹ * (inclusion h ρ * X).trace := by
    rw [← expectation_inclusion_mul, trace_expectation]
  have htr₁ (ρ : Matrix (Λ → S) (Λ → S) ℂ) : ρ.trace = c⁻¹ * (inclusion h ρ).trace := by
    simpa using htr ρ 1
  have hc : c⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  -- the Gibbs weight of `K ⊗ 1` is the included Gibbs weight of `K`
  have hρ : exp (-(β • inclusion h K)) = inclusion h (exp (-(β • K))) := by
    rw [← exp_inclusion, map_neg, map_real_smul _ (continuous_inclusion h)]
  rw [IsHermitian.gibbsState_apply, IsHermitian.gibbsState_apply, hρ, htr, htr₁ (exp _),
    mul_div_mul_left _ _ hc]

end TauCeti.QuantumSpin
