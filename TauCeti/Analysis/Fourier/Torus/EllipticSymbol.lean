/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.Smooth
import TauCeti.Analysis.Fourier.Torus.FourierCoeff

/-!
# The Fourier symbol of a constant-coefficient second-order operator on the torus

On `UnitAddTorus d`, the operator `-∑ i, ∑ j, A i j ∂ᵢ∂ⱼ` has real Fourier symbol
`(2π)² ∑ i, ∑ j, A i j kᵢ kⱼ`. This uses the sign of the nonnegative Laplacian for a
positive definite coefficient matrix. The formula holds for any real matrix and includes
mixed derivatives, as needed for a flat metric in nonorthogonal coordinates.

The eigen-equation on smooth functions holds exactly when every nonzero Fourier coefficient
has the prescribed symbol value. Every integer frequency gives a smooth Fourier eigenmode.
-/

public section

noncomputable section

open Complex _root_.UnitAddTorus
open scoped Real

namespace TauCeti.UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The real Fourier symbol of `-∑ i, ∑ j, A i j ∂ᵢ∂ⱼ` on the unit torus. -/
def secondOrderSymbol (A : Matrix d d ℝ) (k : d → ℤ) : ℝ :=
  (2 * π) ^ 2 * ∑ i, ∑ j, A i j * (k i : ℝ) * (k j : ℝ)

theorem secondOrderSymbol_def (A : Matrix d d ℝ) (k : d → ℤ) :
    secondOrderSymbol A k = (2 * π) ^ 2 * ∑ i, ∑ j, A i j * (k i : ℝ) * (k j : ℝ) :=
  (rfl)

end TauCeti.UnitAddTorus

namespace UnitAddTorus

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The constant-coefficient operator `-∑ i, ∑ j, A i j ∂ᵢ∂ⱼ` on the unit torus. -/
def secondOrderOperator (A : Matrix d d ℝ) (f : UnitAddTorus d → ℂ) : UnitAddTorus d → ℂ :=
  ∑ i, ∑ j, -(A i j : ℂ) • lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1)

theorem secondOrderOperator_apply (A : Matrix d d ℝ) (f : UnitAddTorus d → ℂ) (x : UnitAddTorus d) :
    secondOrderOperator A f x =
      -(∑ i, ∑ j, (A i j : ℂ) * lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1) x) := by
  simp only [secondOrderOperator, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
    Finset.sum_neg_distrib]

end UnitAddTorus

namespace TauCeti.UnitAddTorus

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A constant-coefficient second-order operator preserves smoothness. -/
theorem secondOrderOperator_mem_smoothFunctions (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) : secondOrderOperator A f ∈ smoothFunctions d := by
  refine (smoothFunctions d).sum_mem fun i _ ↦ (smoothFunctions d).sum_mem fun j _ ↦ ?_
  exact (smoothFunctions d).smul_mem _
    (lineDeriv_mem_smoothFunctions (lineDeriv_mem_smoothFunctions hf _) _)

/-- The `k`-th Fourier coefficient of `secondOrderOperator A f` is the coefficient of `f`
multiplied by the real quadratic symbol at `k`. -/
theorem mFourierCoeff_secondOrderOperator (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) (k : d → ℤ) :
    mFourierCoeff (secondOrderOperator A f) k =
      (secondOrderSymbol A k : ℂ) * mFourierCoeff f k := by
  let g (i j : d) : smoothFunctions d :=
    ⟨lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1),
      lineDeriv_mem_smoothFunctions (lineDeriv_mem_smoothFunctions hf _) _⟩
  have hsum : secondOrderOperator A f =
      ((∑ i, ∑ j, -(A i j : ℂ) • g i j : smoothFunctions d) : UnitAddTorus d → ℂ) := by
    simp only [secondOrderOperator, Submodule.coe_sum, Submodule.coe_smul, g]
  have hcoord (i : d) : ∑ j, (k j : ℂ) * ((Pi.single i 1 : d → ℝ) j : ℂ) = (k i : ℂ) := by
    simp [Pi.single_apply, apply_ite Complex.ofReal, mul_ite]
  rw [hsum, ← mFourierCoeffₗ_apply]
  simp only [map_sum, map_smul, mFourierCoeffₗ_apply, g, mFourierCoeff_lineDeriv,
    lineDeriv_mem_smoothFunctions hf, hf, hcoord, smul_eq_mul, secondOrderSymbol,
    ofReal_mul, ofReal_pow, ofReal_ofNat, ofReal_sum, ofReal_intCast, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination -(2 * π : ℂ) ^ 2 * A i j * k i * k j * mFourierCoeff f k * Complex.I_sq

/-- A smooth function satisfies the eigen-equation exactly when its nonzero coefficients lie
at frequencies with the prescribed symbol value. -/
theorem secondOrderOperator_eq_smul_iff (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) {μ : ℂ} :
    secondOrderOperator A f = μ • f ↔
      ∀ k, mFourierCoeff f k ≠ 0 → (secondOrderSymbol A k : ℂ) = μ := by
  constructor
  · intro h k hk
    have hcoeff := mFourierCoeff_secondOrderOperator A hf k
    rw [h, mFourierCoeff_smul, smul_eq_mul] at hcoeff
    exact mul_right_cancel₀ hk hcoeff.symm
  · intro h
    refine eq_of_mFourierCoeff_eq (secondOrderOperator_mem_smoothFunctions A hf)
      ((smoothFunctions d).smul_mem μ hf) fun k ↦ ?_
    rw [mFourierCoeff_secondOrderOperator A hf, mFourierCoeff_smul, smul_eq_mul]
    by_cases hk : mFourierCoeff f k = 0
    · simp [hk]
    · rw [h k hk]

/-- Every nonzero smooth eigenfunction has a nonzero Fourier coefficient at a frequency
whose symbol is its eigenvalue. -/
theorem exists_secondOrderSymbol_eq_of_eigenfunction (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) (hne : f ≠ 0) {μ : ℂ} (h : secondOrderOperator A f = μ • f) :
    ∃ k, mFourierCoeff f k ≠ 0 ∧ (secondOrderSymbol A k : ℂ) = μ := by
  have hex : ∃ k, mFourierCoeff f k ≠ 0 := by
    by_contra! hall
    refine hne (eq_of_mFourierCoeff_eq hf (Submodule.zero_mem _) fun k ↦ (hall k).trans ?_)
    simpa only [zero_smul] using (mFourierCoeff_smul (0 : ℂ) f k).symm
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, hk, (secondOrderOperator_eq_smul_iff A hf).1 h k hk⟩

/-- The Fourier monomial at `k` is a smooth eigenfunction with eigenvalue
`secondOrderSymbol A k`. -/
theorem secondOrderOperator_mFourier (A : Matrix d d ℝ) (k : d → ℤ) :
    secondOrderOperator A (mFourier k) = (secondOrderSymbol A k : ℂ) • ⇑(mFourier k) := by
  refine (secondOrderOperator_eq_smul_iff A (mFourier_mem_smoothFunctions k)).2 fun l hl ↦ ?_
  by_cases h : l = k
  · subst l
    rfl
  · exact (hl (by simp [mFourierCoeff_mFourier, h])).elim

end TauCeti.UnitAddTorus
