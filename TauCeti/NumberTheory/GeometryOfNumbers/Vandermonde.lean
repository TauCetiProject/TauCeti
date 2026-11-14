/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import TauCeti.NumberTheory.GeometryOfNumbers.LinearForms

/-!
# Vandermonde–Minkowski construction of integer polynomials with small values

Let `β₀, …, βₙ` be `n + 1` pairwise distinct real numbers, so that the Vandermonde matrix
`V = Matrix.vandermonde β` with entries `Vᵢₖ = βᵢ ^ k` has nonzero determinant. Given nonnegative
bounds `a₀, …, aₙ` whose product is at least `|det V|`, Minkowski's linear forms theorem
(`Matrix.exists_ne_zero_int_abs_sum_mul_le`) produces a nonzero integer vector `z` satisfying
`|∑ₖ βᵢ ^ k zₖ| ≤ aᵢ` for every `i`. Assembling `z` as the coefficients of
`P = ∑ₖ C (zₖ) * X ^ k ∈ ℤ[X]` gives a nonzero integer polynomial of degree at most `n` with
`|P(βᵢ)| ≤ aᵢ`, while inverting `V` as a continuous linear equivalence on `ℝ ^ (n + 1)` bounds the
coefficient sup norm `P.supNorm` by `c * ‖a‖` for a constant `c ≥ 1` depending only on `β`.

This auxiliary-polynomial supply underlies Wirsing's construction of real algebraic approximations
to a real number `ξ` via separated auxiliary evaluation points.

## Main results

* `Polynomial.exists_one_le_forall_exists_ne_zero_abs_aeval_le_supNorm_le`: uniform
  Vandermonde–Minkowski construction of a nonzero integer polynomial of degree at most `n` with
  prescribed value bounds at `n + 1` distinct real points and controlled coefficient sup norm.

## References

* E. Wirsing, *Approximation mit algebraischen Zahlen beschränkten Grades*, J. reine angew. Math.
  **206** (1961), 67–77, §2.
* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), §3.4,
  Theorem 3.4.
* J.-H. Evertse, *Diophantine approximation, Chapter 2: Geometry of numbers*, §2.2, Corollary 2.6.
-/

public section

namespace Polynomial

/-- **Vandermonde–Minkowski integer-polynomial construction.** For `n + 1` distinct real points
`β : Fin (n + 1) → ℝ`, there is a constant `c ≥ 1` depending only on `β` such that any nonnegative
bounds `a : Fin (n + 1) → ℝ` with `|(Matrix.vandermonde β).det| ≤ ∏ i, a i` admit a nonzero
integer polynomial `P` of degree at most `n` satisfying `|P(β i)| ≤ a i` for every `i` and
`P.supNorm ≤ c * ‖a‖`. -/
theorem exists_one_le_forall_exists_ne_zero_abs_aeval_le_supNorm_le {n : ℕ}
    {β : Fin (n + 1) → ℝ} (hβ : Function.Injective β) :
    ∃ c ≥ 1, ∀ a : Fin (n + 1) → ℝ, 0 ≤ a → |(Matrix.vandermonde β).det| ≤ ∏ i, a i →
      ∃ P : ℤ[X], P ≠ 0 ∧ P.natDegree ≤ n ∧ (∀ i, |aeval (β i) P| ≤ a i) ∧
        P.supNorm ≤ c * ‖a‖ := by
  set V := Matrix.vandermonde β
  have hdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hβ
  let e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    ((Matrix.toLin' V).equivOfDetNeZero (by rwa [LinearMap.det_toLin'])).toContinuousLinearEquiv
  set c := max 1 ‖(e.symm : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))‖
  refine ⟨c, le_max_left _ _, fun a ha hprod ↦ ?_⟩
  obtain ⟨z, hz0, hz⟩ := V.exists_ne_zero_int_abs_sum_mul_le hdet ha hprod
  set P : ℤ[X] := ∑ k : Fin (n + 1), C (z k) * X ^ (k : ℕ)
  have hcoeff (k : Fin (n + 1)) : P.coeff k = z k := by
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    simp [Fin.val_inj]
  have hP0 : P ≠ 0 := fun h0 ↦ hz0 <| _root_.funext fun k : Fin (n + 1) ↦
    (hcoeff k).symm.trans (by simp [h0])
  have hPdeg : P.natDegree ≤ n := natDegree_sum_le_of_forall_le _ _ fun k _ ↦
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 k.isLt)
  have heval (i : Fin (n + 1)) : aeval (β i) P = ∑ k, V i k * (z k : ℝ) := by
    simp [P, map_sum, V, Matrix.vandermonde, mul_comm]
  -- Invert `V` continuously to bound the integer coefficient vector `z` by `c * ‖a‖`.
  set zR : Fin (n + 1) → ℝ := fun k ↦ z k
  have hez : ‖e zR‖ ≤ ‖a‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun i ↦ by
    have hi : (e zR) i = ∑ k, V i k * zR k := by simp [e, Matrix.mulVec_apply_eq_sum]
    rw [Real.norm_eq_abs, hi]
    exact (hz i).trans ((le_abs_self (a i)).trans
      (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i))
  have hzR : ‖zR‖ ≤ c * ‖a‖ := by
    calc ‖zR‖ = ‖e.symm (e zR)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖(e.symm : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))‖ * ‖e zR‖ :=
          (e.symm : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)).le_opNorm (e zR)
      _ ≤ c * ‖a‖ := mul_le_mul (le_max_right _ _) hez (norm_nonneg _) (by positivity)
  have hPsup : P.supNorm ≤ ‖zR‖ := by
    rw [P.supNorm_eq_iSup]
    refine ciSup_le fun m ↦ ?_
    by_cases hm : m < n + 1
    · simpa [hcoeff ⟨m, hm⟩, zR, Int.norm_eq_abs] using norm_le_pi_norm zR ⟨m, hm⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
      exact norm_nonneg zR
  exact ⟨P, hP0, hPdeg, fun i ↦ heval i ▸ hz i, hPsup.trans hzR⟩

end Polynomial
