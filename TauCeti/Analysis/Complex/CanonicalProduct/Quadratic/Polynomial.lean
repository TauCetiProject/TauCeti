/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.ComputeDegree
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import TauCeti.Algebra.Polynomial.Coeff.Basic
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Factor

/-!
# Polynomial representation of finite paired quadratic products

For a paired quadratic canonical product
`f z = c * z ^ m * ∏' n, (1 + z ^ 2 / (γ n) ^ 2)`, each finite partial product over `s : Finset ℕ`
is the complexification of the real polynomial
`TauCeti.pairedPartialPoly c m γ s = C c * X ^ m * ∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2)`.
When only finitely many `γ n` are nonzero, the entire product is therefore a complex polynomial
(`TauCeti.exists_polynomial_eval_of_eq_mul_pow_tprod_one_add_div_sq`).

## Main results

* `TauCeti.pairedPartialPoly`: the finite partial-product real polynomial.
* `TauCeti.eval_map_pairedPartialPoly`: evaluation of its complexification on `ℂ`.
* `TauCeti.coeff_pairedPartialPoly_nonneg`: nonnegativity of coefficients when `0 ≤ c`.
* `TauCeti.coeff_pairedPartialPoly_mono`: monotonicity of coefficients in `s : Finset ℕ`.
* `TauCeti.coeff_pairedPartialPoly_top_pos`: strict positivity of the top-degree coefficient.
* `TauCeti.exists_polynomial_eval_of_eq_mul_pow_tprod_one_add_div_sq`: a paired quadratic product
  with finitely many nonzero `γ n` is a complex polynomial.
-/

public section

open Complex Polynomial
open scoped BigOperators

namespace TauCeti

/-- The finite partial-product real polynomial
`P_s(X) = c * X ^ m * ∏_{n ∈ s} (1 + (γ n)⁻¹ ^ 2 * X ^ 2)`. -/
noncomputable def pairedPartialPoly (c : ℝ) (m : ℕ) (γ : ℕ → ℝ) (s : Finset ℕ) : ℝ[X] :=
  C c * X ^ m * ∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2)

/-- Defining formula for `pairedPartialPoly c m γ s`. -/
theorem pairedPartialPoly_def (c : ℝ) (m : ℕ) (γ : ℕ → ℝ) (s : Finset ℕ) :
    pairedPartialPoly c m γ s = C c * X ^ m * ∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) := by
  rfl

/-- Evaluating the complexification of `pairedPartialPoly c m γ s` at `z : ℂ` recovers the
corresponding finite partial product `(c : ℂ) * z ^ m * ∏ n ∈ s, (1 + z ^ 2 / (γ n : ℂ) ^ 2)`. -/
theorem eval_map_pairedPartialPoly (c : ℝ) (m : ℕ) (γ : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) :
    ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval z =
      (c : ℂ) * z ^ m * ∏ n ∈ s, (1 + z ^ 2 / (γ n : ℂ) ^ 2) := by
  rw [eval_map, ← aeval_def]
  simp only [pairedPartialPoly, map_mul, map_pow, aeval_C, aeval_X, Complex.coe_algebraMap,
    map_prod, map_add, map_one]
  congr 1
  refine Finset.prod_congr rfl fun n _ ↦ ?_
  rw [one_add_div_sq_eq_one_add_inv_sq_mul]
  push_cast
  ring

private theorem coeff_one_add_C_inv_sq_mul_X_sq_nonneg (y : ℝ) (j : ℕ) :
    0 ≤ (1 + C (y⁻¹ ^ 2) * X ^ 2).coeff j := by
  rw [coeff_add, coeff_one, coeff_C_mul_X_pow]
  split_ifs <;> positivity

/-- Every coefficient of `pairedPartialPoly c m γ s` is nonnegative when `0 ≤ c`. -/
theorem coeff_pairedPartialPoly_nonneg {c : ℝ} (hc : 0 ≤ c) (m : ℕ) (γ : ℕ → ℝ)
    (s : Finset ℕ) : ∀ d, 0 ≤ (pairedPartialPoly c m γ s).coeff d := by
  classical
  have hC : ∀ d, 0 ≤ (C c).coeff d := fun d ↦ by rw [coeff_C]; split_ifs <;> positivity
  have hX : ∀ d, 0 ≤ (X ^ m : ℝ[X]).coeff d := fun d ↦ by
    rw [coeff_X_pow]; split_ifs <;> norm_num
  have hprod : ∀ d, 0 ≤ (∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2)).coeff d := by
    refine Finset.prod_induction _ (fun p : ℝ[X] ↦ ∀ d, 0 ≤ p.coeff d)
      (fun _ _ hp hq d ↦ coeff_mul_nonneg hp hq d) (fun d ↦ ?_)
      (fun n _ ↦ coeff_one_add_C_inv_sq_mul_X_sq_nonneg (γ n))
    rw [coeff_one]; split_ifs <;> norm_num
  rw [pairedPartialPoly_def]
  exact coeff_mul_nonneg (coeff_mul_nonneg hC hX) hprod

/-- The coefficients of `pairedPartialPoly c m γ s` are monotone with respect to `s : Finset ℕ`. -/
theorem coeff_pairedPartialPoly_mono {c : ℝ} (hc : 0 ≤ c) (m : ℕ) (γ : ℕ → ℝ)
    {t s : Finset ℕ} (hts : t ⊆ s) (d : ℕ) :
    (pairedPartialPoly c m γ t).coeff d ≤ (pairedPartialPoly c m γ s).coeff d := by
  classical
  have hmono : Monotone (fun u ↦ (pairedPartialPoly c m γ u).coeff d) :=
    Finset.monotone_iff_forall_le_insert.mpr fun u n hn ↦ by
      have hstep : pairedPartialPoly c m γ (insert n u) =
          pairedPartialPoly c m γ u * (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) := by
        simp only [pairedPartialPoly_def, Finset.prod_insert hn]; ring
      rw [hstep]
      exact coeff_le_coeff_mul (coeff_pairedPartialPoly_nonneg hc m γ u)
        (coeff_one_add_C_inv_sq_mul_X_sq_nonneg (γ n)) (by simp) d
  exact hmono hts

/-- If every `n ∈ t` has `γ n ≠ 0`, the degree-`(m + 2 * t.card)` coefficient of
`pairedPartialPoly c m γ t` is `c * ∏ n ∈ t, (γ n)⁻¹ ^ 2 > 0`. -/
theorem coeff_pairedPartialPoly_top_pos {c : ℝ} (hc : 0 < c) (m : ℕ) (γ : ℕ → ℝ)
    (t : Finset ℕ) (ht : ∀ n ∈ t, γ n ≠ 0) :
    0 < (pairedPartialPoly c m γ t).coeff (m + 2 * t.card) := by
  classical
  rw [pairedPartialPoly_def]
  rw [mul_assoc, coeff_C_mul, mul_comm (X ^ m), add_comm m, coeff_mul_X_pow]
  have hdeg : ∀ n ∈ t, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2 : ℝ[X]).natDegree ≤ 2 := fun n _ ↦ by
    compute_degree!
  rw [mul_comm 2 t.card,
    coeff_prod_of_natDegree_le t (fun n ↦ 1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) 2 hdeg]
  refine mul_pos hc (Finset.prod_pos fun n hn ↦ ?_)
  simp [coeff_one, sq_pos_of_ne_zero (ht n hn)]

/-- A paired quadratic product with only finitely many nonzero entries `γ n` is the evaluation of a
complex polynomial. -/
theorem exists_polynomial_eval_of_eq_mul_pow_tprod_one_add_div_sq
    {f : ℂ → ℂ} {c : ℝ} {m : ℕ} {γ : ℕ → ℝ}
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (hfin : {n : ℕ | γ n ≠ 0}.Finite) :
    ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z := by
  classical
  refine ⟨(pairedPartialPoly c m γ hfin.toFinset).map (algebraMap ℝ ℂ), fun z ↦ ?_⟩
  rw [eval_map_pairedPartialPoly, hf_eq z]
  congr 1
  rw [tprod_eq_prod (s := hfin.toFinset) fun n hn ↦ ?_]
  have hγ0 : γ n = 0 := by
    by_contra hne
    exact hn (hfin.mem_toFinset.mpr hne)
  simp [hγ0]

end TauCeti
