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
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Basic

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
