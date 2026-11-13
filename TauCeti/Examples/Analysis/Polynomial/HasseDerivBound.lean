/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.ComputeDegree
public import TauCeti.Analysis.Polynomial.HasseDerivBound

/-!
# Examples of bounds on evaluated Hasse derivatives

For `f = X²` the binomial bound on `‖D^[1] f (2)‖ = 4` is `choose 1 1 + choose 2 1 · 2 = 5`; at the
point `10` it is `21` against the true value `20`, while the coarse bound is `3 · 4 · 100 = 1200`.
For `k = 3 > 2` the binomial sum is empty. For `f = 1 + X + X²` at `1` the binomial bound `3` is an
equality and the coarse bound is `12`.

The confluent Vandermonde matrix for the nodes `(0, 1)` with multiplicities `(2, 1)` has rows
`[1, 0, 0]`, `[0, 1, 0]`, `[1, 1, 1]`. With the per-node bounds `(0, 1)` its second row is bounded
by `1`; with the common bound `1` at both nodes, by `choose 2 1 = 2`. Its third row has squared
Euclidean length at most `3`.
-/

public section

open Finset

namespace TauCeti.HasseDerivBoundExample

open Polynomial

theorem norm_coeff_X_sq_le (j : ℕ) : ‖(X ^ 2 : ℂ[X]).coeff j‖ ≤ 1 := by
  rw [coeff_X_pow]; split_ifs <;> simp

theorem norm_coeff_one_add_X_add_X_sq_le (j : ℕ) :
    ‖(1 + X + X ^ 2 : ℂ[X]).coeff j‖ ≤ 1 := by
  rcases j with _ | _ | _ | j <;> simp [coeff_X, coeff_one, coeff_X_pow]

example : (hasseDeriv 1 (X ^ 2 : ℂ[X])).eval 2 = 4 := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]; norm_num

example : ‖(hasseDeriv 1 (X ^ 2 : ℂ[X])).eval 2‖ ≤ 5 := by
  refine (norm_eval_hasseDeriv_le (d := 2) (H := 1) (A := 2) (natDegree_X_pow_le 2)
    (fun j _ ↦ norm_coeff_X_sq_le j) (by simp) 1).trans_eq ?_
  rw [show Icc 1 2 = {1, 2} by ext; simp; omega]; norm_num

example : ‖(hasseDeriv 3 (X ^ 2 : ℂ[X])).eval 2‖ ≤ 0 := by
  refine (norm_eval_hasseDeriv_le (d := 2) (H := 1) (A := 2) (natDegree_X_pow_le 2)
    (fun j _ ↦ norm_coeff_X_sq_le j) (by simp) 3).trans_eq ?_
  simp

example : ‖(1 + X + X ^ 2 : ℂ[X]).eval 1‖ ≤ 3 := by
  have := norm_eval_hasseDeriv_le (f := (1 + X + X ^ 2 : ℂ[X])) (d := 2) (H := 1) (A := 1)
    (by compute_degree!) (fun j _ ↦ norm_coeff_one_add_X_add_X_sq_le j) (a := 1) (by simp) 0
  rw [show Icc 0 2 = {0, 1, 2} by ext; simp; omega] at this
  simpa using this

example : ‖(1 + X + X ^ 2 : ℂ[X]).eval 1‖ ≤ 12 := by
  have := norm_eval_hasseDeriv_le_coarse (f := (1 + X + X ^ 2 : ℂ[X])) (d := 2) (H := 1) (A := 1)
    (by compute_degree!) (fun j _ ↦ norm_coeff_one_add_X_add_X_sq_le j) (a := 1) (by simp) 0
  norm_num at this ⊢

example : ‖(hasseDeriv 1 (X ^ 2 : ℂ[X])).eval 10‖ = 20 := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial]; norm_num

example : ‖(hasseDeriv 1 (X ^ 2 : ℂ[X])).eval 10‖ ≤ 21 := by
  refine (norm_eval_hasseDeriv_le (d := 2) (H := 1) (A := 10) (natDegree_X_pow_le 2)
    (fun j _ ↦ norm_coeff_X_sq_le j) (by simp) 1).trans_eq ?_
  rw [show Icc 1 2 = {1, 2} by ext; simp; omega]; norm_num

example : ‖(hasseDeriv 1 (X ^ 2 : ℂ[X])).eval 10‖ ≤ 1200 := by
  refine (norm_eval_hasseDeriv_le_coarse (d := 2) (H := 1) (A := 10) (natDegree_X_pow_le 2)
    (fun j _ ↦ norm_coeff_X_sq_le j) (by simp) 1).trans_eq ?_
  norm_num

/-- The confluent Vandermonde matrix for the nodes `(0, 1)` with multiplicities `(2, 1)`: the entry
in row `r` and column `c` is `D^[k r] (X ^ c)` at the node `a r`, with `a = (0, 0, 1)` and
`k = (0, 1, 0)`. -/
noncomputable def confluentVandermonde : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun r c ↦ (hasseDeriv (![0, 1, 0] r) (X ^ (c : ℕ) : ℂ[X])).eval (![0, 0, 1] r)

example (c : Fin 3) : ‖confluentVandermonde 1 c‖ ≤ 1 :=
  (norm_jet_entry_le_sup' (a := (![0, 0, 1] : Fin 3 → ℂ)) (k := ![0, 1, 0])
    (e := fun c : Fin 3 ↦ (c : ℕ)) (fun _ _ ↦ rfl) (A := (![0, 0, 1] : Fin 3 → ℝ))
    (fun r ↦ by fin_cases r <;> simp) 1 c).trans <| sup'_le _ _ fun c _ ↦ by fin_cases c <;> simp

example (c : Fin 3) : ‖confluentVandermonde 1 c‖ ≤ 2 :=
  (norm_jet_entry_le_sup' (a := (![0, 0, 1] : Fin 3 → ℂ)) (k := ![0, 1, 0])
    (e := fun c : Fin 3 ↦ (c : ℕ)) (fun _ _ ↦ rfl) (A := fun _ ↦ 1)
    (fun r ↦ by fin_cases r <;> simp) 1 c).trans <| sup'_le _ _ fun c _ ↦ by fin_cases c <;> simp

example : ∑ c, ‖confluentVandermonde 2 c‖ ^ 2 ≤ 3 :=
  (sum_sq_norm_jet_entry_le (a := (![0, 0, 1] : Fin 3 → ℂ)) (k := ![0, 1, 0])
    (e := fun c : Fin 3 ↦ (c : ℕ)) (fun _ _ ↦ rfl) (A := fun _ ↦ 1)
    (fun r ↦ by fin_cases r <;> simp) 2).trans_eq <| by simp

end TauCeti.HasseDerivBoundExample
