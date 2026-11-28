/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Tactic.Ring

/-!
# Alternant determinants and the branching rule

For a commutative ring `R`, a vector `x : Fin N → R`, and an exponent sequence `l : ℕ → ℕ`, the
alternant `TauCeti.alternant x l` is the determinant `det (x a ^ (l (N - 1 - j) + j))` when
`l N = 0` and `0` otherwise.

We prove column reduction for general monotone power matrices (`det (x a ^ p j)`) and deduce the
branching rule for alternants: for an antitone `l : ℕ →₀ ℕ` and any index `i : Fin (N + 1)`,
`alternant x l` factors as `(-1) ^ i.val * (∏ a ≠ i, (x a - x i))` times the sum over all
interlacing shifts `γ ∈ Icc 0 (l - l.comapDomain Nat.succ Nat.succ_injective.injOn)` of
`x i ^ (γ.sum fun _ n ↦ n) * alternant (x ∘ i.succAbove) (l - γ)`.

## Main statements

* `TauCeti.alternant`: the alternant determinant `det (x a ^ (l (N - 1 - j) + j))` (when `l N = 0`).
* `TauCeti.det_pow_eq_det_sub_mul_geom_sum`: column reduction of `det (x a ^ p j)` for a monotone
  exponent vector `p : Fin (N + 1) → ℕ`.
* `TauCeti.alternant_succ`: the branching rule for `alternant x l` along any coordinate `i`.

## Provenance

Adapted from `Matrix.det_pow_eq_det_sub_mul_geom_sum` and `New.GL.alternant_succ` in
`grh/src/Lib/GLn/SchurModule/MinorBasis.lean` (with `New.GL.alternant` from
`grh/src/Lib/GLn/SchurModule/Basic.lean`) of `grh-lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
generalized from `ℂ` to an arbitrary commutative ring `R`.
-/

@[expose] public section

open Finset Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- For `x : Fin N → R` and `l : ℕ → ℕ`, the alternant `det (x a ^ (l (N - 1 - j) + j))` if
`l N = 0`, and `0` otherwise. -/
def alternant {N : ℕ} (x : Fin N → R) (l : ℕ → ℕ) : R :=
  if l N = 0 then det (of fun a j : Fin N ↦ x a ^ (l j.rev + j)) else 0

/-- Column reduction for a matrix of powers: for a monotone exponent sequence `p : Fin (N + 1) → ℕ`
and a row `i`, subtracting `x i ^ (p (j + 1) - p j)` times column `j` from column `j + 1` turns
entry `(a, j + 1)` into `(x a - x i)` times the geometric sum over `p j ≤ k < p (j + 1)`. -/
theorem det_pow_eq_det_sub_mul_geom_sum {N : ℕ} (x : Fin (N + 1) → R)
    (i : Fin (N + 1)) (p : Fin (N + 1) → ℕ) (h_mono : ∀ j : Fin N, p j.castSucc ≤ p j.succ) :
    det (of fun a j : Fin (N + 1) ↦ x a ^ p j) =
      det (of fun a : Fin (N + 1) ↦ Matrix.vecCons (x a ^ p 0) fun j : Fin N ↦ (x a - x i) *
        ∑ k ∈ Ico (p j.castSucc) (p j.succ), x a ^ k * x i ^ (p j.succ - 1 - k)) := by
  refine det_eq_of_forall_col_eq_smul_add_pred (fun j ↦ x i ^ (p j.succ - p j.castSucc))
    (fun _ ↦ rfl) fun a j ↦ ?_
  simp only [of_apply, Matrix.cons_val_succ, mul_geom_sum₂_Ico _ _ (h_mono j)]
  ring

/-- The branching rule for alternants over any commutative ring `R`: for an antitone finitely
supported weight `l : ℕ →₀ ℕ` and an index `i : Fin (N + 1)`, `alternant x l` expands along
row `i` as `(-1) ^ i.val * (∏ a, (x (i.succAbove a) - x i))` times the sum over interlacing
shifts `γ` of `x i ^ (γ.sum fun _ n ↦ n) * alternant (x ∘ i.succAbove) (l - γ)`. -/
theorem alternant_succ {N : ℕ} (l : ℕ →₀ ℕ) (hl_anti : Antitone l) (i : Fin (N + 1))
    (x : Fin (N + 1) → R) :
    alternant x l =
      (-1) ^ i.val * (∏ a : Fin N, (x (i.succAbove a) - x i)) *
        ∑ γ ∈ Icc 0 (l - l.comapDomain Nat.succ Nat.succ_injective.injOn),
          x i ^ (γ.sum fun _ n ↦ n) * alternant (x ∘ i.succAbove) ⇑(l - γ) := by
  have h_beyond {n : ℕ} (hn : N + 1 ≤ n) : l n ≤ l (N + 1) := hl_anti hn
  let p (j : Fin (N + 1)) : ℕ := l j.rev + j
  have h_mono (j : Fin N) : p j.castSucc ≤ p j.succ := add_le_add (hl_anti (by grind)) (by simp)
  suffices h :
      ∑ g ∈ Fintype.piFinset (fun j : Fin N ↦ Ico (p j.castSucc) (p j.succ)) with l (N + 1) = 0,
        ∑ σ : Equiv.Perm (Fin N), (-1) ^ (i : ℕ) * x i ^ l N * (((Equiv.Perm.sign σ : ℤ) : R) *
          ((∏ a : Fin N, (x (i.succAbove a) - x i)) *
            ((∏ j : Fin N, x (i.succAbove (σ j)) ^ g j) *
              x i ^ ∑ j : Fin N, (l (j.succ.rev : ℕ) + (j : ℕ) - g j)))) =
      ∑ γ ∈ Icc 0 (l - l.comapDomain Nat.succ Nat.succ_injective.injOn) with l N - γ N = 0,
        ∑ σ : Equiv.Perm (Fin N), ((-1) ^ (i : ℕ) * ∏ a : Fin N, (x (i.succAbove a) - x i)) *
          (x i ^ (γ.sum fun _ n ↦ n) * (((Equiv.Perm.sign σ : ℤ) : R) *
            ∏ j : Fin N, x (i.succAbove (σ j)) ^ (l (j.rev : ℕ) - γ (j.rev : ℕ) + (j : ℕ)))) by
    rw [alternant, det_pow_eq_det_sub_mul_geom_sum x i p h_mono, det_succ_row _ i]
    rw [sum_filter, sum_filter, ← ite_sum_zero, Finset.sum_comm] at h
    simpa [p, alternant, Fin.sum_univ_succ, det_apply', prod_univ_sum, Finset.mul_sum,
      Equiv.prod_comp _ fun a ↦ x (i.succAbove a) - x i, -Fin.val_rev, prod_mul_distrib,
      prod_pow_eq_pow_sum] using h
  clear h_mono
  let μ (g : Fin N → ℕ) (n : ℕ) : ℕ :=
    if hn : n < N then g (Fin.rev ⟨n, hn⟩) - Fin.rev ⟨n, hn⟩ else 0
  refine sum_bij' (fun g hg ↦ Finsupp.onFinset (range (N + 1)) (fun n ↦ l n - μ g n) ?support)
    (fun γ _ j ↦ (l - γ) j.rev + j) ?to_mem ?inv_mem ?left_inv ?right_inv ?terms
  case support => grind
  case to_mem | inv_mem | left_inv | right_inv =>
    simp [μ, le_tsub_iff_left (hl_anti _), -Fin.val_rev, Finsupp.le_def]
    grind
  case terms =>
    intro g hg
    rw [Finsupp.onFinset_sum (by grind) (fun _ ↦ rfl)]
    simp only [Finsupp.onFinset_apply, sum_range_succ, ← Fin.sum_univ_eq_sum_range, μ,
      Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.rev_rev, lt_self_iff_false, Nat.sub_zero]
    refine sum_congr rfl fun σ _ ↦ ?_
    have h_exp : l N + ∑ j : Fin N, (l (j.succ.rev : ℕ) + (j : ℕ) - g j) =
        ∑ j : Fin N, (l (j : ℕ) - (g j.rev - (j.rev : ℕ))) + l N := by
      rw [add_comm, ← Fin.rev_bijective.sum_comp fun j : Fin N ↦ l j - (g j.rev - j.rev)]
      exact congrArg (· + l N) (sum_congr rfl fun j _ ↦ by simp only [Fin.rev_rev]; grind)
    have h_prod : ∏ j : Fin N, x (i.succAbove (σ j)) ^ g j = ∏ j : Fin N,
        x (i.succAbove (σ j)) ^ (l (j.rev : ℕ) - (l (j.rev : ℕ) - (g j - (j : ℕ))) + (j : ℕ)) :=
      prod_congr rfl fun j _ ↦ congrArg _ (by grind)
    rw [← h_prod, ← h_exp, pow_add]; ring

end TauCeti
