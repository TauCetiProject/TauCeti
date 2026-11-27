/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianCutoff
public import TauCeti.NumberTheory.LSeries.ResidueClassTail
import TauCeti.NumberTheory.LSeries.Term

/-!
# Left-arc bounds for the continued von Mangoldt tail

Near `s = 1`, the pole-cleared tail is the difference between the uncut continued numerator
and a finite Dirichlet polynomial multiplied by `s - 1`. On the left arc of the prime-window
circle, the polynomial can be bounded at a real reference point to the right of the arc.
The continued term is controlled by the logarithmic derivatives of the Dirichlet L-functions.

The Gaussian normalization and the left-arc argument follow
`New.exists_prime_modEq_one_log_mem` in `grh/src/Lib/Analytic/Primes.lean` of lsernau/grh-lean
(revision `72fead1`).
-/

public section

open Complex DirichletCharacter Finset

namespace ArithmeticFunction.vonMangoldt

variable {q : ℕ} [NeZero q]

/-- On the prime-window circle, bound the Gaussian-weighted continued tail by the residue
and logarithmic derivative bound at `1 + z`, and the absolute mass of the removed terms at
`1 + v`. Here the removed indices have logarithm at most the Gaussian-shifted cutoff
(in particular, indices below `exp U` qualify), and `v ≥ Re z`. The first term retains the
Gaussian decay of the uncut numerator. -/
theorem norm_gaussian_mul_residueClassTailNumerator_le (a : (ZMod q)ˣ) (S : Finset ℕ)
    {X U v M : ℝ} {z : ℂ} (hz : ‖(X : ℂ) * z‖ = 1) (hv : z.re ≤ v)
    (hS : ∀ n ∈ S, Real.log n ≤ U + TauCeti.LSeries.gaussianShift X z)
    (h₀ : ‖logDeriv (LFunctionTrivChar₁ q) (1 + z)‖ ≤ M)
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖logDeriv χ.LFunction (1 + z)‖ ≤ M) :
    let G := Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2)
    ‖G * residueClassTailNumerator a S z‖ ≤
      ‖G‖ * ((q.totient : ℝ)⁻¹ + ‖z‖ * M) +
        ‖z‖ * (Real.exp ((U + TauCeti.LSeries.gaussianShift X z) * v - 2) *
          ∑ n ∈ S, ‖LSeries.term (fun m ↦ (residueClass (a : ZMod q) m : ℂ)) (1 + (v : ℂ)) n‖) := by
  intro G
  let C := U + TauCeti.LSeries.gaussianShift X z
  let t (s : ℂ) := LSeries.term (fun m ↦ (residueClass (a : ZMod q) m : ℂ)) s
  have hG : ‖G‖ = Real.exp (C * z.re - 2) := by
    have he := TauCeti.LSeries.re_gaussian_eq hz U
    dsimp only [G, C]
    rw [norm_exp]
    congr 1
    simp only [sub_re, add_re, re_ofNat] at he ⊢
    linarith only [he]
  have hterm (n : ℕ) (hn : n ∈ S) : ‖G * t (1 + z) n‖ ≤
      Real.exp (C * v - 2) * ‖t (1 + (v : ℂ)) n‖ := by
    rw [norm_mul, hG, TauCeti.LSeries.norm_term_eq_exp_mul _ _ (1 + (v : ℂ)) n,
      ← mul_assoc, ← Real.exp_add]
    simp only [add_re, one_re, ofReal_re, add_sub_add_left_eq_sub]
    gcongr
    calc
      C * z.re - 2 + Real.log n * (v - z.re)
          ≤ C * z.re - 2 + C * (v - z.re) := by
            gcongr
            exact hS n hn
      _ = C * v - 2 := by ring
  rw [residueClassTailNumerator_eq_empty_sub, mul_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_residueClassTailNumerator_empty_le a h₀ h)
      (norm_nonneg G)
  · rw [mul_left_comm, norm_mul, mul_sum, Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (sum_le_sum hterm)) (norm_nonneg z)

end ArithmeticFunction.vonMangoldt
