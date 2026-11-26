/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.ZMod.Units
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic

/-!
# Dirichlet L-functions at levels with the same prime factors

Raising the level without adding any prime factor leaves the L-function unchanged away from
its possible pole. For principal characters the entire pole-cleared functions agree everywhere,
including at `1`. Thus an inducing character at a smaller level with the same prime factors
can be used for analytic estimates without any correction factors.

This is the analytic comparison used in `New.exists_regularL_eq_of_sq_eq_one` in
`grh/src/Lib/Analytic/Primes.lean` of https://github.com/lsernau/grh-lean (rev. `72fead1`).
-/

public section

namespace DirichletCharacter

/-- Raising the level without adding prime factors leaves the L-function unchanged, away from
`1` in the principal case and everywhere in the nonprincipal case. -/
theorem LFunction_changeLevel_eq_of_primeFactors_eq {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) (h : N.primeFactors = M.primeFactors)
    {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) : (χ.changeLevel hMN).LFunction s = χ.LFunction s := by
  rw [LFunction_changeLevel hMN χ hs, h, Finset.prod_eq_one, mul_one]
  intro p hp
  simp [χ.map_nonunit (ZMod.not_isUnit_of_mem_primeFactors hp)]

/-- The entire pole-cleared L-functions of principal characters agree at levels with the same
prime factors, including their residue values at `1`. -/
theorem LFunctionTrivChar₁_eq_of_primeFactors_eq {M N : ℕ} [NeZero M] [NeZero N]
    (h : N.primeFactors = M.primeFactors) : LFunctionTrivChar₁ N = LFunctionTrivChar₁ M := by
  funext s
  rcases eq_or_ne s 1 with rfl | hs
  · simp only [LFunctionTrivChar₁, Function.update_self, h]
  · simp only [LFunctionTrivChar₁_apply_of_ne_one _ hs, LFunctionTrivChar_eq_mul_riemannZeta hs, h]

end DirichletCharacter
