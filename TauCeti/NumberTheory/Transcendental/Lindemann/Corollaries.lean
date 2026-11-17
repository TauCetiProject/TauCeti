/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.AlgebraicLogs

import Mathlib.Analysis.Complex.IsIntegral
import TauCeti.NumberTheory.Transcendental.Lindemann.Theorem

/-!
# The Hermite–Lindemann theorem and the transcendence of `π`

This file derives the classical consequences of the Lindemann–Weierstrass theorem
`TauCeti.linearIndependent_exp`, which says that the exponentials of pairwise distinct algebraic
numbers are linearly independent over the algebraic numbers.

* The Hermite–Lindemann theorem: `exp α` is transcendental for every nonzero algebraic `α`.
  Otherwise `exp α - β · exp 0 = 0` with `β = exp α` algebraic would be a nontrivial linear
  relation between the exponentials of the distinct algebraic numbers `α` and `0`.
* `π` is transcendental: otherwise `πi` would be a nonzero algebraic number with algebraic
  exponential `exp (πi) = -1`.
* Every nonzero logarithm of an algebraic number is transcendental, for every branch of the
  logarithm. Equivalently, the `ℚ`-subspace `TauCeti.algebraicLogs` of logarithms of algebraic
  numbers meets the algebraic numbers only in `0`.

## Main results

* `TauCeti.transcendental_exp_of_isAlgebraic`: `exp α` is transcendental for algebraic `α ≠ 0`.
* `TauCeti.transcendental_pi`: `π` is transcendental.
* `TauCeti.transcendental_of_mem_algebraicLogs`: every nonzero `λ ∈ 𝓛` is transcendental.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.2, Corollary 4.9.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §1.1, Theorem 1.2 and its reformulation for logarithms of algebraic numbers.
-/

public section

open Complex

namespace TauCeti

/-- **The Hermite–Lindemann theorem.** The exponential of a nonzero algebraic number is
transcendental. -/
theorem transcendental_exp_of_isAlgebraic {α : ℂ} (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) :
    Transcendental ℚ (exp α) := by
  intro hexp
  -- The exponentials of the distinct algebraic numbers `α` and `0` are linearly independent over
  -- the algebraic numbers, so `1 · exp α - exp α · exp 0 = 0` is impossible.
  let a : integralClosure ℚ ℂ := ⟨α, hα.isIntegral⟩
  have ha : a ≠ 0 := fun h ↦ hα0 congr(($h : ℂ))
  have hind : LinearIndependent (integralClosure ℚ ℂ) ![exp α, 1] := by
    convert linearIndependent_exp ![a, 0] (fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [ha, ha.symm]) using 1
    ext i
    fin_cases i <;> simp [a]
  have h := LinearIndependent.pair_iff.1 hind 1 (-⟨exp α, hexp.isIntegral⟩) (by
    simp [Subalgebra.smul_def])
  exact one_ne_zero h.1

/-- **The transcendence of `π`** (Lindemann). -/
theorem transcendental_pi : Transcendental ℚ Real.pi := by
  intro hπ
  -- Otherwise `πi` is a nonzero algebraic number whose exponential `-1` is algebraic.
  have hπI : IsAlgebraic ℚ ((Real.pi : ℂ) * I) :=
    (hπ.algebraMap (A := ℂ)).mul (isIntegral_I ℚ).isAlgebraic
  refine transcendental_exp_of_isAlgebraic hπI
    (mul_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero) I_ne_zero) ?_
  rw [exp_pi_mul_I]
  exact isAlgebraic_one.neg

/-- **Hermite–Lindemann for logarithms.** Every nonzero logarithm of an algebraic number, for any
branch of the logarithm, is transcendental. -/
theorem transcendental_of_mem_algebraicLogs {l : ℂ} (hl : l ∈ algebraicLogs) (hl0 : l ≠ 0) :
    Transcendental ℚ l :=
  fun h ↦ transcendental_exp_of_isAlgebraic h hl0 (mem_algebraicLogs.1 hl)

end TauCeti
