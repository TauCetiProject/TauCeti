/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.ComputeDegree
import TauCeti.RingTheory.PowerSeries.Entire.Resultant

/-!
# Examples of entire division and entire resultants

Over an arbitrary complete normed commutative ring `R`, which may have nilpotents:

* dividing `X³` by `X² + a X + b` gives quotient `X - a` and remainder `(a² - b) X + a b`;
* `Res(X², a + b X) = a²`;
* `Res(1, F) = 1` for every `F`, including `F = 0`, while `Res(P, 0) = Res(P, P) = 0` for monic
  `P` of positive degree.
-/

open Polynomial

open scoped PowerSeries

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] (a b : R)

-- Division of `X³` by `X² + a X + b`: quotient `X - a`, remainder `(a² - b) X + a b`.
example :
    ((X ^ 3 : R[X]) : R⟦X⟧).divByMonic (X ^ 2 + C a * X + C b) = ((X - C a : R[X]) : R⟦X⟧) ∧
      ((X ^ 3 : R[X]) : R⟦X⟧).modByMonic (X ^ 2 + C a * X + C b) =
        C (a ^ 2 - b) * X + C (a * b) := by
  nontriviality R
  have hP : (X ^ 2 + C a * X + C b : R[X]).Monic := by monicity!
  rw [PowerSeries.divByMonic_coe _ hP, PowerSeries.modByMonic_coe _ hP]
  obtain ⟨hq, hr⟩ := div_modByMonic_unique (f := X ^ 3) (X - C a) (C (a ^ 2 - b) * X + C (a * b))
    hP ⟨by simp only [map_sub, map_mul, map_pow]; ring, by
      calc degree (C (a ^ 2 - b) * X + C (a * b)) ≤ 1 := by compute_degree
        _ < 2 := by norm_num
        _ = degree (X ^ 2 + C a * X + C b) := by symm; compute_degree!⟩
  exact ⟨by rw [hq], hr⟩

-- `Res(X², a + b X) = a²`, also over rings with nilpotents.
example : entireResultant (X ^ 2 : R[X]) ((C a + C b * X : R[X]) : R⟦X⟧) = a ^ 2 := by
  nontriviality R
  rw [entireResultant_coe (monic_X_pow 2) _ (n := 1) (by compute_degree!), natDegree_X_pow,
    resultant_X_pow_left _ _ _ (by compute_degree!)]
  simp

-- `Res(1, F) = 1` for every `F`, including `F = 0`.
example : entireResultant (1 : R[X]) (0 : R⟦X⟧) = 1 := entireResultant_one_left 0

-- `Res(P, 0) = Res(P, P) = 0` for monic `P` of positive degree.
example (P : R[X]) (hP : P.Monic) (hd : 0 < P.natDegree) :
    entireResultant P 0 = 0 ∧ entireResultant P P = 0 := by
  simp [entireResultant_zero_right hP, entireResultant_self hP, hd.ne']
