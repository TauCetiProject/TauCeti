/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Height.LocalLinearForm
import TauCeti.NumberTheory.NumberField.Global.Places.Rat

/-!
# Tests of local linear-form height bounds

The finite-place estimate needs its archimedean constant even at the `2`-adic place.
The height of an unnormalized linear-form value cannot be bounded by projective heights:
scaling a vector changes that value but not its projective height.
These examples also check the one-coordinate case and totalized division at a zero value.
-/

open Finset Height NumberField

/-- The factor `card ι ^ [K : ℚ]` cannot be dropped at a finite place: for the two constant
unit tuples, the local value of their dot product at the `2`-adic place is `1/2`. -/
example : ∃ v : FinitePlace ℚ,
    ¬ ((⨆ i : Fin 2, v ((1 : Fin 2 → ℚ) i)) * ⨆ i : Fin 2, v ((1 : Fin 2 → ℚ) i)) ≤
      mulHeight (1 : Fin 2 → ℚ) * mulHeight (1 : Fin 2 → ℚ) *
        v (∑ i : Fin 2, (1 : Fin 2 → ℚ) i * (1 : Fin 2 → ℚ) i) := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let v := FinitePlace.mk ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
  have hv : v (2 : ℚ) = 1 / 2 := by
    rw [Nat.Primes.finitePlace_mk_apply]
    have h := congrArg ((↑) : ℚ → ℝ) (padicNorm.padicNorm_p_of_prime (p := 2))
    norm_num at h ⊢
    exact h
  refine ⟨v, ?_⟩
  norm_num [hv]

/-- The finite-place estimate gives the sharp lower bound for the local value of `2`. -/
example (v : FinitePlace ℚ) : 1 / 2 ≤ v (2 : ℚ) := by
  have h := v.iSup_mul_iSup_le (1 : Fin 2 → ℚ) 1 (by norm_num)
  norm_num at h ⊢
  linarith

/-- A vector of projective height one may have a coordinate value of arbitrarily large
height. Thus the local estimate must keep the local factor of the vector, not bound the
height of an unnormalized value by its projective height. -/
example (N : ℕ) [NeZero N] : mulHeight (![N, 0] : Fin 2 → ℚ) = 1 ∧
    mulHeight₁ ((![N, 0] : Fin 2 → ℚ) 0) = N := by
  constructor
  · rw [mulHeight_swap, mulHeight_cons_zero]
    simp
  · exact_mod_cast Rat.mulHeight₁_natCast N

/-- For one nonzero coordinate at each side, the local inequality is attained exactly. -/
example (v : FinitePlace ℚ) :
    (⨆ i : Fin 1, v ((fun _ ↦ (2 : ℚ)) i)) *
        (⨆ i : Fin 1, v ((fun _ ↦ (3 : ℚ)) i)) =
      (Fintype.card (Fin 1) : ℝ) ^ Module.finrank ℚ ℚ *
        (mulHeight (fun _ : Fin 1 ↦ (2 : ℚ)) * mulHeight (fun _ : Fin 1 ↦ (3 : ℚ))) *
          v (∑ _ : Fin 1, (2 : ℚ) * 3) := by
  simp [map_mul]

/-- The normalized coordinate-height estimate also covers a vanishing linear-form value. -/
example : mulHeight₁ ((1 : ℚ) * 1 / ∑ i : Fin 2, (![1, 1] : Fin 2 → ℚ) i *
    (![1, -1] : Fin 2 → ℚ) i) = 1 := by
  norm_num [Fin.sum_univ_two]
