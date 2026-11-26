/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Padic.IntegralComparison

import TauCeti.NumberTheory.HeckeRing.GL2.DiagonalCosetDegree

/-!
# Rank-two `p`-adic Hecke double-coset degrees

Combining the integral `p`-adic degree comparison
(`HeckeRing.GLn.degree_padicNatPowDiagCoset_eq_degree_diagCoset`) with the `GL₂` `Γ₀`-index formula
(`HeckeRing.GL2.degree_diagCoset_of_ratio_eq_prime_pow`) gives the explicit degree `p + 1` of the
`p`-adic double coset `[GL₂(ℤ_p) · diag(1, p) · GL₂(ℤ_p)]` (and `3` at `p = 2`).

## Main results

* `HeckeRing.GL2.degree_padicNatPowDiagCoset_fin_two_one_p`: `deg(diag(1, p)) = p + 1` in rank `2`.
* `HeckeRing.GL2.degree_padicNatPowDiagCoset_fin_two_at_two`: `deg(diag(1, 2)) = 3` in rank `2` at
  `p = 2`.
-/

public section

open HeckeRing.GLn

namespace HeckeRing.GL2

/-- **Rank-`2` degree check**: the `p`-adic double coset of `diag(1, p)` in `M_2(ℤ_p) ∩ GL_2(ℚ_p)`
has degree `p + 1`, matching the global `SL_2(ℤ)` degree of `T(1, p)`. -/
theorem degree_padicNatPowDiagCoset_fin_two_one_p (p : ℕ) [Fact p.Prime] :
    (padicNatPowDiagCoset 2 p ![0, 1]).degree = p + 1 := by
  have hmono : Monotone (![0, 1] : Fin 2 → ℕ) := fun i j hij ↦ by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  rw [degree_padicNatPowDiagCoset_eq_degree_diagCoset]
  have hdeg := degree_diagCoset_of_ratio_eq_prime_pow p (Fact.out : p.Prime)
    (primePowDiag 2 p ![0, 1]) (isDvdChain_primePowDiag 2 p ![0, 1] hmono) 1 Nat.one_pos
    (by simp)
  simpa using hdeg

/-- At `p = 2` in rank `2`, the `2`-adic double coset of `diag(1, 2)` has degree `3`. -/
theorem degree_padicNatPowDiagCoset_fin_two_at_two :
    (padicNatPowDiagCoset 2 2 ![0, 1]).degree = 3 :=
  degree_padicNatPowDiagCoset_fin_two_one_p 2

end HeckeRing.GL2

end
