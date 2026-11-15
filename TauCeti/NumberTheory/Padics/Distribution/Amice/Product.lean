/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm
import TauCeti.NumberTheory.Padics.Factorial

/-!
# Cauchy products in the dual Amice stage norms

The factorial-weighted norm `amiceDualNorm p h` is submultiplicative on series with bounded
weighted coefficients. The estimate holds at the same level `h`, without passing to a larger
radius or another analytic stage. It supplies the moment-side estimate for additive convolution:
the moments of a convolution are the Cauchy product of its two moment sequences.

We first bound each weighted product coefficient by arbitrary uniform bounds on the two
factors, then establish boundedness before taking real suprema. Only ultrametricity of the
coefficient ring is required; neither completeness nor a scalar action by `ℚ_p` is needed.

The factorial weights are submultiplicative because
`⌊i / pʰ⌋! ⌊j / pʰ⌋!` divides `⌊(i + j) / pʰ⌋!` in the integers.
The coefficient sum is Mathlib's `PowerSeries.coeff_mul`.
-/

public section

open Nat

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} {h : ℕ}

section Coefficients

variable [SeminormedRing K] [IsUltrametricDist K] {F G : PowerSeries K}

/-- Uniform bounds on two factorial-weighted coefficient families give a product bound
on every weighted coefficient of their Cauchy product. -/
theorem norm_coeff_mul_mul_norm_factorial_le {C D : ℝ}
    (hF : ∀ n, ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ ≤ C)
    (hG : ∀ n, ‖G.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ ≤ D) (n : ℕ) :
    ‖(F * G).coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖ ≤ C * D := by
  have hC : 0 ≤ C := (by positivity : 0 ≤ ‖F.coeff 0‖ * ‖((0 / p ^ h)! : ℚ_[p])‖).trans (hF 0)
  have hD : 0 ≤ D := (by positivity : 0 ≤ ‖G.coeff 0‖ * ‖((0 / p ^ h)! : ℚ_[p])‖).trans (hG 0)
  have hw : 0 < ‖((n / p ^ h)! : ℚ_[p])‖ := norm_pos_iff.mpr (by
    exact_mod_cast factorial_ne_zero (n / p ^ h))
  rw [PowerSeries.coeff_mul, ← le_div_iff₀ hw]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun ij hij ↦ ?_
  rw [le_div_iff₀ hw]
  have hij' : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  calc
    ‖F.coeff ij.1 * G.coeff ij.2‖ * ‖((n / p ^ h)! : ℚ_[p])‖ ≤
        (‖F.coeff ij.1‖ * ‖G.coeff ij.2‖) *
          (‖((ij.1 / p ^ h)! : ℚ_[p])‖ * ‖((ij.2 / p ^ h)! : ℚ_[p])‖) :=
      mul_le_mul (norm_mul_le _ _)
        (hij' ▸ Padic.norm_factorial_div_add_le (p ^ h) ij.1 ij.2)
        (norm_nonneg _) (by positivity)
    _ = (‖F.coeff ij.1‖ * ‖((ij.1 / p ^ h)! : ℚ_[p])‖) *
        (‖G.coeff ij.2‖ * ‖((ij.2 / p ^ h)! : ℚ_[p])‖) := by ring
    _ ≤ C * D := mul_le_mul (hF _) (hG _) (by positivity) hC

/-- Bounded factorial-weighted coefficient families are closed under Cauchy products.
This assertion is at one fixed stage, not just on the open unit disc. -/
theorem bddAbove_norm_coeff_mul_norm_factorial_mul
    (hF : BddAbove (Set.range fun n ↦ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖))
    (hG : BddAbove (Set.range fun n ↦ ‖G.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖)) :
    BddAbove (Set.range fun n ↦ ‖(F * G).coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖) := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨D, hD⟩ := hG
  exact ⟨C * D, Set.forall_mem_range.mpr
    (norm_coeff_mul_mul_norm_factorial_le
      (Set.forall_mem_range.mp hC) (Set.forall_mem_range.mp hD))⟩

end Coefficients

variable [NormedRing K] [IsUltrametricDist K] {F G : PowerSeries K}

/-- The dual Amice stage norm is submultiplicative whenever both weighted coefficient
families are bounded. No loss of analytic level or extra constant is necessary. -/
theorem amiceDualNorm_mul_le
    (hF : BddAbove (Set.range fun n ↦ ‖F.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖))
    (hG : BddAbove (Set.range fun n ↦ ‖G.coeff n‖ * ‖((n / p ^ h)! : ℚ_[p])‖)) :
    amiceDualNorm p h (F * G) ≤ amiceDualNorm p h F * amiceDualNorm p h G := by
  exact amiceDualNorm_le <| norm_coeff_mul_mul_norm_factorial_le
    (le_amiceDualNorm hF) (le_amiceDualNorm hG)

end TauCeti
