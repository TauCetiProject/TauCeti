/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
public import TauCeti.Combinatorics.NoncrossingPartition.Norm
public import TauCeti.Probability.FreeProbability.Cumulant.Bounds
public import TauCeti.Probability.FreeProbability.Cumulant.Series

/-!
# Exponential growth of free cumulants

If `‖φ(a^k)‖ ≤ C^k`, then `‖κ_n(a, …, a)‖ ≤ (16 C)^n`. Indeed, Möbius inversion has at most
`4^n` terms, each Möbius coefficient has norm at most `4^n`, and each block moment product
has norm at most `C^n`. The constant `16` is not claimed to be optimal.

Consequently the native free cumulant and R-series converge absolutely whenever
`16 C ‖z‖ < 1`. This supplies a disk of convergence without assuming positivity or a trace.
The R-series uses the convention `R(z) = ∑ κ_(n+1) z^n`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 10–12.
-/

public section

open Finset IncidenceAlgebra PowerSeries

namespace TauCeti

variable {R A α : Type*} [NormedCommRing R] [NormOneClass R] [Monoid A] [LinearOrder α]

/-- Exponentially bounded moments give exponentially bounded free cumulants. The estimate
includes the empty position set, whose cumulant is `1`. -/
theorem norm_freeCumulant_const_le_pow (φ : A → R) (a : A) {s : Finset α} {C : ℝ}
    (hC : 0 ≤ C) (hm : ∀ k ≤ #s, ‖φ (a ^ k)‖ ≤ C ^ k) :
    ‖freeCumulant φ (fun _ => a) s‖ ≤ (16 * C) ^ #s := by
  rw [freeCumulant_const_eq_coeff_freeCumulantSeries, coeff_freeCumulantSeries]
  have hbound : ‖freeCumulant φ (fun _ : Fin #s => a) univ‖ ≤
      ∑ π : NoncrossingPartition (univ : Finset (Fin #s)),
        ‖mu R π ⊤‖ * ∏ B ∈ π.1.parts, C ^ #B :=
    norm_freeCumulant_const_le φ a (fun k hk => hm k (by simpa using hk))
  refine hbound.trans ?_
  calc
    (∑ π : NoncrossingPartition (univ : Finset (Fin #s)),
        ‖mu R π ⊤‖ * ∏ B ∈ π.1.parts, C ^ #B)
        ≤ ∑ _π : NoncrossingPartition (univ : Finset (Fin #s)), (4 : ℝ) ^ #s * C ^ #s := by
      refine sum_le_sum fun π _ => ?_
      have hprod : ∏ B ∈ π.1.parts, C ^ #B = C ^ #s := by
        rw [prod_pow_eq_pow_sum, π.1.sum_card_parts, card_univ, Fintype.card_fin]
      rw [hprod]
      exact mul_le_mul_of_nonneg_right (NoncrossingPartition.norm_mu_top_le π) (pow_nonneg hC _)
    _ ≤ (4 : ℝ) ^ #s * ((4 : ℝ) ^ #s * C ^ #s) := by
      rw [sum_const, card_univ, nsmul_eq_mul, NoncrossingPartition.card_fin_eq_catalan]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.catalan_le_four_pow #s)
        (by positivity)
    _ = (16 * C) ^ #s := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow]
      norm_num

section Series

variable {φ : A → R} {a : A} {C : ℝ}

/-- Absolute convergence of the free cumulant series on an explicit disk. -/
theorem summable_norm_coeff_freeCumulantSeries_mul_pow (hC : 0 ≤ C)
    (hm : ∀ k, ‖φ (a ^ k)‖ ≤ C ^ k) {z : R} (hz : 16 * C * ‖z‖ < 1) :
    Summable (fun n => ‖coeff n (freeCumulantSeries φ a) * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (by positivity : 0 ≤ 16 * C * ‖z‖) hz)
  calc
    ‖coeff n (freeCumulantSeries φ a) * z ^ n‖
        ≤ (16 * C) ^ n * ‖z‖ ^ n := by
      refine (norm_mul_le _ _).trans (mul_le_mul ?_ (norm_pow_le z n) (norm_nonneg _) ?_)
      · rw [coeff_freeCumulantSeries]
        simpa using norm_freeCumulant_const_le_pow φ a (s := (univ : Finset (Fin n)))
          hC (fun k _ => hm k)
      · positivity
    _ = (16 * C * ‖z‖) ^ n := (mul_pow _ _ _).symm

/-- Absolute convergence of the shifted R-series on the same disk as the cumulant series. -/
theorem summable_norm_coeff_rSeries_mul_pow (hC : 0 ≤ C)
    (hm : ∀ k, ‖φ (a ^ k)‖ ≤ C ^ k) {z : R} (hz : 16 * C * ‖z‖ < 1) :
    Summable (fun n => ‖coeff n (rSeries φ a) * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ 16 * C * ‖z‖) hz).mul_left (16 * C))
  calc
    ‖coeff n (rSeries φ a) * z ^ n‖
        ≤ (16 * C) ^ (n + 1) * ‖z‖ ^ n := by
      refine (norm_mul_le _ _).trans (mul_le_mul ?_ (norm_pow_le z n) (norm_nonneg _) ?_)
      · rw [coeff_rSeries]
        simpa using norm_freeCumulant_const_le_pow φ a (s := (univ : Finset (Fin (n + 1))))
          hC (fun k _ => hm k)
      · positivity
    _ = 16 * C * (16 * C * ‖z‖) ^ n := by rw [pow_succ, mul_pow]; ring

end Series

end TauCeti
