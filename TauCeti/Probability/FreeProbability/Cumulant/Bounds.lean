/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Probability.FreeProbability.Cumulant.Basic

/-!
# Bounds for free cumulants

For `φ : A → R` with values in a normed commutative ring, a free cumulant of a constant word
`(x, …, x)` along `s` is bounded in terms of bounds for the moments `φ (x ^ k)` with `k ≤ #s`
alone. Expanding the cumulant by Möbius inversion over the noncrossing partitions of `s` gives the
explicit bound `∑_{π ∈ NC(s)} ‖μ(π, 1_s)‖ ∏_{B ∈ π} M #B`, which depends on `x` only through the
moment bounds `M`. Families whose moments are bounded uniformly therefore have uniformly bounded
cumulants, as used in the cumulant proof of the free central limit theorem.

## Main results

* `TauCeti.norm_freeCumulant_const_le` — a free cumulant of a constant word is bounded by a
  constant depending only on bounds for the moments of its letter.
-/

public section

open Finset IncidenceAlgebra

namespace TauCeti

variable {R A α : Type*} [NormedCommRing R] [NormOneClass R] [Monoid A] [LinearOrder α]

/-- *Uniform bound for free cumulants*: if the moments of `x` of order at most `#s` are bounded by
`‖φ (x ^ k)‖ ≤ M k`, then the free cumulant of the constant word `(x, …, x)` along `s` is bounded
by `∑_{π ∈ NC(s)} ‖μ(π, 1_s)‖ ∏_{B ∈ π} M #B`, which depends on `x` only through `M`. -/
theorem norm_freeCumulant_const_le (φ : A → R) (x : A) {s : Finset α} {M : ℕ → ℝ}
    (hM : ∀ k ≤ #s, ‖φ (x ^ k)‖ ≤ M k) :
    ‖freeCumulant φ (fun _ => x) s‖ ≤
      ∑ π : NoncrossingPartition s, ‖mu R π ⊤‖ * ∏ B ∈ π.1.parts, M #B := by
  rw [freeCumulant_eq_sum_mu_mul_partitionMoment]
  refine (norm_sum_le _ _).trans (sum_le_sum fun π _ => ?_)
  rw [partitionMoment_const]
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (Finset.norm_prod_le _ _).trans (prod_le_prod₀ (fun _ _ => norm_nonneg _)
    fun B hB => hM _ (card_le_card (π.1.le hB)))

end TauCeti
