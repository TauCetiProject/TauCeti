/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The power series `(1 + X) ^ pⁿ - 1`

For a prime `p`, the power series `ω_n = (1 + X) ^ pⁿ - 1` over a commutative ring `O` cut out the
finite levels of the Iwasawa algebra `O⟦X⟧`. This file collects facts about them that do not
depend on the level maps. In characteristic `p` the Frobenius identity gives `ω_n = X ^ pⁿ`. Over
a local ring in which `p` is not a unit, `ω_n` lies in the `(n + 1)`-st power of the maximal ideal
of `O⟦X⟧`, so over a noetherian such ring the principal ideals `(ω_n)` meet in zero by Krull's
intersection theorem.

The polynomial counterparts, in particular that `(1 + X) ^ pⁿ - 1` is distinguished at every ideal
containing `p`, are in `TauCeti.RingTheory.Polynomial.Distinguished`.

## Main results

* `PowerSeries.one_add_X_pow_sub_one_eq_X_pow`: in characteristic `p`, `ω_n = X ^ pⁿ`.
* `PowerSeries.one_add_X_pow_sub_one_mem_maximalIdeal_pow`: `ω_n` lies in the `(n + 1)`-st power
  of the maximal ideal of `O⟦X⟧` when `p` is not a unit of the local ring `O`.
* `PowerSeries.iInf_span_one_add_X_pow_sub_one_eq_bot`: over a noetherian local ring in which `p`
  is not a unit, `⋂ₙ (ω_n) = 0`.
-/

public section

open IsLocalRing

namespace PowerSeries

variable {p : ℕ} {O : Type*} [CommRing O]

variable (p O) in
/-- **`ω_n = X ^ pⁿ` in characteristic `p`.** Over a ring of characteristic `p` the series
`(1 + X) ^ pⁿ - 1` is the monomial `X ^ pⁿ`, by the Frobenius identity. -/
theorem one_add_X_pow_sub_one_eq_X_pow [Fact p.Prime] [CharP O p] (n : ℕ) :
    (1 + X : O⟦X⟧) ^ p ^ n - 1 = X ^ p ^ n := by
  have : CharP O⟦X⟧ p := charP_of_injective_ringHom C_injective p
  rw [add_pow_char_pow, one_pow, add_sub_cancel_left]

variable [IsLocalRing O] (hp : (p : O) ∈ maximalIdeal O)
include hp

/-- The series `ω_n = (1 + X) ^ pⁿ - 1` lies in the `(n + 1)`-st power of the maximal ideal of
`O⟦X⟧`: `ω_0 = X`, and `ω_{n+1} = ω_n · ∑_{i < p} (1 + X) ^ (i pⁿ)`, whose second factor has
constant coefficient `p`. -/
theorem one_add_X_pow_sub_one_mem_maximalIdeal_pow (n : ℕ) :
    (1 + X : O⟦X⟧) ^ p ^ n - 1 ∈ maximalIdeal O⟦X⟧ ^ (n + 1) := by
  induction n with
  | zero => simpa using TauCeti.PowerSeries.X_mem_maximalIdeal
  | succ n ih =>
    rw [pow_succ p n, pow_mul, ← geom_sum_mul, pow_succ' (maximalIdeal O⟦X⟧)]
    refine Ideal.mul_mem_mul ?_ ih
    rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff, Ideal.mem_comap]
    simpa using hp

/-- **The ideals `(ω_n)` meet in zero.** Over a noetherian local ring `O` in which `p` is not a
unit, no nonzero element of `O⟦X⟧` is divisible by every `ω_n = (1 + X) ^ pⁿ - 1`, since `ω_n`
lies in the `(n + 1)`-st power of the maximal ideal of the noetherian local ring `O⟦X⟧`. -/
theorem iInf_span_one_add_X_pow_sub_one_eq_bot [IsNoetherianRing O] :
    ⨅ n : ℕ, Ideal.span {(1 + X : O⟦X⟧) ^ p ^ n - 1} = ⊥ := by
  refine eq_bot_iff.mpr <| (le_iInf fun n ↦ ?_).trans
    (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal O⟦X⟧) (maximalIdeal.isMaximal _).ne_top).le
  refine (iInf_le _ n).trans ?_
  rw [Ideal.span_singleton_le_iff_mem]
  exact Ideal.pow_le_pow_right n.le_succ (one_add_X_pow_sub_one_mem_maximalIdeal_pow hp n)

end PowerSeries
