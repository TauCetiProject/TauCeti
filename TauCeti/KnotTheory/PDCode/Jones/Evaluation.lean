/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Jones.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.KnotTheory.PDCode.ResolvedCircle.Planar
import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# Special evaluations of the Jones polynomial

For every nonempty planar oriented PD-code `D` with `c` link components, evaluating the Jones
polynomial `D.jonesPolynomial` at `t ^ (1/2) = -1` (so `t = 1`) yields `2 ^ (c - 1)`
(`TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`).

The proof evaluates the Jones state sum directly at `T ↦ -1`: each state `s` with `k(s)` circles
and `|S(s)|` `B`-smoothings contributes `(-1) ^ (|S(s)| + n₋) 2 ^ (k(s) - 1)`. Using the planar
normalization-sign parity `TauCeti.OrientedPDCode.neg_one_pow_card_false_add_negativeCrossingCount`
and doubling to clear the `-1` in the exponent, the sum reduces to
`(-1) ^ (n + c) ∑ₛ (-2) ^ k(s) = 2 ^ c` via `TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`.

## Main results

* `TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`: for a nonempty planar code, evaluating
  the Jones polynomial at `t ^ (1/2) = -1` gives `2 ^ (c - 1)`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, Theorems 14–15 (p. 107).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
-/

public section

open Finset LaurentPolynomial

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-- At `t ^ (1/2) = -1`, the Jones weight of a state `s` evaluates to `(-1) ^ (|S(s)| + n₋)`,
where `|S(s)| = #{i | s i = false}` counts the `B`-smoothings in `s`. -/
private theorem eval₂_neg_one_jonesStateWeight (D : OrientedPDCode n) (s : Fin n → Bool) :
    eval₂ (RingHom.id ℤ) (-1 : ℤˣ) (D.jonesStateWeight s) =
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) := by
  rw [jonesStateWeight_def, map_prod, negativeCrossingCount_def, Finset.card_filter,
    Finset.card_filter, ← Finset.sum_add_distrib, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> cases s i <;> simp [h]

/-- **Evaluating the Jones polynomial of a nonempty planar diagram at `t ^ (1/2) = -1` gives
`2 ^ (c - 1)`** (Jones 1985, Theorems 14–15; Lickorish 1997, Chapter 3). -/
theorem eval₂_neg_one_jonesPolynomial (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
    (hpos : 0 < D.toPDCode.componentCount) :
    eval₂ (RingHom.id ℤ) (-1 : ℤˣ) D.jonesPolynomial = (2 : ℤ) ^ (D.componentCount - 1) := by
  have heval : eval₂ (RingHom.id ℤ) (-1 : ℤˣ) D.jonesPolynomial =
      ∑ s : Fin n → Bool, (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) *
        (2 : ℤ) ^ (D.toPDCode.stateLoopCount s - 1) := by
    rw [jonesPolynomial_def, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_mul, map_pow, eval₂_neg_one_jonesStateWeight]
    have hloop : eval₂ (RingHom.id ℤ) (-1 : ℤˣ) (-(T 1 + T (-1)) : ℤ[T;T⁻¹]) = 2 := by
      simp only [map_neg, map_add, eval₂_T, zpow_one, zpow_neg_one, Units.val_neg, Units.val_one]
      norm_num
    rw [hloop]
  have hdouble : 2 * eval₂ (RingHom.id ℤ) (-1 : ℤˣ) D.jonesPolynomial =
      (2 : ℤ) ^ D.componentCount := by
    rw [heval, Finset.mul_sum]
    have hterm (s : Fin n → Bool) :
        2 * ((-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) *
            (2 : ℤ) ^ (D.toPDCode.stateLoopCount s - 1)) =
          (-1 : ℤ) ^ (n + D.componentCount) * (-2 : ℤ) ^ D.toPDCode.stateLoopCount s := by
      have hpos_s : 1 ≤ D.toPDCode.stateLoopCount s :=
        D.toPDCode.one_le_stateLoopCount_of_componentCount_pos hpos s
      have htwo : (2 : ℤ) * 2 ^ (D.toPDCode.stateLoopCount s - 1) =
          2 ^ D.toPDCode.stateLoopCount s := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hpos_s]
      rw [D.neg_one_pow_card_false_add_negativeCrossingCount hD s, pow_add, neg_pow (2 : ℤ)]
      linear_combination (-1 : ℤ) ^ (n + D.componentCount) *
        (-1 : ℤ) ^ D.toPDCode.stateLoopCount s * htwo
    simp_rw [hterm, ← Finset.mul_sum, D.toPDCode.sum_neg_two_pow_stateLoopCount, ← mul_assoc,
      ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
  obtain ⟨k, hk⟩ : ∃ k, D.toPDCode.componentCount = k + 1 :=
    ⟨D.toPDCode.componentCount - 1, by omega⟩
  rw [hk, pow_succ'] at hdouble
  rw [hk, Nat.add_sub_cancel]
  omega

end TauCeti.OrientedPDCode
