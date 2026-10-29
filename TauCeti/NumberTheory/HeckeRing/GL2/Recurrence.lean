/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.MultiplicationTable

import TauCeti.Algebra.LinearRecurrence.OrderTwo
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The `GL₂` multiplication table: the prime-power recurrence

Shimura's Theorem 3.24(4): the summed Hecke operators at a prime satisfy

`T(p^(k+1)) = T(p) · T(pᵏ) − p · T(p,p) · T(p^(k−1))`   for `k ≥ 1`,

which determines every `T(pᵏ)` from `T(p)` and the scalar operator. The proof feeds the
key product identity `T(p) · T(1,pᵏ) = T(1,p^(k+1)) + m · T(p,pᵏ)` into the telescoping
identity `T(1,pᵏ) = T(pᵏ) − T(p,p) · T(p^(k−2))`, by strong induction on `k`.

The recurrence then yields the full product formula
`T(pʳ) · T(pˢ) = ∑_{i ≤ r} pⁱ · T(p,p)ⁱ · T(p^(r+s−2i))` for `r ≤ s`, again by strong
induction: each summand splits in two through the recurrence, and the scalar operator is
central, so the shifted copy cancels against the subtracted term.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), recurrence section.

## Main results

* `HeckeRing.GL2.heckeTDiag_p_prime_pow_eq`: `T(p, pᵏ) = T(p,p) · T(1, p^(k−1))`.
* `HeckeRing.GL2.heckeT_prime_pow_recurrence`: the prime-power recurrence.
* `HeckeRing.GL2.heckeT_prime_pow_mul`: the product formula
  `T(pʳ) · T(pˢ) = ∑_{i ≤ r} pⁱ · T(p,p)ⁱ · T(p^(r+s−2i))` for `r ≤ s`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Theorem 3.24.
-/

public section

open Matrix HeckeRing DoubleCoset Finset HeckeRing.GLn

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

omit hp in
/-- `T(p, pᵏ) = T(p,p) · T(1, p^(k−1))` for `k ≥ 1`: the index shift at the bottom of the
divisor pair.

Like the index shift it specializes, this is unconditional: `heckeTDiag` is zero-extended,
so no positivity or primality hypothesis is needed. -/
lemma heckeTDiag_p_prime_pow_eq (k : ℕ) (hk : 0 < k) :
    heckeTDiag p (p ^ k) = heckeTScalar p * heckeTDiag 1 (p ^ (k - 1)) := by
  have h0 := heckeTScalar_mul_heckeTDiag_prime_pow p 0 (k - 1)
  rw [show k - 1 + 1 = k from Nat.succ_pred_eq_of_pos hk] at h0
  simpa [pow_zero, zero_add, pow_one] using h0.symm

/-- **The scalar operator is central**, in the form `T(1, p) · T(p,p) = T(p,p) · T(1, p)`.
Every commutation below is this one transported: the `T(p)` form is it after
`heckeT_prime`, and the `p • T(p,p)` form is that scaled. Primality plays no part. -/
private lemma commute_heckeTDiag_one_heckeTScalar :
    Commute (heckeTDiag 1 p) (heckeTScalar p) :=
  -- transposition is an anti-involution fixing every Hecke coset, and a ring carrying one is
  -- commutative on the cosets it fixes
  HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
    (transposeAntiInvolution_onHeckeCoset_eq_self 2) (heckeTDiag 1 p) (heckeTScalar p)

include hp in
/-- `T(p)` commutes with the scalar operator `T(p,p)`. The shape the recurrence steps meet,
whose left factor is written `T(p)` rather than `T(1, p)`. -/
private lemma commute_heckeT_prime_heckeTScalar :
    Commute (heckeT p) (heckeTScalar p) := by
  rw [heckeT_prime p hp]
  exact commute_heckeTDiag_one_heckeTScalar p

include hp in
/-- The inductive step of the recurrence for exponents `≥ 3`: substitute the recurrence at
`k` into the key product identity, then rearrange. -/
private lemma heckeT_prime_pow_recurrence_step (k : ℕ) (hk_pos : 0 < k)
    (ih : ∀ j : ℕ, j < k + 2 → 0 < j →
      heckeT (p ^ (j + 1)) =
        heckeT p * heckeT (p ^ j) - (p : ℤ) • (heckeTScalar p * heckeT (p ^ (j - 1)))) :
    heckeT (p ^ (k + 2 + 1)) =
      heckeT p * heckeT (p ^ (k + 2)) - (p : ℤ) • (heckeTScalar p * heckeT (p ^ (k + 1))) := by
  have h5 := heckeT_prime_mul_heckeTDiag_one_prime_pow p hp (k + 2)
  rw [heckeTDiag_p_prime_pow_eq p (k + 2) (by omega)] at h5
  have h2 := heckeTDiag_one_prime_pow_eq p hp (k + 2 + 1) (by omega)
  conv at h2 => rhs; rw [show (k + 2 + 1) - 2 = k + 1 by omega]
  rw [h2] at h5
  simp only [show k + 2 ≠ 1 by omega, ite_false, show k + 2 - 1 = k + 1 by omega] at h5
  rw [heckeTDiag_one_prime_pow_eq p hp (k + 2) (by omega)] at h5
  -- distribute `T(p)` over the telescoped difference
  rw [mul_sub] at h5
  have h2k1 := heckeTDiag_one_prime_pow_eq p hp (k + 1) (by omega)
  conv at h2k1 => rhs; rw [show (k + 1) - 2 = k - 1 by omega]
  rw [h2k1] at h5
  conv at h5 => lhs; rw [show k + 2 - 2 = k by omega]
  -- and `T(p,p)` over the difference on the right
  conv at h5 => rhs; rw [mul_sub]
  -- the scalar operator is central, and the induction hypothesis rewrites `T(p) · T(pᵏ)`
  have hcomm := (commute_heckeT_prime_heckeTScalar p hp).eq
  have hih : heckeT p * heckeT (p ^ k) =
      heckeT (p ^ (k + 1)) + (p : ℤ) • (heckeTScalar p * heckeT (p ^ (k - 1))) := by
    rw [ih k (by omega) hk_pos]
    abel
  rw [smul_sub,
    ← mul_assoc (heckeT p) (heckeTScalar p) (heckeT (p ^ k)),
    hcomm,
    mul_assoc (heckeTScalar p) (heckeT p) (heckeT (p ^ k)),
    hih, mul_add (heckeTScalar p), mul_smul_comm (p : ℤ),
    ← mul_assoc (heckeTScalar p) (heckeTScalar p), sub_eq_iff_eq_add] at h5
  linear_combination (norm := module) -h5

include hp in
/-- The prime-power recurrence at `k = 1`: `T(p²) = T(p)² − p · T(p,p)`. -/
private lemma heckeT_prime_pow_recurrence_one :
    heckeT (p ^ (1 + 1)) =
      heckeT p * heckeT (p ^ 1) - (p : ℤ) • (heckeTScalar p * heckeT (p ^ (1 - 1))) := by
  have h5 := heckeT_prime_mul_heckeTDiag_one_prime_pow p hp 1
  rw [heckeTDiag_p_prime_pow_eq p 1 (by omega)] at h5
  have h2 := heckeTDiag_one_prime_pow_eq p hp (1 + 1) (by omega)
  -- `heckeTDiag_one_prime_pow_eq` spells the exponent `(k + 1) - 2`, while `h5` and the goal
  -- carry it as `k - 1`. Equal, but not syntactically so: normalising either side to the
  -- numeral instead leaves the `rw [h2] at h5` below with no matching pattern.
  conv at h2 => rhs; rw [show (1 + 1) - 2 = 1 - 1 by omega]
  rw [h2] at h5
  simp only [Nat.sub_self, ite_true] at h5 ⊢
  rw [pow_zero, heckeT_one, heckeTDiag_one_one, mul_one, pow_one, heckeT_prime p hp] at h5
  rw [pow_zero, heckeT_one, mul_one, pow_one, heckeT_prime p hp]
  rw [add_smul, one_smul] at h5
  linear_combination (norm := module) -h5

include hp in
/-- The prime-power recurrence at `k = 2`: `T(p³) = T(p) · T(p²) − p · T(p,p) · T(p)`. -/
private lemma heckeT_prime_pow_recurrence_two :
    heckeT (p ^ (2 + 1)) =
      heckeT p * heckeT (p ^ 2) - (p : ℤ) • (heckeTScalar p * heckeT (p ^ (2 - 1))) := by
  have h5 := heckeT_prime_mul_heckeTDiag_one_prime_pow p hp 2
  rw [heckeTDiag_p_prime_pow_eq p 2 (by omega)] at h5
  have h2 := heckeTDiag_one_prime_pow_eq p hp (2 + 1) (by omega)
  -- as at `k = 1`: the exponent must be respelled the way `h5` writes it, since normalising
  -- to the numeral leaves the `rw [h2] at h5` below with no matching pattern.
  conv at h2 => rhs; rw [show (2 + 1) - 2 = 2 - 1 by omega]
  rw [h2] at h5
  -- the multiplicity carries an `if k = 1` guard that has to be discharged before the
  -- exponent can be reduced; the numeral simprocs (`Nat.reduceSub`, `reduceIte`) do both at
  -- once and over-reduce, leaving the closing `linear_combination` shapes `ring` cannot match
  simp only [show (2 : ℕ) ≠ 1 by omega, ite_false, show (2 : ℕ) - 1 = 1 by omega] at h5 ⊢
  rw [heckeTDiag_one_prime_pow_eq p hp 2 (by omega)] at h5
  rw [mul_sub] at h5
  simp only [Nat.sub_self] at h5 ⊢
  rw [pow_zero, heckeT_one, mul_one, pow_one, heckeT_prime p hp] at h5
  rw [pow_one, heckeT_prime p hp]
  rw [(commute_heckeTDiag_one_heckeTScalar p).eq] at h5
  linear_combination (norm := module) -h5

include hp in
/-- **Shimura, Theorem 3.24(4)** — the prime-power recurrence:
`T(p^(k+1)) = T(p) · T(pᵏ) − p · T(p,p) · T(p^(k−1))` for `k ≥ 1`, which determines every
`T(pᵏ)` from `T(p)` and the scalar operator. -/
theorem heckeT_prime_pow_recurrence : ∀ k : ℕ, 0 < k →
    heckeT (p ^ (k + 1)) =
      heckeT p * heckeT (p ^ k) - (p : ℤ) • (heckeTScalar p * heckeT (p ^ (k - 1))) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro hk
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · exact heckeT_prime_pow_recurrence_one p hp
  rcases k with _ | k
  · exact heckeT_prime_pow_recurrence_two p hp
  · exact heckeT_prime_pow_recurrence_step p hp (k + 1) (by omega) ih

section Centrality

/-! ## The product formula

`r ↦ T(pʳ)` is a second-order linear recurrence: `heckeT_prime_pow_recurrence` says it obeys
`d (r + 2) = D * d (r + 1) - S * d r` with `D = T(p)` and `S = p • T(p,p)`. The product formula
is therefore an instance of `TauCeti.linearRec₂_mul_eq_sum_pow_mul`, which holds for any such
sequence over any ring in which `D` and `S` commute — and here they do, the scalar operator
being central. -/

include hp in
/-- `T(p)` commutes with the scalar operator `p • T(p,p)`. This is the pair the product
formula hands to `linearRec₂_mul_eq_sum_pow_mul`, whose hypothesis is exactly that the two
recurrence coefficients commute. -/
private lemma commute_heckeT_prime_smul_heckeTScalar :
    Commute (heckeT p) ((p : ℤ) • heckeTScalar p) :=
  (commute_heckeT_prime_heckeTScalar p hp).smul_right _

include hp in
/-- **Shimura, Theorem 3.24(4)** — the prime-power product formula:
`T(pʳ) · T(pˢ) = ∑_{i ≤ r} pⁱ · T(p,p)ⁱ · T(p^(r+s−2i))` for `r ≤ s`.

This is `TauCeti.linearRec₂_mul_eq_sum_pow_mul` at `d = fun r ↦ T(pʳ)`, `D = T(p)` and
`S = p • T(p,p)`; all that is left is to match the summand, since the general statement writes
`S ^ i * _` where this one writes `pⁱ • (T(p,p)ⁱ * _)`. -/
theorem heckeT_prime_pow_mul : ∀ r s : ℕ, r ≤ s →
    heckeT (p ^ r) * heckeT (p ^ s) =
      ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (heckeTScalar p ^ i * heckeT (p ^ (r + s - 2 * i))) := by
  intro r s hrs
  have hrec : ∀ n : ℕ, heckeT (p ^ (n + 2)) =
      heckeT p * heckeT (p ^ (n + 1)) - ((p : ℤ) • heckeTScalar p) * heckeT (p ^ n) := by
    intro n
    have h := heckeT_prime_pow_recurrence p hp (n + 1) (by omega)
    rw [show n + 1 + 1 = n + 2 by omega, show n + 1 - 1 = n by omega] at h
    rw [h, smul_mul_assoc]
  rw [TauCeti.linearRec₂_mul_eq_sum_pow_mul (d := fun n ↦ heckeT (p ^ n)) (by simp) (by simp)
    (commute_heckeT_prime_smul_heckeTScalar p hp) hrec hrs]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_pow, smul_mul_assoc]


end Centrality

end HeckeRing.GL2
