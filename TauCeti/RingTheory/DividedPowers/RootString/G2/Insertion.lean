/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.G2.ShortPair

/-!
# Integral short-root insertion in the positive G₂ algebra

For positive Chevalley root vectors `x, y, z, w, v, s` corresponding to
`α, β, α+β, 2α+β, 3α+β, 3α+2β`, with `α` short, this file computes the
coefficients of `x⁽ⁿ⁾ y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾ x⁽ᶠ⁾` in the same ordered
monomials. The coefficients are natural numbers, including the powers of two and three
coming from the short-root strings. No bad prime is inverted in the coefficients.

`TauCeti.Associative.G2.dividedPower_mul_orderedMonomial` combines the two root-string
straightening rules with the central-commutator rules for `[x,w] = 3v` and `[w,z] = 3s`.
The last crossing is essential: the `w` factors released while crossing `y` need not
commute with the remaining `z` factors. The four summation indices record these four
successive crossings. The formula is an identity in a rational algebra; interpreting
it after integral specialization does not mean dividing by factorials in positive
characteristic. No independence of the ordered monomials is asserted.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The two root-string formulas are those in
`TauCeti.RingTheory.DividedPowers.RootString.G2.Basic` and
`TauCeti.RingTheory.DividedPowers.RootString.G2.ShortPair`.
-/

public section

namespace TauCeti.Associative.G2

open Finset

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z w v s : A}

/-- The positive type-G₂ ordered monomial `y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾ x⁽ᶠ⁾`. -/
noncomputable def orderedMonomial (x y z w v s : A) (a b c d e f : ℕ) : A :=
  dividedPower a y * dividedPower b z * dividedPower c w * dividedPower d v *
    dividedPower e s * dividedPower f x

/-- The six factors of a type-G₂ ordered monomial. -/
theorem orderedMonomial_def (x y z w v s : A) (a b c d e f : ℕ) :
    orderedMonomial x y z w v s a b c d e f =
      dividedPower a y * dividedPower b z * dividedPower c w * dividedPower d v *
        dividedPower e s * dividedPower f x := (rfl)

-- Only the w/z crossing is noncommutative in the product of these two tails.
private theorem collect_tails (hwz : w * z = z * w + 3 • s)
    (hzv : Commute z v) (hzs : Commute z s) (hwv : Commute w v)
    (hws : Commute w s) (hvs : Commute v s) (b c d e B C D E f : ℕ) :
    (dividedPower b z * dividedPower c w * dividedPower d v * dividedPower e s) *
        (dividedPower B z * dividedPower C w * dividedPower D v * dividedPower E s *
          dividedPower f x) =
      ∑ t ∈ range (min c B + 1),
        (3 ^ t * Nat.choose (b + (B - t)) b * Nat.choose (c - t + C) (c - t) *
          Nat.choose (d + D) d * Nat.choose (t + e) t *
          Nat.choose (t + e + E) (t + e)) •
        (dividedPower (b + (B - t)) z * dividedPower (c - t + C) w *
          dividedPower (d + D) v * dividedPower (t + e + E) s * dividedPower f x) := by
  classical
  have hmove := dividedPower_mul_dividedPower_of_commutator_eq_nsmul hwz hws hzs c B
  simp only [mul_assoc]
  rw [(commute_dividedPower_dividedPower hzs.symm e B).left_comm,
    (commute_dividedPower_dividedPower hzv.symm d B).left_comm,
    (commute_dividedPower_dividedPower hws.symm e C).left_comm,
    (commute_dividedPower_dividedPower hwv.symm d C).left_comm,
    (commute_dividedPower_dividedPower hvs.symm e D).left_comm,
    ← mul_assoc (dividedPower c w), hmove]
  simp only [mul_sum, sum_mul]
  refine sum_congr rfl fun t _ => ?_
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [(commute_dividedPower_dividedPower hws.symm t (c - t)).left_comm,
    (commute_dividedPower_dividedPower hws.symm t C).left_comm,
    (commute_dividedPower_dividedPower hvs.symm t d).left_comm,
    (commute_dividedPower_dividedPower hvs.symm t D).left_comm]
  rw [← mul_assoc (dividedPower b z), mul_dividedPower,
    ← mul_assoc (dividedPower (c - t) w), mul_dividedPower,
    ← mul_assoc (dividedPower d v), mul_dividedPower,
    ← mul_assoc (dividedPower t s), mul_dividedPower]
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [← mul_assoc (dividedPower (t + e) s), mul_dividedPower]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  congr 1
  ac_rfl

-- Cross z by the short-pair rule, then cross w by its central commutator 3v.
private theorem insert_tail (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hzs : Commute z s)
    (hwv : Commute w v) (hws : Commute w s) (hvs : Commute v s)
    (n b c d e f : ℕ) :
    dividedPower n x * (dividedPower b z * dividedPower c w * dividedPower d v *
        dividedPower e s * dividedPower f x) =
      ∑ q ∈ g2ShortPairIndex n b,
        ∑ r ∈ range (min (n - q.1 - 2 * q.2.1 - q.2.2) c + 1),
          (2 ^ q.1 * 3 ^ (q.2.1 + q.2.2) * 3 ^ r *
            Nat.choose (q.1 + (c - r)) q.1 * Nat.choose (q.2.1 + r) q.2.1 *
            Nat.choose (q.2.1 + r + d) (q.2.1 + r) * Nat.choose (q.2.2 + e) q.2.2 *
            Nat.choose (n - q.1 - 2 * q.2.1 - q.2.2 - r + f)
              (n - q.1 - 2 * q.2.1 - q.2.2 - r)) •
          (dividedPower (b - q.1 - q.2.1 - 2 * q.2.2) z *
            dividedPower (q.1 + (c - r)) w * dividedPower (q.2.1 + r + d) v *
            dividedPower (q.2.2 + e) s *
            dividedPower (n - q.1 - 2 * q.2.1 - q.2.2 - r + f) x) := by
  classical
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    dividedPower_mul_dividedPower_of_g2_short_pair hxz hxw hwz hxv hxs hzs hwv hws hvs]
  simp only [sum_mul, smul_mul_assoc]
  refine sum_congr rfl fun q _ => ?_
  have hmove := dividedPower_mul_dividedPower_of_commutator_eq_nsmul hxw hxv hwv
    (n - q.1 - 2 * q.2.1 - q.2.2) c
  simp only [mul_assoc]
  rw [← mul_assoc (dividedPower (n - q.1 - 2 * q.2.1 - q.2.2) x), hmove]
  simp only [mul_sum, sum_mul, Finset.smul_sum]
  refine sum_congr rfl fun r _ => ?_
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [(commute_dividedPower_dividedPower hws.symm q.2.2 (c - r)).left_comm,
    (commute_dividedPower_dividedPower hwv.symm q.2.1 (c - r)).left_comm,
    (commute_dividedPower_dividedPower hvs.symm q.2.2 r).left_comm,
    (commute_dividedPower_dividedPower hxv (n - q.1 - 2 * q.2.1 - q.2.2 - r) d).left_comm,
    (commute_dividedPower_dividedPower hvs.symm q.2.2 d).left_comm,
    (commute_dividedPower_dividedPower hxs (n - q.1 - 2 * q.2.1 - q.2.2 - r) e).left_comm]
  rw [← mul_assoc (dividedPower q.1 w), mul_dividedPower,
    ← mul_assoc (dividedPower q.2.1 v), mul_dividedPower]
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [← mul_assoc (dividedPower (q.2.1 + r) v), mul_dividedPower,
    ← mul_assoc (dividedPower q.2.2 s), mul_dividedPower,
    mul_dividedPower (n - q.1 - 2 * q.2.1 - q.2.2 - r) f]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
  congr 1
  ac_rfl

/-- **Integral insertion of a short simple-root divided power in type G₂.**
The indices `p`, `q`, `r`, and `t` record, respectively, the crossings of `x` with `y`,
of the residual `x` with `z`, of the residual `x` with `w`, and of the released `w`
with the remaining `z`. The local letters `N, B, K, C, D, E, F` are residual exponents.
Every coefficient is a natural number. The relations imposed are only those used in
these crossings and in collecting the commuting factors. -/
theorem dividedPower_mul_orderedMonomial
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hzv : Commute z v) (hzs : Commute z s) (hwv : Commute w v)
    (hws : Commute w s) (hvs : Commute v s) (n a b c d e f : ℕ) :
    dividedPower n x * orderedMonomial x y z w v s a b c d e f =
      ∑ p ∈ chainG2Index n a,
        let N := n - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2
        ∑ q ∈ g2ShortPairIndex N b,
          let B := b - q.1 - q.2.1 - 2 * q.2.2
          let K := N - q.1 - 2 * q.2.1 - q.2.2
          ∑ r ∈ range (min K c + 1),
            let C := q.1 + (c - r)
            let D := q.2.1 + r + d
            let E := q.2.2 + e
            let F := K - r + f
            ∑ t ∈ range (min p.2.1 B + 1),
              (2 ^ q.1 * 3 ^ (q.2.1 + q.2.2) * 3 ^ r *
                Nat.choose C q.1 * Nat.choose (q.2.1 + r) q.2.1 *
                Nat.choose D (q.2.1 + r) * Nat.choose E q.2.2 * Nat.choose F (K - r) *
                (3 ^ t * Nat.choose (p.1 + (B - t)) p.1 *
                  Nat.choose (p.2.1 - t + C) (p.2.1 - t) *
                  Nat.choose (p.2.2.1 + D) p.2.2.1 * Nat.choose (t + p.2.2.2) t *
                  Nat.choose (t + p.2.2.2 + E) (t + p.2.2.2))) •
              orderedMonomial x y z w v s (a - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2)
                (p.1 + (B - t)) (p.2.1 - t + C) (p.2.2.1 + D) (t + p.2.2.2 + E) F := by
  classical
  simp only [orderedMonomial_def]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul
      hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs]
  simp only [sum_mul]
  refine sum_congr rfl fun p _ => ?_
  -- Keep the first released tail on the left while inserting the residual x into the second.
  simp only [mul_assoc]
  have htail := insert_tail hxz hxw hwz hxv hxs hzs hwv hws hvs
    (n - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) b c d e f
  simp only [mul_assoc] at htail
  rw [htail]
  simp only [mul_sum, mul_smul_comm]
  refine sum_congr rfl fun q _ => ?_
  refine sum_congr rfl fun r _ => ?_
  -- The remaining noncommuting w/z crossing accounts for the fourth summation.
  have hcollect := collect_tails (x := x) hwz hzv hzs hwv hws hvs
    p.1 p.2.1 p.2.2.1 p.2.2.2 (b - q.1 - q.2.1 - 2 * q.2.2)
    (q.1 + (c - r)) (q.2.1 + r + d) (q.2.2 + e)
    (n - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2 - q.1 - 2 * q.2.1 - q.2.2 - r + f)
  simp only [mul_assoc] at hcollect
  rw [hcollect]
  simp only [mul_sum, Finset.smul_sum]
  refine sum_congr rfl fun t _ => ?_
  simp only [mul_smul_comm, smul_smul, mul_assoc]

end TauCeti.Associative.G2
