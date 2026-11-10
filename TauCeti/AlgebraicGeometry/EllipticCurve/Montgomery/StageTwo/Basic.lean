/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates
public import TauCeti.Data.ZMod.GCD
public import Mathlib.Algebra.Field.ZMod
import TauCeti.Data.Int.Round

/-!
# Stage-2 detection from Montgomery cross differences

Let `p ∣ n` be prime and let `Q` be a native point of the monic Montgomery model over
`ZMod p`, with `B ≠ 0`. If `[q]Q = 0` and `q = m + j` or `q = m - j`, the coordinate
pairs of `[m]Q` and `[j]Q` have vanishing cross difference. Any raw pairs over `ZMod n`
representing those coordinates modulo `p` therefore have a cross difference whose gcd
with `n` is divisible by `p`.

In the elliptic-curve method, `Q = [M]P` and the annihilation follows from
`addOrderOf P ∣ M * q`. Taking `m = i * w`, a nearest-multiple decomposition provides
`j = |q - i * w|` with `2 * j ≤ w`. The theorems here apply to arbitrary representatives,
including zero reductions, in every characteristic and without ellipticity. They detect
a prime divisor, not necessarily a proper factor; `ZMod.one_lt_gcd_val_and_gcd_val_lt_of_castHom`
can certify the latter using nonvanishing modulo another divisor.

## References

* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1:
  the stage-2 cross-difference test.
* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1: projective `x`-coordinates.
-/

public section

namespace TauCeti.Montgomery

variable {n p : ℕ} [Fact p.Prime] {A B : ZMod p}

/-- **Stage-2 detection from an annihilating scalar.** If `[q]Q = 0` and `q = m ± j`,
raw representatives modulo `p` of the coordinates of `[m]Q` and `[j]Q` have cross-difference
gcd divisible by `p`. The reduced representatives need not be nonzero. -/
theorem prime_dvd_gcd_cross_of_zsmul_eq_zero (hpn : p ∣ n) (hB : B ≠ 0)
    (Q : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {q m j : ℤ}
    (hq : q • Q = 0) (h : q = m + j ∨ q = m - j)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • Q)) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (j • Q)) = 0) :
    p ∣ Nat.gcd (R.cross S).val n := by
  apply ((R.cross S).dvd_gcd_val_iff_castHom_eq_zero hpn).mpr
  rw [← Pair.cross_map]
  have hcoords := cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero hq h
  have hRS := Pair.cross_eq_zero_trans (coordinates_ne_zero hB (m • Q)) hR hcoords
  exact Pair.cross_eq_zero_trans (coordinates_ne_zero hB (j • Q)) hRS
    (Pair.cross_eq_zero_comm.mp hS)

/-- **Stage-2 detection after the stage-1 multiplier.** If `addOrderOf P ∣ M * q` and
`q = i * w ± j`, representatives of the coordinates of `[i * w]([M]P)` and `[j]([M]P)`
modulo `p` detect `p` in their cross-difference gcd. No primality assumption on `q`,
positivity assumption on `w`, or nonzero assumption on `[M]P` is needed. -/
theorem prime_dvd_gcd_cross_of_addOrderOf_dvd_mul (hpn : p ∣ n) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {M q : ℕ} {i w j : ℤ}
    (horder : addOrderOf P ∣ M * q) (h : (q : ℤ) = i * w + j ∨ (q : ℤ) = i * w - j)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B ((i * w) • (M • P))) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B (j • (M • P))) = 0) :
    p ∣ Nat.gcd (R.cross S).val n := by
  apply prime_dvd_gcd_cross_of_zsmul_eq_zero hpn hB (M • P) R S ?_ h hR hS
  rw [natCast_zsmul, ← mul_nsmul]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp horder

/-- For a positive step `w`, there is a nearest-multiple index `i` with
`2 * |q - i * w| ≤ w` such that any representatives of the corresponding giant and baby
steps detect `p`, provided `addOrderOf P ∣ M * q`. This includes `j = 0` and the endpoint
`2 * j = w`. -/
theorem exists_two_mul_abs_sub_mul_le_and_prime_dvd_gcd_cross (hpn : p ∣ n) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) {M q : ℕ} (horder : addOrderOf P ∣ M * q)
    {w : ℤ} (hw : 0 < w) :
    ∃ i : ℤ, 2 * |(q : ℤ) - i * w| ≤ w ∧
      ∀ R S : Pair (ZMod n),
        (R.map (ZMod.castHom hpn (ZMod p))).cross
          (coordinates A B ((i * w) • (M • P))) = 0 →
        (S.map (ZMod.castHom hpn (ZMod p))).cross
          (coordinates A B (|(q : ℤ) - i * w| • (M • P))) = 0 →
        p ∣ Nat.gcd (R.cross S).val n := by
  obtain ⟨i, hi⟩ := Int.exists_two_mul_abs_sub_mul_le (q : ℤ) hw.ne'
  rw [abs_of_pos hw] at hi
  refine ⟨i, hi, fun R S hR hS ↦
    prime_dvd_gcd_cross_of_addOrderOf_dvd_mul hpn hB P R S horder ?_ hR hS⟩
  rcases abs_choice ((q : ℤ) - i * w) with h | h <;> rw [h]
  exacts [.inl (by ring), .inr (by ring)]

end TauCeti.Montgomery
