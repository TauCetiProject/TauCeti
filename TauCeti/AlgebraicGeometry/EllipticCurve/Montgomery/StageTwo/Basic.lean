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
`ZMod p`. If `[q]Q = 0` and `q = m + j` or `q = m - j`, the coordinate
pairs of `[m]Q` and `[j]Q` have vanishing cross difference. Any raw pairs over `ZMod n`
representing those coordinates modulo `p` therefore have a cross difference whose gcd
with `n` is divisible by `p`.

In the elliptic-curve method, `Q = [M]P` and the annihilation follows from
`addOrderOf P ∣ M * q`. Taking `m = i * w`, a nearest-multiple decomposition provides
`j = |q - i * w|` with `2 * j ≤ w`. The sufficiency theorems apply to arbitrary representatives,
including zero reductions, in every characteristic and without ellipticity. When `B ≠ 0` and both
reduced representatives are nonzero modulo `p`, divisibility `p ∣ gcd((R.cross S).val, n)` is
equivalent to `[m - j]Q = 0` or `[m + j]Q = 0` (`prime_dvd_gcd_cross_iff_zsmul_eq_zero`). Combining
annihilation modulo `p` with nonvanishing — or non-annihilation of `[m ± j]Q'` — modulo another
divisor of positive `n` certifies a proper factor.

## Main results

* `TauCeti.Montgomery.prime_dvd_gcd_cross_of_zsmul_eq_zero` and
  `TauCeti.Montgomery.prime_dvd_gcd_cross_of_addOrderOf_dvd_mul`: stage-2 prime-divisor detection
  from `[q]Q = 0` with `q = m ± j` and after the stage-1 multiplier `M`.
* `TauCeti.Montgomery.prime_dvd_gcd_cross_iff_zsmul_eq_zero` and
  `TauCeti.Montgomery.prime_dvd_gcd_cross_iff_addOrderOf_dvd_mul`: exact stage-2 prime-divisor
  criteria for `B ≠ 0` and nonzero reduced representatives.
* `TauCeti.Montgomery.exists_two_mul_abs_sub_mul_le_and_prime_dvd_gcd_cross`: existence of a
  nearest-multiple index `i` with `2 * |q - i * w| ≤ w` whose giant/baby steps detect `p`.
* `TauCeti.Montgomery.one_lt_gcd_cross_and_gcd_cross_lt_of_zsmul_eq_zero` and
  `TauCeti.Montgomery.one_lt_gcd_cross_and_gcd_cross_lt_of_zsmul_eq_zero_of_ne_zero`: stage-2
  proper-factor certificates.

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
theorem prime_dvd_gcd_cross_of_zsmul_eq_zero (hpn : p ∣ n)
    (Q : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {q m j : ℤ}
    (hq : q • Q = 0) (h : q = m + j ∨ q = m - j)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • Q)) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (j • Q)) = 0) :
    p ∣ Nat.gcd (R.cross S).val n := by
  apply ((R.cross S).dvd_gcd_val_iff_castHom_eq_zero hpn).mpr
  rw [← Pair.cross_map]
  have hcoords := cross_coordinates_zsmul_eq_zero_of_zsmul_eq_zero hq h
  have hRS := Pair.cross_eq_zero_trans (coordinates_ne_zero_of_nontrivial (m • Q)) hR hcoords
  exact Pair.cross_eq_zero_trans (coordinates_ne_zero_of_nontrivial (j • Q)) hRS
    (Pair.cross_eq_zero_comm.mp hS)

/-- **Exact stage-2 prime-divisor criterion.** When `B ≠ 0` and `R`, `S` reduce modulo `p` to
nonzero representatives of `[m]Q` and `[j]Q`, the prime `p` divides `gcd((R.cross S).val, n)` if
and only if `[m - j]Q = 0` or `[m + j]Q = 0`. Both `B ≠ 0` and nonzeroness of the reduced
representatives are necessary for the converse. -/
theorem prime_dvd_gcd_cross_iff_zsmul_eq_zero (hpn : p ∣ n) (hB : B ≠ 0)
    (Q : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {m j : ℤ}
    (hR0 : R.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hS0 : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • Q)) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (j • Q)) = 0) :
    p ∣ Nat.gcd (R.cross S).val n ↔ (m - j) • Q = 0 ∨ (m + j) • Q = 0 := by
  rw [(R.cross S).dvd_gcd_val_iff_castHom_eq_zero hpn, ← Pair.cross_map,
    cross_eq_zero_iff_zsmul_eq_zero_of_cross_coordinates_eq_zero hB hR0 hS0 hR hS]

/-- **Stage-2 detection after the stage-1 multiplier.** If `addOrderOf P ∣ M * q` and
`q = i * w ± j`, representatives of the coordinates of `[i * w]([M]P)` and `[j]([M]P)`
modulo `p` detect `p` in their cross-difference gcd. No primality assumption on `q`,
positivity assumption on `w`, or nonzero assumption on `[M]P` is needed. -/
theorem prime_dvd_gcd_cross_of_addOrderOf_dvd_mul (hpn : p ∣ n)
    (P : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {M q : ℕ} {i w j : ℤ}
    (horder : addOrderOf P ∣ M * q) (h : (q : ℤ) = i * w + j ∨ (q : ℤ) = i * w - j)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B ((i * w) • (M • P))) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B (j • (M • P))) = 0) :
    p ∣ Nat.gcd (R.cross S).val n := by
  apply prime_dvd_gcd_cross_of_zsmul_eq_zero hpn (M • P) R S ?_ h hR hS
  rw [natCast_zsmul, ← mul_nsmul]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp horder

/-- **Exact stage-2 prime-divisor criterion after the stage-1 multiplier.** When `B ≠ 0` and `R`,
`S` reduce modulo `p` to nonzero representatives of `[i * w]([M]P)` and `[j]([M]P)`, the prime `p`
divides `gcd((R.cross S).val, n)` if and only if `(addOrderOf P : ℤ)` divides `M * (i * w - j)` or
`M * (i * w + j)`. -/
theorem prime_dvd_gcd_cross_iff_addOrderOf_dvd_mul (hpn : p ∣ n) (hB : B ≠ 0)
    (P : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {M : ℕ} {i w j : ℤ}
    (hR0 : R.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hS0 : S.map (ZMod.castHom hpn (ZMod p)) ≠ 0)
    (hR : (R.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B ((i * w) • (M • P))) = 0)
    (hS : (S.map (ZMod.castHom hpn (ZMod p))).cross
      (coordinates A B (j • (M • P))) = 0) :
    p ∣ Nat.gcd (R.cross S).val n ↔
      (addOrderOf P : ℤ) ∣ M * (i * w - j) ∨ (addOrderOf P : ℤ) ∣ M * (i * w + j) := by
  rw [prime_dvd_gcd_cross_iff_zsmul_eq_zero hpn hB (M • P) R S hR0 hS0 hR hS,
    ← natCast_zsmul, ← mul_zsmul, ← mul_zsmul, mul_comm _ (M : ℤ), mul_comm _ (M : ℤ),
    ← addOrderOf_dvd_iff_zsmul_eq_zero, ← addOrderOf_dvd_iff_zsmul_eq_zero]

/-- For a positive step `w`, there is a nearest-multiple index `i` with
`2 * |q - i * w| ≤ w` such that any representatives of the corresponding giant and baby
steps detect `p`, provided `addOrderOf P ∣ M * q`. This includes `j = 0` and the endpoint
`2 * j = w`. -/
theorem exists_two_mul_abs_sub_mul_le_and_prime_dvd_gcd_cross (hpn : p ∣ n)
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
    prime_dvd_gcd_cross_of_addOrderOf_dvd_mul hpn P R S horder ?_ hR hS⟩
  rcases abs_choice ((q : ℤ) - i * w) with h | h <;> rw [h]
  exacts [.inl (by ring), .inr (by ring)]

/-- Stage-2 annihilation modulo `p`, together with a cross difference nonzero modulo another
divisor `r`, certifies a proper factor of the positive modulus. -/
theorem one_lt_gcd_cross_and_gcd_cross_lt_of_zsmul_eq_zero [NeZero n] (hpn : p ∣ n)
    (Q : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {q m j : ℤ}
    (hq : q • Q = 0) (h : q = m + j ∨ q = m - j)
    (hRp : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • Q)) = 0)
    (hSp : (S.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (j • Q)) = 0)
    {r : ℕ} (hrn : r ∣ n) (hr : ZMod.castHom hrn (ZMod r) (R.cross S) ≠ 0) :
    1 < Nat.gcd (R.cross S).val n ∧ Nat.gcd (R.cross S).val n < n :=
  (R.cross S).one_lt_gcd_val_and_gcd_val_lt_of_castHom (Fact.out : p.Prime).one_lt hpn hrn
    (((R.cross S).dvd_gcd_val_iff_castHom_eq_zero hpn).mp
      (prime_dvd_gcd_cross_of_zsmul_eq_zero hpn Q R S hq h hRp hSp)) hr

/-- **Stage-2 proper-factor certification from non-annihilation.** If `q = m ± j` annihilates `Q`
modulo a prime `p ∣ n`, while modulo another prime `r ∣ n` the model has `B' ≠ 0`, `R` and `S`
reduce to nonzero representatives of `[m]Q'` and `[j]Q'`, and neither `[m - j]Q'` nor `[m + j]Q'`
vanishes, then `gcd((R.cross S).val, n)` is strictly between `1` and `n`. Nonzeroness of `B` or of
the reductions of `R` and `S` is not required at `p`. -/
theorem one_lt_gcd_cross_and_gcd_cross_lt_of_zsmul_eq_zero_of_ne_zero [NeZero n] (hpn : p ∣ n)
    (Q : (model A B).toAffine.Point) (R S : Pair (ZMod n)) {q m j : ℤ}
    (hq : q • Q = 0) (h : q = m + j ∨ q = m - j)
    (hRp : (R.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (m • Q)) = 0)
    (hSp : (S.map (ZMod.castHom hpn (ZMod p))).cross (coordinates A B (j • Q)) = 0)
    {r : ℕ} [Fact r.Prime] {A' B' : ZMod r} (hrn : r ∣ n) (hB' : B' ≠ 0)
    (Q' : (model A' B').toAffine.Point)
    (hsub : (m - j) • Q' ≠ 0) (hadd : (m + j) • Q' ≠ 0)
    (hRr0 : R.map (ZMod.castHom hrn (ZMod r)) ≠ 0)
    (hSr0 : S.map (ZMod.castHom hrn (ZMod r)) ≠ 0)
    (hRr : (R.map (ZMod.castHom hrn (ZMod r))).cross (coordinates A' B' (m • Q')) = 0)
    (hSr : (S.map (ZMod.castHom hrn (ZMod r))).cross (coordinates A' B' (j • Q')) = 0) :
    1 < Nat.gcd (R.cross S).val n ∧ Nat.gcd (R.cross S).val n < n := by
  refine one_lt_gcd_cross_and_gcd_cross_lt_of_zsmul_eq_zero hpn Q R S hq h hRp hSp hrn ?_
  rw [Ne, ← (R.cross S).dvd_gcd_val_iff_castHom_eq_zero hrn,
    prime_dvd_gcd_cross_iff_zsmul_eq_zero hrn hB' Q' R S hRr0 hSr0 hRr hSr]
  exact not_or.mpr ⟨hsub, hadd⟩

end TauCeti.Montgomery
