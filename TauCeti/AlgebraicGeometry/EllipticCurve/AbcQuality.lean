/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Radical.NatInt

import TauCeti.Data.Rat.AbcTriple

/-!
# The abc quality of an elliptic curve over `ℚ`

Let `E` be an elliptic curve over `ℚ` with `j`-invariant `j`. Write `j / 1728 = a / c` in lowest
terms with `c > 0`, and set `b = c - a`. Then `a + b = c` with `a`, `b`, `c` pairwise coprime.
Since `j = c₄³ / Δ` and `1728 Δ = c₄³ - c₆²`, the triple `(a, b, c)` is the reduced form of
`(c₄³, -c₆², 1728 Δ)`. The **abc quality** of `E` is the quality of that triple,
`log max(|a|, |b|, |c|) / log rad(a b c)`.

The quality is defined only for `j ≠ 0` and `j ≠ 1728`, which is exactly the condition
`a b c ≠ 0` (`a = 0` exactly when `j = 0`, by `Rat.num_ne_zero`, and `b = 0` exactly when
`j = 1728`, by `Rat.den_sub_num_ne_zero`), and `WeierstrassCurve.abcQuality` takes it as a
hypothesis. At `j = 0` or `j = 1728` the radical is `rad 0 = 1`, and the quotient would
evaluate to `0` by division by zero: a meaningful-looking number where there is no invariant.

## Main definitions

* `WeierstrassCurve.abcQuality E h`: the abc quality of `E`, for
  `h : E.j ≠ 0 ∧ E.j ≠ 1728`.

## Main results

* `WeierstrassCurve.abcQuality_eq_of_j_div_eq`: the quality is computed by any triple of integers
  `a + b = c` with `a` and `c` coprime and `j / 1728 = a / c`, whatever the sign of `c`.
* `WeierstrassCurve.abcQuality_eq_of_j_eq`: the quality depends on `j` alone. In particular it is
  invariant under an admissible change of variables, `WeierstrassCurve.variableChange_abcQuality`.
* `WeierstrassCurve.abcQuality_pos`: the quality is positive.

## Implementation notes

The radical is taken in `ℕ`, of `|a b c|`, and then cast to `ℝ`. Taken in `ℝ` it would be `1` for
every nonzero argument, since every nonzero real number is a unit.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009, §III.1:
  `j = c₄³ / Δ` and `1728 Δ = c₄³ - c₆²`.
* LMFDB, column `abc_quality` of `ec_curvedata`: "quality of the abc-triple associated to the
  `j`-invariant".

## Provenance

`abcQuality` is adapted from LeanBridge (`github.com/CBirkbeck/LeanBridge`, Apache-2.0), file
`LeanBridge/ForMathlib/4-EC.lean` at `JaneShi99/LeanBridge@d84dd305` (branch
`formalize/ec-defs`), by Jane Shi, where it is defined for every elliptic curve over `ℚ`. Here it
takes the hypothesis `j ≠ 0 ∧ j ≠ 1728`.
-/

public section

namespace WeierstrassCurve

open UniqueFactorizationMonoid

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The abc quality** of an elliptic curve `E` over `ℚ`: with `j / 1728 = a / c` in lowest terms
and `b = c - a`, the quality `log max(|a|, |b|, |c|) / log rad(a b c)` of the abc triple
`(a, b, c)`. The hypothesis `j ≠ 0 ∧ j ≠ 1728` is exactly `a b c ≠ 0`; without it the quotient
would be `0` by division by zero. -/
noncomputable def abcQuality (_h : E.j ≠ 0 ∧ E.j ≠ 1728) : ℝ :=
  let a := (E.j / 1728).num
  let c := ((E.j / 1728).den : ℤ)
  let b := c - a
  Real.log (max (max a.natAbs b.natAbs) c.natAbs) /
    Real.log (radical (a * b * c).natAbs : ℕ)

/-- `abcQuality`, unfolded. This is the interface to `WeierstrassCurve.abcQuality` outside its
defining module. -/
@[simp]
theorem abcQuality_def (h : E.j ≠ 0 ∧ E.j ≠ 1728) :
    E.abcQuality h =
      Real.log (max (max (E.j / 1728).num.natAbs
          (((E.j / 1728).den : ℤ) - (E.j / 1728).num).natAbs) ((E.j / 1728).den : ℤ).natAbs) /
        Real.log (radical ((E.j / 1728).num * (((E.j / 1728).den : ℤ) - (E.j / 1728).num) *
          ((E.j / 1728).den : ℤ)).natAbs : ℕ) :=
  (rfl)

/-- **The abc quality is the quality of any reduced triple for `j / 1728`**: if `a + b = c` with
`a` and `c` coprime and `j / 1728 = a / c`, then the abc quality of `E` is
`log max(|a|, |b|, |c|) / log rad(a b c)`. The sign of `c` is arbitrary. -/
theorem abcQuality_eq_of_j_div_eq (h : E.j ≠ 0 ∧ E.j ≠ 1728) {a b c : ℤ} (hac : IsCoprime a c)
    (habc : a + b = c) (hj : E.j / 1728 = a / c) :
    E.abcQuality h =
      Real.log (max (max a.natAbs b.natAbs) c.natAbs) /
        Real.log (radical (a * b * c).natAbs : ℕ) := by
  obtain rfl : b = c - a := eq_sub_of_add_eq' habc
  have hcop : Nat.Coprime a.natAbs c.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hac
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · -- Write `a / c` as `(-a) / (-c)` with a positive denominator.
    have hj' : E.j / 1728 = ((-a : ℤ) : ℚ) / ((-c : ℤ) : ℚ) := by
      rw [hj, Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
    have hcop' : Nat.Coprime (-a).natAbs (-c).natAbs := by rwa [Int.natAbs_neg, Int.natAbs_neg]
    have hnum := Rat.num_div_eq_of_coprime (neg_pos.mpr hc) hcop'
    have hden := Rat.den_div_eq_of_coprime (neg_pos.mpr hc) hcop'
    rw [← hj'] at hnum hden
    rw [abcQuality_def, hnum, hden]
    simp only [Int.natAbs_mul, Int.natAbs_neg, neg_sub_neg, ← neg_sub c a]
  · exact absurd (by simpa using hj) h.1
  · have hnum := Rat.num_div_eq_of_coprime hc hcop
    have hden := Rat.den_div_eq_of_coprime hc hcop
    rw [← hj] at hnum hden
    rw [abcQuality_def, hnum, hden]

/-- **The abc quality depends on `j` alone**: two elliptic curves over `ℚ` with the same
`j`-invariant have the same abc quality. -/
theorem abcQuality_eq_of_j_eq (h : E.j ≠ 0 ∧ E.j ≠ 1728) {E' : WeierstrassCurve ℚ}
    [E'.IsElliptic] (h' : E'.j ≠ 0 ∧ E'.j ≠ 1728) (hj : E.j = E'.j) :
    E.abcQuality h = E'.abcQuality h' := by
  simp only [abcQuality_def, hj]

/-- The abc quality is invariant under an admissible change of variables over `ℚ`. -/
theorem variableChange_abcQuality (C : VariableChange ℚ)
    (h' : (C • E).j ≠ 0 ∧ (C • E).j ≠ 1728) (h : E.j ≠ 0 ∧ E.j ≠ 1728) :
    (C • E).abcQuality h' = E.abcQuality h :=
  abcQuality_eq_of_j_eq _ h' h (variableChange_j E C)

/-- The abc quality is positive. -/
theorem abcQuality_pos (h : E.j ≠ 0 ∧ E.j ≠ 1728) : 0 < E.abcQuality h := by
  rw [abcQuality_def]
  set q := E.j / 1728
  have hq₀ : q ≠ 0 := div_ne_zero h.1 (by norm_num)
  have hq₁ : q ≠ 1 := (div_eq_one_iff_eq (by norm_num)).not.mpr h.2
  have ha := Rat.num_ne_zero.mpr hq₀
  have hb := q.den_sub_num_ne_zero.mpr hq₁
  have hc := q.den_pos
  have habc : q.num * (q.den - q.num) * q.den ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha hb) (Nat.cast_ne_zero.mpr q.den_ne_zero)
  -- The largest of `|a|`, `|b|`, `|c|` is at least `2`, and at most `|a b c|`.
  have hmax : 2 ≤ max (max q.num.natAbs ((q.den : ℤ) - q.num).natAbs) (q.den : ℤ).natAbs := by
    omega
  have hle : max (max q.num.natAbs ((q.den : ℤ) - q.num).natAbs) (q.den : ℤ).natAbs ≤
      (q.num * (q.den - q.num) * q.den).natAbs :=
    max_le (max_le (Int.natAbs_le_of_dvd_ne_zero (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) habc)
      (Int.natAbs_le_of_dvd_ne_zero (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) habc))
      (Int.natAbs_le_of_dvd_ne_zero (dvd_mul_left _ _) habc)
  apply div_pos <;> apply Real.log_pos
  · exact_mod_cast hmax
  · exact_mod_cast Nat.one_lt_radical_iff.mpr (by omega)

end WeierstrassCurve

end
