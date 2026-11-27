/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.Basic.Real.ConjExponents

/-!
# Hölder exponent triples in `ℝ≥0∞`

Elementary facts about Hölder exponents: the missing exponent `r` of a triple with
`1/p + 1/r = 1/q` exists once `q ≤ p`; the Hölder condition `1/p + 1/q ≤ 1` bounds both
exponents below by `1` and the conjugate exponent of `p` above by `q`; the conjugate exponent
is antitone, finite for `p > 1` and greater than `1` for finite `p`; and the exponent
conjugate to `p > 2` is less than `2`, as for the supercritical exponents of planar Sobolev and
Cauchy-transform estimates, while the exponent conjugate to `p ≥ 2` is at most `2` and the exponent
conjugate to `p < 2` is greater than `2`. An exponent `p > 2` satisfies `1/p + 1/p < 1`. In `ℝ≥0`,
the only exponent conjugate to `2` is `2`.

## Main declarations

* `ENNReal.HolderTriple.of_le`: for `q ≤ p`, the triple `(p, (q⁻¹ - p⁻¹)⁻¹, q)`.
* `ENNReal.HolderTriple.exists_le_of_inv_add_inv_le`: for `1/p + 1/q ≤ 1/r`, a triple
  `(p, q', r)` with `q' ≤ q`.
* `ENNReal.one_le_left_of_inv_add_inv_le_one`, `ENNReal.one_le_right_of_inv_add_inv_le_one`:
  `1/p + 1/q ≤ 1` forces `1 ≤ p` and `1 ≤ q`.
* `ENNReal.conjExponent_le_of_inv_add_inv_le_one`: `1/p + 1/q ≤ 1` forces `p' ≤ q` for the
  conjugate exponent `p'` of `p`.
* `ENNReal.inv_add_inv_lt_one_of_two_lt`: an exponent `p > 2` satisfies `1/p + 1/p < 1`.
* `ENNReal.one_lt_conjExponent`, `ENNReal.conjExponent_ne_top`, `ENNReal.inv_toReal_conjExponent`,
  `ENNReal.conjExponent_le_conjExponent`: the conjugate exponent `p'` of a finite `p` exceeds `1`,
  is finite with `1/p' = 1 - 1/p` when `p > 1`, and decreases as `p` increases.
* `ENNReal.HolderConjugate.lt_two`: the conjugate of an exponent `p > 2` is less than `2`.
* `ENNReal.HolderConjugate.le_two`: the conjugate of an exponent `p ≥ 2` is at most `2`.
* `ENNReal.HolderConjugate.two_lt`: the conjugate of an exponent `p < 2` is greater than `2`.
* `ENNReal.HolderConjugate.le_inv_one_sub_inv`,
  `ENNReal.HolderConjugate.inv_toReal_sub_inv_toReal_inv_one_sub_inv`: for `1 ≤ p ≤ q`, the
  conjugate `q'` of `q` is at most the conjugate `p' = (1 - 1/p)⁻¹` of `p`, and
  `1/q' - 1/p' = 1/p - 1/q`.
* `NNReal.HolderConjugate.eq_two`: an exponent in `ℝ≥0` conjugate to `2` is `2`.
-/

public section

open scoped ENNReal

namespace ENNReal.HolderTriple

/-- For `q ≤ p`, the exponent `r = (q⁻¹ - p⁻¹)⁻¹` satisfies `1/p + 1/r = 1/q`. -/
theorem of_le {p q : ℝ≥0∞} (hqp : q ≤ p) : HolderTriple p (q⁻¹ - p⁻¹)⁻¹ q :=
  ⟨by rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_inv.2 hqp)]⟩

/-- If `1/p + 1/q ≤ 1/r`, there is an exponent `q' ≤ q` with `1/p + 1/q' = 1/r`. -/
theorem exists_le_of_inv_add_inv_le {p q r : ℝ≥0∞} (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) :
    ∃ q', HolderTriple p q' r ∧ q' ≤ q := by
  rcases eq_or_ne p 0 with rfl | hp
  · obtain rfl : r = 0 := ENNReal.inv_eq_top.1 (top_le_iff.1 (by simpa using hpqr))
    exact ⟨0, inferInstance, zero_le⟩
  refine ⟨(r⁻¹ - p⁻¹)⁻¹, of_le (ENNReal.inv_le_inv.1 (le_self_add.trans hpqr)),
    ENNReal.inv_le_inv.1 ?_⟩
  rw [inv_inv]
  exact ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 hp) hpqr

end ENNReal.HolderTriple

namespace ENNReal

variable {p q : ℝ≥0∞}

/-- The Hölder condition `1/p + 1/q ≤ 1` forces `1 ≤ p`. -/
theorem one_le_left_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : 1 ≤ p :=
  ENNReal.inv_le_one.1 (le_self_add.trans hpq)

/-- The Hölder condition `1/p + 1/q ≤ 1` forces `1 ≤ q`. -/
theorem one_le_right_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : 1 ≤ q :=
  ENNReal.inv_le_one.1 (le_add_self.trans hpq)

/-- Under the Hölder condition `1/p + 1/q ≤ 1`, the conjugate exponent of `p` is at most `q`. -/
theorem conjExponent_le_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : p.conjExponent ≤ q := by
  have hp1 := one_le_left_of_inv_add_inv_le_one hpq
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have h1 : p⁻¹ + p.conjExponent⁻¹ = 1 := by
    rw [HolderTriple.inv_add_inv_eq_inv p p.conjExponent 1, inv_one]
  exact ENNReal.inv_le_inv.1 (ENNReal.le_of_add_le_add_left
    (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp1).ne') (h1 ▸ hpq))

/-- The exponent conjugate to a finite exponent is greater than `1`. -/
theorem one_lt_conjExponent (hp : p ≠ ⊤) : 1 < p.conjExponent :=
  ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.2 (ENNReal.sub_ne_top hp))

/-- The exponent conjugate to an exponent greater than `1` is finite. -/
theorem conjExponent_ne_top (hp : 1 < p) : p.conjExponent ≠ ⊤ := by
  rw [ENNReal.conjExponent, Ne, ENNReal.add_eq_top, not_or, ENNReal.inv_eq_top,
    tsub_eq_zero_iff_le]
  exact ⟨ENNReal.one_ne_top, not_le.2 hp⟩

/-- For a finite exponent `p > 1`, the reciprocal of its conjugate exponent is `1 - 1/p`. -/
theorem inv_toReal_conjExponent (hp1 : 1 < p) (hp : p ≠ ⊤) :
    p.conjExponent.toReal⁻¹ = 1 - p.toReal⁻¹ := by
  have : p.HolderConjugate p.conjExponent := .conjExponent hp1.le
  have h := (HolderConjugate.toReal_of_ne_top hp (conjExponent_ne_top hp1)
    (p := p) (q := p.conjExponent)).inv_add_inv_eq_one
  linarith

/-- Taking the conjugate exponent reverses the order. -/
theorem conjExponent_le_conjExponent (hpq : p ≤ q) : q.conjExponent ≤ p.conjExponent := by
  rw [ENNReal.conjExponent, ENNReal.conjExponent]
  gcongr

/-- An exponent `p > 2` satisfies the strict Hölder condition `1/p + 1/p < 1` with itself. -/
theorem inv_add_inv_lt_one_of_two_lt (hp : 2 < p) : p⁻¹ + p⁻¹ < 1 := by
  rw [← ENNReal.inv_two_add_inv_two]
  exact ENNReal.add_lt_add (ENNReal.inv_lt_inv.2 hp) (ENNReal.inv_lt_inv.2 hp)

end ENNReal

namespace ENNReal.HolderConjugate

/-- The exponent conjugate to `p > 2` is less than `2`. -/
theorem lt_two {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : 2 < p) : q < 2 := by
  by_contra hq
  have h := ENNReal.add_lt_add_of_lt_of_le (ENNReal.inv_ne_top.2 (ne_zero q p))
    (ENNReal.inv_lt_inv.2 hp) (ENNReal.inv_le_inv.2 (not_lt.1 hq))
  rw [inv_add_inv_eq_one p q, ENNReal.inv_two_add_inv_two] at h
  exact lt_irrefl _ h

/-- The exponent conjugate to `p ≥ 2` is at most `2`. -/
theorem le_two {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : 2 ≤ p) : q ≤ 2 := by
  by_contra hq
  have h := ENNReal.add_lt_add_of_le_of_lt (ENNReal.inv_ne_top.2 (ne_zero p q))
    (ENNReal.inv_le_inv.2 hp) (ENNReal.inv_lt_inv.2 (not_le.1 hq))
  rw [inv_add_inv_eq_one p q, ENNReal.inv_two_add_inv_two] at h
  exact lt_irrefl _ h

/-- The exponent conjugate to `p < 2` is greater than `2`. -/
theorem two_lt {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p < 2) : 2 < q := by
  by_contra hq
  have h := ENNReal.add_lt_add_of_lt_of_le (ENNReal.inv_ne_top.2 two_ne_zero)
    (ENNReal.inv_lt_inv.2 hp) (ENNReal.inv_le_inv.2 (not_lt.1 hq))
  rw [inv_add_inv_eq_one p q, ENNReal.inv_two_add_inv_two] at h
  exact lt_irrefl _ h

/-- For `p ≤ q`, the exponent `q'` conjugate to `q` is at most the exponent `(1 - 1/p)⁻¹`
conjugate to `p`. -/
theorem le_inv_one_sub_inv {p q q' : ℝ≥0∞} [q'.HolderConjugate q] (hpq : p ≤ q) :
    q' ≤ (1 - p⁻¹)⁻¹ := by
  rw [← ENNReal.inv_le_inv, inv_inv, ← one_sub_inv q q']
  exact tsub_le_tsub_left (ENNReal.inv_le_inv.2 hpq) 1

/-- For `1 ≤ p`, the exponent `q'` conjugate to `q` and the exponent `(1 - 1/p)⁻¹` conjugate to `p`
have the same reciprocal gap as `p` and `q`: `1/q' - (1 - 1/p) = 1/p - 1/q`. -/
theorem inv_toReal_sub_inv_toReal_inv_one_sub_inv {p q q' : ℝ≥0∞} [q'.HolderConjugate q]
    (hp : 1 ≤ p) : q'.toReal⁻¹ - ((1 - p⁻¹)⁻¹).toReal⁻¹ = (p⁻¹).toReal - (q⁻¹).toReal := by
  rw [← ENNReal.toReal_inv, ← ENNReal.toReal_inv, inv_inv, ← one_sub_inv q q',
    ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 (one_le q q')) ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 hp) ENNReal.one_ne_top,
    _root_.sub_sub_sub_cancel_left]

end ENNReal.HolderConjugate

namespace NNReal.HolderConjugate

open scoped NNReal

/-- The only exponent in `ℝ≥0` conjugate to `2` is `2`. -/
theorem eq_two {p : ℝ≥0} (h : p.HolderConjugate 2) : p = 2 := by
  have : (2 : ℝ≥0∞).HolderConjugate p := by simpa using h.symm.coe_ennreal
  exact_mod_cast ENNReal.HolderConjugate.unique (p := 2) (q := p) 2

end NNReal.HolderConjugate
