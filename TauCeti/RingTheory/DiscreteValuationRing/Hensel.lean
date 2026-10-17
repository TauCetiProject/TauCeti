/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import TauCeti.RingTheory.Henselian.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Hensel's lemma with an estimate over a discrete valuation ring

Let `A` be a discrete valuation ring with additive valuation `v = IsDiscreteValuationRing.addVal`,
and let `F` be a polynomial over `A`. If `y₀` is an approximate root of `F` in the sense that
`2 v(F'(y₀)) < v(F(y₀))`, then `F` has a root `z` with
`v(F(y₀)) = v(F'(y₀)) + v(z − y₀)`, and `z` is the only root of `F` with
`v(F'(y₀)) < v(z − y₀)`. This is Mathlib's `hensels_lemma`, which is stated over `ℤ_[p]` in norm
spelling, here over an arbitrary Henselian discrete valuation ring (for instance a complete one,
by `TauCeti.IsAdicComplete.henselianLocalRing`) in `addVal` spelling.

The quantitative statement is what distinguishes this from `HenselianLocalRing`, which lifts a
simple root modulo the maximal ideal without a distance bound: the estimate locates the root in a
ball around `y₀` whose radius is read off `F(y₀)` and `F'(y₀)`, which is what is needed to count
roots of nearby polynomials.

Two parts of the argument need no Henselian hypothesis and are stated separately. Two distinct
roots `z ≠ z'` of `F` satisfy `v(z' − z) ≤ v(F'(z))`, by the Taylor expansion of `F` at `z`; and
the order of `F'` is constant on the ball `v(y' − y) > v(F'(y))`.

## Main results

* `Polynomial.eq_of_isRoot_of_addVal_lt`: a root of `F` closer to a root `z` than the order of
  `F'(z)` is `z`.
* `Polynomial.addVal_derivative_eval_eq_of_lt`: the order of `F'` is constant on the ball
  `v(y' − y) > v(F'(y))`.
* `Polynomial.exists_isRoot_addVal_eval_eq`: Hensel's lemma with an estimate, a root `z` with
  `v(F(y₀)) = v(F'(y₀)) + v(z − y₀)`.
* `Polynomial.existsUnique_isRoot_addVal_lt`: that root is the unique root of `F` in the ball
  `v(z − y₀) > v(F'(y₀))`.

## Implementation notes

Write `d = F'(y₀)`. The polynomial `F(y₀ + d X)` has all its coefficients divisible by `d²`: its
constant coefficient `F(y₀)` by the hypothesis, its linear coefficient `d · d`, and its higher
coefficients through the factor `dᵏ`. The quotient `G` satisfies `G(0) = F(y₀) / d² ∈ 𝔪` and
`G'(0) = 1`, so Hensel's lemma without monicity
(`TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal`) gives a root `t ∈ 𝔪` of `G`.
Writing `0 = G(t) = G(0) + t + k t²` shows `v(t) = v(G(0))`, which is the estimate for
`z = y₀ + d t`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chap. II, §2.
-/

public section

open IsDiscreteValuationRing

namespace Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- **Separation of roots.** A root `z'` of `F` whose distance to a root `z` has order larger than
that of `F'(z)` is equal to `z`. Equivalently, two distinct roots `z ≠ z'` of `F` satisfy
`addVal (z' - z) ≤ addVal (F'(z))`. -/
theorem eq_of_isRoot_of_addVal_lt (F : A[X]) {z z' : A} (hz : F.IsRoot z) (hz' : F.IsRoot z')
    (hlt : addVal A (F.derivative.eval z) < addVal A (z' - z)) : z' = z := by
  obtain ⟨k, hk⟩ := exists_mul_sq_add_linear_part_eq_eval_add F z (z' - z)
  rw [add_sub_cancel, hz'.eq_zero, hz.eq_zero, add_zero] at hk
  by_contra hne
  -- The Taylor expansion at `z` gives `(k (z' - z) + F'(z)) (z' - z) = 0`.
  have hfac : (k * (z' - z) + F.derivative.eval z) * (z' - z) = 0 := by
    linear_combination hk
  have hder : F.derivative.eval z = -(k * (z' - z)) :=
    eq_neg_of_add_eq_zero_right ((mul_eq_zero.mp hfac).resolve_right (sub_ne_zero.mpr hne))
  refine hlt.not_ge ?_
  rw [hder, addVal_le_iff_dvd]
  exact (dvd_mul_left _ _).neg_right

/-- The order of the derivative is constant on a ball whose radius exceeds it: if
`addVal (F'(y)) < addVal (y' - y)`, then `F'(y')` and `F'(y)` have the same order. -/
theorem addVal_derivative_eval_eq_of_lt (F : A[X]) {y y' : A}
    (hlt : addVal A (F.derivative.eval y) < addVal A (y' - y)) :
    addVal A (F.derivative.eval y') = addVal A (F.derivative.eval y) := by
  have hdiff : addVal A (y' - y) ≤
      addVal A (F.derivative.eval y' - F.derivative.eval y) :=
    addVal_le_iff_dvd.mpr (sub_dvd_eval_sub y' y _)
  rw [← add_sub_cancel (F.derivative.eval y) (F.derivative.eval y')]
  exact (addVal A).map_add_eq_of_lt_left (hlt.trans_le hdiff)

/-- **Hensel's lemma with an estimate** over a Henselian discrete valuation ring. If the order of
`F` at `y₀` exceeds twice the order of its derivative there, then `F` has a root `z` whose
distance to `y₀` has order exactly `addVal (F(y₀)) - addVal (F'(y₀))`. This is the existence
part of Mathlib's `hensels_lemma` in `addVal` spelling; the uniqueness of `z` in that ball is
`Polynomial.existsUnique_isRoot_addVal_lt`. -/
theorem exists_isRoot_addVal_eval_eq [HenselianLocalRing A] (F : A[X]) (y₀ : A)
    (hlt : addVal A (F.derivative.eval y₀) + addVal A (F.derivative.eval y₀) <
      addVal A (F.eval y₀)) :
    ∃ z : A, F.IsRoot z ∧
      addVal A (F.eval y₀) = addVal A (F.derivative.eval y₀) + addVal A (z - y₀) := by
  set d := F.derivative.eval y₀ with hd_def
  have hd : d ≠ 0 := by
    rintro hd0
    rw [hd0, addVal_zero, top_add] at hlt
    exact not_top_lt hlt
  -- The polynomial `F (y₀ + d X)` is `d²` times a polynomial `G`.
  have hdvd : C (d * d) ∣ (taylor y₀ F).comp (C d * X) := by
    refine (C_dvd_iff_dvd_coeff _ _).mpr fun k ↦ ?_
    rw [comp_C_mul_X_coeff]
    rcases k with _ | _ | k
    · rw [taylor_coeff_zero, pow_zero, mul_one, ← addVal_le_iff_dvd, addVal_mul]
      exact hlt.le
    · rw [taylor_coeff_one, pow_one]
    · exact (Dvd.intro (d ^ k) (by ring)).mul_left _
  obtain ⟨G, hG⟩ := hdvd
  have hGeval : ∀ t, d * d * G.eval t = F.eval (d * t + y₀) := fun t ↦ by
    rw [← eval_C (a := d * d) (x := t), ← eval_mul, ← hG, eval_comp, taylor_eval]
    simp
  have hG0 : d * d * G.eval 0 = F.eval y₀ := by simpa using hGeval 0
  have hG'0 : G.derivative.eval 0 = 1 := by
    have h := congrArg (fun p ↦ p.derivative.coeff 0) hG
    simp only [coeff_derivative, comp_C_mul_X_coeff, derivative_C_mul, coeff_C_mul] at h
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    refine (mul_left_cancel₀ (mul_ne_zero hd hd) ?_).symm
    simpa using h
  have hval : addVal A (F.eval y₀) = addVal A d + addVal A d + addVal A (G.eval 0) := by
    rw [← hG0, addVal_mul, addVal_mul]
  -- Hensel's lemma at the approximate root `0` of `G`, whose derivative there is `1`.
  have hG0m : G.eval 0 ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← addVal_eq_zero_iff]
    intro h0
    rw [hval, h0, add_zero] at hlt
    exact hlt.false
  obtain ⟨t, ht, htm⟩ := TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal G hG0m
    (hG'0 ▸ isUnit_one)
  rw [sub_zero] at htm
  refine ⟨d * t + y₀, ?_, ?_⟩
  · rw [IsRoot, ← hGeval, ht.eq_zero, mul_zero]
  -- From `0 = G(t) = G(0) + t + k t²` with `t ∈ 𝔪`, the orders of `t` and `G(0)` agree.
  obtain ⟨k, hk⟩ := exists_mul_sq_add_linear_part_eq_eval_add G 0 t
  rw [zero_add, ht.eq_zero, hG'0, one_mul] at hk
  have htpos : 0 < addVal A t := by
    rw [pos_iff_ne_zero, Ne, addVal_eq_zero_iff]
    exact htm
  have hunit : addVal A (1 + k * t) = 0 := by
    refine ((addVal A).map_add_eq_of_lt_left ?_).trans addVal_one
    rw [addVal_one, addVal_mul]
    exact htpos.trans_le le_add_self
  have hGt : G.eval 0 = -(t * (1 + k * t)) := by linear_combination hk
  rw [hval, hGt, (addVal A).map_neg, addVal_mul, hunit, add_zero, add_sub_cancel_right,
    addVal_mul, add_assoc]

/-- **Hensel's lemma with uniqueness** over a Henselian discrete valuation ring. If the order of
`F` at `y₀` exceeds twice the order of its derivative there, then `F` has exactly one root `z`
whose distance to `y₀` has order larger than that of `F'(y₀)`. Its distance to `y₀` is given by
`Polynomial.exists_isRoot_addVal_eval_eq`. -/
theorem existsUnique_isRoot_addVal_lt [HenselianLocalRing A] (F : A[X]) (y₀ : A)
    (hlt : addVal A (F.derivative.eval y₀) + addVal A (F.derivative.eval y₀) <
      addVal A (F.eval y₀)) :
    ∃! z : A, F.IsRoot z ∧ addVal A (F.derivative.eval y₀) < addVal A (z - y₀) := by
  obtain ⟨z, hz, hval⟩ := F.exists_isRoot_addVal_eval_eq y₀ hlt
  have hzlt : addVal A (F.derivative.eval y₀) < addVal A (z - y₀) :=
    lt_of_add_lt_add_left (hval ▸ hlt)
  refine ⟨z, ⟨hz, hzlt⟩, fun z' ⟨hz', hz'lt⟩ ↦ F.eq_of_isRoot_of_addVal_lt hz hz' ?_⟩
  rw [F.addVal_derivative_eval_eq_of_lt hzlt, ← sub_sub_sub_cancel_right z' z y₀]
  exact lt_min hz'lt hzlt |>.trans_le ((addVal A).map_sub _ _)

end Polynomial
