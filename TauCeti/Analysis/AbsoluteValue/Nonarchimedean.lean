/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Algebra.Polynomial.Monic

/-!
# Nonarchimedean absolute values

Three facts about nonarchimedean real absolute values, the first two of which Mathlib has only for
norms or for valuations. They are what is needed to describe the absolute values of a finite
extension of number fields lying over a finite place without passing to a completion: such an
absolute value is bounded on `ℤ`, hence nonarchimedean and bounded by `1` on the ring of integers,
and it is a real power, with exponent the inverse of a local degree, of the absolute value of a
finite place of the extension.

* `AbsoluteValue.isNonarchimedean_iff_forall_natCast_le_one`: an absolute value on a field is
  nonarchimedean if and only if it is bounded by `1` on the natural numbers. Mathlib has the
  forward implication for every nonarchimedean function, `IsNonarchimedean.apply_natCast_le_one`,
  and the reverse one for the norm of a normed division ring,
  `IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one`; here the latter is
  transferred to absolute values through `WithAbs`. Consequently an absolute value lying over a
  nonarchimedean one is nonarchimedean, `AbsoluteValue.isNonarchimedean_of_liesOver`.
* `IsNonarchimedean.apply_le_one_of_isIntegral`: a nonarchimedean absolute value on an
  `R`-algebra which is bounded by `1` on the image of `R` is bounded by `1` on every element
  integral over `R`. Over `ℤ` the hypothesis on `R` is automatic,
  `IsNonarchimedean.apply_le_one_of_isIntegral_int`. This is the absolute-value analogue of
  Mathlib's `Valuation.Integers.isIntegral_iff_v_le_one`, and the proof follows the same size
  argument on the equation of integrality.
* `AbsoluteValue.nonarchRpow`: for `t > 0`, the function `x ↦ v x ^ t` is again an absolute value
  when `v` is nonarchimedean, equivalent to `v`, nonarchimedean, and lying over the corresponding
  power of the restriction of `v`. For an archimedean absolute value only `t ≤ 1` works in
  general; the example at the end of the file checks that `|·| ^ 2` on `ℚ` is not an absolute
  value.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Chapter 1.
-/

public section

open Polynomial

namespace AbsoluteValue

section Field

variable {F : Type*} [Field F] {v : AbsoluteValue F ℝ}

/-- An absolute value on a field which is bounded by `1` on the natural numbers is
nonarchimedean. -/
theorem isNonarchimedean_of_forall_natCast_le_one (h : ∀ n : ℕ, v n ≤ 1) :
    IsNonarchimedean v := by
  have : IsUltrametricDist (WithAbs v) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      simpa [WithAbs.norm_eq_apply_ofAbs, ← WithAbs.equiv_apply, map_natCast] using h n
  intro x y
  have h := IsUltrametricDist.norm_add_le_max (WithAbs.toAbs v x) (WithAbs.toAbs v y)
  rwa [← WithAbs.toAbs_add, WithAbs.norm_toAbs_eq, WithAbs.norm_toAbs_eq,
    WithAbs.norm_toAbs_eq] at h

/-- An absolute value on a field is nonarchimedean if and only if it is bounded by `1` on the
natural numbers. -/
theorem isNonarchimedean_iff_forall_natCast_le_one :
    IsNonarchimedean v ↔ ∀ n : ℕ, v n ≤ 1 :=
  ⟨fun hv _ ↦ hv.apply_natCast_le_one (by simp) v.map_one,
    isNonarchimedean_of_forall_natCast_le_one⟩

/-- An absolute value on a field lying over a nonarchimedean absolute value is nonarchimedean: it
agrees with the latter on the natural numbers, where both are therefore bounded by `1`. -/
theorem isNonarchimedean_of_liesOver {K : Type*} [CommSemiring K] [Nontrivial K] [Algebra K F]
    [FaithfulSMul K F] {u : AbsoluteValue K ℝ} [v.LiesOver u] (hu : IsNonarchimedean u) :
    IsNonarchimedean v :=
  isNonarchimedean_of_forall_natCast_le_one fun n ↦ by
    have h : v (algebraMap K F n) = u n := by rw [← LiesOver.under_eq v u, under_def, comp_apply]
    rw [← map_natCast (algebraMap K F), h]
    exact hu.apply_natCast_le_one (by simp) (map_one _)

end Field

end AbsoluteValue

namespace IsNonarchimedean

variable {R F : Type*} [CommRing R] [Ring F] [Algebra R F] {v : AbsoluteValue F ℝ}

/-- A nonarchimedean absolute value on an `R`-algebra which is bounded by `1` on the image of `R`
is bounded by `1` on every element integral over `R`.

This is the absolute-value analogue of the forward implication of Mathlib's
`Valuation.Integers.isIntegral_iff_v_le_one`, and the proof follows it. -/
theorem apply_le_one_of_isIntegral (hv : IsNonarchimedean v)
    (h : ∀ r : R, v (algebraMap R F r) ≤ 1) {x : F} (hx : IsIntegral R x) : v x ≤ 1 := by
  by_contra! hx1
  have : Nontrivial F := ⟨x, 0, by rintro rfl; rw [map_zero] at hx1; linarith⟩
  obtain ⟨p, hpm, hp⟩ := hx
  have hn : p.natDegree ≠ 0 := by
    intro hn
    rw [hpm.natDegree_eq_zero] at hn
    simp [hn] at hp
  -- The equation of integrality, `x ^ n = -∑_{i < n} aᵢ xⁱ`, is violated in size.
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul,
    add_eq_zero_iff_neg_eq] at hp
  obtain ⟨i, hi, hle⟩ := hv.finset_image_add_of_nonempty
    (fun i ↦ algebraMap R F (p.coeff i) * x ^ i) (Finset.nonempty_range_iff.mpr hn)
  rw [Finset.mem_range] at hi
  have hlt : v x ^ i < v x ^ p.natDegree := pow_lt_pow_right₀ hx1 hi
  have hvx := congrArg v hp
  rw [v.map_neg, v.map_pow] at hvx
  rw [hvx, v.map_mul, v.map_pow] at hle
  exact (hle.trans (mul_le_of_le_one_left (by positivity) (h _))).not_gt hlt

/-- A nonarchimedean absolute value is bounded by `1` on every element integral over `ℤ`. -/
theorem apply_le_one_of_isIntegral_int (hv : IsNonarchimedean v) {x : F} (hx : IsIntegral ℤ x) :
    v x ≤ 1 := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · simp [Subsingleton.elim x 0]
  refine hv.apply_le_one_of_isIntegral (fun r ↦ ?_) hx
  simpa using hv.apply_intCast_le_one (by simp) v.map_one v.map_neg (n := r)

end IsNonarchimedean

namespace AbsoluteValue

variable {R : Type*} [Semiring R] (v : AbsoluteValue R ℝ) (hv : IsNonarchimedean v) {t : ℝ}
  (ht : 0 < t)

/-- The `t`-th power `x ↦ v x ^ t` of a nonarchimedean absolute value `v`, for `t > 0`, as an
absolute value. The strong triangle inequality is what makes it subadditive; for an archimedean
`v` and `t > 1` it is in general not an absolute value. -/
noncomputable def nonarchRpow : AbsoluteValue R ℝ where
  toFun x := v x ^ t
  map_mul' x y := by simp [Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) t
  eq_zero' x := by simp [Real.rpow_eq_zero (v.nonneg x) ht.ne']
  add_le' x y := by
    have hmax : v (x + y) ^ t ≤ max (v x ^ t) (v y ^ t) := by
      rw [← Real.rpow_max (v.nonneg x) (v.nonneg y) ht.le]
      exact Real.rpow_le_rpow (v.nonneg _) (hv x y) ht.le
    exact hmax.trans (max_le_add_of_nonneg (Real.rpow_nonneg (v.nonneg x) t)
      (Real.rpow_nonneg (v.nonneg y) t))

@[simp]
theorem nonarchRpow_apply (x : R) : v.nonarchRpow hv ht x = v x ^ t :=
  (rfl)

/-- A real power of a nonarchimedean absolute value is nonarchimedean. -/
theorem isNonarchimedean_nonarchRpow : IsNonarchimedean (v.nonarchRpow hv ht) := fun x y ↦ by
  simpa [Real.rpow_max (v.nonneg x) (v.nonneg y) ht.le] using
    Real.rpow_le_rpow (v.nonneg _) (hv x y) ht.le

/-- A nonarchimedean absolute value is equivalent to each of its positive real powers. -/
theorem isEquiv_nonarchRpow : v.IsEquiv (v.nonarchRpow hv ht) := fun x y ↦ by
  simp [Real.rpow_le_rpow_iff (v.nonneg x) (v.nonneg y) ht]

@[simp]
theorem nonarchRpow_one : v.nonarchRpow hv one_pos = v := by
  ext
  simp

@[simp]
theorem nonarchRpow_nonarchRpow {s : ℝ} (hs : 0 < s)
    (hv' : IsNonarchimedean (v.nonarchRpow hv hs)) :
    (v.nonarchRpow hv hs).nonarchRpow hv' ht = v.nonarchRpow hv (mul_pos hs ht) := by
  ext
  simp [Real.rpow_mul (v.nonneg _)]

/-- Real powers of nonarchimedean absolute values preserve lying over: if `w` lies over `u`, then
`w ^ t` lies over `u ^ t`. -/
theorem liesOver_nonarchRpow {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    [FaithfulSMul K L] {w : AbsoluteValue L ℝ} {u : AbsoluteValue K ℝ} [w.LiesOver u]
    (hw : IsNonarchimedean w) (hu : IsNonarchimedean u) :
    (w.nonarchRpow hw ht).LiesOver (u.nonarchRpow hu ht) := by
  refine ⟨ext fun x ↦ ?_⟩
  simp [under_def, ← LiesOver.under_eq w u]

end AbsoluteValue

/- For an archimedean absolute value a power with exponent greater than `1` need not be an
absolute value: `|·| ^ 2` on `ℚ` violates the triangle inequality at `1 + 1`. -/
example : ¬ ∃ w : AbsoluteValue ℚ ℝ, ∀ x, w x = |(x : ℝ)| ^ (2 : ℝ) := by
  rintro ⟨w, hw⟩
  have h := w.add_le 1 1
  norm_num [hw, Real.rpow_two] at h
