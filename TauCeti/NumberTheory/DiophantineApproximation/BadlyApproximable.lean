/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
public import TauCeti.FieldTheory.Minpoly.Primitive
public import TauCeti.NumberTheory.DiophantineApproximation.SimultaneousExponent
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.NumberTheory.DiophantineApproximation.Dirichlet

/-!
# Badly approximable numbers and Littlewood's conjecture

A real number `ξ` is *badly approximable* if it is irrational and there is `c > 0` with
`q ‖q ξ‖ ≥ c` for every integer `q ≥ 1`, where `‖x‖ = |x - round x|` is the distance to the
nearest integer. Equivalently, `|ξ - r| ≥ c / den(r) ^ 2` for every rational `r`
(`badlyApproximable_iff_forall_ratCast`), so for a fixed badly approximable `ξ` the constant in
Dirichlet's bound `|ξ - p / q| < 1 / q ^ 2` cannot be made arbitrarily small. Badly
approximable numbers have irrationality exponent exactly `2`
(`BadlyApproximable.irrationalityExponent_eq`), so they are not Liouville numbers, and
one-dimensional simultaneous exponent exactly `1`
(`BadlyApproximable.simultaneousExponent_eq_one`). The property is
invariant under the rational affine maps `ξ ↦ ξ + r` and `ξ ↦ r ξ` with `r ≠ 0`. Liouville's
inequality makes every real quadratic irrational badly approximable
(`badlyApproximable_of_natDegree_minpoly_eq_two`); in particular `√2` is
(`badlyApproximable_sqrt_two`).

Littlewood's conjecture asserts that `inf_{y ≥ 1} y ‖y α‖ ‖y β‖ = 0` for all real `α`, `β`. It is
open, and is recorded here only as the proposition `LittlewoodConjecture`. It holds for `α`, `β`
as soon as one of them is not badly approximable (`littlewood_of_not_badlyApproximable`), so it
reduces to pairs of badly approximable numbers (`littlewoodConjecture_iff_badlyApproximable`).
Dirichlet's theorem in nearest-integer form
(`Real.infinite_setOf_mul_abs_mul_sub_round_le_one`) gives the weaker unconditional statement
that `y ‖y α‖ ‖y β‖ ≤ 1` for infinitely many `y ≥ 1` (`Real.infinite_setOf_mul_le_one`).

## Main definitions

* `TauCeti.BadlyApproximable ξ`: `ξ` is irrational and `q ‖q ξ‖` is bounded below by a positive
  constant for `q ≥ 1`.
* `TauCeti.LittlewoodConjecture`: Littlewood's conjecture, as a proposition.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 2, §2.2,
  Exercises 2.6 and 2.7 and p. 23.
-/

public section

open Filter Polynomial
open scoped ENNReal

namespace TauCeti

/-- A real number `ξ` is *badly approximable* if it is irrational and there is a constant
`c > 0` with `c ≤ q ‖q ξ‖` for every natural number `q ≥ 1`, where `‖x‖ = |x - round x|` is
the distance from `x` to the nearest integer. -/
def BadlyApproximable (ξ : ℝ) : Prop :=
  Irrational ξ ∧ ∃ c > (0 : ℝ), ∀ q : ℕ, 0 < q → c ≤ q * |q * ξ - round (q * ξ)|

/-- The irrationality condition in `BadlyApproximable` is automatic: `ξ` is badly approximable
exactly when `q ‖q ξ‖` is bounded below by a positive constant for `q ≥ 1`. -/
theorem badlyApproximable_iff {ξ : ℝ} :
    BadlyApproximable ξ ↔ ∃ c > (0 : ℝ), ∀ q : ℕ, 0 < q → c ≤ q * |q * ξ - round (q * ξ)| := by
  refine ⟨And.right, fun ⟨c, hc, h⟩ ↦ ⟨?_, c, hc, h⟩⟩
  rintro ⟨r, rfl⟩
  have := h (1 * r.den) (by simp [r.den_pos])
  rw [r.abs_den_mul_sub_round_eq_zero, mul_zero] at this
  exact this.not_gt hc

/-- A badly approximable number is irrational. -/
theorem BadlyApproximable.irrational {ξ : ℝ} (h : BadlyApproximable ξ) : Irrational ξ :=
  h.1

/-- A rational number is not badly approximable. -/
@[simp]
theorem _root_.Rat.not_badlyApproximable (r : ℚ) : ¬BadlyApproximable r :=
  fun h ↦ r.not_irrational h.irrational

/-- `ξ` is badly approximable exactly when there is `c > 0` such that every rational number `r`
satisfies `|ξ - r| ≥ c / den(r) ^ 2`. -/
theorem badlyApproximable_iff_forall_ratCast {ξ : ℝ} :
    BadlyApproximable ξ ↔ ∃ c > (0 : ℝ), ∀ r : ℚ, c / (r.den : ℝ) ^ 2 ≤ |ξ - r| := by
  rw [badlyApproximable_iff]
  refine ⟨fun ⟨c, hc, h⟩ ↦ ⟨c, hc, fun r ↦ ?_⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, hc, fun q hq ↦ ?_⟩⟩
  · -- Compare with the integer `num r` instead of the nearest integer to `den r * ξ`.
    have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    rw [div_le_iff₀ (by positivity), mul_comm, Rat.cast_def (K := ℝ) r,
      ← mul_abs_mul_sub_eq_sq_mul_abs_sub_div hden]
    exact (h r.den r.den_pos).trans
      (mul_le_mul_of_nonneg_left (round_le _ _) hden.le)
  · -- The fraction `round (q ξ) / q` has denominator at most `q`.
    set m := round ((q : ℝ) * ξ)
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hden : ((m : ℚ) / q).den ≤ q := by
      refine Nat.le_of_dvd hq ?_
      simpa [div_eq_mul_inv, Rat.inv_natCast_den_of_pos hq] using Rat.mul_den_dvd (m : ℚ) (q⁻¹)
    have hden' : (0 : ℝ) < ((m : ℚ) / q).den := by exact_mod_cast Rat.den_pos _
    have := h ((m : ℚ) / q)
    push_cast at this
    rw [mul_abs_mul_sub_eq_sq_mul_abs_sub_div hq', ← div_le_iff₀' (by positivity)]
    exact (div_le_div_of_nonneg_left hc.le (by positivity)
      (pow_le_pow_left₀ hden'.le (by exact_mod_cast hden) 2)).trans this

/-- A badly approximable number is not a Liouville number with any exponent `p > 2`. -/
theorem BadlyApproximable.not_liouvilleWith {ξ p : ℝ} (h : BadlyApproximable ξ) (hp : 2 < p) :
    ¬LiouvilleWith p ξ := by
  intro hL
  obtain ⟨c, hc, hξ⟩ := badlyApproximable_iff.mp h
  -- Approximations with exponent `s ∈ (2, p)` exist for infinitely many denominators `n`, but
  -- `n ^ (2 - s)` eventually drops below `c`.
  obtain ⟨s, hs2, hsp⟩ := exists_between hp
  have hsmall : ∀ᶠ n : ℕ in atTop, 0 < n ∧ (n : ℝ) ^ (2 - s) < c := by
    refine (eventually_gt_atTop 0).and ?_
    have := (tendsto_rpow_neg_atTop (sub_pos.mpr hs2)).comp tendsto_natCast_atTop_atTop
    simpa [neg_sub] using this.eventually (gt_mem_nhds hc)
  obtain ⟨n, ⟨hn, hnc⟩, m, -, hm⟩ := (hsmall.and_frequently (hL.frequently_lt_rpow_neg hsp)).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : c < c := calc
    c ≤ n * |n * ξ - round (n * ξ)| := hξ n hn
    _ ≤ n * |n * ξ - m| := mul_le_mul_of_nonneg_left (round_le _ _) hn'.le
    _ = (n : ℝ) ^ (2 : ℝ) * |ξ - m / n| := by
      rw [mul_abs_mul_sub_eq_sq_mul_abs_sub_div hn', Real.rpow_two]
    _ < (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (-s) := by gcongr
    _ = (n : ℝ) ^ (2 - s) := by rw [← Real.rpow_add hn', sub_eq_add_neg]
    _ < c := hnc
  exact lt_irrefl c this

/-- A badly approximable number has irrationality exponent `2`. -/
theorem BadlyApproximable.irrationalityExponent_eq {ξ : ℝ} (h : BadlyApproximable ξ) :
    irrationalityExponent ξ = 2 :=
  le_antisymm ((irrationalityExponent_le_two_iff ξ).mpr fun _ hp ↦ h.not_liouvilleWith hp)
    ((two_le_irrationalityExponent_iff ξ).mpr h.irrational)

/-- A badly approximable number has one-dimensional simultaneous exponent `1`. -/
theorem BadlyApproximable.simultaneousExponent_eq_one {ξ : ℝ} (h : BadlyApproximable ξ) :
    simultaneousExponent ![ξ] = 1 := by
  apply (ENNReal.add_left_inj ENNReal.one_ne_top).mp
  rw [h.irrational.simultaneousExponent_add_one, h.irrationalityExponent_eq, one_add_one_eq_two]

/-- A badly approximable number is not a Liouville number. -/
theorem BadlyApproximable.not_liouville {ξ : ℝ} (h : BadlyApproximable ξ) : ¬Liouville ξ :=
  fun hL ↦ h.not_liouvilleWith (by norm_num : (2 : ℝ) < 3) (hL.liouvilleWith 3)

/-- Adding a rational number preserves bad approximability. -/
theorem BadlyApproximable.add_ratCast {ξ : ℝ} (h : BadlyApproximable ξ) (s : ℚ) :
    BadlyApproximable (ξ + s) := by
  obtain ⟨c, hc, hξ⟩ := badlyApproximable_iff_forall_ratCast.mp h
  have hs : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  refine badlyApproximable_iff_forall_ratCast.mpr ⟨c / (s.den : ℝ) ^ 2, by positivity, fun r ↦ ?_⟩
  -- `ξ + s - r = ξ - (r - s)` and `den (r - s) ≤ den r * den s`.
  have hden : ((r - s).den : ℝ) ≤ r.den * s.den := by
    exact_mod_cast Nat.le_of_dvd (by positivity) (Rat.sub_den_dvd r s)
  have hden' : (0 : ℝ) < (r - s).den := by exact_mod_cast Rat.den_pos _
  have := hξ (r - s)
  rw [Rat.cast_sub, sub_sub_eq_add_sub] at this
  refine le_trans ?_ this
  rw [div_div, ← mul_pow, mul_comm (s.den : ℝ)]
  gcongr

/-- Multiplying by a nonzero rational number preserves bad approximability. -/
theorem BadlyApproximable.ratCast_mul {ξ : ℝ} (h : BadlyApproximable ξ) {s : ℚ} (hs : s ≠ 0) :
    BadlyApproximable (s * ξ) := by
  obtain ⟨c, hc, hξ⟩ := badlyApproximable_iff_forall_ratCast.mp h
  have hs' : (0 : ℝ) < |(s : ℝ)| := by positivity
  have hnum : (0 : ℝ) < |(s.num : ℝ)| := by positivity
  refine badlyApproximable_iff_forall_ratCast.mpr
    ⟨|(s : ℝ)| * c / (s.num : ℝ) ^ 2, by positivity, fun r ↦ ?_⟩
  -- `s ξ - r = s (ξ - r / s)` and `den (r / s) ≤ den r * |num s|`.
  have hden : ((r / s).den : ℝ) ≤ r.den * |(s.num : ℝ)| := by
    have := Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd r s⁻¹)
    rw [Rat.den_inv_of_ne_zero hs] at this
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, div_eq_mul_inv]
    exact_mod_cast this
  have hden' : (0 : ℝ) < (r / s).den := by exact_mod_cast Rat.den_pos _
  have hsξ : (s : ℝ) * ξ - r = s * (ξ - (r / s : ℚ)) := by
    push_cast
    field_simp
  rw [hsξ, abs_mul, ← sq_abs (s.num : ℝ), mul_div_assoc, mul_div_assoc, div_div]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ (hξ (r / s))) hs'.le
  rw [mul_comm, ← mul_pow]
  gcongr

/-- Adding a rational number does not change bad approximability. -/
@[simp]
theorem badlyApproximable_add_ratCast_iff {ξ : ℝ} {s : ℚ} :
    BadlyApproximable (ξ + s) ↔ BadlyApproximable ξ :=
  ⟨fun h ↦ by simpa using h.add_ratCast (-s), fun h ↦ h.add_ratCast s⟩

/-- Multiplying by a nonzero rational number does not change bad approximability. -/
@[simp]
theorem badlyApproximable_ratCast_mul_iff {ξ : ℝ} {s : ℚ} (hs : s ≠ 0) :
    BadlyApproximable (s * ξ) ↔ BadlyApproximable ξ :=
  ⟨fun h ↦ by simpa [hs] using h.ratCast_mul (inv_ne_zero hs), fun h ↦ h.ratCast_mul hs⟩

/-- Negation does not change bad approximability. -/
@[simp]
theorem badlyApproximable_neg_iff {ξ : ℝ} : BadlyApproximable (-ξ) ↔ BadlyApproximable ξ := by
  simpa using badlyApproximable_ratCast_mul_iff (ξ := ξ) (s := -1) (by norm_num)

/-! ### Quadratic irrationals -/

/-- **Liouville's theorem in degree two.** An irrational root of a nonzero integer polynomial of
degree at most `2` is badly approximable. -/
theorem _root_.Irrational.badlyApproximable_of_aeval_eq_zero {ξ : ℝ} (hξ : Irrational ξ)
    {f : ℤ[X]} (hf : f ≠ 0) (hdeg : f.natDegree ≤ 2) (hroot : aeval ξ f = 0) :
    BadlyApproximable ξ := by
  obtain ⟨A, hA, hAf⟩ := Liouville.exists_pos_real_of_irrational_root hξ hf
    (by rwa [eval_map_algebraMap])
  refine badlyApproximable_iff.mpr ⟨A⁻¹, inv_pos.mpr hA, fun q hq ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
  have key := hAf (round (((b + 1 : ℕ) : ℝ) * ξ)) b
  push_cast at key ⊢
  rw [inv_le_iff_one_le_mul₀ hA, mul_abs_mul_sub_eq_sq_mul_abs_sub_div (by linarith)]
  refine key.trans ?_
  rw [← mul_assoc]
  gcongr
  exact le_add_of_nonneg_left b.cast_nonneg

/-- **Liouville's theorem in degree two.** A real number whose minimal polynomial over `ℚ` has
degree `2` is badly approximable. -/
theorem badlyApproximable_of_natDegree_minpoly_eq_two {ξ : ℝ}
    (h : (minpoly ℚ ξ).natDegree = 2) : BadlyApproximable ξ := by
  have hint : IsIntegral ℚ ξ := by
    by_contra hn
    simp [minpoly.eq_zero hn] at h
  have hirr : Irrational ξ := by
    rintro ⟨r, rfl⟩
    have := minpoly.natDegree_eq_one_iff.mpr ⟨r, eq_ratCast (algebraMap ℚ ℝ) r⟩
    omega
  exact hirr.badlyApproximable_of_aeval_eq_zero (primitiveMinpoly_ne_zero ξ)
    (by rw [natDegree_primitiveMinpoly, h]) (aeval_primitiveMinpoly hint.isAlgebraic)

/-- `√2` is badly approximable. -/
theorem badlyApproximable_sqrt_two : BadlyApproximable √2 :=
  irrational_sqrt_two.badlyApproximable_of_aeval_eq_zero (f := X ^ 2 - C 2)
    (X_pow_sub_C_ne_zero two_pos 2) (by rw [natDegree_X_pow_sub_C]) (by simp [map_ofNat])

/-! ### Littlewood's conjecture -/

/-- **Littlewood's conjecture**: for all real `α`, `β` and every `ε > 0` there is `y ≥ 1` with
`y ‖y α‖ ‖y β‖ < ε`, where `‖x‖ = |x - round x|`. This is an open problem; it is recorded as a
proposition to be used as an explicit hypothesis. -/
def LittlewoodConjecture : Prop :=
  ∀ α β : ℝ, ∀ ε > (0 : ℝ), ∃ y : ℕ, 0 < y ∧
    y * |y * α - round (y * α)| * |y * β - round (y * β)| < ε

/-- The quantified formulation of Littlewood's conjecture. -/
theorem littlewoodConjecture_def :
    LittlewoodConjecture ↔ ∀ α β : ℝ, ∀ ε > (0 : ℝ), ∃ y : ℕ, 0 < y ∧
      y * |y * α - round (y * α)| * |y * β - round (y * β)| < ε :=
  Iff.rfl

/-- Littlewood's conjecture holds for a pair `(α, β)` as soon as `α` is not badly
approximable. -/
theorem littlewood_of_not_badlyApproximable {α : ℝ} (hα : ¬BadlyApproximable α) (β : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℕ, 0 < y ∧ y * |y * α - round (y * α)| * |y * β - round (y * β)| < ε := by
  rw [badlyApproximable_iff] at hα
  push Not at hα
  obtain ⟨y, hy, hyα⟩ := hα ε hε
  refine ⟨y, hy, lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) ?_) hyα⟩
  exact (abs_sub_round _).trans (by norm_num)

/-- Littlewood's conjecture reduces to pairs of badly approximable numbers. -/
theorem littlewoodConjecture_iff_badlyApproximable :
    LittlewoodConjecture ↔ ∀ α β : ℝ, BadlyApproximable α → BadlyApproximable β →
      ∀ ε > (0 : ℝ), ∃ y : ℕ, 0 < y ∧
        y * |y * α - round (y * α)| * |y * β - round (y * β)| < ε := by
  refine ⟨fun h α β _ _ ↦ h α β, fun h α β ε hε ↦ ?_⟩
  by_cases hα : BadlyApproximable α
  · by_cases hβ : BadlyApproximable β
    · exact h α β hα hβ ε hε
    · obtain ⟨y, hy, hyε⟩ := littlewood_of_not_badlyApproximable hβ α hε
      exact ⟨y, hy, by rwa [mul_right_comm]⟩
  · exact littlewood_of_not_badlyApproximable hα β hε

/-! ### Examples -/

example : simultaneousExponent ![√2] = 1 :=
  badlyApproximable_sqrt_two.simultaneousExponent_eq_one

example : simultaneousExponent ![√2, √3] ≤ 1 := by
  calc
    simultaneousExponent ![√2, √3] ≤
        simultaneousExponent (![√2, √3] ∘ fun _ : Fin 1 ↦ 0) :=
      simultaneousExponent_le_comp _ _
    _ = simultaneousExponent ![√2] := by
      congr 1
      funext i
      fin_cases i
      simp
    _ = 1 := badlyApproximable_sqrt_two.simultaneousExponent_eq_one

example : BadlyApproximable Real.goldenRatio :=
  Real.goldenRatio_irrational.badlyApproximable_of_aeval_eq_zero (f := X ^ 2 - X - 1)
    (by intro h; simpa [coeff_X, coeff_one] using congr_arg (coeff · 2) h) (by compute_degree!)
    (by simp [Real.goldenRatio_sq])

example : ¬BadlyApproximable (liouvilleNumber 10) := fun h ↦
  h.not_liouville (liouville_liouvilleNumber (by norm_num))

example (q : ℚ) (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℕ, 0 < y ∧ y * |y * (q : ℝ) - round (y * (q : ℝ))| * |y * β - round (y * β)| < ε :=
  littlewood_of_not_badlyApproximable q.not_badlyApproximable β hε

/-- Littlewood's conjecture genuinely needs two numbers: for `√2` alone, `y ‖y √2‖` stays
bounded away from `0`. -/
example : ¬∀ α : ℝ, ∀ ε > (0 : ℝ), ∃ y : ℕ, 0 < y ∧ y * |y * α - round (y * α)| < ε := by
  intro h
  obtain ⟨c, hc, hsqrt⟩ := badlyApproximable_iff.mp badlyApproximable_sqrt_two
  obtain ⟨y, hy, hyc⟩ := h √2 c hc
  exact (hsqrt y hy).not_gt hyc

end TauCeti
