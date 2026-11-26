/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Dilating an arithmetic function by squares

For an arithmetic function `f`, its dilation by squares `f_□` takes the value `f(m)` at `m²` and
vanishes off the perfect squares. Dilation is multiplicative for the Dirichlet product,
`(f * g)_□ = f_□ * g_□`, and fixes the unit `1`, because `n ↦ n²` is an injective monoid map
under which a pair of squares `(a², b²)` has product `m²` exactly when `ab = m`. Thus `ζ_□` is the
indicator of the positive squares and `μ_□` is its Dirichlet inverse.

A convolution with a dilated function is a sum over the square divisors `d² ∣ n`, and its summatory
function is a sum over `d ≤ √N`. These are the identities behind the relation between the
summatory functions of the Liouville and Möbius functions.

## Main declarations

* `ArithmeticFunction.dilateSq`: the dilation `f_□` of `f` by squares.
* `ArithmeticFunction.dilateSq_mul`, `ArithmeticFunction.dilateSq_one`: dilation respects the
  Dirichlet product and fixes `1`.
* `ArithmeticFunction.mul_dilateSq_apply`: `(f * g_□)(n) = ∑_{d² ∣ n} f(n / d²) g(d)`.
* `ArithmeticFunction.sum_Ioc_dilateSq_mul`:
  `∑_{0 < n ≤ N} (g_□ * f)(n) = ∑_{0 < d ≤ √N} g(d) ∑_{0 < k ≤ N / d²} f(k)`.
-/

public section

open Finset

namespace ArithmeticFunction

variable {R : Type*}

section Zero

variable [Zero R] (f : ArithmeticFunction R)

/-- The dilation of `f` by squares: the arithmetic function with value `f m` at `m ^ 2` and `0` off
the perfect squares. -/
def dilateSq : ArithmeticFunction R where
  toFun n := if IsSquare n then f n.sqrt else 0
  map_zero' := by simp

theorem dilateSq_apply (n : ℕ) : f.dilateSq n = if IsSquare n then f n.sqrt else 0 := (rfl)

@[simp]
theorem dilateSq_apply_sq (m : ℕ) : f.dilateSq (m ^ 2) = f m := by
  simp [dilateSq_apply, sq, Nat.sqrt_eq]

theorem dilateSq_apply_of_not_isSquare {n : ℕ} (hn : ¬IsSquare n) : f.dilateSq n = 0 := by
  simp [dilateSq_apply, hn]

/-- A dilated function vanishes off the perfect squares. -/
theorem exists_eq_sq_of_dilateSq_apply_ne_zero {n : ℕ} (hn : f.dilateSq n ≠ 0) :
    ∃ m, n = m ^ 2 := by
  by_contra h
  refine hn (f.dilateSq_apply_of_not_isSquare ?_)
  rintro ⟨m, rfl⟩
  exact h ⟨m, (sq m).symm⟩

end Zero

section Semiring

variable [Semiring R]

@[simp]
theorem dilateSq_one : (1 : ArithmeticFunction R).dilateSq = 1 := by
  ext n
  by_cases hn : IsSquare n
  · obtain ⟨m, rfl⟩ := hn
    rw [← sq, dilateSq_apply_sq, ArithmeticFunction.one_apply, ArithmeticFunction.one_apply]
    simp
  · rw [dilateSq_apply_of_not_isSquare _ hn, ArithmeticFunction.one_apply_ne]
    rintro rfl
    exact hn ⟨1, rfl⟩

/-- A pair `x` with `x.1 * x.2 = n` on which `f_□(x.1) g_□(x.2) ≠ 0` is a pair of squares
`(a², b²)`, and then `n = (ab)²`. -/
private theorem exists_eq_sq_of_dilateSq_mul_ne_zero {f g : ArithmeticFunction R} {n : ℕ}
    {x : ℕ × ℕ} (hx : x ∈ n.divisorsAntidiagonal) (hne : f.dilateSq x.1 * g.dilateSq x.2 ≠ 0) :
    ∃ a b, x = (a ^ 2, b ^ 2) ∧ n = (a * b) ^ 2 := by
  obtain ⟨a, ha⟩ := f.exists_eq_sq_of_dilateSq_apply_ne_zero (left_ne_zero_of_mul hne)
  obtain ⟨b, hb⟩ := g.exists_eq_sq_of_dilateSq_apply_ne_zero (right_ne_zero_of_mul hne)
  rw [Nat.mem_divisorsAntidiagonal, ha, hb, ← mul_pow] at hx
  exact ⟨a, b, Prod.ext ha hb, hx.1.symm⟩

/-- Dilation by squares is multiplicative for the Dirichlet product:
`(f * g)_□ = f_□ * g_□`. -/
theorem dilateSq_mul (f g : ArithmeticFunction R) :
    (f * g).dilateSq = f.dilateSq * g.dilateSq := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  by_cases hn : IsSquare n
  · obtain ⟨m, rfl⟩ := hn
    rw [← sq, dilateSq_apply_sq, ArithmeticFunction.mul_apply]
    refine sum_bij_ne_zero (fun x _ _ ↦ (x.1 ^ 2, x.2 ^ 2)) ?_ ?_ ?_ ?_
    · intro x hx _
      rw [Nat.mem_divisorsAntidiagonal] at hx ⊢
      exact ⟨by rw [← mul_pow, hx.1], pow_ne_zero 2 hx.2⟩
    · intro x _ _ y _ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.pow_left_injective two_ne_zero h.1)
        (Nat.pow_left_injective two_ne_zero h.2)
    · intro y hy hne
      have hm := (Nat.mem_divisorsAntidiagonal.1 hy).2
      obtain ⟨a, b, rfl, hab⟩ := exists_eq_sq_of_dilateSq_mul_ne_zero hy hne
      refine ⟨(a, b), ?_, ?_, rfl⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        exact ⟨Nat.pow_left_injective two_ne_zero hab.symm, by rintro rfl; simp at hm⟩
      · rwa [dilateSq_apply_sq, dilateSq_apply_sq] at hne
    · intro x _ _
      rw [dilateSq_apply_sq, dilateSq_apply_sq]
  · rw [dilateSq_apply_of_not_isSquare _ hn]
    refine (sum_eq_zero fun x hx ↦ ?_).symm
    by_contra hne
    obtain ⟨a, b, -, hab⟩ := exists_eq_sq_of_dilateSq_mul_ne_zero hx hne
    exact hn ⟨a * b, by rw [hab, sq]⟩

/-- A convolution with a dilated function is a sum over the square divisors:
`(f * g_□)(n) = ∑_{d² ∣ n} f(n / d²) g(d)`. -/
theorem mul_dilateSq_apply (f g : ArithmeticFunction R) (n : ℕ) :
    (f * g.dilateSq) n = ∑ d ∈ n.divisors with d ^ 2 ∣ n, f (n / d ^ 2) * g d := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' fun a b ↦ f a * g.dilateSq b]
  symm
  refine sum_bij_ne_zero (fun d _ _ ↦ d ^ 2) ?_ ?_ ?_ ?_
  · intro d hd _
    rw [mem_filter, Nat.mem_divisors] at hd
    exact Nat.mem_divisors.2 ⟨hd.2, hd.1.2⟩
  · intro d _ _ e _ _ h
    exact Nat.pow_left_injective two_ne_zero h
  · intro b hb hne
    obtain ⟨d, rfl⟩ := g.exists_eq_sq_of_dilateSq_apply_ne_zero (right_ne_zero_of_mul hne)
    have hd := Nat.mem_divisors.1 hb
    refine ⟨d, mem_filter.2 ⟨Nat.mem_divisors.2 ⟨(dvd_pow_self d two_ne_zero).trans hd.1, hd.2⟩,
      hd.1⟩, ?_, rfl⟩
    rwa [dilateSq_apply_sq] at hne
  · intro d _ _
    rw [dilateSq_apply_sq]

/-- The summatory function of a convolution with a dilated function is a sum over `d ≤ √N`:
`∑_{0 < n ≤ N} (g_□ * f)(n) = ∑_{0 < d ≤ √N} g(d) ∑_{0 < k ≤ N / d²} f(k)`. -/
theorem sum_Ioc_dilateSq_mul (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (g.dilateSq * f) n =
      ∑ d ∈ Ioc 0 N.sqrt, g d * ∑ k ∈ Ioc 0 (N / d ^ 2), f k := by
  rw [sum_Ioc_mul_eq_sum_sum]
  symm
  refine sum_bij_ne_zero (fun d _ _ ↦ d ^ 2) ?_ ?_ ?_ ?_
  · intro d hd _
    rw [mem_Ioc] at hd ⊢
    exact ⟨pow_pos hd.1 2, Nat.le_sqrt'.1 hd.2⟩
  · intro d _ _ e _ _ h
    exact Nat.pow_left_injective two_ne_zero h
  · intro m hm hne
    obtain ⟨d, rfl⟩ := g.exists_eq_sq_of_dilateSq_apply_ne_zero (left_ne_zero_of_mul hne)
    rw [mem_Ioc] at hm
    refine ⟨d, mem_Ioc.2 ⟨pos_of_ne_zero ?_, Nat.le_sqrt'.2 hm.2⟩, ?_, rfl⟩
    · rintro rfl
      simp at hm
    · rwa [dilateSq_apply_sq] at hne
  · intro d _ _
    rw [dilateSq_apply_sq]

end Semiring

end ArithmeticFunction
