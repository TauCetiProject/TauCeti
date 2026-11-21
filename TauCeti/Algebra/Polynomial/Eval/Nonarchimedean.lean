/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Polynomial.Monic
public import TauCeti.Algebra.Order.Ring.IsPowMul

/-!
# Roots of monic polynomials under nonarchimedean power-multiplicative functions

Let `f` be a nonnegative, submultiplicative, power-multiplicative and nonarchimedean function on a
nontrivial ring `R`, with values in a linearly ordered monoid with zero in which multiplication
on the right by a positive element is strictly monotone, such as a nonarchimedean
power-multiplicative ring seminorm or a valuation. If `x : R` is a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `R` itself, then some `i < d` satisfies
`f x ^ (d - i) ≤ f aᵢ` (`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`):
otherwise every lower term `aᵢ xⁱ` would be strictly smaller than `xᵈ`, which is impossible in
the nonarchimedean relation `xᵈ = -∑_{i < d} aᵢ xⁱ`.

For real-valued `f` with `f 0 = 0`, taking `(d - i)`-th roots gives the root bound
`Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero` over every ring, in
`TauCeti.Analysis.Normed.Unbundled.RootBound`.
-/

public section

namespace Polynomial.Monic

variable {R Γ : Type*} [Ring R] [MonoidWithZero Γ] [LinearOrder Γ] [MulPosStrictMono Γ]
  {f : R → Γ} {p : R[X]} {x : R}

/-- A root `x` of a monic polynomial `p` of degree `d` over a nontrivial ring satisfies
`f x ^ (d - i) ≤ f (p.coeff i)` for some `i < d`, for every nonarchimedean, power-multiplicative,
nonnegative, submultiplicative function `f` into a linearly ordered monoid with zero in which
multiplication on the right by a positive element is strictly monotone, such as a nonarchimedean
power-multiplicative ring seminorm or a valuation. -/
theorem exists_apply_pow_le_apply_coeff_of_eval_eq_zero [Nontrivial R] (hp : p.Monic)
    (hf_nn : ∀ a, 0 ≤ f a) (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hx : p.eval x = 0) :
    ∃ i < p.natDegree, f x ^ (p.natDegree - i) ≤ f (p.coeff i) := by
  set d := p.natDegree
  have hd : 0 < d := natDegree_pos_of_eval₂_root hp.ne_zero (RingHom.id R) hx fun _ ↦ id
  by_contra! h
  -- Every lower term `aᵢ xⁱ` is strictly smaller than `xᵈ`, which is impossible in the
  -- ultrametric relation `xᵈ = -∑_{i < d} aᵢ xⁱ`.
  have hxd0 : 0 < f x ^ d := (hf_nn _).trans_lt (by simpa using h 0 hd)
  have hterm (i : ℕ) (hi : i < d) : f (p.coeff i * x ^ i) < f x ^ d := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using h 0 hi
    have hxi : f (x ^ i) = f x ^ i := hf_pm x hi0
    have hpow : f x ^ (d - i) * f x ^ i = f x ^ d := by rw [← pow_add, Nat.sub_add_cancel hi.le]
    -- `f x ^ i` is nonnegative, and nonzero since `f x ^ d = f x ^ (d - i) * f x ^ i` is positive.
    have hxi0 : 0 < f x ^ i :=
      (hxi ▸ hf_nn (x ^ i)).lt_of_ne' <| right_ne_zero_of_mul <| hpow ▸ hxd0.ne'
    calc f (p.coeff i * x ^ i) ≤ f (p.coeff i) * f x ^ i := hxi ▸ hf_mul _ _
      _ < f x ^ (d - i) * f x ^ i := mul_lt_mul_of_pos_right (h i hi) hxi0
      _ = f x ^ d := hpow
  obtain ⟨i, hi, hsum⟩ := hf_na.finset_image_add_of_nonempty (fun i ↦ p.coeff i * x ^ i)
    (Finset.nonempty_range_iff.mpr hd.ne')
  have hxd : x ^ d = -∑ i ∈ Finset.range d, p.coeff i * x ^ i := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at hx
    exact eq_neg_of_add_eq_zero_right hx
  have := (hsum.trans_lt (hterm i (Finset.mem_range.mp hi))).trans_eq (hf_pm x hd).symm
  rw [hxd] at this
  exact (this.trans_le (hf_pm.map_neg_le hf_nn hf_mul _)).false

end Polynomial.Monic
