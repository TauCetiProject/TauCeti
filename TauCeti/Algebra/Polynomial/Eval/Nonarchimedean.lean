/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import TauCeti.Algebra.Order.Ring.IsPowMul

/-!
# Evaluation of polynomials under nonarchimedean functions

For a nonarchimedean function `f` on a ring, with values in a linearly ordered type, that is
invariant under negation, such as a valuation or a nonarchimedean absolute value or ring seminorm,
the leading term of a polynomial `p` dominates its value at `t` as soon as it dominates each lower
term: `f (p.eval t) = f (leadingCoeff p * t ^ natDegree p)`
(`IsNonarchimedean.apply_eval_eq_leadingCoeff_mul_pow`). This is the polynomial evaluation form of
Mathlib's `IsNonarchimedean.apply_sum_eq_of_lt`, applied to `p.eval t = ∑ i ≤ d, aᵢ tⁱ`.

More generally, a term `aₖ tᵏ` of any index that dominates every other term of index at most
`natDegree p` gives the value: `f (p.eval t) = f (p.coeff k * t ^ k)`
(`IsNonarchimedean.apply_eval_eq_coeff_mul_pow`).

Let `f` be a nonnegative, submultiplicative, power-multiplicative and nonarchimedean function on a
nontrivial ring `R`, with values in a linearly ordered monoid with zero in which multiplication
on the right by a positive element is strictly monotone, such as a nonarchimedean
power-multiplicative ring seminorm or a valuation. If `x : R` is a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `R` itself, then some `i < d` satisfies
`f x ^ (d - i) ≤ f aᵢ` (`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`).
Otherwise `f (aᵢ xⁱ) < f (xᵈ)` for every `i < d`. As `f (-a) = f a` (`IsPowMul.map_neg_eq_map`), the
leading-term criterion then gives `f 0 = f (p.eval x) = f (xᵈ)`, contradicting
`f 0 ≤ f a₀ < f (xᵈ)`, where the first inequality is the nonarchimedean inequality for `a₀ + -a₀`.

Applied to the equation of integrality mapped into an `R`-algebra, the root bound shows that such
an `f` which is at most `1` on the image of `R` is at most `1` on every element integral over `R`
(`IsNonarchimedean.apply_le_one_of_isIntegral_of_isPowMul`). This is the common argument behind
the bounds for nonarchimedean absolute values (`IsNonarchimedean.apply_le_one_of_isIntegral`) and
for power-multiplicative ultrametric seminorms (`IsUltrametricDist.norm_le_one_of_isIntegral`).

For real-valued `f` with `f 0 = 0`, taking `(d - i)`-th roots gives the root bound
`Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero` over every ring, in
`TauCeti.Analysis.Normed.Unbundled.RootBound`.

The root bound is the form, for a function on a ring and roots in that ring, of the bound of the
norm of a root by the spectral value of a polynomial ([BGR] §3.1.2, Proposition 1(1)), which
Mathlib has as `norm_root_le_spectralValue` for coefficients in a normed field and roots in a
normed algebra over it. The argument, that otherwise the leading term would dominate, is the same.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.1.2
  (Proposition 1).
-/

public section

open Polynomial

/-- **The leading term of a polynomial dominates its value when it dominates each lower term**:
for a nonarchimedean function `f` on a ring, with values in a linearly ordered type, that is
invariant under negation, if
`f (p.coeff i * t ^ i) < f (leadingCoeff p * t ^ natDegree p)` for every `i < natDegree p`, then
`f (p.eval t) = f (leadingCoeff p * t ^ natDegree p)`. This is the polynomial evaluation form of
Mathlib's `IsNonarchimedean.apply_sum_eq_of_lt`. -/
theorem IsNonarchimedean.apply_eval_eq_leadingCoeff_mul_pow {R Γ : Type*} [Ring R]
    [LinearOrder Γ] {f : R → Γ} (hf_na : IsNonarchimedean f) (hf_neg : ∀ a, f (-a) = f a)
    {p : R[X]} {t : R}
    (hp : ∀ i < p.natDegree, f (p.coeff i * t ^ i) < f (p.leadingCoeff * t ^ p.natDegree)) :
    f (p.eval t) = f (p.leadingCoeff * t ^ p.natDegree) := by
  rw [← coeff_natDegree] at hp ⊢
  rw [eval_eq_sum_range]
  exact hf_na.apply_sum_eq_of_lt _ hf_neg (Finset.self_mem_range_succ _) fun j hj hjd ↦
    hp j ((Finset.mem_range_succ_iff.mp hj).lt_of_ne hjd)

/-- **A dominant term of a polynomial gives its value**: for a nonarchimedean function `f` on a
ring, with values in a linearly ordered type, that is invariant under negation, if
`f (p.coeff i * t ^ i) < f (p.coeff k * t ^ k)` for every `i ≤ natDegree p` with `i ≠ k`, then
`f (p.eval t) = f (p.coeff k * t ^ k)`. The index `k` need not be the degree of `p` (it is at
most the degree, as `f 0` is the least value of `f`); for `k = natDegree p` this is
`IsNonarchimedean.apply_eval_eq_leadingCoeff_mul_pow`. -/
theorem IsNonarchimedean.apply_eval_eq_coeff_mul_pow {R Γ : Type*} [Ring R] [LinearOrder Γ]
    {f : R → Γ} (hf_na : IsNonarchimedean f) (hf_neg : ∀ a, f (-a) = f a) {p : R[X]} {t : R}
    {k : ℕ} (hp : ∀ i ≤ p.natDegree, i ≠ k → f (p.coeff i * t ^ i) < f (p.coeff k * t ^ k)) :
    f (p.eval t) = f (p.coeff k * t ^ k) := by
  have hk : k ≤ p.natDegree := by
    by_contra! hk
    -- `f 0 ≤ f a` for every `a`, by the nonarchimedean inequality for `a + -a`
    have h0 := hf_na (p.coeff 0 * t ^ 0) (-(p.coeff 0 * t ^ 0))
    rw [add_neg_cancel, hf_neg, max_self] at h0
    have h := hp 0 (Nat.zero_le _) (by omega)
    rw [coeff_eq_zero_of_natDegree_lt hk, zero_mul] at h
    exact h0.not_gt h
  rw [eval_eq_sum_range]
  exact hf_na.apply_sum_eq_of_lt _ hf_neg (Finset.mem_range_succ_iff.mpr hk)
    fun j hj hjk ↦ hp j (Finset.mem_range_succ_iff.mp hj) hjk

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
  have hd : 0 < d := natDegree_pos_of_eval₂_root hp.ne_zero (RingHom.id R) (by rwa [eval₂_id])
    fun _ ↦ id
  by_contra! h
  have hf_neg := hf_pm.map_neg_eq_map hf_nn hf_mul
  -- Every lower term `aᵢ xⁱ` is strictly smaller than the leading term `xᵈ`, which therefore
  -- dominates `p.eval x = 0`; but `f 0 ≤ f a₀ < f (xᵈ)` by the ultrametric inequality.
  have hxd0 : 0 < f x ^ d := (hf_nn _).trans_lt (by simpa using h 0 hd)
  have hterm (i : ℕ) (hi : i < d) : f (p.coeff i * x ^ i) < f (p.leadingCoeff * x ^ d) := by
    rw [hp.leadingCoeff, one_mul, hf_pm x hd]
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
  have heval := hf_na.apply_eval_eq_leadingCoeff_mul_pow hf_neg hterm
  rw [hx] at heval
  have h0 := hf_na (p.coeff 0 * x ^ 0) (-(p.coeff 0 * x ^ 0))
  rw [add_neg_cancel, hf_neg, max_self] at h0
  exact (h0.trans_lt (hterm 0 hd)).ne heval

end Polynomial.Monic

namespace IsNonarchimedean

variable {R F Γ : Type*} [CommRing R] [Ring F] [Algebra R F] [MonoidWithZero Γ] [LinearOrder Γ]
  [ZeroLEOneClass Γ] [PosMulMono Γ] [MulPosStrictMono Γ] {f : F → Γ}

/-- A nonnegative, submultiplicative, power-multiplicative and nonarchimedean function on an
`R`-algebra, such as a nonarchimedean absolute value or a power-multiplicative ultrametric
seminorm, which is at most `1` on the image of `R` is at most `1` on every element integral
over `R`.

This is the forward implication of Mathlib's `Valuation.Integers.isIntegral_iff_v_le_one` for
such functions, and the proof follows it: a coefficient `aᵢ` of the equation of integrality has
`f x ^ (d - i) ≤ f aᵢ ≤ 1`. -/
theorem apply_le_one_of_isIntegral_of_isPowMul (hf_na : IsNonarchimedean f)
    (hf_nn : ∀ a, 0 ≤ f a) (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (hf_pm : IsPowMul f)
    (h : ∀ r : R, f (algebraMap R F r) ≤ 1) {x : F} (hx : IsIntegral R x) : f x ≤ 1 := by
  by_contra! hx1
  have : Nontrivial F := ⟨x, algebraMap R F 0, fun hx0 ↦ (h 0).not_gt (hx0 ▸ hx1)⟩
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨i, hi, hle⟩ := (hpm.map (algebraMap R F)).exists_apply_pow_le_apply_coeff_of_eval_eq_zero
    hf_nn hf_mul hf_pm hf_na (by rwa [eval_map])
  rw [coeff_map] at hle
  exact (one_lt_pow₀ hx1 (Nat.sub_pos_of_lt hi).ne').not_ge (hle.trans (h _))

end IsNonarchimedean
