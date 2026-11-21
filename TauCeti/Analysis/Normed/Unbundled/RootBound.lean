/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Roots of monic polynomials under power-multiplicative seminorms

Let `f` be a nonarchimedean, power-multiplicative ring seminorm on a ring `R`, and let `x : R` be
a root of a monic polynomial `p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `R` itself. Then `f x` is
controlled by the coefficients: if `R` is nontrivial, some `i < d` satisfies
`f x ^ (d - i) ≤ f aᵢ`, and hence, over every ring,

`f x ≤ max_{i < d} f aᵢ ^ (1 / (d - i))`.

Over the zero ring, `d = 0` and the maximum is `0`. Both bounds only use that `f` is nonnegative,
submultiplicative, power-multiplicative and nonarchimedean, and the second also that `f 0 = 0`.
The first bound only compares natural powers, so it holds for such functions into a linearly
ordered monoid with zero in which multiplication on the right by a positive element is strictly
monotone, such as valuations.

This is the ring-seminorm form of the bound of the norm of a root by the spectral value of a
polynomial, `norm_root_le_spectralValue`, which treats coefficients in a normed field and roots in
an algebra over it. Here the coefficients and the root live in the same ring, as in the integral
equations used to bound supremum seminorms of affinoid algebras.

Conversely, if `p` has `d` roots in a domain, counted with multiplicity, then each coefficient is
bounded by the largest root: `f aᵢ ≤ M ^ (d - i)` whenever `f a ≤ M` for every root `a`. Together
the two bounds identify `max_{i < d} f aᵢ ^ (1 / (d - i))` with the largest value of `f` on the
roots of a split monic polynomial. This adapts the second half of the proof of Mathlib's
`max_norm_root_eq_spectralValue` ([BGR] §3.1.2, Proposition 1(2)) to ring seminorms.

## Main results

* `Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`: over a nontrivial ring,
  some `i < d` satisfies `f x ^ (d - i) ≤ f aᵢ`, for `f` with values in a linearly ordered monoid
  with zero.
* `Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero`: over every ring,
  `f x ≤ ⨆ i < d, f aᵢ ^ (1 / (d - i))`, for real-valued `f` with `f 0 = 0`.
* `Multiset.apply_esymm_le_pow`: `f (s.esymm k) ≤ M ^ k` when `f a ≤ M` on `s` and `k ≤ card s`.
* `Polynomial.Monic.apply_coeff_le_pow_of_card_roots`: `f aᵢ ≤ M ^ (d - i)` when `p` has `d` roots,
  all with `f`-value at most `M`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.1.2
  (Proposition 1) and §3.8.1.
-/

public section

namespace Polynomial.Monic

section Pow

variable {R Γ : Type*} [Ring R] [MonoidWithZero Γ] [LinearOrder Γ] [MulPosStrictMono Γ]
  {f : R → Γ} {p : R[X]} {x : R}

/-- A nonnegative, submultiplicative, power-multiplicative function satisfies `f (-a) ≤ f a`. -/
private theorem apply_neg_le (hf_nn : ∀ a, 0 ≤ f a) (hf_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (hf_pm : IsPowMul f) (a : R) : f (-a) ≤ f a := by
  -- Either `f` vanishes, or `f 1 ≤ 1` and `f (-1) ≤ 1`, as `f 1 = f 1 ^ 2 = f (-1) ^ 2`.
  have hsq (b : R) : f (b ^ 2) = f b * f b := by rw [hf_pm b one_le_two, pow_two]
  rcases (hf_nn 1).eq_or_lt with h1 | h1
  · have h0 (b : R) : f b = 0 :=
      le_antisymm (by simpa [← h1] using hf_mul 1 b) (hf_nn b)
    rw [h0, h0]
  have h11 : f 1 ≤ 1 := le_of_not_gt fun h ↦ (mul_lt_mul_of_pos_right h h1).ne <| by
    rw [one_mul, ← hsq, one_pow]
  have hm1 : f (-1) ≤ 1 := le_of_not_gt fun h ↦ by
    have hpos : 0 < f (-1) := (hf_nn _).lt_of_ne fun h0 ↦ h1.ne' <| by
      rw [← neg_one_sq, hsq, ← h0, mul_zero]
    have := mul_lt_mul_of_pos_right h hpos
    rw [one_mul, ← hsq, neg_one_sq] at this
    exact (this.trans_le h11).not_gt h
  calc f (-a) = f (-1 * a) := by rw [neg_one_mul]
    _ ≤ f (-1) * f a := hf_mul _ _
    _ ≤ 1 * f a := mul_le_mul_of_nonneg_right hm1 (hf_nn a)
    _ = f a := one_mul _

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
    -- `f x ^ i` is nonnegative, and nonzero since `f x ^ d = f x ^ (d - i) * f x ^ i` is positive.
    have hxi0 : 0 < f x ^ i := (hxi ▸ hf_nn (x ^ i)).lt_of_ne fun h0 ↦ hxd0.ne <| by
      rw [← Nat.sub_add_cancel hi.le, pow_add, ← h0, mul_zero]
    calc f (p.coeff i * x ^ i) ≤ f (p.coeff i) * f x ^ i := hxi ▸ hf_mul _ _
      _ < f x ^ (d - i) * f x ^ i := mul_lt_mul_of_pos_right (h i hi) hxi0
      _ = f x ^ d := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  obtain ⟨i, hi, hsum⟩ := hf_na.finset_image_add_of_nonempty (fun i ↦ p.coeff i * x ^ i)
    (Finset.nonempty_range_iff.mpr hd.ne')
  have hxd : x ^ d = -∑ i ∈ Finset.range d, p.coeff i * x ^ i := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at hx
    exact eq_neg_of_add_eq_zero_right hx
  have := (hsum.trans_lt (hterm i (Finset.mem_range.mp hi))).trans_eq (hf_pm x hd).symm
  rw [hxd] at this
  exact (this.trans_le (apply_neg_le hf_nn hf_mul hf_pm _)).false

end Pow

variable {R : Type*} [Ring R] {f : R → ℝ} {p : R[X]} {x : R}

/-- **Root bound for monic polynomials.** A root `x` of a monic polynomial `p` of degree `d` over
any ring satisfies `f x ≤ ⨆ i < d, f (p.coeff i) ^ (1 / (d - i))`, for every nonarchimedean,
power-multiplicative, nonnegative, submultiplicative function `f` with `f 0 = 0`, such as a
nonarchimedean power-multiplicative ring seminorm. -/
theorem apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero (hp : p.Monic) (hf0 : f 0 = 0)
    (hf_nn : ∀ a, 0 ≤ f a) (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hx : p.eval x = 0) :
    f x ≤ ⨆ i : Fin p.natDegree, f (p.coeff i) ^ (1 / (p.natDegree - i : ℝ)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim x 0, hf0]
    exact Real.iSup_nonneg fun _ ↦ Real.rpow_nonneg (hf_nn _) _
  · obtain ⟨i, hi, hle⟩ := hp.exists_apply_pow_le_apply_coeff_of_eval_eq_zero hf_nn hf_mul hf_pm
      hf_na hx
    refine le_ciSup_of_le (Set.finite_range _).bddAbove ⟨i, hi⟩ ?_
    rw [one_div, ← Nat.cast_sub hi.le, Real.le_rpow_inv_iff_of_pos (hf_nn x) (hf_nn _)
      (by exact_mod_cast Nat.sub_pos_of_lt hi), Real.rpow_natCast]
    exact hle

end Polynomial.Monic

section Roots

open Polynomial

variable {R F : Type*} [CommRing R] [FunLike F R ℝ] [RingSeminormClass F R ℝ] {f : F}

/-- The elementary symmetric functions of a multiset are bounded by powers of a bound on its
elements: if `f a ≤ M` for every `a ∈ s`, then `f (s.esymm k) ≤ M ^ k` for every `k` up to the
cardinality of `s`, for every nonarchimedean ring seminorm `f` with `f 1 ≤ 1`. This adapts the
coefficient half of the proof of Mathlib's `max_norm_root_eq_spectralValue`
([BGR] §3.1.2, Proposition 1(2)). -/
theorem Multiset.apply_esymm_le_pow (hf1 : f 1 ≤ 1) (hf_na : IsNonarchimedean f)
    {s : Multiset R} {M : ℝ} (hM : ∀ a ∈ s, f a ≤ M) {k : ℕ} (hk : k ≤ Multiset.card s) :
    f (s.esymm k) ≤ M ^ k := by
  -- The sum over the subfamilies of size `k` is dominated by one of its products.
  obtain ⟨t, ht, hts, hle⟩ := hf_na.multiset_powerset_image_add (Multiset.card s - k) s
  rw [Nat.sub_sub_self hk] at ht hle
  rw [Multiset.esymm]
  calc _ ≤ f t.prod := hle
    _ ≤ (t.map f).prod := Multiset.le_prod_of_submultiplicative_of_nonneg f (apply_nonneg f)
        hf1 (map_mul_le_mul f) t
    _ ≤ M ^ Multiset.card t := Multiset.prod_map_le_pow_card (fun a _ ↦ apply_nonneg f a)
        fun a ha ↦ hM a (hts a ha)
    _ = M ^ k := by rw [ht]

/-- **Coefficients are bounded by the roots.** If a monic polynomial `p` of degree `d` over a
domain has `d` roots counted with multiplicity, and `f a ≤ M` for every root `a`, then
`f (p.coeff i) ≤ M ^ (d - i)` for every `i`, for every nonarchimedean ring seminorm `f` with
`f 1 ≤ 1`. This complements
`Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero`. -/
theorem Polynomial.Monic.apply_coeff_le_pow_of_card_roots [IsDomain R] {p : R[X]} (hp : p.Monic)
    (hf1 : f 1 ≤ 1) (hf_na : IsNonarchimedean f)
    (hroots : Multiset.card p.roots = p.natDegree) {M : ℝ} (hM : ∀ a ∈ p.roots, f a ≤ M)
    (i : ℕ) : f (p.coeff i) ≤ M ^ (p.natDegree - i) := by
  rcases le_or_gt i p.natDegree with hi | hi
  · rw [coeff_eq_esymm_roots_of_card hroots hi, hp.leadingCoeff, one_mul]
    have hesymm := Multiset.apply_esymm_le_pow hf1 hf_na hM (k := p.natDegree - i) (by omega)
    rcases neg_one_pow_eq_or R (p.natDegree - i) with h | h
    · rwa [h, one_mul]
    · rwa [h, neg_one_mul, map_neg_eq_map]
  · rw [coeff_eq_zero_of_natDegree_lt hi, map_zero, Nat.sub_eq_zero_of_le hi.le, pow_zero]
    exact zero_le_one

end Roots
