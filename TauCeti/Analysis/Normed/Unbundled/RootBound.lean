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
controlled by the coefficients: some `i < d` satisfies `f x ^ (d - i) ≤ f aᵢ`, and hence

`f x ≤ max_{i < d} f aᵢ ^ (1 / (d - i))`.

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

* `Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`: some `i < d` satisfies
  `f x ^ (d - i) ≤ f aᵢ`.
* `Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero`:
  `f x ≤ ⨆ i < d, f aᵢ ^ (1 / (d - i))`.
* `Multiset.apply_esymm_le_pow`: `f (s.esymm k) ≤ M ^ k` when `f a ≤ M` on `s` and `k ≤ card s`.
* `Polynomial.Monic.apply_coeff_le_pow_of_card_roots`: `f aᵢ ≤ M ^ (d - i)` when `p` has `d` roots,
  all with `f`-value at most `M`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.1.2
  (Proposition 1) and §3.8.1.
-/

public section

namespace Polynomial.Monic

variable {R F : Type*} [Ring R] [FunLike F R ℝ] [RingSeminormClass F R ℝ] {f : F}
  {p : R[X]} {x : R}

/-- A root `x` of a monic polynomial `p` of degree `d` over a nontrivial ring satisfies
`f x ^ (d - i) ≤ f (p.coeff i)` for some `i < d`, for every nonarchimedean power-multiplicative
ring seminorm `f`. -/
theorem exists_apply_pow_le_apply_coeff_of_eval_eq_zero [Nontrivial R] (hp : p.Monic)
    (hf_pm : IsPowMul f) (hf_na : IsNonarchimedean f) (hx : p.eval x = 0) :
    ∃ i < p.natDegree, f x ^ (p.natDegree - i) ≤ f (p.coeff i) := by
  set d := p.natDegree
  have hd : 0 < d := by
    refine Nat.pos_of_ne_zero fun hd ↦ ?_
    rw [hp.natDegree_eq_zero.mp hd, eval_one] at hx
    exact one_ne_zero hx
  by_contra! h
  -- Every lower term `aᵢ xⁱ` is strictly smaller than `xᵈ`, which is impossible in the
  -- ultrametric relation `xᵈ = -∑_{i < d} aᵢ xⁱ`.
  have hx0 : 0 < f x := by
    refine (apply_nonneg f x).lt_of_ne fun h0 ↦ ?_
    have := (apply_nonneg f (p.coeff 0)).trans_lt (h 0 hd)
    rw [← h0, zero_pow (by omega)] at this
    exact lt_irrefl _ this
  have hterm (i : ℕ) (hi : i < d) : f (p.coeff i * x ^ i) < f x ^ d := by
    have hpow : f (x ^ i) ≤ f x ^ i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa using hf_pm.map_one_le_one
      · exact (hf_pm x hi0).le
    calc f (p.coeff i * x ^ i) ≤ f (p.coeff i) * f (x ^ i) := map_mul_le_mul f _ _
      _ ≤ f (p.coeff i) * f x ^ i := by gcongr
      _ < f x ^ (d - i) * f x ^ i := by gcongr; exact h i hi
      _ = f x ^ d := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  obtain ⟨i, hi, hsum⟩ := hf_na.finset_image_add_of_nonempty (fun i ↦ p.coeff i * x ^ i)
    (Finset.nonempty_range_iff.mpr hd.ne')
  have hxd : x ^ d = -∑ i ∈ Finset.range d, p.coeff i * x ^ i := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at hx
    exact eq_neg_of_add_eq_zero_right hx
  have := (hsum.trans_lt (hterm i (Finset.mem_range.mp hi))).trans_eq (hf_pm x hd).symm
  rw [hxd, map_neg_eq_map] at this
  exact lt_irrefl _ this

/-- **Root bound for monic polynomials.** A root `x` of a monic polynomial `p` of degree `d`
satisfies `f x ≤ ⨆ i < d, f (p.coeff i) ^ (1 / (d - i))`, for every nonarchimedean
power-multiplicative ring seminorm `f`. -/
theorem apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero (hp : p.Monic) (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hx : p.eval x = 0) :
    f x ≤ ⨆ i : Fin p.natDegree, f (p.coeff i) ^ (1 / (p.natDegree - i : ℝ)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim x 0, map_zero]
    exact Real.iSup_nonneg fun _ ↦ Real.rpow_nonneg (apply_nonneg f _) _
  · obtain ⟨i, hi, hle⟩ := hp.exists_apply_pow_le_apply_coeff_of_eval_eq_zero hf_pm hf_na hx
    refine le_ciSup_of_le (Set.finite_range _).bddAbove ⟨i, hi⟩ ?_
    have hdi : (p.natDegree - i : ℝ) = ((p.natDegree - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hi.le]
    rw [one_div, hdi, Real.le_rpow_inv_iff_of_pos (apply_nonneg f x) (apply_nonneg f _)
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
