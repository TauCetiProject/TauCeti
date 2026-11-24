/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Polynomial.Vieta
public import TauCeti.Algebra.Polynomial.Eval.Nonarchimedean

/-!
# Roots of monic polynomials under power-multiplicative seminorms

Let `f : R → ℝ` be a nonnegative, submultiplicative, power-multiplicative and nonarchimedean
function on a ring `R` with `f 0 = 0`, such as a nonarchimedean power-multiplicative ring
seminorm, and let `x : R` be a root of a monic polynomial `p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `R`
itself. Then `f x` is controlled by the coefficients: over every ring,

`f x ≤ ⨆ i < d, f aᵢ ^ (1 / (d - i))`,

a real supremum over the finitely many `i < d`, which is `0` when `d = 0`. Over the zero ring,
`d = 0` and `f x = f 0 = 0`. Over a nontrivial ring this follows from
`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`, which gives some `i < d`
with `f x ^ (d - i) ≤ f aᵢ`.

This is the ring-seminorm form of the bound of the norm of a root by the spectral value of a
polynomial, `norm_root_le_spectralValue`, which treats coefficients in a normed field and roots in
an algebra over it. Here the coefficients and the root live in the same ring, as in the integral
equations used to bound supremum seminorms of affinoid algebras.

Conversely, for a nonarchimedean ring seminorm `f` with `f 1 ≤ 1`, if `p` has `d` roots in a
domain, counted with multiplicity, then each coefficient is bounded by the values of `f` on the
roots: `f aᵢ ≤ M ^ (d - i)` whenever `f a ≤ M` for every root `a`. For a power-multiplicative such
`f` and a split monic polynomial of positive degree `d`, the two bounds together identify the
supremum `⨆ i < d, f aᵢ ^ (1 / (d - i))` with the largest value of `f` on the roots. This adapts
the second half of the proof of Mathlib's `max_norm_root_eq_spectralValue` ([BGR] §3.1.2,
Proposition 1(2)) to ring seminorms.

## Main results

* `Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero`: over every ring,
  `f x ≤ ⨆ i < d, f aᵢ ^ (1 / (d - i))`, for every `f : R → ℝ` as above (nonnegative,
  submultiplicative, power-multiplicative and nonarchimedean, with `f 0 = 0`).
* `Multiset.apply_esymm_le_pow`: `f (s.esymm k) ≤ M ^ k` when `f a ≤ M` on `s` and `k ≤ card s`.
* `Polynomial.Monic.apply_coeff_le_pow_of_card_roots`: `f aᵢ ≤ M ^ (d - i)` when `p` has `d` roots,
  all with `f`-value at most `M`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.1.2
  (Proposition 1) and §3.8.1.
-/

public section

namespace Polynomial.Monic

variable {R : Type*} [Ring R] {f : R → ℝ} {p : R[X]} {x : R}

/-- **Root bound for monic polynomials.** A root `x` of a monic polynomial `p` of degree `d` over
any ring satisfies `f x ≤ ⨆ i < d, f (p.coeff i) ^ (1 / (d - i))`, for every nonarchimedean,
power-multiplicative, nonnegative, submultiplicative real-valued function `f : R → ℝ` with
`f 0 = 0`, such as a nonarchimedean power-multiplicative ring seminorm. -/
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
