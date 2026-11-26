/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Roots of cyclotomic and related polynomials at primitive roots of unity

A primitive `e`-th root of unity in a domain is a root of the cyclotomic polynomial `Φ_e` over any
ring, once its coefficients are mapped into the domain along a ring homomorphism. If a rational
polynomial vanishes at one primitive `h`-th root of unity in a `ℚ`-algebra domain, it vanishes at
every primitive `h`-th root of unity in any `ℚ`-algebra domain. Consequently, two polynomials over
`ℚ[X]` whose coefficients evaluate identically at one primitive `h`-th root of unity also become
equal at any primitive `h`-th root of unity in any `ℚ`-algebra domain. In an integral domain
containing a suitable primitive root of unity, this file also records the root multisets of
`∑ k ∈ Finset.range (n + 1), X ^ k`, `X ^ n + 1`, and `(X ^ (n - 1) + 1) * (X + 1)`.

## Main results

* `IsPrimitiveRoot.eval₂_cyclotomic`: a primitive `e`-th root of unity in a domain is a root of
  `cyclotomic e S` along any ring homomorphism `S →+* R`.
* `IsPrimitiveRoot.aeval_eq_zero_of_aeval_eq_zero`: if `p : ℚ[X]` vanishes at a primitive `h`-th
  root of unity `ζ₀`, it vanishes at any primitive `h`-th root of unity `ζ`.
* `IsPrimitiveRoot.isRoot_map_of_isRoot_map`: root transfer across primitive `h`-th roots of unity
  for rational polynomials.
* `Polynomial.map_aeval_map_C`: mapping `p.map C` by coefficientwise `aeval r` yields
  `p.map (algebraMap R A)`.
* `Polynomial.map_aeval_eq_of_isPrimitiveRoot`: equality of `(ℚ[X])[X]` polynomials after
  coefficientwise evaluation at one primitive `h`-th root transfers to any primitive `h`-th root.
* `Polynomial.roots_sum_range_X_pow`, `Polynomial.roots_X_pow_add_one`, and
  `Polynomial.roots_X_pow_add_one_mul_X_add_one`: root multisets of `∑ k < n + 1, X ^ k`,
  `X ^ n + 1`, and `(X ^ (n - 1) + 1) * (X + 1)` over any integral domain with a primitive root of
  unity.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

/-- A primitive `e`-th root of unity `r` in a domain `R` is a root of the cyclotomic polynomial
`Φ_e` over any ring, mapped to `R` along any ring homomorphism `f`. Mathlib's
`IsPrimitiveRoot.isRoot_cyclotomic` is the case of `Φ_e` taken over `R` itself. -/
theorem eval₂_cyclotomic {e : ℕ} {S R : Type*} [Ring S] [CommRing R] [IsDomain R] [NeZero e]
    (f : S →+* R) {r : R} (hr : IsPrimitiveRoot r e) : (cyclotomic e S).eval₂ f r = 0 := by
  rw [← eval_map, map_cyclotomic]
  exact hr.isRoot_cyclotomic (NeZero.pos e)

/-- **Rational cyclotomic evaluation transfer.** If a polynomial over `ℚ` evaluates to zero at one
primitive `h`-th root of unity in a `ℚ`-algebra domain, then it evaluates to zero at any primitive
`h`-th root of unity in any `ℚ`-algebra domain. -/
theorem aeval_eq_zero_of_aeval_eq_zero {K A : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K]
    [CommRing A] [IsDomain A] [Algebra ℚ A] {h : ℕ} (hh : 0 < h) {ζ₀ : K}
    (hζ₀ : IsPrimitiveRoot ζ₀ h) {ζ : A} (hζ : IsPrimitiveRoot ζ h) {p : ℚ[X]}
    (hp : aeval ζ₀ p = 0) : aeval ζ p = 0 := by
  have : NeZero h := ⟨hh.ne'⟩
  have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.mpr hh.ne'⟩
  have hdvd : cyclotomic h ℚ ∣ p := by
    rw [hζ₀.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh)]
    exact minpoly.dvd ℚ ζ₀ hp
  obtain ⟨q, rfl⟩ := hdvd
  rw [map_mul, aeval_def, hζ.eval₂_cyclotomic (algebraMap ℚ A), zero_mul]

/-- **Root transfer for rational polynomials.** If a primitive `h`-th root of unity `ζ₀` in a
`ℚ`-algebra domain is a root of a rational polynomial `p`, then any primitive `h`-th root of unity
`ζ` in any `ℚ`-algebra domain is also a root of `p`. -/
theorem isRoot_map_of_isRoot_map {K A : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K]
    [CommRing A] [IsDomain A] [Algebra ℚ A] {h : ℕ} (hh : 0 < h) {ζ₀ : K}
    (hζ₀ : IsPrimitiveRoot ζ₀ h) {ζ : A} (hζ : IsPrimitiveRoot ζ h) {p : ℚ[X]}
    (hp : (p.map (algebraMap ℚ K)).IsRoot ζ₀) : (p.map (algebraMap ℚ A)).IsRoot ζ := by
  rw [IsRoot.def, ← eval₂_eq_eval_map, ← aeval_def] at hp ⊢
  exact hζ₀.aeval_eq_zero_of_aeval_eq_zero hh hζ hp

end IsPrimitiveRoot

namespace Polynomial

/-- Coefficientwise evaluation of `p.map C` at `r` recovers `p.map (algebraMap R A)`. -/
@[simp]
theorem map_aeval_map_C {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (p : R[X]) (r : A) :
    (p.map Polynomial.C).map (↑(aeval r : R[X] →ₐ[R] A) : R[X] →+* A) =
      p.map (algebraMap R A) := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  simp

/-- **Cyclotomic transfer for `(ℚ[X])[X]` polynomials.** If two polynomials over `ℚ[X]` have equal
images under coefficientwise evaluation at a primitive `h`-th root of unity `ζ₀` in a `ℚ`-algebra
domain, then they have equal images under coefficientwise evaluation at any primitive `h`-th root
of unity `ζ` in any `ℚ`-algebra domain. -/
theorem map_aeval_eq_of_isPrimitiveRoot (F₁ F₂ : (ℚ[X])[X]) {K A : Type*}
    [CommRing K] [IsDomain K] [Algebra ℚ K] [CommRing A] [IsDomain A] [Algebra ℚ A]
    {h : ℕ} (hh : 0 < h) {ζ₀ : K} (hζ₀ : IsPrimitiveRoot ζ₀ h) {ζ : A} (hζ : IsPrimitiveRoot ζ h)
    (heq : F₁.map (aeval ζ₀).toRingHom = F₂.map (aeval ζ₀).toRingHom) :
    F₁.map (aeval ζ).toRingHom = F₂.map (aeval ζ).toRingHom := by
  ext k
  have hk₀ : aeval ζ₀ (F₁.coeff k - F₂.coeff k) = 0 := by
    have hcoeff := congrArg (fun p : K[X] ↦ p.coeff k) heq
    simp only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hcoeff
    rw [map_sub, hcoeff, sub_self]
  have hk : aeval ζ (F₁.coeff k - F₂.coeff k) = 0 :=
    hζ₀.aeval_eq_zero_of_aeval_eq_zero hh hζ hk₀
  rw [map_sub, sub_eq_zero] at hk
  simpa only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hk

/-- In an integral domain `K` with a primitive `(n + 1)`-th root of unity `ζ`, the root multiset of
`∑ k ∈ Finset.range (n + 1), X ^ k` consists of `ζ ^ 1, ζ ^ 2, …, ζ ^ n`, each with multiplicity
one. -/
theorem roots_sum_range_X_pow {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (n + 1)) :
    (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k).roots =
      Multiset.ofList ((List.range n).map fun k => ζ ^ (k + 1)) := by
  have hp : (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k) * (X - C 1) = X ^ (n + 1) - C 1 := by
    simpa only [C_1] using geom_sum_mul (X : K[X]) (n + 1)
  have hroots : (∑ k ∈ Finset.range (n + 1), (X : K[X]) ^ k).roots + {1} =
      (Multiset.range (n + 1)).map fun k => ζ ^ k * 1 := by
    rw [← roots_X_sub_C, ← roots_mul (hp ▸ X_pow_sub_C_ne_zero (Nat.succ_pos n) 1), hp,
      ← nthRoots, hζ.nthRoots_eq (one_pow (n + 1))]
  rw [← Multiset.coe_range, List.range_succ_eq_map, Multiset.map_coe, List.map_cons, List.map_map,
    pow_zero, one_mul, ← Multiset.cons_coe, ← Multiset.singleton_add, add_comm] at hroots
  exact (add_left_cancel hroots).trans
    (congrArg Multiset.ofList (List.map_congr_left fun k _ => mul_one _))

/-- In an integral domain `K` with a primitive `(2 * n)`-th root of unity `ζ` (`0 < n`), the root
multiset of `X ^ n + 1` consists of the odd powers `ζ ^ 1, ζ ^ 3, …, ζ ^ (2n - 1)`, each with
multiplicity one. -/
theorem roots_X_pow_add_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    ((X : K[X]) ^ n + 1).roots =
      Multiset.ofList ((List.range n).map fun k => ζ ^ (2 * k + 1)) := by
  have hneg : ζ ^ n = -1 :=
    (Nat.mul_div_left 2 hn ▸ hζ.pow_of_dvd hn.ne' (dvd_mul_left n 2)).eq_neg_one_of_two_right
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) n := by
    simpa [Nat.mul_div_cancel_left n two_pos] using hζ.pow_of_dvd two_ne_zero (dvd_mul_right 2 n)
  have hx : (X : K[X]) ^ n + 1 = X ^ n - C (-1) := by simp [sub_neg_eq_add]
  rw [hx, ← nthRoots, hζ2.nthRoots_eq hneg, ← Multiset.coe_range, Multiset.map_coe]
  exact congrArg Multiset.ofList (List.map_congr_left fun k _ => by rw [← pow_mul, ← pow_succ])

/-- In an integral domain `K` with a primitive `(2 * (n - 1))`-th root of unity `ζ` (`2 ≤ n`), the
root multiset of `(X ^ (n - 1) + 1) * (X + 1)` consists of `ζ ^ (2k + 1)` (`k < n - 1`) together
with `ζ ^ (n - 1) = -1` (so `-1` has multiplicity two when `n` is even). -/
theorem roots_X_pow_add_one_mul_X_add_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hn : 2 ≤ n) (hζ : IsPrimitiveRoot ζ (2 * (n - 1))) :
    (((X : K[X]) ^ (n - 1) + 1) * (X + 1)).roots =
      Multiset.ofList (((List.range (n - 1)).map (fun k => 2 * k + 1) ++ [n - 1]).map (ζ ^ ·)) := by
  have hm : 0 < n - 1 := by omega
  have hp1 : (X : K[X]) ^ (n - 1) + 1 ≠ 0 := by simpa using X_pow_add_C_ne_zero hm (1 : K)
  have hp2 : (X : K[X]) + 1 ≠ 0 := by simpa using X_pow_add_C_ne_zero zero_lt_one (1 : K)
  have hneg : ζ ^ (n - 1) = -1 :=
    (Nat.mul_div_left 2 hm ▸ hζ.pow_of_dvd hm.ne' (dvd_mul_left (n - 1) 2)).eq_neg_one_of_two_right
  have hx1 : (X + 1 : K[X]).roots = {ζ ^ (n - 1)} := by
    rw [← C_1, roots_X_add_C, hneg]
  rw [roots_mul (mul_ne_zero hp1 hp2), roots_X_pow_add_one hm hζ, hx1, List.map_append,
    List.map_map, List.map_singleton]
  rfl

end Polynomial
