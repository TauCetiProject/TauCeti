/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Valuation.LocalSubring
public import TauCeti.RingTheory.Valuation.Sum

/-!
# Valuations of polynomial expressions

A valuation takes value at most `1` on every polynomial expression in an element of value at most
`1`, provided the images of the coefficients also have value at most `1`. Concretely, the ring of
integers `v.integer` is a subring containing the images of the coefficients, so it contains every
`aeval t p` with `t` in it; the proof below is the ultrametric bound on the coefficient sum, which
is what `Valuation` supplies directly.

For the tautological valuation of a valuation subring containing a field of constants, a polynomial
with nonzero constant term evaluated at an element of value less than `1` has value exactly `1`:
the constant term strictly dominates all the others. This is the polynomial estimate used in
Stichtenoth's proof that valuation rings of algebraic function fields are discrete.

Finally, weighted coefficient bounds of the form
`v (P.coeff k * x ^ k) * S ^ a ≤ A ^ a * S ^ k` are stable under products, powers and suitable
composition, and bound the value of the polynomial at `x`. This controls truncated composites of
power series.

## Main results

* `Valuation.aeval_le_one`: `v (Polynomial.aeval t p) ≤ 1` whenever `v t ≤ 1` and the images of
  the coefficients have value at most `1`.
* `TauCeti.valuation_aeval_eq_one`: a polynomial with nonzero constant term has value `1` when
  evaluated at an element of the maximal ideal of a valuation subring containing the coefficients.
* `Valuation.map_coeff_mul_mul_pow_le`, `Valuation.map_coeff_pow_mul_pow_le`,
  `Valuation.map_coeff_comp_mul_pow_le`, `Valuation.map_eval_mul_le`: weighted bounds on the
  terms of products, powers and composites of polynomials at a point, and the resulting bound on
  the value. They evaluate truncated composites of power series in nonarchimedean fields, such as
  the logarithm series after the exponential series.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0–1 infrastructure: the place-at-infinity
argument for isogenies in
`AlgebraicGeometry/EllipticCurve/Isogeny/InfinityPlace.lean` needs exactly this to see that a
pulled-back affine function of a Weierstrass curve — a polynomial in the pulled-back coordinates —
stays in the valuation ring at infinity. The statement is about a valuation and a polynomial and
nothing else, so it is stated here rather than there.

`TauCetiRoadmap/AlgebraicCurves/README.md`, Layer 0: `TauCeti.valuation_aeval_eq_one` is the
constant-term estimate used in Stichtenoth, Lemma 1.1.7, on the path to existence of places.
-/

public section

namespace Valuation

variable {R L Γ₀ : Type*} [CommSemiring R] [Ring L] [Algebra R L]
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A valuation integral on the coefficients is at most `1` on polynomial expressions in an
element of the integers.** -/
theorem aeval_le_one (v : Valuation L Γ₀) (hR : ∀ r : R, v (algebraMap R L r) ≤ 1)
    {t : L} (ht : v t ≤ 1) (p : Polynomial R) : v (Polynomial.aeval t p) ≤ 1 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine v.map_sum_le fun i _ ↦ ?_
  rw [Algebra.smul_def, v.map_mul, v.map_pow]
  exact mul_le_one' (hR _) (pow_le_one' ht i)

end Valuation

namespace Valuation

open Polynomial

/-! ### Weighted coefficient bounds for products and compositions

Fix `x`, a scale `A` and a ratio `S`. Say that a polynomial `P` has *weight `a`* if
`v (P.coeff k * x ^ k) * S ^ a ≤ A ^ a * S ^ k` for every `k`. Weights add under multiplication,
so `Q ^ n` has weight `n` when `Q` has weight `1`. If `S ≤ 1`, a polynomial of weight `1` whose
coefficients below degree `M` vanish has `v (P.eval x) * S ≤ A * S ^ M`. When the coefficients of
`F` satisfy
`v (F.coeff n) * A ^ n * S ≤ A * S ^ n`, the composite `F.comp Q` has weight `1` whenever `Q`
does. These bounds evaluate a truncated composite of two power series, such as the logarithm
series after the exponential series, at a point of a nonarchimedean field. -/

section Monoid

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
  {v : Valuation R Γ₀} {x : R} {A S : Γ₀}

/-- Weights add under multiplication of polynomials. -/
theorem map_coeff_mul_mul_pow_le {P Q : R[X]} {a b : ℕ}
    (hP : ∀ k, v (P.coeff k * x ^ k) * S ^ a ≤ A ^ a * S ^ k)
    (hQ : ∀ k, v (Q.coeff k * x ^ k) * S ^ b ≤ A ^ b * S ^ k) (k : ℕ) :
    v ((P * Q).coeff k * x ^ k) * S ^ (a + b) ≤ A ^ (a + b) * S ^ k := by
  rw [coeff_mul, Finset.sum_mul]
  refine v.map_sum_mul_le fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  calc v (P.coeff ij.1 * Q.coeff ij.2 * x ^ k) * S ^ (a + b)
      = v (P.coeff ij.1 * x ^ ij.1) * S ^ a * (v (Q.coeff ij.2 * x ^ ij.2) * S ^ b) := by
        simp only [← hij, pow_add, map_mul]
        ac_rfl
    _ ≤ A ^ a * S ^ ij.1 * (A ^ b * S ^ ij.2) := mul_le_mul' (hP _) (hQ _)
    _ = A ^ (a + b) * S ^ k := by
        rw [← hij, pow_add, pow_add]
        ac_rfl

/-- The `n`-th power of a polynomial of weight `1` has weight `n`. -/
theorem map_coeff_pow_mul_pow_le {Q : R[X]} (hQ : ∀ k, v (Q.coeff k * x ^ k) * S ≤ A * S ^ k)
    (n k : ℕ) : v ((Q ^ n).coeff k * x ^ k) * S ^ n ≤ A ^ n * S ^ k := by
  induction n generalizing k with
  | zero =>
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [coeff_one, hk]
  | succ n ih =>
    rw [pow_succ]
    exact map_coeff_mul_mul_pow_le ih (by simpa using hQ) k

/-- A polynomial of weight `1` whose coefficients vanish below degree `M` has
`v (G.eval x) * S ≤ A * S ^ M`, provided `S ≤ 1`. -/
theorem map_eval_mul_le {G : R[X]} {M : ℕ} (hS : S ≤ 1) (hG₀ : ∀ k < M, G.coeff k = 0)
    (hG : ∀ k, v (G.coeff k * x ^ k) * S ≤ A * S ^ k) : v (G.eval x) * S ≤ A * S ^ M := by
  rw [eval_eq_sum, Polynomial.sum_def]
  refine v.map_sum_mul_le fun k _ ↦ ?_
  rcases lt_or_ge k M with hk | hk
  · simp [hG₀ k hk]
  · exact (hG k).trans (mul_le_mul_right (pow_le_pow_right_of_le_one' hS hk) A)

end Monoid

section Group

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation R Γ₀} {x : R} {A S : Γ₀}

/-- Composition with a polynomial `F` whose coefficients satisfy
`v (F.coeff n) * A ^ n * S ≤ A * S ^ n` preserves weight `1`. -/
theorem map_coeff_comp_mul_pow_le {F Q : R[X]}
    (hF : ∀ n, v (F.coeff n) * A ^ n * S ≤ A * S ^ n)
    (hQ : ∀ k, v (Q.coeff k * x ^ k) * S ≤ A * S ^ k) (k : ℕ) :
    v ((F.comp Q).coeff k * x ^ k) * S ≤ A * S ^ k := by
  rw [comp_eq_sum_left, Polynomial.sum_def, finsetSum_coeff, Finset.sum_mul]
  refine v.map_sum_mul_le fun n _ ↦ ?_
  have hQn := map_coeff_pow_mul_pow_le hQ n k
  rw [coeff_C_mul, mul_assoc, map_mul, mul_assoc]
  rcases eq_or_ne (A ^ n * S ^ n) 0 with h0 | h0
  · -- A vanishing scale forces the `n`-th power term, or the weight `S`, to vanish.
    rcases eq_or_ne S 0 with rfl | hS
    · simp
    have hA : A ^ n = 0 := (mul_eq_zero.mp h0).resolve_right (pow_ne_zero n hS)
    have hv : v ((Q ^ n).coeff k * x ^ k) * S ^ n = 0 :=
      le_antisymm (hQn.trans_eq (by rw [hA, zero_mul])) zero_le
    simp [(mul_eq_zero.mp hv).resolve_right (pow_ne_zero n hS)]
  refine le_of_mul_le_mul_right ?_ (zero_lt_iff.mpr h0)
  calc v (F.coeff n) * (v ((Q ^ n).coeff k * x ^ k) * S) * (A ^ n * S ^ n)
      = v (F.coeff n) * A ^ n * S * (v ((Q ^ n).coeff k * x ^ k) * S ^ n) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ ≤ A * S ^ n * (A ^ n * S ^ k) := mul_le_mul' (hF n) hQn
    _ = A * S ^ k * (A ^ n * S ^ n) := by ac_rfl

end Group

end Valuation

open Polynomial

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {A : ValuationSubring F}

/-- A polynomial with nonzero constant term, evaluated at a nonunit of a valuation subring
containing the constants, is a unit: the constant term dominates. -/
theorem valuation_aeval_eq_one (hk : ∀ c : k, algebraMap k F c ∈ A) {x : F}
    (hx : A.valuation x < 1) {p : k[X]} (hp : p.coeff 0 ≠ 0) :
    A.valuation (aeval x p) = 1 := by
  have hkle : ∀ c : k, A.valuation (algebraMap k F c) ≤ 1 :=
    fun c ↦ (A.valuation_le_one_iff _).2 (hk c)
  have : A.valuation.IsTrivialOn k := .of_le_one _ hkle
  obtain ⟨q, hq⟩ : (X : k[X]) ∣ p - C (p.coeff 0) := X_dvd_iff.2 (by simp)
  have hsplit : aeval x p = x * aeval x q + algebraMap k F (p.coeff 0) := by
    have := congrArg (aeval x) hq
    simp only [map_sub, map_mul, aeval_X, aeval_C] at this
    linear_combination (norm := ring_nf) this
  rw [hsplit, Valuation.map_add_eq_of_lt_right, Valuation.IsTrivialOn.eq_one _ hp]
  rw [Valuation.IsTrivialOn.eq_one (A := k) _ hp, map_mul]
  calc A.valuation x * A.valuation (aeval x q)
      ≤ A.valuation x * 1 := by gcongr; exact A.valuation.aeval_le_one hkle hx.le q
    _ = A.valuation x := mul_one _
    _ < 1 := hx

end TauCeti

end
