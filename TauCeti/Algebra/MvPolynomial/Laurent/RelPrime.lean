/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.MonoidAlgebra.RelPrime
public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial
import Mathlib.Algebra.MvPolynomial.Division
import TauCeti.Algebra.MonoidAlgebra.Units

/-!
# Relative primality between polynomial and Laurent rings

Because `TauCeti.LaurentRing R K` localizes `MvPolynomial K R` at the variables `X i`, a polynomial
becomes a unit in `LaurentRing R K` if and only if it is a monomial with a unit coefficient
(`MvPolynomial.isUnit_toLaurent_iff`). Relative primality in `LaurentRing R K` therefore descends to
`MvPolynomial K R` whenever no variable `X i` divides both polynomials — in particular whenever one
of the polynomials has no variable factor (`MvPolynomial.isRelPrime_of_isRelPrime_toLaurent`). Over
a commutative domain (`[CommRing R] [NoZeroDivisors R]`), monomial division yields the converse and
gives the complete characterization `MvPolynomial.isRelPrime_iff_isRelPrime_toLaurent`.

Combining polynomial descent with `AddMonoidAlgebra.isRelPrime_prod_one_add_single` proves relative
primality in `MvPolynomial K R` for binomials `1 + monomial a c` and finite products
`∏ r ∈ s, (1 + monomial a (c r))` along `ℤ`-linearly independent exponent directions `a, b`.

Finally, in the Laurent ring `LaurentRing R K` for distinct variables `i ≠ j`, `1 + X i` and
`1 + X j` are relatively prime (`TauCeti.LaurentRing.isRelPrime_one_add_X`), yet over any nontrivial
commutative ring they generate a proper ideal (`TauCeti.LaurentRing.span_one_add_X_ne_top`,
`TauCeti.LaurentRing.not_isCoprime_one_add_X`), witnessed by evaluating all variables at `-1`.

## Main results

* `MvPolynomial.isUnit_toLaurent_iff`: `IsUnit (toLaurent d)` iff `d` is a monomial with unit
  coefficient.
* `MvPolynomial.isRelPrime_of_isRelPrime_toLaurent`: polynomial descent of relative primality from
  `LaurentRing R K` when no variable divides both polynomials (or when one has no variable factor).
* `MvPolynomial.isRelPrime_toLaurent`, `MvPolynomial.isRelPrime_iff_isRelPrime_toLaurent`: ascent
  and full characterization of relative primality under `toLaurent` over a commutative domain.
* `MvPolynomial.isRelPrime_prod_one_add_monomial`, `MvPolynomial.isRelPrime_one_add_monomial`:
  relative primality of binomials and their products along independent exponent directions.
* `TauCeti.LaurentRing.isRelPrime_one_add_X`, `TauCeti.LaurentRing.not_isCoprime_one_add_X`,
  `TauCeti.LaurentRing.span_one_add_X_ne_top`: `1 + X i` and `1 + X j` (`i ≠ j`) are relatively
  prime in `LaurentRing R K` without being coprime.
-/

public section

open AddMonoidAlgebra TauCeti

namespace MvPolynomial

section CommSemiring

variable {R K : Type*} [CommSemiring R]

/-- Every monomial in `MvPolynomial K R` with unit coefficient maps to a unit in
`LaurentRing R K`. -/
theorem isUnit_toLaurent_monomial (s : K →₀ ℕ) {r : R} (hr : IsUnit r) :
    IsUnit (toLaurent (monomial s r)) := by
  obtain ⟨u, rfl⟩ := hr
  rw [toLaurent_monomial]
  exact isUnit_iff_exists.mpr
    ⟨single (-(s.mapRange Nat.cast Nat.cast_zero : K →₀ ℤ)) ((u⁻¹ : Rˣ) : R),
      by simp [single_mul_single, AddMonoidAlgebra.one_def],
      by simp [single_mul_single, AddMonoidAlgebra.one_def]⟩

variable [NoZeroDivisors R]

/-- Over a nontrivial semiring without zero divisors, `toLaurent d` is a unit of `LaurentRing R K`
if and only if `d` is a monomial with a unit coefficient. -/
theorem isUnit_toLaurent_iff [Nontrivial R] {d : MvPolynomial K R} :
    IsUnit (toLaurent d) ↔ ∃ (s : K →₀ ℕ) (r : R), IsUnit r ∧ d = monomial s r := by
  refine ⟨fun h ↦ ?_, fun ⟨s, r, hr, hd⟩ ↦ hd ▸ isUnit_toLaurent_monomial s hr⟩
  obtain ⟨m, r, -, hr, hd⟩ := (AddMonoidAlgebra.isUnit_iff_exists_single (toLaurent d)).mp h
  have hm_mem : m ∈ (toLaurent d).coeff.support := by
    rw [hd, coeff_single, Finsupp.mem_support_iff, Finsupp.single_eq_same]
    exact hr.ne_zero
  have hm_nonneg : ∀ i, 0 ≤ m i :=
    mem_range_toLaurent_iff.mp ⟨d, rfl⟩ m hm_mem
  let s : K →₀ ℕ := m.mapRange Int.toNat Int.toNat_zero
  have hs : (s.mapRange Nat.cast Nat.cast_zero : K →₀ ℤ) = m := by
    ext i
    simpa [s] using hm_nonneg i
  refine ⟨s, r, hr, toLaurent_injective ?_⟩
  rw [hd, toLaurent_monomial, hs]

/-- **Polynomial descent of relative primality.** If `toLaurent p` and `toLaurent q` are relatively
prime in `LaurentRing R K` and no variable `X i` divides both `p` and `q`, then `p` and `q` are
relatively prime in `MvPolynomial K R`. -/
theorem isRelPrime_of_isRelPrime_toLaurent {p q : MvPolynomial K R}
    (hL : IsRelPrime (toLaurent p) (toLaurent q))
    (hX : ∀ i : K, ¬ (X i ∣ p ∧ X i ∣ q)) :
    IsRelPrime p q := by
  cases subsingleton_or_nontrivial R
  · exact fun _ _ _ ↦ isUnit_of_subsingleton _
  intro d hdp hdq
  have hu : IsUnit (toLaurent d) :=
    hL (map_dvd toLaurent hdp) (map_dvd toLaurent hdq)
  obtain ⟨s, r, hr, rfl⟩ := isUnit_toLaurent_iff.mp hu
  have hs0 : s = 0 := by
    ext i
    by_contra hi
    have hXd : (X i : MvPolynomial K R) ∣ monomial s r :=
      X_dvd_monomial.mpr (Or.inr hi)
    exact hX i ⟨hXd.trans hdp, hXd.trans hdq⟩
  rw [hs0, monomial_zero']
  exact hr.map C

/-- Polynomial descent for a polynomial with no variable factor: if `toLaurent p` and `toLaurent q`
are relatively prime and `∀ i, ¬ X i ∣ p`, then `IsRelPrime p q`. -/
theorem isRelPrime_of_isRelPrime_toLaurent_of_forall_not_X_dvd {p q : MvPolynomial K R}
    (hL : IsRelPrime (toLaurent p) (toLaurent q))
    (hX : ∀ i : K, ¬ X i ∣ p) :
    IsRelPrime p q :=
  isRelPrime_of_isRelPrime_toLaurent hL fun i ⟨hp, _⟩ ↦ hX i hp

/-- **Finite products of polynomial binomials along independent directions are relatively
prime.** -/
theorem isRelPrime_prod_one_add_monomial {ι κ : Type*} {a b : K →₀ ℕ}
    (hab : LinearIndependent ℤ
      ![a.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero,
        b.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero])
    (s : Finset ι) (t : Finset κ) (c : ι → R) (d : κ → R) :
    IsRelPrime (∏ r ∈ s, (1 + monomial a (c r))) (∏ r ∈ t, (1 + monomial b (d r))) := by
  classical
  cases subsingleton_or_nontrivial R
  · exact fun _ _ _ ↦ isUnit_of_subsingleton _
  have ha : a ≠ 0 := by
    rintro rfl
    exact one_ne_zero (LinearIndependent.pair_iff.mp hab 1 0 (by simp)).1
  have hL : IsRelPrime
      (toLaurent (∏ r ∈ s, (1 + monomial a (c r))))
      (toLaurent (∏ r ∈ t, (1 + monomial b (d r)))) := by
    simpa only [map_prod, map_add, map_one, toLaurent_monomial] using
      AddMonoidAlgebra.isRelPrime_prod_one_add_single hab s t c d
  refine isRelPrime_of_isRelPrime_toLaurent_of_forall_not_X_dvd hL fun i hdiv ↦ ?_
  obtain ⟨u, hu⟩ := hdiv
  have hcc : constantCoeff (∏ r ∈ s, (1 + monomial a (c r))) = 1 := by
    rw [map_prod]
    refine Finset.prod_eq_one fun r _ ↦ ?_
    simp [constantCoeff_monomial, ha]
  have hzero : constantCoeff (∏ r ∈ s, (1 + monomial a (c r))) = 0 := by
    rw [hu, map_mul, constantCoeff_X, zero_mul]
  exact one_ne_zero (hcc.symm.trans hzero)

/-- Polynomial binomials `1 + monomial a c` and `1 + monomial b d` along `ℤ`-linearly independent
exponent directions are relatively prime. -/
theorem isRelPrime_one_add_monomial {a b : K →₀ ℕ}
    (hab : LinearIndependent ℤ
      ![a.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero,
        b.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero])
    (c d : R) :
    IsRelPrime (1 + monomial a c) (1 + monomial b d) := by
  simpa using isRelPrime_prod_one_add_monomial hab {()} {()} (fun _ ↦ c) (fun _ ↦ d)

end CommSemiring

section CommRing

variable {R K : Type*} [CommRing R] [NoZeroDivisors R]

/-- Over a commutative domain, relative primality in `MvPolynomial K R` ascends to
`LaurentRing R K`. -/
theorem isRelPrime_toLaurent {p q : MvPolynomial K R} (h : IsRelPrime p q) :
    IsRelPrime (toLaurent p) (toLaurent q) := by
  classical
  intro D ⟨U, hPU⟩ ⟨V, hQV⟩
  obtain ⟨n, hn⟩ := LaurentRing.exists_forall_mul_toLaurent_monomial ({D, U, V} : Finset _)
  obtain ⟨d, hd⟩ := hn D (by simp)
  obtain ⟨u, hu⟩ := hn U (by simp)
  obtain ⟨v, hv⟩ := hn V (by simp)
  have hmon_mul : toLaurent (monomial (n + n) (1 : R)) =
      toLaurent (monomial n 1) * toLaurent (monomial n 1) := by
    rw [← map_mul, monomial_mul_monomial, one_mul]
  have hdp : d ∣ monomial (n + n) 1 * p := by
    refine ⟨u, toLaurent_injective ?_⟩
    rw [map_mul, map_mul, hmon_mul, hPU, ← hd, ← hu]
    ring
  have hdq : d ∣ monomial (n + n) 1 * q := by
    refine ⟨v, toLaurent_injective ?_⟩
    rw [map_mul, map_mul, hmon_mul, hQV, ← hd, ← hv]
    ring
  obtain ⟨m₁, r₁, -, hr₁p, rfl⟩ := dvd_monomial_mul_iff_exists.mp hdp
  have hr₁q : r₁ ∣ monomial (n + n) 1 * q :=
    (dvd_mul_left r₁ (monomial m₁ 1)).trans hdq
  obtain ⟨m₂, r₂, -, hr₂q, rfl⟩ := dvd_monomial_mul_iff_exists.mp hr₁q
  have hr₂p : r₂ ∣ p := (dvd_mul_left r₂ (monomial m₂ 1)).trans hr₁p
  have hur₂ : IsUnit r₂ := h hr₂p hr₂q
  have hunit_rhs : IsUnit (toLaurent (monomial m₁ 1 * (monomial m₂ 1 * r₂))) := by
    rw [← mul_assoc, monomial_mul_monomial, one_mul, map_mul]
    exact (isUnit_toLaurent_monomial (m₁ + m₂) isUnit_one).mul (hur₂.map toLaurent)
  rw [← hd] at hunit_rhs
  exact isUnit_of_mul_isUnit_left hunit_rhs

/-- **Characterization of polynomial relative primality via the Laurent ring.** Over a nontrivial
commutative ring without zero divisors, `p, q : MvPolynomial K R` are relatively prime if and only
if their images in `LaurentRing R K` are relatively prime and no variable divides both `p` and
`q`. -/
theorem isRelPrime_iff_isRelPrime_toLaurent [Nontrivial R] {p q : MvPolynomial K R} :
    IsRelPrime p q ↔
      IsRelPrime (toLaurent p) (toLaurent q) ∧
        ∀ i : K, ¬ (X i ∣ p ∧ X i ∣ q) :=
  ⟨fun h ↦ ⟨isRelPrime_toLaurent h, fun i ⟨hp, hq⟩ ↦ (prime_X (i := i)).not_isUnit (h hp hq)⟩,
    fun ⟨hL, hX⟩ ↦ isRelPrime_of_isRelPrime_toLaurent hL hX⟩

end CommRing

end MvPolynomial

namespace TauCeti.LaurentRing

section RelPrime

variable {R K : Type*}

/-- For distinct variables `i ≠ j`, `1 + X i` and `1 + X j` are relatively prime in
`LaurentRing R K` over any commutative semiring without zero divisors. -/
theorem isRelPrime_one_add_X [CommSemiring R] [NoZeroDivisors R] {i j : K} (hij : i ≠ j) :
    IsRelPrime (1 + X (R := R) i) (1 + X j) := by
  classical
  have hli : LinearIndependent ℤ ![Finsupp.single i (1 : ℤ), Finsupp.single j (1 : ℤ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hi : s = 0 := by
      simpa [Finsupp.single_apply, hij, hij.symm] using congrArg (fun f : K →₀ ℤ ↦ f i) hst
    have hj : t = 0 := by
      simpa [Finsupp.single_apply, hij, hij.symm] using congrArg (fun f : K →₀ ℤ ↦ f j) hst
    exact ⟨hi, hj⟩
  simpa [X_def] using AddMonoidAlgebra.isRelPrime_one_add_single hli (1 : R) (1 : R)

/-- Over any nontrivial commutative ring, `1 + X i` and `1 + X j` are not coprime in
`LaurentRing R K`. -/
theorem not_isCoprime_one_add_X [CommRing R] [Nontrivial R] (i j : K) :
    ¬ IsCoprime (1 + X (R := R) i) (1 + X j) := by
  rintro ⟨u, v, huv⟩
  let φ : LaurentRing R K →ₐ[R] R := aeval (fun _ : K ↦ (-1 : Rˣ))
  have hφ := congrArg φ huv
  simp only [map_add, map_mul, map_one, φ, aeval_X, Units.val_neg, Units.val_one,
    add_neg_cancel, mul_zero, add_zero] at hφ
  exact zero_ne_one hφ

/-- Over any nontrivial commutative ring, the ideal generated by `1 + X i` and `1 + X j` in
`LaurentRing R K` is proper. -/
theorem span_one_add_X_ne_top [CommRing R] [Nontrivial R] (i j : K) :
    Ideal.span ({1 + X (R := R) i, 1 + X j} : Set (LaurentRing R K)) ≠ ⊤ := by
  intro htop
  have h1 : (1 : LaurentRing R K) ∈ Ideal.span ({1 + X i, 1 + X j} : Set (LaurentRing R K)) :=
    htop ▸ Submodule.mem_top
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp h1
  exact not_isCoprime_one_add_X i j ⟨u, v, huv⟩

end RelPrime

end TauCeti.LaurentRing
