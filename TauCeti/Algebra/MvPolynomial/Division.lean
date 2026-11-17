/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Divisibility by powers of a variable

A power `Xᵢ ^ k` of one variable of a multivariate polynomial ring divides `Xⱼ ^ l * p`, for a
different variable `Xⱼ`, exactly when it divides `p`: multiplying by `Xⱼ ^ l` shifts every exponent
vector in the support of `p` by `l` in the coordinate `j` only, which does not change the exponents
of `Xᵢ`. No hypothesis on the coefficient semiring is needed.

This is the divisibility input to the computation of the global sections of the twisting sheaves
`𝒪(n)` on projective space, where the two monomials are powers of two homogeneous coordinates.

## Main results

* `MvPolynomial.monomial_one_dvd_iff`, `MvPolynomial.X_pow_dvd_iff`, `MvPolynomial.X_dvd_iff`:
  divisibility by `monomial k 1`, `Xᵢ ^ n`, and `Xᵢ` in terms of the exponent support.
* `MvPolynomial.X_pow_dvd_X_pow_mul_iff`: for `i ≠ j`, `Xᵢ ^ k ∣ Xⱼ ^ l * p ↔ Xᵢ ^ k ∣ p`.
* `MvPolynomial.exists_eq_monomial_mul_and_forall_not_X_dvd`: every nonzero polynomial factors as
  `monomial k 1 * q` with `q` divisible by no variable `Xᵢ`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- `monomial k 1` divides `p` if and only if every exponent vector in the support of `p` is
coordinatewise at least `k`. -/
theorem monomial_one_dvd_iff {k : σ →₀ ℕ} {p : MvPolynomial σ R} :
    monomial k (1 : R) ∣ p ↔ ∀ s ∈ p.support, k ≤ s := by
  rw [monomial_one_dvd_iff_modMonomial_eq_zero, MvPolynomial.ext_iff]
  refine ⟨fun h s hs ↦ by_contra fun hle ↦ ?_, fun h s ↦ ?_⟩
  · exact mem_support_iff.mp hs (by simpa [coeff_modMonomial_of_not_le p hle] using h s)
  · by_cases hle : k ≤ s
    · simp [coeff_modMonomial_of_le p hle]
    · simp only [coeff_modMonomial_of_not_le p hle]
      simpa using fun hs ↦ hle (h s (mem_support_iff.mpr hs))

/-- A power `Xᵢ ^ n` divides `p` if and only if every supported exponent of `p` has `i`-th
coordinate at least `n`. -/
theorem X_pow_dvd_iff {i : σ} {n : ℕ} {p : MvPolynomial σ R} :
    X i ^ n ∣ p ↔ ∀ s ∈ p.support, n ≤ s i := by
  simp [X_pow_eq_monomial, monomial_one_dvd_iff, Finsupp.single_le_iff]

/-- A variable `Xᵢ` divides `p` if and only if every supported exponent of `p` has nonzero `i`-th
coordinate. -/
theorem X_dvd_iff {i : σ} {p : MvPolynomial σ R} :
    X i ∣ p ↔ ∀ s ∈ p.support, s i ≠ 0 := by
  simpa [Nat.one_le_iff_ne_zero] using X_pow_dvd_iff (i := i) (n := 1) (p := p)

/-- A polynomial with nonzero constant term is divisible by no variable `Xᵢ`. -/
theorem not_X_dvd_of_constantCoeff_ne_zero {p : MvPolynomial σ R}
    (hp : constantCoeff p ≠ 0) (i : σ) : ¬ X i ∣ p := fun h ↦ by
  have h0 : (0 : σ →₀ ℕ) ∈ p.support := mem_support_iff.mpr (by simpa [constantCoeff_eq] using hp)
  exact X_dvd_iff.mp h 0 h0 rfl

/-- **Factoring out the greatest common monic monomial.** Every nonzero multivariate polynomial `p`
factors as `monomial k 1 * q` where `k` is the coordinatewise infimum of `p.support` and no
variable `Xᵢ` divides `q`. -/
theorem exists_eq_monomial_mul_and_forall_not_X_dvd {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ (k : σ →₀ ℕ) (q : MvPolynomial σ R), p = monomial k 1 * q ∧ ∀ i, ¬ X i ∣ q := by
  classical
  have hsupp : p.support.Nonempty := support_nonempty.mpr hp
  let k : σ →₀ ℕ := p.support.inf' hsupp fun s ↦ s
  have hmod : p.modMonomial k = 0 :=
    monomial_one_dvd_iff_modMonomial_eq_zero.mp
      (monomial_one_dvd_iff.mpr fun s hs ↦ Finset.inf'_le (fun s ↦ s) hs)
  refine ⟨k, p.divMonomial k, ?_, fun i hXi ↦ ?_⟩
  · have hdiv := divMonomial_add_modMonomial p k
    rwa [hmod, add_zero, eq_comm] at hdiv
  · have hle : k + Finsupp.single i 1 ≤ k := Finset.le_inf' hsupp (fun s ↦ s) fun s hs ↦ by
      have hks : k ≤ s := Finset.inf'_le (fun s ↦ s) hs
      have hts : s - k ∈ (p.divMonomial k).support := by
        rw [mem_support_iff, coeff_divMonomial, add_tsub_cancel_of_le hks]
        exact mem_support_iff.mp hs
      have hne : (s - k) i ≠ 0 := X_dvd_iff.mp hXi (s - k) hts
      intro j
      simp only [Finsupp.add_apply]
      by_cases hij : i = j
      · subst hij
        simp only [Finsupp.single_eq_same]
        simp only [Finsupp.tsub_apply] at hne
        omega
      · simpa [Finsupp.single_apply, hij] using hks j
    have hi := hle i
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hi
    omega

/-- **A power of a variable divides a polynomial times a power of another variable iff it divides
the polynomial.** -/
theorem X_pow_dvd_X_pow_mul_iff {i j : σ} (hij : i ≠ j) {k l : ℕ} {p : MvPolynomial σ R} :
    X i ^ k ∣ X j ^ l * p ↔ X i ^ k ∣ p := by
  refine ⟨fun h ↦ ?_, fun h ↦ dvd_mul_of_dvd_right h _⟩
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero] at h ⊢
  ext m
  by_cases hm : Finsupp.single i k ≤ m
  · exact coeff_modMonomial_of_le _ hm
  -- the coefficient of `p` at `m` is that of `Xⱼ ^ l * p` at `m + l eⱼ`, which has the same
  -- exponent of `Xᵢ` as `m`
  have hm' : ¬Finsupp.single i k ≤ m + Finsupp.single j l := by
    simpa [Finsupp.single_le_iff, Finsupp.single_apply, hij.symm] using hm
  have h' := congrArg (fun q ↦ q.coeff (m + Finsupp.single j l)) h
  rw [coeff_modMonomial_of_not_le _ hm', X_pow_eq_monomial, add_comm m, coeff_monomial_mul,
    one_mul] at h'
  rw [coeff_modMonomial_of_not_le _ hm, h']
  simp

end MvPolynomial
