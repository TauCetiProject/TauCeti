/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Divisibility and remainder by powers of a variable

A power `Xᵢ ^ k` of one variable of a multivariate polynomial ring divides `Xⱼ ^ l * p`, for a
different variable `Xⱼ`, exactly when it divides `p`: multiplying by `Xⱼ ^ l` shifts every exponent
vector in the support of `p` by `l` in the coordinate `j` only, which does not change the exponents
of `Xᵢ`. No hypothesis on the coefficient semiring is needed.

Dividing out or reducing modulo a monomial can only drop variables from `vars`, and reducing modulo
`Xᵢ` evaluates `Xᵢ` to `0` (`MvPolynomial.aeval_update_X_zero_eq_modMonomial`) and eliminates `i`
from `vars` (`MvPolynomial.notMem_vars_modMonomial_single`). Because evaluation at `Xᵢ = 0` is an
algebra homomorphism, remainder modulo `Xᵢ` is multiplicative over any commutative semiring
(`MvPolynomial.modMonomial_single_mul`), so `Xᵢ` is prime to products and monic monomial factors
can be cancelled from divisibility relations over `[CommSemiring R] [NoZeroDivisors R]` without any
additive cancellation or subtraction hypothesis.

This is the divisibility input to the computation of the global sections of the twisting sheaves
`𝒪(n)` on projective space, where the two monomials are powers of two homogeneous coordinates, and
to variable elimination by minimal-exponent slicing in multihomogeneous polynomials.

## Main results

* `MvPolynomial.monomial_one_dvd_iff`, `MvPolynomial.X_pow_dvd_iff`, `MvPolynomial.X_dvd_iff`:
  divisibility by `monomial k 1`, `Xᵢ ^ n`, and `Xᵢ` in terms of the exponent support.
* `MvPolynomial.X_pow_dvd_X_pow_mul_iff`: for `i ≠ j`, `Xᵢ ^ k ∣ Xⱼ ^ l * p ↔ Xᵢ ^ k ∣ p`.
* `MvPolynomial.not_X_dvd_of_constantCoeff_ne_zero`, `MvPolynomial.not_isUnit_X`,
  `MvPolynomial.exists_eq_monomial_mul_and_forall_not_X_dvd`: no variable `Xᵢ` is a unit over a
  nontrivial semiring, and every nonzero polynomial factors as `monomial k 1 * q` with `q`
  divisible by no variable `Xᵢ`.
* `MvPolynomial.aeval_update_X_zero_eq_modMonomial`, `MvPolynomial.modMonomial_single_mul`: setting
  `X i` to `0` computes the remainder `p.modMonomial (Finsupp.single i 1)`, which is multiplicative.
* `MvPolynomial.X_dvd_mul_iff_of_noZeroDivisors`, `MvPolynomial.dvd_X_mul_iff_of_not_X_dvd`,
  `MvPolynomial.dvd_monomial_one_mul_iff_of_forall_not_X_dvd`: over `[CommSemiring R]
  [NoZeroDivisors R]`, `Xᵢ` divides a product iff it divides a factor, and factors prime to all
  variables cancel monic monomial multipliers.
* `MvPolynomial.mem_support_modMonomial`, `MvPolynomial.support_modMonomial_subset`,
  `MvPolynomial.coeff_modMonomial_of_mem_support`: support and coefficient characterization of
  `modMonomial`.
* `MvPolynomial.vars_divMonomial_subset`, `MvPolynomial.vars_modMonomial_subset`,
  `MvPolynomial.notMem_vars_modMonomial_single`: variable-set bounds for monomial division and
  remainder.
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

/-- Over a nontrivial commutative semiring, no variable `Xᵢ` is a unit. -/
theorem not_isUnit_X [Nontrivial R] (i : σ) : ¬ IsUnit (X i : MvPolynomial σ R) :=
  fun h ↦ not_isUnit_zero (by simpa using h.map constantCoeff : IsUnit (0 : R))

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

/-- An exponent vector lies in the support of `p.modMonomial s` if and only if it lies in the
support of `p` and is not bounded below by `s`. -/
theorem mem_support_modMonomial {p : MvPolynomial σ R} {s m : σ →₀ ℕ} :
    m ∈ (p.modMonomial s).support ↔ m ∈ p.support ∧ ¬ s ≤ m := by
  by_cases h : s ≤ m <;> simp [h]

/-- Taking the remainder modulo a monomial selects a subset of the support. -/
theorem support_modMonomial_subset (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (p.modMonomial s).support ⊆ p.support :=
  fun _ hm ↦ (mem_support_modMonomial.mp hm).1

/-- Every exponent in the support of `p.modMonomial s` has the same coefficient as in `p`. -/
theorem coeff_modMonomial_of_mem_support {p : MvPolynomial σ R} {s m : σ →₀ ℕ}
    (hm : m ∈ (p.modMonomial s).support) :
    (p.modMonomial s).coeff m = p.coeff m :=
  coeff_modMonomial_of_not_le p (mem_support_modMonomial.mp hm).2

/-- Dividing by a monomial does not introduce new variables. -/
theorem vars_divMonomial_subset (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (p.divMonomial s).vars ⊆ p.vars := by
  classical
  intro j hj
  rw [mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨m, hm, hmj⟩ := hj
  rw [mem_support_iff, coeff_divMonomial, ← mem_support_iff] at hm
  exact ⟨s + m, hm, by simp [Finsupp.mem_support_iff] at hmj ⊢; omega⟩

/-- Taking the remainder modulo a monomial does not introduce new variables. -/
theorem vars_modMonomial_subset (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (p.modMonomial s).vars ⊆ p.vars := by
  classical
  intro j hj
  rw [mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨m, hm, hmj⟩ := hj
  exact ⟨m, support_modMonomial_subset p s hm, hmj⟩

/-- Taking the remainder modulo `X i` eliminates `i` from the variables of `p`. -/
@[simp]
theorem notMem_vars_modMonomial_single (p : MvPolynomial σ R) (i : σ) :
    i ∉ (p.modMonomial (Finsupp.single i 1)).vars := by
  classical
  rw [mem_vars_iff_mem_support]
  rintro ⟨m, hm, hmi⟩
  refine (mem_support_modMonomial.mp hm).2 ?_
  rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
  exact Finsupp.mem_support_iff.mp hmi

/-- Evaluating `X i` to `0` and leaving every other variable unchanged computes the remainder
modulo `X i`. -/
theorem aeval_update_X_zero_eq_modMonomial [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) :
    aeval (Function.update X i (0 : MvPolynomial σ R)) p = p.modMonomial (Finsupp.single i 1) := by
  conv_lhs => rw [← p.modMonomial_add_divMonomial_single i]
  rw [map_add, map_mul, aeval_X, Function.update_self, zero_mul, add_zero]
  -- Variable `i` does not occur in `p.modMonomial (Finsupp.single i 1)`, so `Function.update X i 0`
  -- agrees with `X` on its `vars`.
  conv_rhs => rw [← aeval_X_left_apply (p.modMonomial (Finsupp.single i 1))]
  rw [aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
  exact eval₂Hom_congr' rfl
    (fun j _ hj ↦ Function.update_of_ne (ne_of_mem_of_not_mem hj (by simp)) _ _) rfl

/-- Reducing a product modulo `X i` multiplies the remainders modulo `X i`. -/
@[simp]
theorem modMonomial_single_mul (i : σ) (p q : MvPolynomial σ R) :
    (p * q).modMonomial (Finsupp.single i 1) =
      p.modMonomial (Finsupp.single i 1) * q.modMonomial (Finsupp.single i 1) := by
  classical
  simp only [← aeval_update_X_zero_eq_modMonomial, map_mul]

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- Over a commutative semiring without zero divisors, a variable `X i` divides a product if and
only if it divides one of the factors (extending `MvPolynomial.X_dvd_mul_iff`, which assumes
`CommRing R` and `IsCancelMulZero R`). -/
theorem X_dvd_mul_iff_of_noZeroDivisors {i : σ} {p q : MvPolynomial σ R} :
    X i ∣ p * q ↔ X i ∣ p ∨ X i ∣ q := by
  rw [X_dvd_iff_modMonomial_eq_zero, X_dvd_iff_modMonomial_eq_zero,
    X_dvd_iff_modMonomial_eq_zero, modMonomial_single_mul, mul_eq_zero]

/-- Over a commutative semiring without zero divisors, if `X i` does not divide `g`, then `g`
divides `X i * q` if and only if `g` divides `q`. -/
theorem dvd_X_mul_iff_of_not_X_dvd {i : σ} {g q : MvPolynomial σ R}
    (hXg : ¬ X i ∣ g) : g ∣ X i * q ↔ g ∣ q := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun h ↦ dvd_mul_of_dvd_right h (X i)⟩
  have hXu : X i ∣ u := (X_dvd_mul_iff_of_noZeroDivisors.mp ⟨q, hu.symm⟩).resolve_left hXg
  obtain ⟨u', rfl⟩ := hXu
  exact ⟨u', X_mul_cancel_left_iff.mp (by simpa only [mul_left_comm, mul_assoc] using hu)⟩

/-- Over a commutative semiring without zero divisors, if no variable `X i` divides `g`, then `g`
divides `monomial m 1 * q` if and only if `g` divides `q`. -/
theorem dvd_monomial_one_mul_iff_of_forall_not_X_dvd {m : σ →₀ ℕ} {g q : MvPolynomial σ R}
    (hX : ∀ i : σ, ¬ X i ∣ g) : g ∣ monomial m 1 * q ↔ g ∣ q := by
  induction m using Finsupp.induction_linear generalizing q with
  | zero => simp
  | add m₁ m₂ hm₁ hm₂ =>
    have hmul : (monomial (m₁ + m₂) 1 : MvPolynomial σ R) * q =
        monomial m₁ 1 * (monomial m₂ 1 * q) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [hmul, hm₁, hm₂]
  | single i n =>
    induction n generalizing q with
    | zero => simp
    | succ n ih =>
      have hsucc : (monomial (Finsupp.single i (n + 1)) 1 : MvPolynomial σ R) * q =
          X i * (monomial (Finsupp.single i n) 1 * q) := by
        rw [add_comm n 1, Finsupp.single_add, ← mul_assoc, X, monomial_mul_monomial, one_mul]
      rw [hsucc, dvd_X_mul_iff_of_not_X_dvd (hX i), ih]

end NoZeroDivisors

end MvPolynomial
