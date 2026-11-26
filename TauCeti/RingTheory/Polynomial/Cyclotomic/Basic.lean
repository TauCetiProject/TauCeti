/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Basic identities for cyclotomic polynomials

`Polynomial.cyclotomic_five` gives the fifth cyclotomic polynomial as the finite geometric
sum `X⁴ + X³ + X² + X + 1` over any ring.

Mathlib defines `Φ₅` abstractly, as a product over primitive roots of unity, and only unfolds it
to a sum through `Polynomial.cyclotomic_prime`. Recording the expanded form once, as a `simp`
lemma over an arbitrary ring, lets explicit factorisation and Galois-group computations work with
the concrete coefficients directly. It is used for the factorisation of `Φ₅` over a field
containing `√5` in `TauCeti.RingTheory.Polynomial.Cyclotomic.SqrtFive`, and to identify
`X⁴ + X³ + X² + X + 1` with `Φ₅` in the worked quartic examples in
`TauCeti.FieldTheory.GaloisGroups.Quartic.Examples`, where its Galois group over `ℚ` is
computed as `(ℤ/5)ˣ`.

`Polynomial.cyclotomic_twelve`, `Polynomial.cyclotomic_eighteen` and
`Polynomial.cyclotomic_thirty` expand `Φ₁₂`, `Φ₁₈` and `Φ₃₀` in the same way, which is what is
needed to check that these polynomials annihilate an explicit matrix.

Over a nonzero ring, `Polynomial.cyclotomic_ne_one` records that a cyclotomic polynomial of
positive order is not `1`.

Over any ring, `Polynomial.monic_cyclotomic_comp_X_add_one` and
`Polynomial.natDegree_cyclotomic_comp_X_add_one` record that the shifted cyclotomic polynomial
`Φ_n(X + 1)` is monic of degree `φ(n)`, and `Polynomial.cyclotomic_comp_X_add_one_dvd` shows that
`Φ_m(X + 1)` divides `(1 + X) ^ n - 1` whenever `m ∣ n`. The first two are used for the shifted
prime-power cyclotomic polynomials in `TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow`. Over a
commutative `ℚ`-algebra, `Polynomial.isCoprime_cyclotomic` shows that `Φ_m` and `Φ_n` are coprime
for `m ≠ n`, so over a characteristic-zero domain no nonunit polynomial can divide both `Φ_m` and
`Φ_n` (`Polynomial.not_dvd_cyclotomic_of_dvd`), nor both `Φ_m(X + 1)` and `Φ_n(X + 1)`
(`Polynomial.not_dvd_cyclotomic_comp_X_add_one_of_dvd`). For a prime `p`,
`Polynomial.coeff_cyclotomic_prime_comp_X_add_one` gives the coefficients of `Φ_p(X + 1)` as the
binomial coefficients `p choose (n + 1)`; this is the explicit form behind the Eisenstein property
of `Φ_p(X + 1)` at `p`, and it computes the Newton polygon of `Φ_p(X + 1)` over a `p`-adic field.
-/

public section

namespace Polynomial

/-- The fifth cyclotomic polynomial is `X ^ 4 + X ^ 3 + X ^ 2 + X + 1`. -/
@[simp]
theorem cyclotomic_five (R : Type*) [Ring R] : cyclotomic 5 R = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  abel

/-- The twelfth cyclotomic polynomial is `X ^ 4 - X ^ 2 + 1`. -/
@[simp]
theorem cyclotomic_twelve (R : Type*) [Ring R] : cyclotomic 12 R = X ^ 4 - X ^ 2 + 1 := by
  suffices cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 by
    rw [← map_cyclotomic_int, this]
    simp
  rw [show (12 : ℕ) = 6 * 2 from rfl,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide), cyclotomic_six]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

/-- The eighteenth cyclotomic polynomial is `X ^ 6 - X ^ 3 + 1`. -/
@[simp]
theorem cyclotomic_eighteen (R : Type*) [Ring R] : cyclotomic 18 R = X ^ 6 - X ^ 3 + 1 := by
  suffices cyclotomic 18 ℤ = X ^ 6 - X ^ 3 + 1 by
    rw [← map_cyclotomic_int, this]
    simp
  rw [show (18 : ℕ) = 6 * 3 from rfl,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_three (by decide), cyclotomic_six]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

/-- The thirtieth cyclotomic polynomial is `X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1`. -/
@[simp]
theorem cyclotomic_thirty (R : Type*) [Ring R] :
    cyclotomic 30 R = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  suffices cyclotomic 30 ℤ = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 by
    rw [← map_cyclotomic_int, this]
    simp
  have h := cyclotomic_expand_eq_cyclotomic_mul (p := 5) (n := 6) Nat.prime_five (by decide) ℤ
  apply mul_right_cancel₀ (cyclotomic_ne_zero 6 ℤ)
  rw [show (30 : ℕ) = 6 * 5 from rfl, ← h, cyclotomic_six]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

section Ring

variable {R : Type*} [Ring R]

/-- `Φ_n(X + 1)` has degree `φ(n)`. -/
@[simp]
theorem natDegree_cyclotomic_comp_X_add_one [Nontrivial R] (n : ℕ) :
    ((cyclotomic n R).comp (X + 1)).natDegree = n.totient := by
  have h1 : (X + 1 : R[X]).leadingCoeff = 1 := by simpa using (monic_X_add_C (1 : R)).leadingCoeff
  rw [natDegree_comp_eq_of_mul_ne_zero (by simp [(cyclotomic.monic n R).leadingCoeff, h1]),
    natDegree_cyclotomic]
  simp

/-- Over a nonzero ring, a cyclotomic polynomial of positive order is not `1`, as it has positive
degree. -/
theorem cyclotomic_ne_one [Nontrivial R] {n : ℕ} (hn : 0 < n) : cyclotomic n R ≠ 1 := fun h ↦ by
  simpa [h] using degree_cyclotomic_pos n R hn

/-- `Φ_n(X + 1)` is monic. -/
theorem monic_cyclotomic_comp_X_add_one (n : ℕ) : ((cyclotomic n R).comp (X + 1)).Monic := by
  simpa using (cyclotomic.monic n R).comp_X_add_C 1

/-- For a prime `p`, the coefficients of `Φ_p(X + 1)` are the binomial coefficients
`p choose (n + 1)`. -/
@[simp]
theorem coeff_cyclotomic_prime_comp_X_add_one (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((cyclotomic p R).comp (X + 1)).coeff n = (p.choose (n + 1) : R) := by
  rw [cyclotomic_prime, geom_sum_X_comp_X_add_one_eq_sum, finsetSum_coeff]
  simp only [← C_eq_natCast, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- `Φ_m(X + 1)` divides `(1 + X) ^ n - 1` whenever `m ∣ n`. -/
theorem cyclotomic_comp_X_add_one_dvd {m n : ℕ} (h : m ∣ n) :
    (cyclotomic m R).comp (X + 1) ∣ (1 + X) ^ n - 1 := by
  have hZ : (cyclotomic m ℤ).comp (X + 1) ∣ (1 + X : ℤ[X]) ^ n - 1 := by
    simpa [add_comm (1 : ℤ[X]) X] using
      _root_.map_dvd (compRingHom (X + 1 : ℤ[X]))
        ((cyclotomic.dvd_X_pow_sub_one m ℤ).trans (dvd_pow_sub_one_of_dvd h))
  simpa [Polynomial.map_comp] using _root_.map_dvd (mapRingHom (Int.castRingHom R)) hZ

end Ring

/-- Over a commutative `ℚ`-algebra, the cyclotomic polynomials `Φ_m` and `Φ_n` are coprime for
`m ≠ n`. -/
theorem isCoprime_cyclotomic {R : Type*} [CommRing R] [Algebra ℚ R] {m n : ℕ} (h : m ≠ n) :
    IsCoprime (cyclotomic m R) (cyclotomic n R) := by
  simpa using (cyclotomic.isCoprime_rat h).map (mapRingHom (algebraMap ℚ R))

/-- Over a characteristic-zero integral domain, a nonunit polynomial dividing `Φ_n` divides no
`Φ_m` with `m ≠ n`. -/
theorem not_dvd_cyclotomic_of_dvd {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {F : R[X]}
    (hFu : ¬ IsUnit F) {m n : ℕ} (hmn : m ≠ n) (hdn : F ∣ cyclotomic n R) :
    ¬ F ∣ cyclotomic m R := by
  intro hdm
  let φ := algebraMap R (FractionRing R)
  have hcop : IsCoprime ((cyclotomic m R).map φ) ((cyclotomic n R).map φ) := by
    simpa using isCoprime_cyclotomic (R := FractionRing R) hmn
  have hu : IsUnit (F.map φ) :=
    hcop.isUnit_of_dvd' (Polynomial.map_dvd φ hdm) (Polynomial.map_dvd φ hdn)
  have hdeg : F.natDegree = 0 := by
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective R (FractionRing R))]
    exact natDegree_eq_zero_of_isUnit hu
  obtain ⟨G, hFG⟩ := hdn
  have h1 : F.coeff 0 * G.leadingCoeff = 1 := by
    rw [← hdeg, ← leadingCoeff, ← leadingCoeff_mul, ← hFG, (cyclotomic.monic n R).leadingCoeff]
  exact hFu (eq_C_of_natDegree_eq_zero hdeg ▸ (IsUnit.of_mul_eq_one _ h1).map C)

/-- Over a characteristic-zero integral domain, a nonunit polynomial dividing `Φ_n(X + 1)` divides
no `Φ_m(X + 1)` with `m ≠ n`. -/
theorem not_dvd_cyclotomic_comp_X_add_one_of_dvd {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {F : R[X]} (hFu : ¬ IsUnit F) {m n : ℕ} (hmn : m ≠ n)
    (hdn : F ∣ (cyclotomic n R).comp (X + 1)) :
    ¬ F ∣ (cyclotomic m R).comp (X + 1) := by
  intro hdm
  have h1 (P : R[X]) : (P.comp (X - 1)).comp (X + 1) = P := by
    rw [comp_assoc, sub_comp, X_comp, one_comp, add_sub_cancel_right, comp_X]
  have h2 (P : R[X]) : (P.comp (X + 1)).comp (X - 1) = P := by
    rw [comp_assoc, add_comp, X_comp, one_comp, sub_add_cancel, comp_X]
  have hFu' : ¬ IsUnit (F.comp (X - 1)) := fun hu ↦
    hFu (by rw [← h1 F]; exact hu.map (compRingHom (X + 1 : R[X])))
  exact not_dvd_cyclotomic_of_dvd hFu' hmn
    (by rw [← h2 (cyclotomic n R)]; exact _root_.map_dvd (compRingHom (X - 1 : R[X])) hdn)
    (by rw [← h2 (cyclotomic m R)]; exact _root_.map_dvd (compRingHom (X - 1 : R[X])) hdm)

end Polynomial
