/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.DirichletCharacter.Basic

/-!
# Twisted divisor sums

This file defines the twisted divisor sum

`sigma e psi phi n = sum_{d | n} psi (n / d) * phi d * d ^ e`

attached to two Dirichlet characters. These sums are the nonconstant Fourier coefficients of
Eisenstein series with character: the weight-`k` coefficient uses exponent `e = k - 1`.

The definition is expressed as a Dirichlet convolution of multiplicative arithmetic functions.
The resulting API includes its divisor-sum formula, multiplicativity, and its values at prime
powers. For characters of level one it specializes to Mathlib's ordinary divisor sum
`ArithmeticFunction.sigma`.

## Main declarations

* `DirichletCharacter.twistedDivisorSum`: the arithmetic function of twisted divisor sums;
* `DirichletCharacter.isMultiplicative_twistedDivisorSum`: its multiplicativity;
* `DirichletCharacter.twistedDivisorSum_apply_prime_pow`: its prime-power formula;
* `DirichletCharacter.twistedDivisorSum_apply_prime_pow_of_dvd_left_level`: its
  bad-level specialization;
* `DirichletCharacter.twistedDivisorSum_modOne_eq_sigma`: its reduction to the ordinary
  divisor sum;
* `DirichletCharacter.twistedDivisorSum_changeLevel_of_coprime`: raising the levels of the
  characters does not change the values at integers prime to the new level;
* `DirichletCharacter.linearIndependent_twistedDivisorSum`: for a positive exponent, the twisted
  divisor sums of distinct pairs of characters of level `N` are linearly independent as functions
  on the integers prime to `N`.

The independence statement compares values at products `p q` of two distinct primes, which
Dirichlet's theorem on primes in arithmetic progressions places in arbitrary residue classes
modulo `N`. Since `p q` has the four divisors `1, p, q, p q`, the value
`(psi p + phi p p^e) (psi q + phi q q^e)` is an affine function of `p^e` and of `q^e` whose
coefficient of `p^e` (at `q^e`-degree zero) is `phi p psi q`, the value of a character of
`(ZMod N)ˣ × (ZMod N)ˣ`;
independence then follows from Artin's independence of characters
(`linearIndependent_monoidHom`).

The convention follows Diamond--Shurman, *A First Course in Modular Forms*, Chapter 4
(especially Sections 4.5--4.8).
-/

public section

namespace DirichletCharacter

open ArithmeticFunction

variable {R : Type*} [CommSemiring R] {u v : ℕ}

/-- The twisted divisor sum attached to `psi`, `phi`, and the exponent `e`.

At a positive integer `n` its value is
`sum_{d | n} psi (n / d) * phi d * d ^ e`. It is packaged as an arithmetic function so that
Dirichlet convolution supplies its multiplicativity. -/
def twistedDivisorSum (e : ℕ) (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) :
    ArithmeticFunction R :=
  toArithmeticFunction (psi ·) *
    (toArithmeticFunction (phi ·)).pmul
      (ArithmeticFunction.pow e : ArithmeticFunction R)

/-- The defining divisor-sum formula for `twistedDivisorSum`. -/
theorem twistedDivisorSum_apply (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) (n : ℕ) :
    twistedDivisorSum e psi phi n =
      ∑ d ∈ n.divisors, psi (n / d) * phi d * (d : R) ^ e := by
  rw [twistedDivisorSum, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b ↦
      toArithmeticFunction (psi ·) a *
        ((toArithmeticFunction (phi ·)).pmul
          (ArithmeticFunction.pow e : ArithmeticFunction R)) b)]
  refine Finset.sum_congr rfl fun (d : ℕ) hd ↦ ?_
  have hn : n ≠ 0 := Nat.ne_zero_of_mem_divisors hd
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdiv_pos : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hd_pos
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.pow_apply]
  rw [
    ← psi.apply_eq_toArithmeticFunction_apply hdiv_pos.ne',
    ← phi.apply_eq_toArithmeticFunction_apply hd_pos.ne']
  simp [hd_pos.ne', mul_assoc]

/-- Twisted divisor sums are multiplicative arithmetic functions. -/
@[arith_mult]
theorem isMultiplicative_twistedDivisorSum (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) : (twistedDivisorSum e psi phi).IsMultiplicative :=
  psi.isMultiplicative_toArithmeticFunction.mul
    (phi.isMultiplicative_toArithmeticFunction.pmul
      ArithmeticFunction.isMultiplicative_pow.natCast)

/-- The twisted divisor sum at `1` is `1`. -/
@[simp]
theorem twistedDivisorSum_one (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) : twistedDivisorSum e psi phi 1 = 1 :=
  (isMultiplicative_twistedDivisorSum e psi phi).map_one

/-- The twisted divisor sum on a prime power is a finite geometric-type sum. -/
theorem twistedDivisorSum_apply_prime_pow (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) (r : ℕ) {p : ℕ} (hp : p.Prime) :
    twistedDivisorSum e psi phi (p ^ r) =
      ∑ j ∈ Finset.range (r + 1),
        psi p ^ (r - j) * phi p ^ j * (p : R) ^ (j * e) := by
  rw [twistedDivisorSum_apply, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp [Nat.pow_div hjr hp.pos, map_pow, Nat.cast_pow, pow_mul]

/-- At a prime, the twisted divisor sum has its two expected Euler-factor terms. -/
theorem twistedDivisorSum_apply_prime (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) {p : ℕ} (hp : p.Prime) :
    twistedDivisorSum e psi phi p = psi p + phi p * (p : R) ^ e := by
  simpa [Finset.sum_range_succ, mul_assoc] using
    twistedDivisorSum_apply_prime_pow e psi phi 1 hp

/-- If `p` divides the level of the left character, only the right-character term remains in
the value at `p ^ r`. -/
theorem twistedDivisorSum_apply_prime_pow_of_dvd_left_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) (r : ℕ) {p : ℕ}
    (hp : p.Prime) (hpu : p ∣ u) :
    twistedDivisorSum e psi phi (p ^ r) = phi p ^ r * (p : R) ^ (r * e) := by
  have hpsi : psi p = 0 := psi.map_nonunit <| by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.dvd_iff_not_coprime.mp hpu
  rw [twistedDivisorSum_apply_prime_pow e psi phi r hp, Finset.sum_eq_single r]
  · simp [hpsi]
  · intro j hj hne
    have hjr : j < r :=
      Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hne
    simp [hpsi, Nat.sub_ne_zero_of_lt hjr]
  · simp

/-- If `p` divides the level of the left character, only the right-character term remains in
the value at `p`. -/
theorem twistedDivisorSum_apply_prime_of_dvd_left_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) {p : ℕ} (hp : p.Prime)
    (hpu : p ∣ u) :
    twistedDivisorSum e psi phi p = phi p * (p : R) ^ e := by
  simpa using
    twistedDivisorSum_apply_prime_pow_of_dvd_left_level e psi phi 1 hp hpu

/-- If `p` divides the level of the right character, only the left-character term remains in
the value at `p ^ r`. -/
theorem twistedDivisorSum_apply_prime_pow_of_dvd_right_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) (r : ℕ) {p : ℕ}
    (hp : p.Prime) (hpv : p ∣ v) : twistedDivisorSum e psi phi (p ^ r) = psi p ^ r := by
  have hphi : phi p = 0 := phi.map_nonunit <| by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.dvd_iff_not_coprime.mp hpv
  rw [twistedDivisorSum_apply_prime_pow e psi phi r hp, Finset.sum_eq_single 0]
  · simp [hphi]
  · intro j _ hne
    simp [hphi, hne]
  · simp

/-- If `p` divides the level of the right character, only the left-character term remains in
the value at `p`. -/
theorem twistedDivisorSum_apply_prime_of_dvd_right_level (e : ℕ)
    (psi : DirichletCharacter R u) (phi : DirichletCharacter R v) {p : ℕ} (hp : p.Prime)
    (hpv : p ∣ v) : twistedDivisorSum e psi phi p = psi p := by
  simpa using
    twistedDivisorSum_apply_prime_pow_of_dvd_right_level e psi phi 1 hp hpv

/-- With both characters of level one, the twisted divisor sum is Mathlib's ordinary divisor
sum `ArithmeticFunction.sigma`. -/
@[simp]
theorem twistedDivisorSum_modOne_eq_sigma (e : ℕ) (psi phi : DirichletCharacter R 1) :
    twistedDivisorSum e psi phi =
      (ArithmeticFunction.sigma e : ArithmeticFunction R) := by
  have h_one : toArithmeticFunction (1 : ℕ → R) =
      (ArithmeticFunction.zeta : ArithmeticFunction R) := by
    rw [← ArithmeticFunction.toArithmeticFunction_eq_self
      (ArithmeticFunction.zeta : ArithmeticFunction R)]
    exact toArithmeticFunction_congr ArithmeticFunction.const_one_eq_zeta
  rw [twistedDivisorSum, DirichletCharacter.modOne_eq_one (χ := psi),
    DirichletCharacter.modOne_eq_one (χ := phi), h_one, ArithmeticFunction.zeta_pmul]
  simpa using congrArg (fun f : ArithmeticFunction ℕ ↦ (f : ArithmeticFunction R))
    (ArithmeticFunction.zeta_mul_pow_eq_sigma (k := e))

/-- Raising the levels of the two characters to a common multiple `N` does not change the twisted
divisor sum at an integer prime to `N`. -/
theorem twistedDivisorSum_changeLevel_of_coprime {N : ℕ} (e : ℕ) (psi : DirichletCharacter R u)
    (phi : DirichletCharacter R v) (hu : u ∣ N) (hv : v ∣ N) {n : ℕ} (hn : n.Coprime N) :
    twistedDivisorSum e (changeLevel hu psi) (changeLevel hv phi) n =
      twistedDivisorSum e psi phi n := by
  rw [twistedDivisorSum_apply, twistedDivisorSum_apply]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' := Nat.dvd_of_mem_divisors hd
  rw [changeLevel_natCast_of_coprime hu psi (hn.coprime_dvd_left (Nat.div_dvd_of_dvd hd')),
    changeLevel_natCast_of_coprime hv phi (hn.coprime_dvd_left hd')]

end DirichletCharacter

namespace DirichletCharacter

variable {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} {s : Finset ι}

/-- If `∑ᵢ gᵢ (aᵢ + bᵢ P) (cᵢ + dᵢ Q)` vanishes for two distinct values of `P` and two distinct
values of `Q`, then the coefficient `∑ᵢ gᵢ bᵢ cᵢ` of `P` vanishes. -/
private theorem sum_mul_mul_eq_zero_of_affine {g a b c d : ι → R} {P₁ P₂ Q₁ Q₂ : R}
    (hP : P₁ ≠ P₂) (hQ : Q₁ ≠ Q₂)
    (h : ∀ P ∈ ({P₁, P₂} : Set R), ∀ Q ∈ ({Q₁, Q₂} : Set R),
      ∑ i ∈ s, g i * ((a i + b i * P) * (c i + d i * Q)) = 0) :
    ∑ i ∈ s, g i * (b i * c i) = 0 := by
  have hexp (P Q : R) : ∑ i ∈ s, g i * ((a i + b i * P) * (c i + d i * Q)) =
      ∑ i ∈ s, g i * (a i * c i) + (∑ i ∈ s, g i * (b i * c i)) * P +
        (∑ i ∈ s, g i * (a i * d i)) * Q + (∑ i ∈ s, g i * (b i * d i)) * (P * Q) := by
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h₁₁ := h P₁ (by simp) Q₁ (by simp)
  have h₁₂ := h P₁ (by simp) Q₂ (by simp)
  have h₂₁ := h P₂ (by simp) Q₁ (by simp)
  have h₂₂ := h P₂ (by simp) Q₂ (by simp)
  rw [hexp] at h₁₁ h₁₂ h₂₁ h₂₂
  have hD : (∑ i ∈ s, g i * (b i * d i)) * ((P₁ - P₂) * (Q₁ - Q₂)) = 0 := by
    linear_combination h₁₁ - h₁₂ - h₂₁ + h₂₂
  have hD : ∑ i ∈ s, g i * (b i * d i) = 0 := by
    simpa [sub_ne_zero.mpr hP, sub_ne_zero.mpr hQ] using hD
  have hB : (∑ i ∈ s, g i * (b i * c i)) * (P₁ - P₂) = 0 := by
    linear_combination h₁₁ - h₂₁ - (P₁ - P₂) * Q₁ * hD
  simpa [sub_ne_zero.mpr hP] using hB

variable [CharZero R] {N : ℕ} [NeZero N]

/-- **Independence of twisted divisor sums.** For a positive exponent `e`, the twisted divisor
sums `n ↦ ∑_{d ∣ n} psi (n / d) phi d d^e` attached to pairwise distinct pairs `(psi, phi)` of
Dirichlet characters of level `N` are linearly independent as functions on the positive integers
prime to `N`. -/
theorem linearIndependent_twistedDivisorSum {e : ℕ} (he : e ≠ 0)
    {psi phi : ι → DirichletCharacter R N} (h : Function.Injective fun i ↦ (psi i, phi i)) :
    LinearIndependent R fun i (n : {n : ℕ // n.Coprime N}) ↦
      twistedDivisorSum e (psi i) (phi i) n := by
  classical
  -- The characters `(x, y) ↦ phi i x * psi i y` of `(ZMod N)ˣ × (ZMod N)ˣ`.
  let G : ι → (ZMod N)ˣ × (ZMod N)ˣ →* R := fun i ↦
    (phi i).toMonoidHom.comp ((Units.coeHom (ZMod N)).comp (MonoidHom.fst _ _)) *
      (psi i).toMonoidHom.comp ((Units.coeHom (ZMod N)).comp (MonoidHom.snd _ _))
  have hG (i : ι) (x y : (ZMod N)ˣ) : G i (x, y) = phi i x * psi i y := rfl
  have hGinj : Function.Injective G := by
    intro i j hij
    have hxy (x y : (ZMod N)ˣ) : phi i x * psi i y = phi j x * psi j y := by
      rw [← hG, ← hG, hij]
    exact h (Prod.ext (MulChar.ext fun y ↦ by simpa using hxy 1 y)
      (MulChar.ext fun x ↦ by simpa using hxy x 1))
  rw [linearIndependent_iff']
  intro s g hsum
  refine linearIndependent_iff'.mp ((linearIndependent_monoidHom _ R).comp G hGinj) s g ?_
  ext ⟨x, y⟩
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, hG, smul_eq_mul,
    Pi.zero_apply]
  -- The vanishing combination, evaluated at `p q` for primes `p ≡ x` and `q ≡ y` modulo `N`.
  have hpq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpx : (p : ZMod N) = x)
      (hqy : (q : ZMod N) = y) :
      ∑ i ∈ s, g i * ((psi i x + phi i x * (p : R) ^ e) *
        (psi i y + phi i y * (q : R) ^ e)) = 0 := by
    have hpN : p.Coprime N := (ZMod.isUnit_iff_coprime p N).mp (hpx ▸ x.isUnit)
    have hqN : q.Coprime N := (ZMod.isUnit_iff_coprime q N).mp (hqy ▸ y.isUnit)
    have := congrFun hsum ⟨p * q, Nat.coprime_mul_iff_left.mpr ⟨hpN, hqN⟩⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(isMultiplicative_twistedDivisorSum e _ _).map_mul_of_coprime
      ((Nat.coprime_primes hp hq).mpr hpq), twistedDivisorSum_apply_prime _ _ _ hp,
      twistedDivisorSum_apply_prime _ _ _ hq, hpx, hqy]
  -- Four primes `q₁ < q₂ < p₁ < p₂` with `p₁ ≡ p₂ ≡ x` and `q₁ ≡ q₂ ≡ y` modulo `N`.
  obtain ⟨q₁, -, hq₁, hq₁y⟩ := Nat.forall_exists_prime_gt_and_eq_mod y.isUnit 0
  obtain ⟨q₂, hq₁₂, hq₂, hq₂y⟩ := Nat.forall_exists_prime_gt_and_eq_mod y.isUnit q₁
  obtain ⟨p₁, hqp, hp₁, hp₁x⟩ := Nat.forall_exists_prime_gt_and_eq_mod x.isUnit q₂
  obtain ⟨p₂, hp₁₂, hp₂, hp₂x⟩ := Nat.forall_exists_prime_gt_and_eq_mod x.isUnit p₁
  have hpow {m n : ℕ} (hmn : m < n) : (m : R) ^ e ≠ (n : R) ^ e := by
    exact_mod_cast (Nat.pow_left_injective he).ne hmn.ne
  refine sum_mul_mul_eq_zero_of_affine (a := fun i ↦ psi i x) (d := fun i ↦ phi i y)
    (hpow hp₁₂) (hpow hq₁₂) ?_
  rintro P hP Q hQ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP hQ
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · exact hpq hp₁ hq₁ (by omega) hp₁x hq₁y
  · exact hpq hp₁ hq₂ (by omega) hp₁x hq₂y
  · exact hpq hp₂ hq₁ (by omega) hp₂x hq₁y
  · exact hpq hp₂ hq₂ (by omega) hp₂x hq₂y

end DirichletCharacter
