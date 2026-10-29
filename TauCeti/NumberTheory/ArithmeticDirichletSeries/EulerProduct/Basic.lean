/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Basic
public import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

/-!
# Canonical local factors and formal Euler products for ideal arithmetic functions

This file develops the Euler-product layer for arithmetic functions on nonzero ideals. It builds
the canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

It then restricts an ideal arithmetic function to the nonzero ideals whose prime factors lie in a
prescribed set of height-one primes, and proves that for a *finite* set of primes the norm
coefficients of that restriction are exactly the product of the local factors, taken in Mathlib's
Dirichlet convolution of arithmetic functions. Passing to Mathlib's formal Euler product gives the
norm coefficients of the original function. Everything here is a formal identity of coefficients:
no analytic convergence hypothesis enters.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.IdealArithmeticFunction.supportedPart f S` is `f` restricted to the nonzero ideals all
  of whose prime factors lie in `S`, and zero elsewhere.

## Main results

* `TauCeti.IdealArithmeticFunction.supportedPart_insert`: for a multiplicative `f`, adjoining one
  prime to the support convolves the restriction with the restriction to the powers of that prime.
* `TauCeti.IdealArithmeticFunction.normCoeff_supportedPart`: the **finite Euler product**
  `normCoeff (supportedPart f S) = ∏ P ∈ S, localArithmeticFactor f P` for a multiplicative `f`
  and a finite set `S` of height-one primes.
* `TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct`: the norm coefficients of a
  multiplicative ideal arithmetic function are Mathlib's formal Euler product of its canonical
  local factors.
* `TauCeti.IdealArithmeticFunction.normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor`:
  at a power `p ^ k` of a rational prime, the norm coefficient is read off from the finitely many
  local factors at the primes above `p`;
  `TauCeti.IdealArithmeticFunction.normCoeff_apply_prime_pow_eq_localArithmeticFactor` is the case
  of a single prime above `p`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor_one_apply_pow` and
  `TauCeti.IdealArithmeticFunction.localArithmeticFactor_one_mul_apply_pow`: the local factors of
  the trivial function at one prime, and the convolution of those at two primes of norm `p`.

## Implementation notes

"Supported on `S`" is spelled `Ideal.IsPrimeTo · Sᶜ`: no prime *outside* `S` divides the ideal.
That predicate, and the splitting `Ideal.IsPrimeTo.exists_eq_pow_mul` of an ideal into a prime
power times a cofactor together with its uniqueness `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul`, live
in `TauCeti/RingTheory/DedekindDomain/Ideal/Basic.lean`, since nothing in them is specific to
a number field. Uniqueness is what makes the induction work: it is why exactly one summand of the
ideal convolution survives at each ideal. The multiplicativity of `f` over a prime-power
factorization, `TauCeti.IdealArithmeticFunction.IsMultiplicative.map_prod_pow`, likewise lives
with the predicate it elaborates, in `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`.

`TauCeti.MultiplicativeIdealWeight.restrictAway` is the opposite regime and is not a substitute:
it restricts *away from* a **finite** set of primes and stays inside the bundled weight carrier. A
finite Euler product needs support on a *finite* set of primes, so all but finitely many primes are
bad; such a function is never a `MultiplicativeIdealWeight`, whose zero support is finite by
definition. Hence `supportedPart` is a plain ideal arithmetic function.

Finiteness is what carries the finite products to the full Euler product. A nonzero ideal has
only finitely many prime divisors, and only finitely many primes have norm at most a given `n`, so
at a fixed norm coefficient the restriction `supportedPart f S` already agrees with `f` as soon as
`S` contains those primes. Each finite product is therefore eventually the exact norm coefficient,
and Mathlib's `ArithmeticFunction.eulerProduct`, being the limit of those finite products, computes
the norm coefficients of `f` itself. The local factors are derived from `f` rather than stored, so
this identity holds for any multiplicative `f` with no further data.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
-/

public section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K]

/-- The absolute norm is multiplicative on prime powers. -/
theorem absNorm_primeIdealPow [IsDedekindDomain (𝓞 K)] (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    Ideal.absNorm (primeIdealPow P e : Ideal (𝓞 K)) = Ideal.absNorm P.asIdeal ^ e := by
  rw [coe_primeIdealPow, map_pow]

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

/-- The canonical local power series of `f` at a height-one prime `P`; its coefficient at `n` is
the value of `f` at the nonzero ideal `P ^ n`. -/
noncomputable def localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ f (P.primeIdealPow n)

/-- Coefficients of the canonical local power series are the prime-power values of `f`. -/
@[simp]
theorem coeff_localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    PowerSeries.coeff n (localPowerSeries f P) =
      f (P.primeIdealPow n) := by
  simp only [localPowerSeries, PowerSeries.coeff_mk]

/-- The constant coefficient of the canonical local power series is `f 1`. -/
@[simp]
theorem constantCoeff_localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (localPowerSeries f P).constantCoeff = f 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_localPowerSeries, P.primeIdealPow_zero]

/-- Conjugating ideal coefficients conjugates the coefficients of every local power series. -/
@[simp]
theorem localPowerSeries_star (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (star f).localPowerSeries P = (f.localPowerSeries P).map (starRingEnd ℂ) := by
  ext n
  simp

/-- The canonical local arithmetic factor at `P`, obtained by substituting `N(P)⁻ˢ` into the
formal prime-power series through Mathlib's `ArithmeticFunction.ofPowerSeries`. -/
noncomputable def localArithmeticFactor [IsDedekindDomain (𝓞 K)] (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℂ :=
  ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (localPowerSeries f P)

/-- The canonical local arithmetic factor is Mathlib's arithmetic function associated to the
local power series at `P`. -/
theorem localArithmeticFactor_def [IsDedekindDomain (𝓞 K)] (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    localArithmeticFactor f P =
      ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (localPowerSeries f P) := by
  rw [localArithmeticFactor]

section NumberField

variable [NumberField K]

/-- At a power of `N(P)`, the local arithmetic factor is the corresponding value at `P ^ n`. -/
@[simp]
theorem localArithmeticFactor_apply_pow (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localArithmeticFactor f P (Ideal.absNorm P.asIdeal ^ n) =
      f (P.primeIdealPow n) := by
  rw [localArithmeticFactor, ArithmeticFunction.ofPowerSeries_apply_pow
    (NumberField.HeightOneSpectrum.one_lt_absNorm P)]
  exact coeff_localPowerSeries f P n

/-- A local arithmetic factor vanishes away from powers of its prime-ideal norm. -/
@[simp]
theorem localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m) :
    localArithmeticFactor f P m = 0 := by
  rw [localArithmeticFactor, ArithmeticFunction.ofPowerSeries_apply
    (NumberField.HeightOneSpectrum.one_lt_absNorm P),
    Function.extend_apply' _ _ _ (by simpa using hm), Pi.zero_apply]

/-- The local arithmetic factor of a conjugate ideal function has conjugate values. -/
@[simp]
theorem localArithmeticFactor_star_apply (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (star f).localArithmeticFactor P n = star (f.localArithmeticFactor P n) := by
  by_cases hn : ∃ e : ℕ, Ideal.absNorm P.asIdeal ^ e = n
  · obtain ⟨e, rfl⟩ := hn
    simp
  · simp [localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq _ P hn]

/-- A nonzero value of a local arithmetic factor is supported on a power of the prime-ideal
norm. -/
theorem exists_pow_eq_of_localArithmeticFactor_apply_ne_zero (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {m : ℕ} (hm : localArithmeticFactor f P m ≠ 0) :
    ∃ n : ℕ, Ideal.absNorm P.asIdeal ^ n = m := by
  by_contra hpow
  exact hm (localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq f P hpow)

/-- If `f` takes the unit ideal to `1`, each canonical local arithmetic factor is a
multiplicative arithmetic function. -/
theorem isMultiplicative_localArithmeticFactor
    {f : IdealArithmeticFunction K} (hf : f 1 = 1)
    (P : HeightOneSpectrum (𝓞 K)) :
    (localArithmeticFactor f P).IsMultiplicative := by
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
  · obtain ⟨p, n, hn, _hpP, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
    exact ⟨p, n, hp.prime, hn, hnorm.symm⟩
  · simpa using hf

/-- If `f` takes the unit ideal to `1`, the formal Euler product of its canonical local factors is
multiplicative as an arithmetic function. -/
theorem isMultiplicative_eulerProduct {f : IdealArithmeticFunction K} (hf : f 1 = 1) :
    (ArithmeticFunction.eulerProduct f.localArithmeticFactor).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_eulerProduct _ (isMultiplicative_localArithmeticFactor hf)

/-- At each coefficient, finite products of the canonical local factors eventually equal their
formal Euler product. -/
theorem tendsTo_eulerProduct_localArithmeticFactor (f : IdealArithmeticFunction K)
    (hf : f 1 = 1) (n : ℕ) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      (∏ P ∈ S, localArithmeticFactor f P) n =
        ArithmeticFunction.eulerProduct f.localArithmeticFactor n := by
  simp_rw [localArithmeticFactor_def]
  exact
    ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries
      (fun P : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm P.asIdeal)
      (fun P ↦ localPowerSeries f P)
      (fun P ↦ (constantCoeff_localPowerSeries f P).trans hf) n

end NumberField

/-- The canonical local power series of the convolution identity is the constant series `1`. -/
@[simp]
theorem localPowerSeries_delta (P : HeightOneSpectrum (𝓞 K)) :
    localPowerSeries (delta : IdealArithmeticFunction K) P = 1 := by
  rw [PowerSeries.ext_iff]
  intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_localPowerSeries, delta_one]
      simp
  | succ n =>
      rw [coeff_localPowerSeries, delta_of_ne_one]
      · simp
      · intro hpow
        have hunit : IsUnit P.asIdeal :=
          IsUnit.of_pow_eq_one
            (by simpa only [P.coe_primeIdealPow, Submonoid.coe_one] using
              congrArg Subtype.val hpow) (Nat.succ_ne_zero n)
        exact P.isPrime.ne_top (Ideal.isUnit_iff.mp hunit)

section IsDedekindDomain

variable [IsDedekindDomain (𝓞 K)]

/-- Every canonical local arithmetic factor of the convolution identity is `1`. -/
@[simp]
theorem localArithmeticFactor_delta (P : HeightOneSpectrum (𝓞 K)) :
    localArithmeticFactor (delta : IdealArithmeticFunction K) P = 1 := by
  rw [localArithmeticFactor, localPowerSeries_delta]
  exact (ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal)).map_one

end IsDedekindDomain

/-! ### Finite Euler products -/

/-- The part of `f` supported on the nonzero ideals all of whose prime factors lie in `S`: it
agrees with `f` there and vanishes on every other nonzero ideal. Being supported on `S` is
`Ideal.IsPrimeTo · Sᶜ`, that no prime outside `S` divides the ideal. Use
`supportedPart_apply_of_isPrimeTo_compl` and `supportedPart_apply_of_not_isPrimeTo_compl` rather
than unfolding. -/
noncomputable def supportedPart (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : IdealArithmeticFunction K :=
  Set.indicator {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ} f

variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}

/-- On an ideal supported on `S`, the restriction of `f` to `S` is `f`. -/
@[simp]
theorem supportedPart_apply_of_isPrimeTo_compl (hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) :
    supportedPart f S A = f A :=
  Set.indicator_of_mem
    (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f

/-- On an ideal with a prime factor outside `S`, the restriction of `f` to `S` vanishes. -/
@[simp]
theorem supportedPart_apply_of_not_isPrimeTo_compl (hA : ¬ Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) :
    supportedPart f S A = 0 :=
  Set.indicator_of_notMem
    (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f

/-- The restriction of `f` to `S` is supported on the ideals supported on `S`. -/
theorem isPrimeTo_compl_of_supportedPart_apply_ne_zero (hA : supportedPart f S A ≠ 0) :
    Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ :=
  not_not.mp fun h ↦ hA (supportedPart_apply_of_not_isPrimeTo_compl h)

/-- Every nonzero ideal is supported on the set of all height-one primes. -/
@[simp]
theorem supportedPart_univ (f : IdealArithmeticFunction K) : supportedPart f Set.univ = f := by
  funext A
  refine supportedPart_apply_of_isPrimeTo_compl ?_
  rw [Set.compl_univ]
  exact Ideal.isPrimeTo_empty.mpr (by simpa using nonZeroDivisors.coe_ne_zero A)

section IsDedekindDomain

variable [IsDedekindDomain (𝓞 K)]

/-- The unit ideal is supported on every set of primes. This is not marked `@[simp]`: `simp`
already reaches it through `supportedPart_apply_of_isPrimeTo_compl`. -/
theorem supportedPart_one (f : IdealArithmeticFunction K) (S : Set (HeightOneSpectrum (𝓞 K))) :
    supportedPart f S 1 = f 1 :=
  supportedPart_apply_of_isPrimeTo_compl (by simp [Ideal.one_eq_top])

/-- Restricting a multiplicative ideal arithmetic function to the ideals supported on `S` keeps it
multiplicative: an ideal is supported on `S` exactly when both factors of a product are. -/
theorem IsMultiplicative.supportedPart (hf : f.IsMultiplicative)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (IdealArithmeticFunction.supportedPart f S).IsMultiplicative := by
  refine ⟨by rw [supportedPart_one, hf.map_one], fun {I J} hIJ ↦ ?_⟩
  by_cases hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ
  · by_cases hJ : Ideal.IsPrimeTo (J : Ideal (𝓞 K)) Sᶜ
    · rw [supportedPart_apply_of_isPrimeTo_compl (A := I * J)
        (by rw [Submonoid.coe_mul]; exact Ideal.isPrimeTo_mul_iff.mpr ⟨hI, hJ⟩),
        supportedPart_apply_of_isPrimeTo_compl hI, supportedPart_apply_of_isPrimeTo_compl hJ,
        hf.map_mul_of_isRelPrime hIJ]
    · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
        (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
        supportedPart_apply_of_not_isPrimeTo_compl hJ, mul_zero]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
      (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
      supportedPart_apply_of_not_isPrimeTo_compl hI, zero_mul]

/-- Only the unit ideal is supported on no prime at all, so the empty restriction is the
convolution identity scaled by the value at the unit ideal. -/
@[simp]
theorem supportedPart_empty (f : IdealArithmeticFunction K) :
    supportedPart f ∅ = f 1 • delta := by
  funext A
  have hiff : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (∅ : Set (HeightOneSpectrum (𝓞 K)))ᶜ ↔ A = 1 := by
    rw [Set.compl_empty, Ideal.isPrimeTo_univ_iff, ← Ideal.one_eq_top]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  rcases eq_or_ne A 1 with rfl | hA
  · simp
  · simp [supportedPart_apply_of_not_isPrimeTo_compl fun h ↦ hA (hiff.mp h),
      delta_of_ne_one hA]

/-- **A surviving `{P}`-part is a power of `P`.**  The restriction to the powers of a single prime
kills every ideal not prime to `{P}ᶜ`, and for a single prime that condition is exactly being a
power of `P`. -/
private theorem exists_eq_pow_of_supportedPart_singleton_apply_ne_zero
    {P : HeightOneSpectrum (𝓞 K)} {I : (Ideal (𝓞 K))⁰} (hI : supportedPart f {P} I ≠ 0) :
    ∃ m : ℕ, (I : Ideal (𝓞 K)) = P.asIdeal ^ m :=
  Ideal.isPrimeTo_compl_singleton_iff.mp (isPrimeTo_compl_of_supportedPart_apply_ne_zero hI)

end IsDedekindDomain

variable [NumberField K]

/-- **Only the `S`-part/`P`-part pair survives.**  Where `A` is `P ^ n` times an ideal `B` prime to
`Sᶜ`, and `C` is that power of `P`, every pair of the antidiagonal of `A` other than `(B, C)`
contributes zero to the convolution. -/
private theorem supportedPart_mul_eq_zero_of_ne {P : HeightOneSpectrum (𝓞 K)} (hPS : P ∈ Sᶜ)
    {A B C : (Ideal (𝓞 K))⁰} {n : ℕ} (hB : Ideal.IsPrimeTo (B : Ideal (𝓞 K)) Sᶜ)
    (hC : (C : Ideal (𝓞 K)) = P.asIdeal ^ n)
    (hA : (A : Ideal (𝓞 K)) = P.asIdeal ^ n * (B : Ideal (𝓞 K))) :
    ∀ p ∈ Ideal.divisorsAntidiagonal A, p ≠ (B, C) →
      supportedPart f S p.1 * supportedPart f {P} p.2 = 0 := by
  intro p hp hne
  by_contra hp0
  have h1 := isPrimeTo_compl_of_supportedPart_apply_ne_zero (left_ne_zero_of_mul hp0)
  obtain ⟨m, h2⟩ :=
    exists_eq_pow_of_supportedPart_singleton_apply_ne_zero (right_ne_zero_of_mul hp0)
  have hmul : (p.1 : Ideal (𝓞 K)) * (p.2 : Ideal (𝓞 K)) = (A : Ideal (𝓞 K)) := by
    rw [← Submonoid.coe_mul, Ideal.mem_divisorsAntidiagonal.mp hp]
  have heq : P.asIdeal ^ m * (p.1 : Ideal (𝓞 K)) = P.asIdeal ^ n * (B : Ideal (𝓞 K)) := by
    rw [← h2, mul_comm, hmul, hA]
  obtain ⟨rfl, hval⟩ :=
    Ideal.eq_and_eq_of_pow_mul_eq_pow_mul P.ne_bot (h1.not_dvd hPS) (hB.not_dvd hPS) heq
  exact hne (Prod.ext (Subtype.ext hval) (Subtype.ext (h2.trans hC.symm)))

/-- **A nonvanishing summand forces the support.**  If any pair in the antidiagonal of `A`
contributes to the convolution, then `A` itself is prime to `(insert P S)ᶜ`: its left factor is
prime to `Sᶜ` and its right factor is a power of `P`. -/
private theorem isPrimeTo_compl_insert_of_supportedPart_mul_ne_zero
    {P : HeightOneSpectrum (𝓞 K)} {A : (Ideal (𝓞 K))⁰} {p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰}
    (hp : p ∈ Ideal.divisorsAntidiagonal A)
    (hp0 : supportedPart f S p.1 * supportedPart f {P} p.2 ≠ 0) :
    Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (insert P S)ᶜ := by
  have h1 := isPrimeTo_compl_of_supportedPart_apply_ne_zero (left_ne_zero_of_mul hp0)
  obtain ⟨m, h2⟩ :=
    exists_eq_pow_of_supportedPart_singleton_apply_ne_zero (right_ne_zero_of_mul hp0)
  rw [← congrArg Subtype.val (Ideal.mem_divisorsAntidiagonal.mp hp), Submonoid.coe_mul]
  refine Ideal.isPrimeTo_mul_iff.mpr
    ⟨h1.mono (Set.compl_subset_compl.mpr (Set.subset_insert P S)), ?_⟩
  rw [h2]
  exact (Ideal.isPrimeTo_asIdeal_iff.mpr (by simp)).pow m

/-- **Splitting off one prime.** For a multiplicative `f`, adjoining a prime `P ∉ S` to the support
convolves the restriction to `S` with the restriction to the powers of `P`; the factorization of an
ideal supported on `insert P S` into its `P`-part and its `S`-part is unique, so exactly one
summand of the convolution survives. -/
theorem supportedPart_insert (hf : f.IsMultiplicative) {P : HeightOneSpectrum (𝓞 K)}
    (hP : P ∉ S) :
    supportedPart f (insert P S) = convolution (supportedPart f S) (supportedPart f {P}) := by
  have hPS : P ∈ Sᶜ := Set.mem_compl hP
  funext A
  rw [convolution_apply]
  by_cases hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) (insert P S)ᶜ
  · obtain ⟨n, J, hJ, hAJ⟩ := hA.exists_eq_pow_mul (𝔭 := P)
    obtain ⟨B, rfl⟩ : ∃ B : (Ideal (𝓞 K))⁰, (B : Ideal (𝓞 K)) = J :=
      ⟨⟨J, mem_nonZeroDivisors_of_ne_zero (by simpa using hJ.ne_bot)⟩, rfl⟩
    have hCP : Ideal.IsPrimeTo ((P.primeIdealPow n : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        ({P} : Set (HeightOneSpectrum (𝓞 K)))ᶜ :=
      Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨n, P.coe_primeIdealPow n⟩
    have hBC : B * P.primeIdealPow n = A :=
      Subtype.ext (by rw [Submonoid.coe_mul, P.coe_primeIdealPow, mul_comm, ← hAJ])
    rw [Finset.sum_eq_single_of_mem (B, P.primeIdealPow n)
        (Ideal.mem_divisorsAntidiagonal.mpr hBC)
        (supportedPart_mul_eq_zero_of_ne hPS hJ (P.coe_primeIdealPow n) hAJ),
      supportedPart_apply_of_isPrimeTo_compl hA, supportedPart_apply_of_isPrimeTo_compl hJ,
      supportedPart_apply_of_isPrimeTo_compl hCP,
      ← hf.map_mul_of_isRelPrime
        ((hJ.mono (Set.singleton_subset_iff.mpr hPS)).isRelPrime hCP), hBC]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl hA]
    exact (Finset.sum_eq_zero fun p hp ↦ not_not.mp fun hp0 ↦
      hA (isPrimeTo_compl_insert_of_supportedPart_mul_ne_zero hp hp0)).symm

/-- The norm coefficients of the restriction to the powers of a single prime `P` are exactly its
canonical local arithmetic factor. -/
@[simp]
theorem normCoeff_supportedPart_singleton (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    normCoeff K (supportedPart f {P}) = localArithmeticFactor f P := by
  have h2 : 2 ≤ Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
  ext n
  rw [normCoeff_eq_sum_normFiber]
  by_cases hn : ∃ k : ℕ, Ideal.absNorm P.asIdeal ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    have hCmem : P.primeIdealPow k ∈ normFiber K (Ideal.absNorm P.asIdeal ^ k) := by
      rw [mem_normFiber, P.coe_primeIdealPow, map_pow]
    have hother : ∀ I ∈ normFiber K (Ideal.absNorm P.asIdeal ^ k), I ≠ P.primeIdealPow k →
        supportedPart f ({P} : Set (HeightOneSpectrum (𝓞 K))) I = 0 := by
      intro I hI hIC
      by_contra hI0
      obtain ⟨j, hj⟩ := exists_eq_pow_of_supportedPart_singleton_apply_ne_zero hI0
      have hjk : Ideal.absNorm P.asIdeal ^ j = Ideal.absNorm P.asIdeal ^ k := by
        rw [← map_pow, ← hj]
        exact (mem_normFiber K).mp hI
      exact hIC (Subtype.ext (by rw [hj, P.coe_primeIdealPow, Nat.pow_right_injective h2 hjk]))
    rw [Finset.sum_eq_single_of_mem (P.primeIdealPow k) hCmem hother,
      supportedPart_apply_of_isPrimeTo_compl
        (Ideal.isPrimeTo_compl_singleton_iff.mpr ⟨k, P.coe_primeIdealPow k⟩),
      localArithmeticFactor_apply_pow]
  · rw [localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq f P hn]
    refine Finset.sum_eq_zero fun I hI ↦ ?_
    by_contra hI0
    obtain ⟨j, hj⟩ := exists_eq_pow_of_supportedPart_singleton_apply_ne_zero hI0
    exact hn ⟨j, by rw [← map_pow, ← hj]; exact (mem_normFiber K).mp hI⟩

/-- **The finite Euler product.** For a multiplicative ideal arithmetic function, the norm
coefficients of its restriction to the ideals supported on a finite set `S` of height-one primes
are the product, in Mathlib's Dirichlet convolution of arithmetic functions, of the canonical
local factors at the primes of `S`. -/
theorem normCoeff_supportedPart (hf : f.IsMultiplicative)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    normCoeff K (supportedPart f (S : Set (HeightOneSpectrum (𝓞 K))))
      = ∏ P ∈ S, localArithmeticFactor f P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, supportedPart_empty, hf.map_one, one_smul, normCoeff_delta,
        Finset.prod_empty]
  | insert P S hPS ih =>
      rw [Finset.coe_insert, supportedPart_insert hf (by simpa using hPS), normCoeff_convolution,
        ih, normCoeff_supportedPart_singleton, Finset.prod_insert hPS, mul_comm]

/-- At a fixed coefficient, restricting to a sufficiently large finite set of prime ideals does
not change the norm coefficient: the norm fibre is finite, and each of its members is eventually
supported. -/
theorem eventually_normCoeff_supportedPart_eq (f : IdealArithmeticFunction K) (n : ℕ) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      normCoeff K (supportedPart f (S : Set (HeightOneSpectrum (𝓞 K)))) n =
        normCoeff K f n := by
  filter_upwards [(Filter.eventually_all_finset (normFiber K n)).mpr
    fun A _ ↦ Ideal.eventually_isPrimeTo_compl (nonZeroDivisors.coe_ne_zero A)] with S hS
  rw [normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
  exact Finset.sum_congr rfl fun A hA ↦ supportedPart_apply_of_isPrimeTo_compl (hS A hA)

/-- **The formal Euler product of norm coefficients.** The norm coefficients of a multiplicative
ideal arithmetic function are Mathlib's `ArithmeticFunction.eulerProduct` of the canonical local
arithmetic factors. This is an equality of arithmetic functions; the analytic infinite product
obtained after evaluating their `LSeries` is a separate absolute-convergence question. -/
theorem normCoeff_eq_eulerProduct (hf : f.IsMultiplicative) :
    normCoeff K f = ArithmeticFunction.eulerProduct f.localArithmeticFactor := by
  ext n
  obtain ⟨S, hcoeff, hprod⟩ := ((eventually_normCoeff_supportedPart_eq f n).and
    (tendsTo_eulerProduct_localArithmeticFactor f hf.map_one n)).exists
  rw [normCoeff_supportedPart hf S] at hcoeff
  exact hcoeff.symm.trans hprod

/-- **The local Euler factor at a rational prime.** For a multiplicative ideal arithmetic function
and a rational prime `p`, the norm coefficient at `p ^ k` is the coefficient at `p ^ k` of the
product of the local factors over any finite set `S` of height-one primes containing every prime
above `p`: an ideal of norm `p ^ k` has only prime factors above `p`. -/
theorem normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor (hf : f.IsMultiplicative)
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal → P ∈ S) (k : ℕ) :
    normCoeff K f (p ^ k) = (∏ P ∈ S, localArithmeticFactor f P) (p ^ k) := by
  rw [← normCoeff_supportedPart hf, normCoeff_eq_sum_normFiber, normCoeff_eq_sum_normFiber]
  refine Finset.sum_congr rfl fun A hA ↦ (supportedPart_apply_of_isPrimeTo_compl ?_).symm
  refine Ideal.isPrimeTo_iff.mpr ⟨nonZeroDivisors.coe_ne_zero A, fun P hP hdvd ↦ hP (hS P ?_)⟩
  -- `N(P)` divides `N(A) = p ^ k`, so it is a positive power of `p`, and `p ∈ P`.
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp
    ((mem_normFiber K).mp hA ▸ map_dvd Ideal.absNorm hdvd)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hj))
  have hmem := Ideal.absNorm_mem P.asIdeal
  rw [hj, Nat.cast_pow] at hmem
  exact P.isPrime.mem_of_pow_mem _ hmem

/-- If `P` is the only height-one prime containing the rational prime `p`, the norm coefficient
of a multiplicative ideal arithmetic function at `p ^ k` is the coefficient at `p ^ k` of the
local factor at `P`. -/
theorem normCoeff_apply_prime_pow_eq_localArithmeticFactor (hf : f.IsMultiplicative)
    {p : ℕ} (hp : p.Prime) (P : HeightOneSpectrum (𝓞 K))
    (hP : ∀ Q : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ Q.asIdeal → Q = P) (k : ℕ) :
    normCoeff K f (p ^ k) = localArithmeticFactor f P (p ^ k) := by
  rw [normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor hf hp {P}
    (fun Q hQ ↦ Finset.mem_singleton.mpr (hP Q hQ)), Finset.prod_singleton]

/-- At a prime of norm `q`, the local factor of the trivial function is `1` at every power of
`q`. -/
theorem localArithmeticFactor_one_apply_pow {P : HeightOneSpectrum (𝓞 K)} {q : ℕ}
    (hP : Ideal.absNorm P.asIdeal = q) (k : ℕ) :
    (1 : IdealArithmeticFunction K).localArithmeticFactor P (q ^ k) = 1 := by
  rw [← hP, localArithmeticFactor_apply_pow, Pi.one_apply]

/-- The local factors of the trivial function at two primes of norm `p` convolve to `k + 1` at
`p ^ k`, the number of ways to write `p ^ k` as a product of two powers of `p`. -/
theorem localArithmeticFactor_one_mul_apply_pow {p : ℕ} (hp : p.Prime)
    {P Q : HeightOneSpectrum (𝓞 K)} (hP : Ideal.absNorm P.asIdeal = p)
    (hQ : Ideal.absNorm Q.asIdeal = p) (k : ℕ) :
    ((1 : IdealArithmeticFunction K).localArithmeticFactor P *
      (1 : IdealArithmeticFunction K).localArithmeticFactor Q) (p ^ k) = k + 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b ↦ (1 : IdealArithmeticFunction K).localArithmeticFactor P a *
      (1 : IdealArithmeticFunction K).localArithmeticFactor Q b),
    Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_congr rfl fun i hi ↦ by
    rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos,
      localArithmeticFactor_one_apply_pow hP, localArithmeticFactor_one_apply_pow hQ, one_mul]]
  simp

end IdealArithmeticFunction

end TauCeti
