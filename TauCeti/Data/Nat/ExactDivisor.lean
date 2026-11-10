/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact divisors of a natural number

`Q` is an **exact divisor** of `N` when `Q ∣ N` and `Q` is coprime to the complementary divisor
`N / Q`; equivalently, `N = Q · M` with `Q` and `M` sharing no prime. Such a `Q` collects the
full power of each prime it contains, so the exact divisors of `N` are exactly the products of
the maximal prime powers `p ^ (N.factorization p)`, and they form a Boolean algebra under the
subsets of `N.primeFactors`. The notion is also called a *unitary* or *Hall* divisor.

The classical notation is `Q ‖ N`, which cannot be used here: `‖ ‖` is norm notation, and in the
same corner of the library `p ^ r ‖ n` means exact `p`-adic divisibility — that `r` is the full
exponent of `p`, a statement about the pair `(p, r)` rather than about the single number `p ^ r`.
The notation introduced instead is `Q ∥ N`, with the parallel bars `∥` in place of the double
vertical line `‖`; it is scoped, so it never competes with the `∥` of `AffineSubspace.Parallel`.

## Main definitions

* `TauCeti.Nat.IsExactDivisor`: the predicate itself.
* `TauCeti.Nat.ExactDivisor`: the exact divisors of a fixed `N`, bundled as a commutative group
  whose multiplication is symmetric difference.
* `TauCeti.Nat.prodPrimePow`: the exact divisor `∏ p ∈ s, p ^ v_p(N)` cut out by a set `s` of
  primes of `N`.
* `TauCeti.Nat.ExactDivisor.primeFactorsEquiv`: the identification of the exact divisors of `N`
  with the subsets of `N.primeFactors`.

## Notation

* `Q ∥ N` for `TauCeti.Nat.IsExactDivisor Q N`, in the `TauCeti.ExactDivisor` scope.

## Main results

* `TauCeti.Nat.isExactDivisor_iff`: the predicate unfolded to its two conditions.
* `TauCeti.Nat.IsExactDivisor.div`: for `N ≠ 0` the complementary divisor `N / Q` is exact too.
* `TauCeti.Nat.IsExactDivisor.ne_zero`: an exact divisor is nonzero. There is no exact divisor
  `0`, because `Nat.Coprime 0 0` is false.
* `TauCeti.Nat.IsExactDivisor.not_sq_dvd`: an exact divisor `Q ≠ 1` of `N` has `Q ^ 2 ∤ N`; for a
  prime `p ∣ N` the converse is `TauCeti.Nat.IsExactDivisor.of_not_sq_dvd`.
* `TauCeti.Nat.isExactDivisor_one`, `TauCeti.Nat.isExactDivisor_self`: `1` and (for `N ≠ 0`) `N`
  itself.
* `TauCeti.Nat.IsExactDivisor.mul`: coprime exact divisors multiply to an exact divisor, so the
  exact divisors of `N` are closed under coprime products.
* `TauCeti.Nat.isExactDivisor_iff_factorization`: exactness read on the factorization — at every
  prime the exponent of `Q` is either `0` or the full exponent of `N`.
* `TauCeti.Nat.IsExactDivisor.gcd`, `TauCeti.Nat.IsExactDivisor.div_gcd`,
  `TauCeti.Nat.IsExactDivisor.coprime_div_gcd`: the Boolean-algebra structure, in the form the
  Atkin–Lehner group law needs — `gcd Q R` and `Q / gcd Q R` are again exact divisors, and the
  second is coprime to `R`.
* `TauCeti.Nat.IsExactDivisor.mul_div_gcd_sq`: `Q * R / gcd (Q, R) ^ 2` — the symmetric
  difference of `Q` and `R` — is an exact divisor too.
* `TauCeti.Nat.ExactDivisor.val_mul`: multiplication in the bundled group has underlying value
  `Q * R / gcd (Q, R) ^ 2`.
* `TauCeti.Nat.isExactDivisor_prodPrimePow`, `TauCeti.Nat.primeFactors_prodPrimePow`,
  `TauCeti.Nat.IsExactDivisor.prodPrimePow_primeFactors`: a subset of `N.primeFactors` cuts out an
  exact divisor with exactly those prime factors, and every exact divisor arises this way — the
  prime-power generation of the family, bundled as
  `TauCeti.Nat.ExactDivisor.primeFactorsEquiv`.
* `TauCeti.Nat.isExactDivisor_primePow`: the maximal prime powers `p ^ v_p(N)` are exact divisors.
* `TauCeti.Nat.coprime_primePow_prodPrimePow`: `p ^ v_p(N)` is prime to `∏ q ∈ s, q ^ v_q(N)` for
  `p ∉ s`.
-/

public section

open scoped symmDiff

namespace TauCeti

namespace Nat

variable {N Q R : ℕ}

/-- `Q` is an **exact divisor** of `N`: it divides `N` and is coprime to the complementary
divisor `N / Q`. Written `Q ‖ N` in the literature and `Q ∥ N` here; see the module docstring for
the change of bars. -/
structure IsExactDivisor (Q N : ℕ) : Prop where
  /-- An exact divisor is a divisor. -/
  dvd : Q ∣ N
  /-- An exact divisor is coprime to its complementary divisor. -/
  coprime : Nat.Coprime Q (N / Q)

@[inherit_doc TauCeti.Nat.IsExactDivisor]
scoped[TauCeti.ExactDivisor] infix:50 " ∥ " => TauCeti.Nat.IsExactDivisor

/-- **An exact divisor is nonzero.** `0` is only a divisor of `0`, whose complementary divisor is
again `0`, and `Nat.Coprime 0 0` is false. -/
theorem IsExactDivisor.ne_zero (h : IsExactDivisor Q N) : Q ≠ 0 := by
  rintro rfl
  simpa using h.coprime

/-- An exact divisor is positive. -/
theorem IsExactDivisor.pos (h : IsExactDivisor Q N) : 0 < Q :=
  Nat.pos_of_ne_zero h.ne_zero

/-- The defining conditions of an exact divisor, as a rewrite rule. -/
@[simp]
theorem isExactDivisor_iff : IsExactDivisor Q N ↔ Q ∣ N ∧ Nat.Coprime Q (N / Q) :=
  ⟨fun h ↦ ⟨h.dvd, h.coprime⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- **The complementary divisor is exact.** For `N ≠ 0`, `N / Q` is again an exact divisor of `N`,
whose own complement is `Q` again (`Nat.div_div_self`). At `N = 0` this fails: `1` is an exact
divisor of `0`, but `0 / 1 = 0` is not. -/
theorem IsExactDivisor.div (h : IsExactDivisor Q N) (hN : N ≠ 0) : IsExactDivisor (N / Q) N :=
  ⟨Nat.div_dvd_of_dvd h.dvd, by rw [Nat.div_div_self h.dvd hN]; exact h.coprime.symm⟩

/-- **An exact divisor other than `1` divides `N` only once**: if `Q ^ 2 ∣ N`, then `Q` divides
the complementary divisor `N / Q`, to which it is coprime, so `Q = 1`. For a prime `p ∥ N` this
says `v_p(N) = 1`. -/
theorem IsExactDivisor.not_sq_dvd (h : IsExactDivisor Q N) (hQ : Q ≠ 1) : ¬ Q ^ 2 ∣ N :=
  fun hsq ↦ hQ (h.coprime.eq_one_of_dvd (Nat.dvd_div_of_mul_dvd (sq Q ▸ hsq)))

/-- **A prime dividing `N` only once is an exact divisor**, the converse of
`IsExactDivisor.not_sq_dvd` for a prime: if `p ∣ N/p` then `p ^ 2 ∣ N`, so `p` is prime to
`N / p`. -/
theorem IsExactDivisor.of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) :
    IsExactDivisor p N :=
  ⟨hpN, hp.coprime_iff_not_dvd.mpr fun h ↦ hpsq (pow_two p ▸ Nat.mul_dvd_of_dvd_div hpN h)⟩

/-- `1` is an exact divisor of every `N`. -/
theorem isExactDivisor_one : IsExactDivisor 1 N :=
  ⟨one_dvd N, Nat.coprime_one_left _⟩

/-- A nonzero `N` is an exact divisor of itself: the complementary divisor is `1`. This is the
case of the Fricke operator inside the Atkin–Lehner family. -/
theorem isExactDivisor_self (hN : N ≠ 0) : IsExactDivisor N N :=
  ⟨dvd_rfl, by rw [Nat.div_self (Nat.pos_of_ne_zero hN)]; exact Nat.coprime_one_right _⟩

/-- **Coprime exact divisors multiply.** The exact divisors of `N` are therefore closed under
coprime products, which is how the family generated by the maximal prime powers of `N` is built
up. -/
theorem IsExactDivisor.mul (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N)
    (hQR : Nat.Coprime Q R) : IsExactDivisor (Q * R) N := by
  have hdvd : Q * R ∣ N := hQR.mul_dvd_of_dvd_of_dvd hQ.dvd hR.dvd
  exact ⟨hdvd, Nat.coprime_mul_iff_left.mpr
    ⟨hQ.coprime.coprime_dvd_right (Nat.div_dvd_div_left hdvd (dvd_mul_right Q R)),
      hR.coprime.coprime_dvd_right (Nat.div_dvd_div_left hdvd (dvd_mul_left R Q))⟩⟩

/-! ### The Boolean-algebra structure -/

/-- **The only exact divisor of `0` is `1`.** The complementary divisor of `Q` in `0` is `0`
again, and `Nat.Coprime Q 0` says `Q = 1`. This is what lets the closure properties below carry
no `N ≠ 0` hypothesis. -/
theorem isExactDivisor_zero_iff : IsExactDivisor Q 0 ↔ Q = 1 :=
  ⟨fun h ↦ by simpa using h.coprime, fun h ↦ h ▸ isExactDivisor_one⟩

/-- **Exactness, read on the factorization.** For `N ≠ 0`, a divisor `Q` of `N` is exact exactly
when at every prime its exponent is either `0` or the full exponent of `N`. In this form the
closure properties below become statements about the exponents of `gcd` and of a quotient, namely
about `min` and truncated subtraction. -/
theorem isExactDivisor_iff_factorization (hN : N ≠ 0) :
    IsExactDivisor Q N ↔
      Q ∣ N ∧ ∀ p, Q.factorization p = 0 ∨ Q.factorization p = N.factorization p := by
  rw [isExactDivisor_iff]
  refine and_congr_right fun hQN ↦ ?_
  have hQ0 : Q ≠ 0 := ne_zero_of_dvd_ne_zero hN hQN
  have hle := (Nat.factorization_le_iff_dvd hQ0 hN).mpr hQN
  have hdiv0 : N / Q ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hQN).mpr ⟨hN, hQ0⟩
  -- coprimality is disjointness of the supports, and `v_p(N / Q) = v_p(N) - v_p(Q)`
  simp only [← Nat.disjoint_primeFactors hQ0 hdiv0, Finset.disjoint_left,
    ← Nat.support_factorization, Finsupp.mem_support_iff, Nat.factorization_div hQN,
    Finsupp.tsub_apply]
  refine forall_congr' fun p ↦ ?_
  have := hle p
  omega

/-- **Exact divisors are closed under `gcd`.** At each prime the exponent of `gcd Q R` is the
minimum of two exponents each of which is `0` or the full exponent of `N`. -/
theorem IsExactDivisor.gcd (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    IsExactDivisor (Nat.gcd Q R) N := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := hR.ne_zero
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff] at hQ hR ⊢
    rw [hQ, hR, Nat.gcd_self]
  rw [isExactDivisor_iff_factorization hN] at hQ hR ⊢
  refine ⟨(Nat.gcd_dvd_left Q R).trans hQ.1, fun p ↦ ?_⟩
  rw [Nat.factorization_gcd hQ0 hR0, Finsupp.inf_apply]
  rcases hQ.2 p with h1 | h1 <;> rcases hR.2 p with h2 | h2 <;> omega

/-- **The quotient of an exact divisor by a `gcd` with another one is exact.** At each prime the
exponent of `Q / gcd Q R` is `0` unless `Q` carries the full exponent of `N` there and `R` carries
none, in which case it is again that full exponent. -/
theorem IsExactDivisor.div_gcd (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    IsExactDivisor (Q / Nat.gcd Q R) N := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := hR.ne_zero
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff] at hQ hR ⊢
    rw [hQ, hR, Nat.gcd_self, Nat.div_self Nat.one_pos]
  rw [isExactDivisor_iff_factorization hN] at hQ hR ⊢
  refine ⟨(Nat.div_dvd_of_dvd (Nat.gcd_dvd_left Q R)).trans hQ.1, fun p ↦ ?_⟩
  rw [Nat.factorization_div (Nat.gcd_dvd_left Q R), Finsupp.tsub_apply,
    Nat.factorization_gcd hQ0 hR0, Finsupp.inf_apply]
  rcases hQ.2 p with h1 | h1 <;> rcases hR.2 p with h2 | h2 <;> omega

/-- **`Q / gcd Q R` is coprime to `R`.** A prime dividing the quotient carries the full exponent
of `N` in `Q` and none of it in `R`; this is the step where the exactness of *both* divisors is
used, and it fails for divisors in general (`Q = 4`, `R = 2`). -/
theorem IsExactDivisor.coprime_div_gcd (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    Nat.Coprime (Q / Nat.gcd Q R) R := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := hR.ne_zero
  have hq0 : Q / Nat.gcd Q R ≠ 0 := (hQ.div_gcd hR).ne_zero
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff] at hQ hR
    simp [hQ, hR]
  rw [isExactDivisor_iff_factorization hN] at hQ hR
  simp only [← Nat.disjoint_primeFactors hq0 hR0, Finset.disjoint_left,
    ← Nat.support_factorization, Finsupp.mem_support_iff,
    Nat.factorization_div (Nat.gcd_dvd_left Q R), Finsupp.tsub_apply,
    Nat.factorization_gcd hQ0 hR0, Finsupp.inf_apply]
  intro p
  rcases hQ.2 p with hq | hq <;> rcases hR.2 p with hr | hr <;> omega

/-- **The symmetric difference of two exact divisors is exact.** `Q * R / gcd (Q, R) ^ 2` is the
product of the coprime exact divisors `Q / gcd (Q, R)` and `R / gcd (Q, R)`; under the
identification of exact divisors with subsets of `N.primeFactors` it is the symmetric difference,
which is why it is the composition law of the Atkin–Lehner family. -/
theorem IsExactDivisor.mul_div_gcd_sq (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    IsExactDivisor (Q * R / Nat.gcd Q R ^ 2) N := by
  have hcop : Nat.Coprime (Q / Nat.gcd Q R) (R / Nat.gcd Q R) :=
    Nat.gcd_div_gcd_div_gcd_of_pos_left hQ.pos
  have hRdiv : IsExactDivisor (R / Nat.gcd Q R) N := by
    rw [Nat.gcd_comm]; exact hR.div_gcd hQ
  rw [sq, ← Nat.div_mul_div_comm (Nat.gcd_dvd_left Q R) (Nat.gcd_dvd_right Q R)]
  exact (hQ.div_gcd hR).mul hRdiv hcop

/-- The least common multiple of two exact divisors of a common number is an exact divisor. -/
theorem IsExactDivisor.lcm (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    IsExactDivisor (Nat.lcm Q R) N := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := hR.ne_zero
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff] at hQ hR ⊢
    rw [hQ, hR, Nat.lcm_self]
  rw [isExactDivisor_iff_factorization hN] at hQ hR ⊢
  refine ⟨Nat.lcm_dvd hQ.1 hR.1, fun p ↦ ?_⟩
  rw [Nat.factorization_lcm hQ0 hR0, Finsupp.sup_apply]
  rcases hQ.2 p with h1 | h1 <;> rcases hR.2 p with h2 | h2 <;> omega

/-! ### Exact divisors from sets of primes -/

/-- **The exact divisor of `N` supported on a set of primes:** the product
`∏ p ∈ s, p ^ v_p(N)` of the maximal prime powers of `N` at the primes of `s`. For
`s ⊆ N.primeFactors` this is the exact divisor of `N` whose prime factors are exactly `s`
(`TauCeti.Nat.isExactDivisor_prodPrimePow`, `TauCeti.Nat.primeFactors_prodPrimePow`), and every
exact divisor arises this way (`TauCeti.Nat.IsExactDivisor.prodPrimePow_primeFactors`). -/
def prodPrimePow (N : ℕ) (s : Finset ℕ) : ℕ := ∏ p ∈ s, p ^ N.factorization p

variable {s t : Finset ℕ}

/-- The empty set cuts out the exact divisor `1`. -/
@[simp]
theorem prodPrimePow_empty : prodPrimePow N ∅ = 1 := Finset.prod_empty

/-- **Adjoining a prime multiplies by its maximal power**: `∏ p ∈ insert q s, p ^ v_p(N)` is
`q ^ v_q(N)` times the product over `s`, for `q ∉ s`. -/
@[simp]
theorem prodPrimePow_insert {q : ℕ} (hq : q ∉ s) :
    prodPrimePow N (insert q s) = q ^ N.factorization q * prodPrimePow N s :=
  Finset.prod_insert hq

/-- `∏ p ∈ s, p ^ v_p(N)` is nonzero, since every `p ^ v_p(N)` is (`Nat.ordProj_pos`). -/
private theorem prodPrimePow_ne_zero : prodPrimePow N s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ ↦ (Nat.ordProj_pos N p).ne'

/-- **The exponents of `∏ p ∈ s, p ^ v_p(N)`:** the full exponent of `N` at the members of `s`,
and `0` elsewhere. Members of `s` that are not prime factors of `N` contribute `1`. -/
@[simp]
theorem factorization_prodPrimePow (q : ℕ) :
    (prodPrimePow N s).factorization q = if q ∈ s then N.factorization q else 0 := by
  rw [prodPrimePow,
    Nat.factorization_prod fun p _ ↦ (Nat.ordProj_pos N p).ne',
    Finset.sum_apply', ← Finset.sum_ite_eq' s q (fun p ↦ N.factorization p)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : p.Prime
  · simp [hp.factorization, Finsupp.single_apply]
  · simp [Nat.factorization_eq_zero_of_not_prime N hp]

/-- **A finite set cuts out an exact divisor.** At each prime the exponent of
`∏ p ∈ s, p ^ v_p(N)` is either `0` or the full exponent of `N`. -/
theorem isExactDivisor_prodPrimePow : IsExactDivisor (prodPrimePow N s) N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [prodPrimePow]
  rw [isExactDivisor_iff_factorization hN]
  refine ⟨(Nat.factorization_le_iff_dvd prodPrimePow_ne_zero hN).mp fun p ↦ ?_, fun p ↦ ?_⟩ <;>
    rw [factorization_prodPrimePow] <;> split_ifs <;> simp

/-- **The prime factors of `∏ p ∈ s, p ^ v_p(N)` are the primes of `N` in `s`**, so distinct
subsets of `N.primeFactors` cut out distinct exact divisors. -/
@[simp]
theorem primeFactors_prodPrimePow : (prodPrimePow N s).primeFactors = s ∩ N.primeFactors := by
  ext q
  simp only [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_prodPrimePow,
    Finset.mem_inter]
  split_ifs <;> simp [*]

/-- **The maximal prime powers are exact divisors.** This also holds when the exponent is zero,
in which case the power is `1`. These generate the family: every exact divisor is a product of
them (`TauCeti.Nat.IsExactDivisor.prodPrimePow_primeFactors`). -/
theorem isExactDivisor_primePow {p : ℕ} : IsExactDivisor (p ^ N.factorization p) N := by
  have := isExactDivisor_prodPrimePow (N := N) (s := {p})
  rwa [prodPrimePow, Finset.prod_singleton] at this

/-- **A maximal prime power is prime to the product over the other primes**: `p ^ v_p(N)` is
coprime to `∏ q ∈ s, q ^ v_q(N)` for `p ∉ s`. -/
theorem coprime_primePow_prodPrimePow {p : ℕ} (hps : p ∉ s) :
    Nat.Coprime (p ^ N.factorization p) (prodPrimePow N s) := by
  -- the prime factors of the two products are `{p} ∩ N.primeFactors` and `s ∩ N.primeFactors`
  have h := (Nat.disjoint_primeFactors (prodPrimePow_ne_zero (N := N) (s := {p}))
    (prodPrimePow_ne_zero (N := N) (s := s))).mp <| by
      rw [primeFactors_prodPrimePow, primeFactors_prodPrimePow]
      exact (Finset.disjoint_singleton_left.mpr hps).mono Finset.inter_subset_left
        Finset.inter_subset_left
  rwa [prodPrimePow, Finset.prod_singleton] at h

/-- An exact divisor of `N` only involves primes of `N`. -/
theorem IsExactDivisor.primeFactors_subset (h : IsExactDivisor Q N) :
    Q.primeFactors ⊆ N.primeFactors := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [isExactDivisor_zero_iff.mp h]
  exact Nat.primeFactors_mono h.dvd hN

/-- **Every exact divisor is the product of the maximal prime powers it contains**: the exponents
of an exact divisor are those of `N` at the primes dividing it. This is the prime-power generation
of the Atkin–Lehner family. -/
theorem IsExactDivisor.prodPrimePow_primeFactors (h : IsExactDivisor Q N) :
    prodPrimePow N Q.primeFactors = Q := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [prodPrimePow, isExactDivisor_zero_iff.mp h]
  refine Nat.eq_of_factorization_eq prodPrimePow_ne_zero h.ne_zero fun p ↦ ?_
  simp only [factorization_prodPrimePow, ← Nat.support_factorization, Finsupp.mem_support_iff]
  rcases ((isExactDivisor_iff_factorization hN).mp h).2 p with h0 | h0 <;> split_ifs <;> omega

/-- **Intersecting sets of primes takes the `gcd`** of the products of maximal prime powers. -/
theorem prodPrimePow_inter :
    prodPrimePow N (s ∩ t) = Nat.gcd (prodPrimePow N s) (prodPrimePow N t) :=
  Nat.eq_of_factorization_eq prodPrimePow_ne_zero (Nat.gcd_ne_zero_left prodPrimePow_ne_zero)
    fun p ↦ by
      simp only [Nat.factorization_gcd prodPrimePow_ne_zero prodPrimePow_ne_zero,
        Finsupp.inf_apply, factorization_prodPrimePow, Finset.mem_inter]
      by_cases p ∈ s <;> by_cases p ∈ t <;> simp [*]

/-- **Removing a subset of primes divides out its product of maximal prime powers.** -/
theorem prodPrimePow_sdiff (hts : t ⊆ s) :
    prodPrimePow N (s \ t) = prodPrimePow N s / prodPrimePow N t :=
  (Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero prodPrimePow_ne_zero)
    (Finset.prod_sdiff hts).symm).symm

/-- **Divisibility between exact divisors is inclusion of their sets of prime factors.** -/
theorem IsExactDivisor.dvd_iff_primeFactors_subset (hQ : IsExactDivisor Q N)
    (hR : IsExactDivisor R N) : Q ∣ R ↔ Q.primeFactors ⊆ R.primeFactors := by
  refine ⟨fun h ↦ Nat.primeFactors_mono h hR.ne_zero, fun hs ↦ ?_⟩
  rw [← hQ.prodPrimePow_primeFactors, ← hR.prodPrimePow_primeFactors]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hs

/-! ### The exact-divisor group -/

/-- **The exact divisors of `N`, bundled as a group.** Multiplication is symmetric difference:
the value of `Q * R` is `Q R / gcd(Q, R)²`. Every element is its own inverse, and the identity is
the exact divisor `1`. -/
structure ExactDivisor (N : ℕ) where
  /-- The underlying natural-number divisor. -/
  val : ℕ
  /-- The underlying value is an exact divisor of `N`. -/
  property : IsExactDivisor val N

namespace ExactDivisor

/-- Two exact divisors are equal when their underlying natural numbers are equal. -/
@[ext]
theorem ext {Q R : ExactDivisor N} (h : Q.val = R.val) : Q = R := by
  cases Q
  cases R
  simp_all

instance : CoeOut (ExactDivisor N) ℕ := ⟨ExactDivisor.val⟩

instance : One (ExactDivisor N) := ⟨⟨1, isExactDivisor_one⟩⟩

/-- Multiplication of exact divisors is symmetric difference, with underlying value
`Q * R / gcd(Q, R) ^ 2`. -/
instance : Mul (ExactDivisor N) where
  mul Q R := ⟨Q.val * R.val / Nat.gcd Q.val R.val ^ 2, Q.property.mul_div_gcd_sq R.property⟩

/-- Inversion is the identity because every exact divisor is self-inverse under symmetric
difference. -/
instance : Inv (ExactDivisor N) := ⟨id⟩

/-- The identity exact divisor has underlying value `1`. -/
@[simp]
theorem val_one : (1 : ExactDivisor N).val = 1 := rfl

/-- **Multiplication of exact divisors is symmetric difference:** its underlying value is
`Q R / gcd(Q, R)²`. -/
@[simp]
theorem val_mul (Q R : ExactDivisor N) :
    (Q * R).val = Q.val * R.val / Nat.gcd Q.val R.val ^ 2 := rfl

/-- Every exact divisor is its own inverse. -/
@[simp]
theorem inv_eq_self (Q : ExactDivisor N) : Q⁻¹ = Q := rfl

/-- An exact divisor of `N` is determined by the set of primes dividing it. -/
theorem primeFactors_injective :
    Function.Injective (fun Q : ExactDivisor N ↦ Q.val.primeFactors) := fun Q R h ↦ ext <| by
  rw [← Q.property.prodPrimePow_primeFactors, ← R.property.prodPrimePow_primeFactors]
  exact congrArg (prodPrimePow N) h

/-- Prime factors turn exact-divisor multiplication into symmetric difference. -/
theorem primeFactors_mul (Q R : ExactDivisor N) :
    (Q * R).val.primeFactors = Q.val.primeFactors ∆ R.val.primeFactors := by
  have hQ0 := Q.property.ne_zero
  have hR0 := R.property.ne_zero
  have hg0 : Nat.gcd Q.val R.val ≠ 0 := Nat.gcd_ne_zero_left hQ0
  ext p
  rcases eq_or_ne N 0 with rfl | hN
  · simp [isExactDivisor_zero_iff.mp Q.property, isExactDivisor_zero_iff.mp R.property]
  have hQ := ((isExactDivisor_iff_factorization hN).mp Q.property).2 p
  have hR := ((isExactDivisor_iff_factorization hN).mp R.property).2 p
  -- `v_p(Q R / gcd(Q, R)²) = v_p(Q) + v_p(R) - 2 min(v_p(Q), v_p(R))`
  simp only [val_mul, Finset.mem_symmDiff, ← Nat.support_factorization, Finsupp.mem_support_iff,
    sq, Nat.factorization_div (mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)),
    Nat.factorization_mul hQ0 hR0, Nat.factorization_mul hg0 hg0, Nat.factorization_gcd hQ0 hR0,
    Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.inf_apply]
  omega

/-- Exact divisors form a Boolean commutative group under symmetric-difference multiplication;
the identity is `1` and every element is its own inverse. -/
instance : CommGroup (ExactDivisor N) where
  one := 1
  mul := (· * ·)
  inv := id
  mul_assoc Q R S := primeFactors_injective <| by
    simp only [primeFactors_mul, symmDiff_assoc]
  one_mul Q := primeFactors_injective <| by simp only [primeFactors_mul, val_one]; simp
  mul_one Q := primeFactors_injective <| by simp only [primeFactors_mul, val_one]; simp
  inv_mul_cancel Q := primeFactors_injective <| by simp only [primeFactors_mul, val_one]; simp
  mul_comm Q R := primeFactors_injective <| by simp only [primeFactors_mul, symmDiff_comm]

/-- **The exact divisors of `N` are exactly the subsets of `N.primeFactors`.** An exact divisor
goes to the set of primes dividing it, and a subset `s` comes back as the product
`∏ p ∈ s, p ^ v_p(N)` of maximal prime powers. Since `primeFactors_mul` carries multiplication to
symmetric difference and `inv_eq_self` makes every element its own inverse, this identifies the
group of exact divisors with the Boolean group of subsets of `N.primeFactors` — abstractly
`(ℤ/2) ^ ω(N)`, generated by the maximal prime powers `p ^ v_p(N)`. -/
def primeFactorsEquiv (N : ℕ) : ExactDivisor N ≃ {s : Finset ℕ // s ⊆ N.primeFactors} where
  toFun Q := ⟨Q.val.primeFactors, Q.property.primeFactors_subset⟩
  invFun s := ⟨prodPrimePow N s.1, isExactDivisor_prodPrimePow⟩
  left_inv Q := ext Q.property.prodPrimePow_primeFactors
  right_inv s := Subtype.ext <| primeFactors_prodPrimePow.trans (Finset.inter_eq_left.mpr s.2)

/-- `primeFactorsEquiv` sends an exact divisor to its set of prime factors. -/
@[simp]
theorem coe_primeFactorsEquiv (Q : ExactDivisor N) :
    (primeFactorsEquiv N Q : Finset ℕ) = Q.val.primeFactors := by
  simp [primeFactorsEquiv]

/-- `primeFactorsEquiv` recovers an exact divisor from a set of primes as a product of maximal
prime powers. -/
@[simp]
theorem val_primeFactorsEquiv_symm (s : {s : Finset ℕ // s ⊆ N.primeFactors}) :
    ((primeFactorsEquiv N).symm s).val = prodPrimePow N s := by
  simp [primeFactorsEquiv]

end ExactDivisor

end Nat

end TauCeti
