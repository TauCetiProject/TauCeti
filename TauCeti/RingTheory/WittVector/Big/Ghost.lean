/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.RingTheory.WittVector.Big.TruncationSet

import Mathlib.Algebra.Regular.SMul
import TauCeti.Data.Nat.Factorization.Basic
import TauCeti.NumberTheory.Basic
import TauCeti.RingTheory.Coprime.Lemmas

/-!
# Big Witt ghost polynomials and Dwork's ghost-image criterion

For a commutative ring `R`, a sequence of Witt coordinates `x : ℕ → R` and a positive integer `n`,
the `n`-th big Witt ghost polynomial is `w_n(x) = ∑_{d ∣ n} d * x_d ^ (n / d)`. On a truncation
set `S`, the ghost map sends `(x_n)_{n ∈ S}` to `(w_n(x))_{n ∈ S}`; the big Witt ring `W_S(R)` is
the ring structure on `R ^ S` that makes it a ring homomorphism. This file proves the two facts
about the ghost map that the construction of `W_S(R)` rests on.

The first is Dwork's lemma, which describes the image of the ghost map. Suppose that for every
prime `p ∈ S` the ring `R` carries a ring endomorphism `φ_p` lifting the `p`-th power map modulo
`p`. Then a sequence `b` is a ghost sequence on `S` if and only if
`b_n ≡ φ_p(b_{n/p})` modulo `p ^ v_p(n)` for every `n ∈ S` and every prime `p ∣ n`. The
endomorphisms `φ_p` need not commute with each other.

The second is injectivity: if no prime in `S` is a zero-divisor of `R`, then the Witt coordinates
on `S` are determined by their ghost components on `S`. Over a ring in which every element of `S`
is a unit, every sequence is the ghost sequence of a unique coordinate sequence on `S`.

## Main definitions

* `TauCeti.BigWitt.ghostPolynomial n x`: the ghost component `∑_{d ∣ n} d * x_d ^ (n / d)`, also
  over nonunital semirings.

## Main results

* `TauCeti.BigWitt.ghostPolynomial_sub_map_ghostPolynomial_div_mem`: for every sequence `x`,
  `w_n(x) ≡ φ_p(w_{n/p}(x))` modulo `p ^ v_p(n)`.
* `TauCeti.BigWitt.ghost_image`: Dwork's lemma, the congruence description of the image of the
  ghost map on a truncation set.
* `TauCeti.BigWitt.eqOn_ghostPolynomial_iff`: injectivity of the ghost map on a truncation set
  whose primes are non-zero-divisors.
* `TauCeti.BigWitt.eqOn_of_ghostPolynomial_eq_of_prime_nsmul_injective`: the same injectivity over
  nonunital semirings.
* `TauCeti.BigWitt.exists_ghostPolynomial_eq_of_isUnit`: surjectivity of the ghost map on a
  truncation set whose elements are units.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), Lemma 1.1.
-/

public section

namespace TauCeti.BigWitt

open Finset

variable {R : Type*}

section NonUnitalSemiring

variable [NonUnitalSemiring R] {n : ℕ} {x y : ℕ → R}

/-- The `n`-th big Witt ghost polynomial `w_n(x) = ∑_{d ∣ n} d * x_d ^ (n / d)`, evaluated on the
coordinates `x`. It is `0` for `n = 0`; only its values at positive `n` are meaningful. Every
exponent `n / d` is positive, so the power is written as iterated multiplication starting at
`x_d`: the same polynomial evaluates on nonunital coefficients. Over a unital semiring it is the
usual divisor sum (`ghostPolynomial_eq_sum`). -/
def ghostPolynomial (n : ℕ) (x : ℕ → R) : R :=
  ∑ d ∈ n.divisors, d • (· * x d)^[n / d - 1] (x d)

/-- The ghost polynomial on a nonunital semiring, by iterated multiplication and natural scalar
multiplication. -/
theorem ghostPolynomial_eq_sum_nsmul (n : ℕ) (x : ℕ → R) :
    ghostPolynomial n x = ∑ d ∈ n.divisors, d • (· * x d)^[n / d - 1] (x d) :=
  (rfl)

@[simp]
theorem ghostPolynomial_zero (x : ℕ → R) : ghostPolynomial 0 x = 0 := by
  simp [ghostPolynomial]

@[simp]
theorem ghostPolynomial_one (x : ℕ → R) : ghostPolynomial 1 x = x 1 := by
  simp [ghostPolynomial]

/-- The ghost components of the zero coordinate sequence vanish. -/
@[simp]
theorem ghostPolynomial_zero_right (n : ℕ) : ghostPolynomial n (0 : ℕ → R) = 0 := by
  simp [ghostPolynomial, Function.iterate_fixed]

/-- The ghost polynomial separates its top coordinate, over a nonunital semiring:
`w_n(x) = ∑_{d ∣ n, d < n} d • x_d ^ (n / d) + n • x_n`. -/
theorem ghostPolynomial_eq_sum_properDivisors_nsmul_add (hn : n ≠ 0) (x : ℕ → R) :
    ghostPolynomial n x =
      ∑ d ∈ n.properDivisors, d • (· * x d)^[n / d - 1] (x d) + n • x n := by
  rw [ghostPolynomial, ← Nat.cons_self_properDivisors hn, sum_cons, add_comm,
    Nat.div_self (Nat.pos_of_ne_zero hn)]
  rfl

/-- The ghost polynomial `w_n` only depends on the coordinates indexed by divisors of `n`. -/
theorem ghostPolynomial_congr (h : ∀ d, d ∣ n → x d = y d) :
    ghostPolynomial n x = ghostPolynomial n y :=
  sum_congr rfl fun d hd ↦ by rw [h d (Nat.dvd_of_mem_divisors hd)]

/-- Ghost polynomials commute with ring homomorphisms, including nonunital ones. -/
@[simp]
theorem map_ghostPolynomial {R' F : Type*} [NonUnitalSemiring R'] [FunLike F R R']
    [NonUnitalRingHomClass F R R']
    (f : F) (n : ℕ) (x : ℕ → R) : f (ghostPolynomial n x) = ghostPolynomial n (f ∘ x) := by
  rw [ghostPolynomial, ghostPolynomial, map_sum]
  refine sum_congr rfl fun d _ ↦ ?_
  have h : Function.Semiconj f (· * x d) (· * f (x d)) := fun a ↦ map_mul f a (x d)
  rw [map_nsmul]
  exact congrArg (d • ·) (h.iterate_right (n / d - 1) (x d))

/-- If two coordinate sequences agree on a truncation set `S`, so do their ghost components. -/
theorem eqOn_ghostPolynomial {S : TruncationSet} (h : Set.EqOn x y S) :
    Set.EqOn (ghostPolynomial · x) (ghostPolynomial · y) S :=
  fun _ hn ↦ ghostPolynomial_congr fun _ hd ↦ h (S.mem_of_dvd hn hd)

/-- **Injectivity of the ghost map, nonunital form.** If multiplication by every element of the
truncation set `S` is injective, then coordinate sequences with the same ghost components on `S`
agree on `S`. -/
theorem eqOn_of_ghostPolynomial_eq [IsLeftCancelAdd R] (S : TruncationSet)
    (hS : ∀ n ∈ S, Function.Injective (n • · : R → R))
    (h : ∀ n ∈ S, ghostPolynomial n x = ghostPolynomial n y) : Set.EqOn x y S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  apply hS n hn
  have hs : ∑ d ∈ n.properDivisors, d • (· * x d)^[n / d - 1] (x d) =
      ∑ d ∈ n.properDivisors, d • (· * y d)^[n / d - 1] (y d) :=
    sum_congr rfl fun d hd ↦ by
      rw [ih d (Nat.mem_properDivisors.1 hd).2 (S.mem_of_dvd hn (Nat.mem_properDivisors.1 hd).1)]
  have hg := h n hn
  rw [ghostPolynomial_eq_sum_properDivisors_nsmul_add (S.ne_zero_of_mem hn),
    ghostPolynomial_eq_sum_properDivisors_nsmul_add (S.ne_zero_of_mem hn), hs] at hg
  exact add_left_cancel hg

/-- **Injectivity of the ghost map, nonunital form.** Injectivity of multiplication by the primes
in the truncation set `S` suffices for coordinates to be determined on `S` by their ghost
components on `S`. -/
theorem eqOn_of_ghostPolynomial_eq_of_prime_nsmul_injective [IsLeftCancelAdd R]
    (S : TruncationSet) (hS : ∀ p, p.Prime → p ∈ S → Function.Injective (p • · : R → R))
    (h : ∀ n ∈ S, ghostPolynomial n x = ghostPolynomial n y) : Set.EqOn x y S := by
  refine eqOn_of_ghostPolynomial_eq S (fun n hn ↦ ?_) h
  have hreg : IsSMulRegular R n := by
    rw [Nat.prod_primeFactors_pow_factorization (S.ne_zero_of_mem hn)]
    refine prod_induction _ (IsSMulRegular R) (fun _ _ ha hb ↦ ha.mul hb)
      (IsSMulRegular.one R) fun p hp ↦ IsSMulRegular.pow _ ?_
    exact hS p (Nat.prime_of_mem_primeFactors hp)
      (S.mem_of_dvd hn (Nat.dvd_of_mem_primeFactors hp))
  exact hreg

end NonUnitalSemiring

section Semiring

variable [Semiring R] {n : ℕ}

/-- Over a unital semiring, the ghost polynomial is the divisor sum
`w_n(x) = ∑_{d ∣ n} d * x_d ^ (n / d)`. -/
theorem ghostPolynomial_eq_sum (n : ℕ) (x : ℕ → R) :
    ghostPolynomial n x = ∑ d ∈ n.divisors, (d : R) * x d ^ (n / d) := by
  refine sum_congr rfl fun d hd ↦ ?_
  have hn : 0 < n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd)
  have hquot := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd))
    (Nat.pos_of_mem_divisors hd)
  rw [nsmul_eq_mul, mul_right_iterate_apply_self, Nat.sub_add_cancel hquot]

/-- The coordinate sequence `1, 0, 0, …` has all its ghost components at positive indices equal
to `1`. -/
@[simp]
theorem ghostPolynomial_single_one (hn : n ≠ 0) :
    ghostPolynomial n (Pi.single 1 1 : ℕ → R) = 1 := by
  rw [ghostPolynomial, sum_eq_single 1]
  · simp [Function.iterate_fixed]
  · intro d _ hd
    simp [Pi.single_eq_of_ne hd, Function.iterate_fixed]
  · simp [hn]

/-- For a prime `p`, `w_p(x) = x_1 ^ p + p * x_p`. -/
theorem ghostPolynomial_prime {p : ℕ} (hp : p.Prime) (x : ℕ → R) :
    ghostPolynomial p x = x 1 ^ p + p * x p := by
  simp [ghostPolynomial_eq_sum, Nat.Prime.sum_divisors hp, Nat.div_self hp.pos, add_comm]

/-- The ghost polynomial separates its top coordinate:
`w_n(x) = ∑_{d ∣ n, d < n} d * x_d ^ (n / d) + n * x_n`. -/
theorem ghostPolynomial_eq_sum_properDivisors_add (hn : n ≠ 0) (x : ℕ → R) :
    ghostPolynomial n x = ∑ d ∈ n.properDivisors, (d : R) * x d ^ (n / d) + n * x n := by
  rw [ghostPolynomial_eq_sum, ← Nat.cons_self_properDivisors hn, sum_cons, add_comm,
    Nat.div_self (Nat.pos_of_ne_zero hn), pow_one]

end Semiring

section CommRing

variable [CommRing R]

/-- **The ghost congruence.** If `φ` is a ring endomorphism lifting the `p`-th power map modulo
`p`, then for every coordinate sequence `x`, `w_n(x) ≡ φ(w_{n/p}(x))` modulo `p ^ v_p(n)`. -/
theorem ghostPolynomial_sub_map_ghostPolynomial_div_mem {p : ℕ} (hp : p.Prime) (φ : R →+* R)
    (hφ : ∀ a : R, φ a - a ^ p ∈ Ideal.span {(p : R)}) (n : ℕ) (x : ℕ → R) :
    ghostPolynomial n x - φ (ghostPolynomial (n / p) x) ∈
      Ideal.span {(p : R) ^ multiplicity p n} := by
  have := Fact.mk hp
  rw [Ideal.mem_span_singleton]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  by_cases hpn : p ∣ n
  swap
  · simp [multiplicity_eq_zero_of_not_dvd hpn]
  obtain ⟨m, rfl⟩ := hpn
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  rw [Nat.mul_div_cancel_left m hp.pos, map_ghostPolynomial, ghostPolynomial_eq_sum,
    ghostPolynomial_eq_sum, ← sum_sdiff (Nat.divisors_subset_of_dvd hn (dvd_mul_left m p)),
    add_sub_assoc, ← sum_sub_distrib]
  refine dvd_add (dvd_sum fun d hd ↦ ?_) (dvd_sum fun d hd ↦ ?_)
  · -- divisors of `p * m` not dividing `m` are divisible by `p ^ v_p(p m)`
    obtain ⟨hd, hdm⟩ := mem_sdiff.1 hd
    refine Dvd.dvd.mul_right ?_ _
    have := hp.pow_multiplicity_dvd_of_dvd_of_not_dvd_div (Nat.dvd_of_mem_divisors hd)
      (by rw [Nat.mul_div_cancel_left m hp.pos]; exact fun h ↦ hdm (Nat.mem_divisors.2 ⟨h, hm⟩))
    exact_mod_cast Nat.cast_dvd_cast (α := R) this
  · -- for `d ∣ m`, compare `d * x_d ^ (p e)` with `d * φ(x_d) ^ e`, where `m = d e`
    obtain ⟨e, rfl⟩ := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := left_ne_zero_of_mul hm
    have he0 : e ≠ 0 := right_ne_zero_of_mul hm
    have h₁ : p * (d * e) / d = p * e := by
      rw [mul_left_comm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    have h₂ : multiplicity p (p * (d * e)) = multiplicity p d + (multiplicity p e + 1) := by
      rw [Nat.multiplicity_mul hp.ne_zero hm, Nat.multiplicity_mul hd0 he0,
        Nat.Prime.multiplicity_self]
      ring
    rw [Function.comp_apply, h₁, Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hd0), ← mul_sub,
      pow_mul, h₂, pow_add]
    have key : (p : R) ^ (multiplicity p e + 1) ∣ φ (x d) ^ e - (x d ^ p) ^ e :=
      dvd_sub_pow_of_dvd_sub_of_pow_dvd (Ideal.mem_span_singleton.1 (hφ (x d)))
        (pow_multiplicity_dvd p e)
    rw [← dvd_neg, neg_sub] at key
    exact mul_dvd_mul (natCast_pow_multiplicity_dvd p d) key

open scoped Classical in
/-- Coordinates chosen in divisor order: the `n`-th coordinate solves
`n * x_n = b_n - ∑_{d ∣ n, d < n} d * x_d ^ (n / d)` whenever this equation has a solution. -/
private noncomputable def ghostPreimage (b : ℕ → R) (n : ℕ) : R :=
  if h : ∃ y : R, (n : R) * y =
      b n - ∑ d ∈ n.properDivisors.attach, (d.val : R) * ghostPreimage b d.val ^ (n / d.val) then
    h.choose
  else 0
termination_by n
decreasing_by exact (Nat.mem_properDivisors.1 d.property).2

/-- If, at each `n ∈ S`, the coordinates chosen below `n` leave a remainder divisible by `n`,
then `ghostPreimage b` has ghost components `b` on `S`. -/
private theorem ghostPolynomial_ghostPreimage {S : TruncationSet} {b : ℕ → R}
    (h : ∀ n ∈ S, (∀ d ∈ n.properDivisors, ghostPolynomial d (ghostPreimage b) = b d) →
      (n : R) ∣ b n - ∑ d ∈ n.properDivisors, (d : R) * ghostPreimage b d ^ (n / d)) :
    ∀ n ∈ S, ghostPolynomial n (ghostPreimage b) = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨y, hy⟩ := h n hn fun d hd ↦
    ih d (Nat.mem_properDivisors.1 hd).2 (S.mem_of_dvd hn (Nat.mem_properDivisors.1 hd).1)
  have hex : ∃ y : R, (n : R) * y = b n - ∑ d ∈ n.properDivisors.attach,
      (d.val : R) * ghostPreimage b d.val ^ (n / d.val) :=
    ⟨y, by rw [sum_attach n.properDivisors fun d ↦ (d : R) * ghostPreimage b d ^ (n / d), hy]⟩
  have hn' : (n : R) * ghostPreimage b n = b n - ∑ d ∈ n.properDivisors.attach,
      (d.val : R) * ghostPreimage b d.val ^ (n / d.val) := by
    rw [ghostPreimage, dite_eq_left hex]
    exact hex.choose_spec
  rw [ghostPolynomial_eq_sum_properDivisors_add (S.ne_zero_of_mem hn), hn',
    sum_attach n.properDivisors fun d ↦ (d : R) * ghostPreimage b d ^ (n / d), add_sub_cancel]

/-- **Dwork's lemma.** Let `S` be a truncation set and, for every prime `p ∈ S`, let `φ p` be a
ring endomorphism of `R` lifting the `p`-th power map modulo `p`. A sequence `b` is the sequence
of ghost components on `S` of some Witt coordinates if and only if
`b_n ≡ φ_p(b_{n/p})` modulo `p ^ v_p(n)` for every `n ∈ S` and every prime `p ∣ n`.
The endomorphisms `φ p` need not commute. -/
theorem ghost_image (S : TruncationSet) (φ : ℕ → R →+* R)
    (hφ : ∀ p, p.Prime → p ∈ S → ∀ a : R, φ p a - a ^ p ∈ Ideal.span {(p : R)})
    (b : ℕ → R) :
    (∃ x : ℕ → R, ∀ n ∈ S, ghostPolynomial n x = b n) ↔
      ∀ p, p.Prime → ∀ n ∈ S, p ∣ n →
        b n - φ p (b (n / p)) ∈ Ideal.span {(p : R) ^ multiplicity p n} := by
  constructor
  · rintro ⟨x, hx⟩ p hp n hn hpn
    rw [← hx n hn, ← hx (n / p) (S.mem_of_dvd hn (Nat.div_dvd_of_dvd hpn))]
    exact ghostPolynomial_sub_map_ghostPolynomial_div_mem hp (φ p)
      (hφ p hp (S.mem_of_dvd hn hpn)) n x
  · intro hb
    refine ⟨ghostPreimage b, ghostPolynomial_ghostPreimage fun n hn hlow ↦ ?_⟩
    -- `n` divides the remainder since every prime power `p ^ v_p(n)` dividing `n` does
    have hn0 := S.ne_zero_of_mem hn
    refine (natCast_dvd_iff_forall_pow_multiplicity_dvd hn0).2 fun p hp ↦ ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    -- the remainder is `(b_n - φ_p(b_{n/p})) - (w_n(x) - φ_p(w_{n/p}(x))) + n x_n`
    have hghost := ghostPolynomial_sub_map_ghostPolynomial_div_mem hp' (φ p)
      (hφ p hp' (S.mem_of_dvd hn hpn)) n (ghostPreimage b)
    rw [ghostPolynomial_eq_sum_properDivisors_add hn0, hlow (n / p) (Nat.mem_properDivisors.2
      ⟨Nat.div_dvd_of_dvd hpn, Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hp'.one_lt⟩)] at hghost
    have hdiv : (p : R) ^ multiplicity p n ∣ n * ghostPreimage b n :=
      (natCast_pow_multiplicity_dvd p n).mul_right _
    have hrem : b n - ∑ d ∈ n.properDivisors, (d : R) * ghostPreimage b d ^ (n / d) =
        b n - φ p (b (n / p)) - (∑ d ∈ n.properDivisors, (d : R) * ghostPreimage b d ^ (n / d) +
          n * ghostPreimage b n - φ p (b (n / p))) + n * ghostPreimage b n := by
      ring
    rw [hrem]
    exact dvd_add (dvd_sub (Ideal.mem_span_singleton.1 (hb p hp' n hn hpn))
      (Ideal.mem_span_singleton.1 hghost)) hdiv

/-- Over a ring in which every element of the truncation set `S` is a unit, every sequence is the
sequence of ghost components on `S` of some Witt coordinates. These are unique on `S` by
`eqOn_ghostPolynomial_iff`. -/
theorem exists_ghostPolynomial_eq_of_isUnit {S : TruncationSet}
    (hS : ∀ n ∈ S, IsUnit (n : R)) (b : ℕ → R) :
    ∃ x : ℕ → R, ∀ n ∈ S, ghostPolynomial n x = b n :=
  ⟨ghostPreimage b, ghostPolynomial_ghostPreimage fun n hn _ ↦ (hS n hn).dvd⟩

/-- **Injectivity of the ghost map.** If every prime in the truncation set `S` is a
non-zero-divisor of `R`, then two coordinate sequences agree on `S` if and only if their ghost
components agree on `S`. -/
theorem eqOn_ghostPolynomial_iff {S : TruncationSet}
    (hS : ∀ p ∈ S, p.Prime → IsSMulRegular R (p : R)) {x y : ℕ → R} :
    Set.EqOn (ghostPolynomial · x) (ghostPolynomial · y) S ↔ Set.EqOn x y S := by
  refine ⟨fun h ↦ eqOn_of_ghostPolynomial_eq_of_prime_nsmul_injective S
    (fun p hp hpS a b hab ↦ hS p hpS hp ?_) fun n hn ↦ h hn, eqOn_ghostPolynomial⟩
  simpa only [smul_eq_mul, nsmul_eq_mul] using hab

end CommRing

end TauCeti.BigWitt
