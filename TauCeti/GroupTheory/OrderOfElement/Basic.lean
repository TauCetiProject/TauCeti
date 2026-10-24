/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Totient
public import TauCeti.Data.Nat.Factorization.MulDvd
import Mathlib.FieldTheory.Finite.Basic

/-!
# Orders of elements and cardinalities

Let `g` have finite order `n` and let `f` divide `n`. The order of `g ^ k` is `n / gcd n k`, so
`f` divides it exactly when `f * gcd n k` divides `n`. That condition is decided one prime of `f`
at a time: it fails at `p` exactly when `k` is divisible by `p ^ (v_p n - v_p f + 1)`, the room
`n` leaves at `p` after `f`, plus one.

In a finite additive group with one, the cardinality casts to `0`, as Mathlib's
`Nat.cast_card_eq_zero` records, so the cardinality minus one casts to `-1`.

An `n`-th root of unity `x` is determined by its powers `x ^ (n / ℓ ^ v_ℓ(n))` at the primes
`ℓ ∣ n`, the projections of `x` to its `ℓ`-primary parts.

By Euler's theorem, raising an `n`-th root of unity to the power `q ^ φ(n)`, for `q` prime to `n`,
does nothing. In a group of order `N`, every `d`-th power is killed by the
`(N / gcd(N, d))`-th power map, since `d * (N / gcd(N, d))` is a multiple of `N`.

An element squaring to `1` only sees the parity of its exponent, so identities between products
of powers of such elements reduce to congruences modulo `2` between the exponents.

If conjugation by `s` raises an element `t` of finite order to a power `q`, then `q` is
prime to the order of `t`, since conjugation preserves orders, and so `s` normalizes the cyclic
subgroup `⟨t⟩`. This is the finite shadow of a relation `s t s⁻¹ = t ^ q`, such as the one between
Frobenius and tame inertia.

A homomorphism into a commutative monoid has finite order exactly when its values have a common
positive exponent equal to one; the source only needs a multiplication and identity.

## Main results

* `MonoidHom.isOfFinOrder_iff_exists_pow_apply_eq_one`: the common-exponent characterization
  of finite order for monoid homomorphisms.

* `IsOfFinOrder.dvd_orderOf_pow_iff`, and its additive counterpart: divisibility of the order of
  a power as non-divisibility of its exponent by a prime power at each prime of `f`.
* `TauCeti.orderOf_eq_orderOf_of_forall_lt_pow_eq_one_iff`: two elements killed by a common
  exponent `n > 0` have the same order when the same powers below `n` are trivial, and its
  additive counterpart.
* `TauCeti.natCast_natCard_sub_one_eq_neg_one`: in a finite additive group with one of
  cardinality `q`, the cast of `q - 1` is `-1`, a companion of Mathlib's `Nat.cast_card_eq_zero`.
* `TauCeti.pow_pow_totient_eq_self`: `x ^ q ^ φ(n) = x` whenever `x ^ n = 1` and `q` is prime to
  `n`.
* `TauCeti.pow_pow_div_gcd_eq_one`: `(x ^ d) ^ (n / gcd(n, d)) = 1` whenever `x ^ n = 1`, and its
  additive counterpart.
* `TauCeti.eq_one_of_pow_ordCompl_eq_one`, `TauCeti.eq_of_pow_ordCompl_eq`: an element `x` with
  `x ^ n = 1` is determined by its powers `x ^ ordCompl[ℓ] n` at the primes `ℓ ∣ n`.
* `TauCeti.mul_pow_eq_of_sq_eq_one`: in a commutative monoid, exponents of elements squaring to
  `1` only matter modulo `2`.
* `TauCeti.coprime_orderOf_of_mul_mul_inv_eq_pow`,
  `TauCeti.mem_normalizer_zpowers_of_mul_mul_inv_eq_pow`: if `s * t * s⁻¹ = t ^ q` with `t` of
  finite order, then `q` is prime to the order of `t` and `s` normalizes `⟨t⟩`.
-/

public section

/-- A homomorphism into a commutative monoid has finite order exactly when all its values have
a common positive exponent equal to one. -/
theorem MonoidHom.isOfFinOrder_iff_exists_pow_apply_eq_one
    {A B : Type*} [MulOneClass A] [CommMonoid B] (f : A →* B) :
    IsOfFinOrder f ↔ ∃ n, 0 < n ∧ ∀ x, f x ^ n = 1 := by
  simp only [isOfFinOrder_iff_pow_eq_one, DFunLike.ext_iff, MonoidHom.pow_apply,
    MonoidHom.one_apply]

namespace IsOfFinOrder

variable {G : Type*} [Monoid G]

/-- **When a number divides the order of a power.** Let `g` have finite order and let `f` divide
that order. Then `f` divides the order of `g ^ k` exactly when, for every prime `p` of `f`, the
exponent `k` is not divisible by `p ^ (v_p (orderOf g) - v_p f + 1)`.

The exponent is the room `orderOf g` leaves at `p` after `f` has taken `v_p f`, plus one: the
order of `g ^ k` is `orderOf g / gcd (orderOf g) k`, so `k` may absorb at most
`v_p (orderOf g) - v_p f` powers of `p`; the first forbidden exponent is that room plus one. -/
@[to_additive
/-- **When a number divides the additive order of a multiple.** Let `g` have finite additive order
and let `f` divide that order. Then `f` divides the additive order of `k • g` exactly when, for
every prime `p` of `f`, the exponent `k` is not divisible by
`p ^ (v_p (addOrderOf g) - v_p f + 1)`. -/]
theorem dvd_orderOf_pow_iff {g : G} (hg : IsOfFinOrder g) {f : ℕ}
    (hf : f ∣ orderOf g) (k : ℕ) :
    f ∣ orderOf (g ^ k) ↔
      ∀ p ∈ f.primeFactors, ¬p ^ ((orderOf g).factorization p - f.factorization p + 1) ∣ k := by
  have h0 : orderOf g ≠ 0 := hg.orderOf_pos.ne'
  rw [hg.orderOf_pow, Nat.dvd_div_iff_mul_dvd (Nat.gcd_dvd_left _ k), mul_comm,
    Nat.mul_dvd_iff_forall_not_pow_dvd h0 hf (Nat.gcd_dvd_left _ k)]
  refine forall₂_congr fun p hp => not_congr ?_
  rw [Nat.dvd_gcd_iff, and_iff_right (Nat.pow_factorization_sub_factorization_add_one_dvd hf hp)]

end IsOfFinOrder

namespace TauCeti

/-- **Comparing orders below a common exponent.** If `x ^ n = 1` and `y ^ n = 1` with `n > 0`,
and `x ^ k = 1 ↔ y ^ k = 1` for every `k < n`, then `x` and `y` have the same order: every power
reduces modulo `n`. -/
@[to_additive
/-- **Comparing additive orders below a common exponent.** If `n • x = 0` and `n • y = 0` with
`n > 0`, and `k • x = 0 ↔ k • y = 0` for every `k < n`, then `x` and `y` have the same additive
order. -/]
theorem orderOf_eq_orderOf_of_forall_lt_pow_eq_one_iff {M N : Type*} [Monoid M] [Monoid N]
    {x : M} {y : N} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : ∀ k < n, x ^ k = 1 ↔ y ^ k = 1) : orderOf x = orderOf y :=
  orderOf_eq_orderOf_iff.2 fun k ↦ by
    rw [pow_eq_pow_mod k hx, pow_eq_pow_mod k hy]
    exact h _ (Nat.mod_lt k hn)

/-- In a finite additive group with one of cardinality `q`, the cast of `q - 1` is `-1`. -/
theorem natCast_natCard_sub_one_eq_neg_one (R : Type*) [AddGroupWithOne R] [Finite R] :
    ((Nat.card R - 1 : ℕ) : R) = -1 := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  have := Fintype.ofFinite R
  rw [Nat.cast_sub Finite.one_lt_card.le, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero,
    Nat.cast_one, zero_sub]

/-- **Euler's theorem on an `n`-th root of unity**: if `x ^ n = 1` in a monoid and `q` is prime to
`n`, then `x ^ q ^ φ(n) = x`, since `q ^ φ(n) ≡ 1 [MOD n]`. -/
theorem pow_pow_totient_eq_self {M : Type*} [Monoid M] {q n : ℕ} (hq : q.Coprime n) {x : M}
    (hx : x ^ n = 1) : x ^ q ^ n.totient = x := by
  rw [pow_eq_pow_mod _ hx, Nat.ModEq.pow_totient hq, ← pow_eq_pow_mod _ hx, pow_one]

/-- If `x ^ n = 1` in a monoid, then every power `x ^ d` is killed by the `(n / gcd(n, d))`-th
power map: `(x ^ d) ^ (n / gcd(n, d)) = 1`. In a group of order `N` this applies with `n = N`
(Mathlib's `pow_card_eq_one'`). -/
@[to_additive nsmul_nsmul_div_gcd_eq_zero
/-- If `n • x = 0` in an additive monoid, then every multiple `d • x` is killed by multiplication
by `n / gcd(n, d)`: `(n / gcd(n, d)) • d • x = 0`. -/]
theorem pow_pow_div_gcd_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1) (d : ℕ) :
    (x ^ d) ^ (n / n.gcd d) = 1 := by
  -- `d * (n / g) = n * (d / g)` with `g = gcd(n, d)` dividing both `n` and `d`.
  rw [← pow_mul, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm d,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), pow_mul, hx, one_pow]

/-- If `x ^ n = 1` with `n ≠ 0`, and `x ^ ordCompl[ℓ] n = 1` for every prime `ℓ ∣ n`, then
`x = 1`. -/
theorem eq_one_of_pow_ordCompl_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hn : n ≠ 0)
    (hx : x ^ n = 1) (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → x ^ ordCompl[ℓ] n = 1) : x = 1 := by
  by_contra hne
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.2 hne)
  have hℓn : ℓ ∣ n := hdvd.trans (orderOf_dvd_of_pow_eq_one hx)
  exact hℓ.one_lt.ne' <| Nat.Coprime.eq_one_of_dvd (Nat.coprime_ordCompl hℓ hn)
    (hdvd.trans (orderOf_dvd_of_pow_eq_one (h ℓ hℓ hℓn)))

/-- Two `n`-th roots of unity in a commutative monoid, `n ≠ 0`, are equal as soon as their powers
`x ^ ordCompl[ℓ] n` agree at every prime `ℓ ∣ n`. -/
theorem eq_of_pow_ordCompl_eq {M : Type*} [CommMonoid M] {x y : M} {n : ℕ} (hn : n ≠ 0)
    (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → x ^ ordCompl[ℓ] n = y ^ ordCompl[ℓ] n) : x = y := by
  -- Both are units, so they can be compared in the commutative group `Mˣ`.
  lift x to Mˣ using IsUnit.of_pow_eq_one hx hn
  lift y to Mˣ using IsUnit.of_pow_eq_one hy hn
  simp only [← Units.val_pow_eq_pow_val, Units.val_eq_one, Units.val_inj] at hx hy h ⊢
  exact div_eq_one.1 <| eq_one_of_pow_ordCompl_eq_one hn (by rw [div_pow, hx, hy, div_one])
    fun ℓ hℓ hℓn ↦ by rw [div_pow, h ℓ hℓ hℓn, div_self']

/-- **Only parities matter for `2`-torsion exponents.** In a commutative monoid whose elements
`u, v, w, z` square to `1`, an identity between products of their powers holds as soon as the
exponents agree modulo `2`: here `S * (u * v) ^ A * (w * z) ^ B * w ^ C * u ^ D` regroups as
`S * z * (v * w) ^ E * u ^ F`. This is the sign bookkeeping behind induction steps on products
of quaternion symbols with binomial exponents. -/
theorem mul_pow_eq_of_sq_eq_one {G : Type*} [CommMonoid G] {S u v w z : G}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hw : w ^ 2 = 1) (hz : z ^ 2 = 1) {A B C D E F : ℕ}
    (hF : F ≡ A + D [MOD 2]) (hE : E ≡ A [MOD 2]) (hBC : E ≡ B + C [MOD 2]) (hB : 1 ≡ B [MOD 2]) :
    S * (u * v) ^ A * (w * z) ^ B * w ^ C * u ^ D = S * z * (v * w) ^ E * u ^ F := by
  conv_rhs => rw [pow_eq_pow_of_modEq hF hu, mul_pow, pow_eq_pow_of_modEq hE hv,
    pow_eq_pow_of_modEq hBC hw, ← pow_one z, pow_eq_pow_of_modEq hB hz]
  simp only [mul_pow, pow_add]
  ac_rfl

section Conj

variable {G : Type*} [Group G] {s t : G} {q : ℕ}

/-- **A conjugate power is a coprime power.** If conjugation by `s` sends an element `t` of finite
order to `t ^ q`, then `q` is prime to the order of `t`: conjugation preserves orders,
and the order of `t ^ q` is `orderOf t / gcd (orderOf t) q`. -/
theorem coprime_orderOf_of_mul_mul_inv_eq_pow (ht : IsOfFinOrder t)
    (h : s * t * s⁻¹ = t ^ q) : q.Coprime (orderOf t) := by
  have hord : orderOf (t ^ q) = orderOf t := by
    rw [← h, ← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective t
  rw [ht.orderOf_pow, Nat.div_eq_self] at hord
  exact Nat.coprime_comm.1 (hord.resolve_left ht.orderOf_pos.ne')

/-- **A conjugate power normalizes the cyclic subgroup.** If conjugation by `s` sends an element
`t` of finite order to `t ^ q`, then `s` normalizes the cyclic subgroup generated by
`t`. Since `q` is prime to the order of `t`, conjugation by `s⁻¹` is a power map on it as well. -/
theorem mem_normalizer_zpowers_of_mul_mul_inv_eq_pow (ht : IsOfFinOrder t)
    (h : s * t * s⁻¹ = t ^ q) : s ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (coprime_orderOf_of_mul_mul_inv_eq_pow ht h)
  -- Conjugation by `s⁻¹` sends `t = (t ^ q) ^ k = (s * t * s⁻¹) ^ k` to `t ^ k`.
  have hinv : s⁻¹ * t * s = t ^ k := by
    conv_lhs => rw [← hk, ← h, conj_pow]
    group
  refine Subgroup.mem_normalizer_iff.2 fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact Subgroup.mem_zpowers_iff.2 ⟨q * n, by rw [← conj_zpow, h, zpow_mul, zpow_natCast]⟩
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine Subgroup.mem_zpowers_iff.2 ⟨k * n, ?_⟩
    have hx' : x = s⁻¹ * t ^ n * s⁻¹⁻¹ := by rw [hn]; group
    rw [hx', ← conj_zpow, inv_inv, hinv, zpow_mul, zpow_natCast]

end Conj

end TauCeti
