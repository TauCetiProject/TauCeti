/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Coprime.Basic
public import TauCeti.Data.Nat.Factorization.MulDvd
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.Algebra.Group.Coprime

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

The order of the image of `g` in a quotient group `G ⧸ K` divides `n` exactly when `g ^ n` lies
in `K`; for a finite quotient, this is how the iterates of `g` that land in `K` are counted.
In particular `g ^ d ∈ K` for `d` that order. When the image of `g` has finite order, `g ^ d` is
the least positive power of `g` lying in `K`; otherwise `d = 0` and `g ^ d = 1`.

## Main results

* `MonoidHom.isOfFinOrder_iff_exists_pow_apply_eq_one`: the common-exponent characterization
  of finite order for monoid homomorphisms.
* `MonoidHom.pow_natCard_eq_one`, and its additive counterpart: raising a homomorphism from a
  group into a commutative monoid to `Nat.card G` yields the trivial homomorphism.

* `IsOfFinOrder.dvd_orderOf_pow_iff`, and its additive counterpart: divisibility of the order of
  a power as non-divisibility of its exponent by a prime power at each prime of `f`.
* `IsConj.orderOf_eq`, and its additive counterpart: conjugate elements of a monoid have the same
  order.
* `IsCoprime.orderOf_zpow`, and its additive counterpart: an integer exponent coprime to the order
  of `x` preserves it.
* `QuotientGroup.orderOf_mk_dvd_iff_pow_mem`, and its additive counterpart: the order of the
  image of `g` in a quotient `G ⧸ K` divides `n` exactly when `g ^ n ∈ K`.
* `Subgroup.mem_of_pow_mem_of_coprime_index`, and its additive counterpart: a normal subgroup
  contains `g` as soon as it contains a power of `g` with exponent coprime to its index.
* `TauCeti.mem_of_pow_eq_one_of_dvd_natCard_of_not_sq_dvd`: for a prime `p` whose square does not
  divide the order of the group, a normal subgroup of order divisible by `p` contains every
  element whose `p`-th power is `1`.
* `Subgroup.liftClass`, `AddSubgroup.liftClass`: the power `g ^ d` of `g` lying in a normal
  subgroup `K`, where `d` is the order of `g` in `G ⧸ K`; it is the least positive such power when
  `d` is positive, and `1` when the image of `g` has infinite order.
* `TauCeti.natCast_natCard_sub_one_eq_neg_one`: in a finite additive group with one of
  cardinality `q`, the cast of `q - 1` is `-1`, a companion of Mathlib's `Nat.cast_card_eq_zero`.
* `TauCeti.pow_pow_totient_eq_self`: `x ^ q ^ φ(n) = x` whenever `x ^ n = 1` and `q` is prime to
  `n`.
* `TauCeti.pow_pow_div_gcd_eq_one`: `(x ^ d) ^ (n / gcd(n, d)) = 1` whenever `x ^ n = 1`, and its
  additive counterpart.
* `TauCeti.eq_one_of_pow_ordCompl_eq_one`, `TauCeti.eq_of_pow_ordCompl_eq`: an element `x` with
  `x ^ n = 1` is determined by its powers `x ^ ordCompl[ℓ] n` at the primes `ℓ ∣ n`.
* `TauCeti.exists_forall_pow_ne_of_not_isOfFinOrder`, and its additive counterpart: an element `H`
  of infinite order has `H ^ k ≠ a` for all large `k`.
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

/-- Raising a homomorphism from a group into a commutative monoid to `Nat.card G` yields the
trivial homomorphism. -/
@[to_additive
/-- Multiplying a homomorphism from an additive group into a commutative additive monoid by
`Nat.card G` yields the zero homomorphism. -/]
theorem MonoidHom.pow_natCard_eq_one {G M : Type*} [Group G] [CommMonoid M] (f : G →* M) :
    f ^ Nat.card G = 1 := by
  ext g
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one', map_one]

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
  rw [Nat.dvd_gcd_iff, and_iff_right <| Nat.pow_factorization_sub_factorization_add_one_dvd hp <|
    (Nat.dvd_of_mem_primeFactors hp).trans hf]

end IsOfFinOrder

/-- Conjugate elements of a monoid have the same order. -/
@[to_additive /-- Additively conjugate elements of an additive monoid have the same additive
order. -/]
theorem IsConj.orderOf_eq {G : Type*} [Monoid G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b :=
  orderOf_eq_orderOf_iff.2 fun n ↦ by
    rw [← isConj_one_right, ← isConj_one_right (a := b ^ n)]
    exact ⟨fun h' ↦ h'.trans (h.pow n), fun h' ↦ h'.trans (h.pow n).symm⟩

/-- An integer exponent coprime to the order of `x` preserves it. This is Mathlib's
`Nat.Coprime.orderOf_pow` for integer exponents. -/
@[to_additive /-- An integer coefficient coprime to the additive order of `x` preserves it. This
is Mathlib's `Nat.Coprime.addOrderOf_nsmul` for integer coefficients. -/]
theorem IsCoprime.orderOf_zpow {G : Type*} [Group G] {x : G} {u : ℤ}
    (h : IsCoprime u (orderOf x)) : orderOf (x ^ u) = orderOf x := by
  rw [← orderOf_pow_natAbs]
  exact Nat.Coprime.orderOf_pow (Nat.Coprime.symm (Int.isCoprime_iff_gcd_eq_one.mp h))

/-- Raising to an integer power coprime to `N` is injective on the elements whose order divides
`N`. -/
@[to_additive /-- Scaling by an integer coprime to `N` is injective on the elements whose additive
order divides `N`. -/]
theorem IsCoprime.injOn_zpow_of_orderOf_dvd {G : Type*} [Group G] {u : ℤ} {N : ℕ}
    (hu : IsCoprime u N) : Set.InjOn (· ^ u) {x : G | orderOf x ∣ N} := fun x hx y hy h ↦
  hu.eq_of_zpow_eq_zpow h <| by
    rw [zpow_natCast, zpow_natCast, orderOf_dvd_iff_pow_eq_one.mp hx,
      orderOf_dvd_iff_pow_eq_one.mp hy]

/-- The order of the image of `g` in `G ⧸ K` divides `n` exactly when `g ^ n` lies in `K`. -/
@[to_additive
/-- The additive order of the image of `g` in `G ⧸ K` divides `n` exactly when `n • g` lies in
`K`. -/]
theorem QuotientGroup.orderOf_mk_dvd_iff_pow_mem {G : Type*} [Group G] (K : Subgroup G)
    [K.Normal] (g : G) (n : ℕ) : orderOf (g : G ⧸ K) ∣ n ↔ g ^ n ∈ K := by
  rw [orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]

/-- A normal subgroup `K` contains `g` as soon as it contains a power `g ^ n` whose exponent is
coprime to the index of `K`. -/
@[to_additive
/-- A normal additive subgroup `K` contains `g` as soon as it contains a multiple `n • g` whose
coefficient is coprime to the index of `K`. -/]
theorem Subgroup.mem_of_pow_mem_of_coprime_index {G : Type*} [Group G] {K : Subgroup G}
    [K.Normal] {n : ℕ} (hn : K.index.Coprime n) {g : G} (hg : g ^ n ∈ K) : g ∈ K := by
  have horder : orderOf (g : G ⧸ K) = 1 :=
    Nat.eq_one_of_dvd_coprimes hn (K.index_eq_card ▸ _root_.orderOf_dvd_natCard _)
      ((QuotientGroup.orderOf_mk_dvd_iff_pow_mem K g n).mpr hg)
  exact (QuotientGroup.eq_one_iff g).mp (orderOf_eq_one_iff.mp horder)

namespace Subgroup

variable {G : Type*} [Group G] (K : Subgroup G) [K.Normal]

/-- The power `g ^ d` of `g` lying in `K`, where `d` is the order of `g` in `G ⧸ K`. When the
image of `g` in `G ⧸ K` has finite order, this is the least positive power of `g` lying in `K`,
and, when `G` is commutative, for an orbit of class `g` it is the class of each of its primitive
lifts to the covering with deck group `G ⧸ K`. For noncommutative `G`, those lifts can instead have
classes conjugate to it by elements of `G`. When the image has infinite order, `d = 0` and this is
`1`. -/
@[to_additive
/-- The multiple `d • g` of `g` lying in `K`, where `d` is the additive order of `g` in `G ⧸ K`.
When the image of `g` in `G ⧸ K` has finite order, this is the least positive multiple of `g`
lying in `K`, and, when `G` is commutative, for an orbit of class `g` it is the class of each of
its primitive lifts to the covering with deck group `G ⧸ K`. For noncommutative `G`, those lifts can
instead have classes conjugate to it by elements of `G`. When the image has infinite order, `d = 0`
and this is `0`. -/]
noncomputable def liftClass (g : G) : K :=
  ⟨g ^ orderOf (g : G ⧸ K), (QuotientGroup.orderOf_mk_dvd_iff_pow_mem K _ _).1 dvd_rfl⟩

/-- The lift class of `g` is `g ^ d`, where `d` is the order of `g` in `G ⧸ K`. -/
@[to_additive (attr := simp)
/-- The lift class of `g` is `d • g`, where `d` is the order of `g` in `G ⧸ K`. -/]
theorem coe_liftClass (g : G) : (K.liftClass g : G) = g ^ orderOf (g : G ⧸ K) :=
  (rfl)

/-- The `n`-th power of the lift class of `g` is `g ^ (d * n)`, where `d` is the order of `g` in
`G ⧸ K`. -/
@[to_additive
/-- The `n`-th iterate of the lift class of `g` is the `(d * n)`-th iterate of `g`, where `d` is
the order of `g` in `G ⧸ K`. -/]
theorem coe_pow_liftClass (g : G) (n : ℕ) :
    ((K.liftClass g ^ n : K) : G) = g ^ (orderOf (g : G ⧸ K) * n) := by
  simp [pow_mul]

end Subgroup

namespace TauCeti

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

/-- An element of infinite order has `H ^ k ≠ a` for all large `k`: the equation `H ^ k = a` holds
for at most one `k`. -/
@[to_additive]
theorem exists_forall_pow_ne_of_not_isOfFinOrder {G : Type*} [LeftCancelMonoid G] {H : G}
    (hH : ¬IsOfFinOrder H) (a : G) :
    ∃ N : ℕ, ∀ k, N ≤ k → H ^ k ≠ a := by
  exact Filter.eventually_atTop.1 (Nat.cofinite_eq_atTop ▸
    (injective_pow_iff_not_isOfFinOrder.2 hH).tendsto_cofinite.eventually
      (Filter.eventually_cofinite_ne a))

/-- For a prime `p`, if `p ^ 2` does not divide the order of a group, then a normal subgroup
whose order is divisible by `p` contains every element whose `p`-th power is `1`. -/
theorem mem_of_pow_eq_one_of_dvd_natCard_of_not_sq_dvd {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) {N : Subgroup G} [N.Normal] {a : G} (ha : a ^ p = 1) (hN : p ∣ Nat.card N)
    (hsq : ¬ p ^ 2 ∣ Nat.card G) : a ∈ N := by
  refine Subgroup.mem_of_pow_mem_of_coprime_index
    (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr fun hi ↦ hsq ?_)) (ha ▸ N.one_mem)
  rw [← N.card_mul_index, pow_two]
  exact Nat.mul_dvd_mul hN hi

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
