/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import TauCeti.GroupTheory.OrderOfElement.NegOne
import TauCeti.NumberTheory.Multiplicity

/-!
# Orders of residues

Let `ℓ` and `a ≠ 1` be natural numbers. For every `j`, the power `ℓ ^ j` divides the
multiplicative order of `a` modulo `ℓ ^ r` for all large `r`
(`ZMod.eventually_pow_dvd_orderOf_natCast`). For a prime `ℓ` not dividing `a`, this order is
positive, so its `ℓ`-adic valuation is unbounded as `r` grows; for a prime `ℓ` dividing `a`, the
order is instead eventually `0`.

When `a` and `ℓ` are not coprime, the residue of `a` is not a unit and its order is `0` from
`r = 1` on. Otherwise it suffices to treat the prime factors of `ℓ`, so let `ℓ` be a prime not
dividing `a`. Then `a > 1`, and the order divides `φ(ℓ ^ r) = ℓ ^ (r - 1) (ℓ - 1)`, so if `ℓ ^ j`
did not divide it, it would divide the number `ℓ ^ (j - 1) (ℓ - 1)`, which does not depend on `r`;
then `ℓ ^ r` would divide the positive number `a ^ (ℓ ^ (j - 1) (ℓ - 1)) - 1` for every `r`,
which is absurd.

For the residue `a = 𝔑𝔭` of a prime `𝔭 ∤ ℓ` of a number field, this order is the residue degree
of `𝔭` in the cyclotomic extension of level `ℓ ^ r`, so the statement says that these residue
degrees become divisible by any given power of `ℓ` along the cyclotomic tower.

Unless `n` is `1` or `2`, the residue `-1` has order `2`, so `2` divides the exponent of `(ℤ/n)ˣ`.

For `n ≠ 0`, a residue whose order is `φ(n)` is a primitive root modulo `n`. A primitive root
modulo `n` is one modulo every divisor of `n`, and for an odd prime `p` a primitive root modulo
`p ²` is one modulo every power of `p`.

The order of `q` modulo `n` decides which of the numbers `q ^ k - 1` are divisible by `n`: those
with `k` a multiple of the order. In particular `p > 1` has order `f` modulo `p ^ f - 1`. Modulo
a prime `p`, an element of even order `2 * m` has `m`-th power `-1`, so if `a / b` has order
`2 * m` then `p` divides `a ^ k + b ^ k` exactly for the odd multiples `k` of `m`; for `b = 1` this
decides which `q ^ k + 1` are divisible by `p`.

## Main results

* `ZMod.orderOf_one_add_natCast_mul_two_pow`: the order of `1 + m` modulo `m * 2 ^ s`
  is `2 ^ s` if `m` is a nonzero multiple of `4`.
* `ZMod.orderOf_natCast_pos_iff`, `ZMod.orderOf_natCast_pos_of_not_dvd`: `(a : ZMod n)` has
  positive multiplicative order iff `a.Coprime n`, and in particular whenever `a` is a prime not
  dividing `n`.
* `ZMod.orderOf_natCast_dvd_orderOf_natCast`: for `m ∣ n`, the order of `a` modulo `m` divides its
  order modulo `n`.
* `ZMod.dvd_pow_sub_one_iff_orderOf_natCast_dvd`: for `q > 0`, `n ∣ q ^ k - 1` iff the order of
  `q` modulo `n` divides `k`.
* `ZMod.eventually_pow_dvd_orderOf_natCast`: for `a ≠ 1` and every `j`, `ℓ ^ j` divides the
  order of `a` modulo `ℓ ^ r` for all large `r`.
* `ZMod.two_pow_le_mul_succ_of_pow_eq_one`: if `a > 1` and `a ^ n ≡ 1` modulo `2 ^ (s + 1)`
  for `n > 0`, then `2 ^ s ≤ n * (a + 1)`.
* `ZMod.two_dvd_exponent_units`: for `n ≠ 1, 2`, `2` divides the exponent of `(ℤ/n)ˣ`.
* `ZMod.isUnit_of_orderOf_eq_totient`, `ZMod.zpowers_eq_top_of_orderOf_eq_totient`: a residue of
  order `φ(n)` is a unit, and generates `(ℤ/n)ˣ`.
* `ZMod.exists_orderOf_natCast_eq_totient`: if `(ℤ/n)ˣ` is cyclic, some natural number has order
  `φ(n)` modulo `n`, that is, is a primitive root modulo `n` when `n ≠ 0`; for `n = 0` the
  witness is the junk value `0`.
* `ZMod.orderOf_natCast_eq_totient_of_dvd`: a primitive root modulo `n` is a primitive root
  modulo every divisor of `n`.
* `ZMod.orderOf_natCast_prime_pow_eq_totient`: for odd `p`, a primitive root modulo `p ²` is a
  primitive root modulo every `p ^ e`.
* `TauCeti.ZMod.orderOf_natCast_pow_sub_one`: for `p > 1`, the order of `p` modulo `p ^ f - 1` is
  `f`.
* `Nat.Prime.dvd_pow_add_pow_iff_of_orderOf_eq_two_mul`: if `a / b` has order `2 * m ≠ 0` modulo
  a prime `p`, then `p ∣ a ^ k + b ^ k` iff `m ∣ k` and `¬ 2 * m ∣ k`.
* `Nat.Prime.dvd_pow_add_one_iff_of_orderOf_natCast_eq_two_mul`: if `q` has order `2 * m ≠ 0`
  modulo a prime `p`, then `p ∣ q ^ k + 1` iff `m ∣ k` and `¬ 2 * m ∣ k`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 4, §1,
  Theorem 2.
-/

public section

namespace ZMod

/-- If `m` is a nonzero multiple of `4`, then the order of `1 + m` modulo `m * 2 ^ s` is `2 ^ s`.
The odd factor of the modulus does not contribute to the order. -/
theorem orderOf_one_add_natCast_mul_two_pow {m : ℕ} (hm : m ≠ 0) (h₄ : 4 ∣ m) (s : ℕ) :
    orderOf (1 + (m : ZMod (m * 2 ^ s))) = 2 ^ s := by
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have hcop : (2 ^ 2).Coprime u := hu.coprime_two_left.pow_left 2
  have hv : 2 ≤ v := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mp
    (hcop.dvd_of_dvd_mul_right (by simpa using h₄ : 2 ^ 2 ∣ 2 ^ v * u))
  have hmod : 2 ^ v * u * 2 ^ s = 2 ^ (s + v) * u := by rw [pow_add]; ac_rfl
  have hodd : ((2 ^ v * u : ℕ) : ZMod u) = 0 :=
    (natCast_eq_zero_iff _ _).mpr (dvd_mul_left _ _)
  rw [hmod]
  let e := chineseRemainder (hu.coprime_two_left.pow_left (s + v))
  have he : orderOf (e (1 + (2 ^ v * u : ℕ))) = orderOf (1 + (2 ^ v * u : ℕ) :
      ZMod (2 ^ (s + v) * u)) := orderOf_injective e.toMonoidHom e.injective _
  rw [← he]
  simp only [map_add, map_one, map_natCast, Prod.orderOf, Prod.fst_add, Prod.snd_add,
    Prod.fst_one, Prod.snd_one, Prod.fst_natCast, Prod.snd_natCast, hodd, add_zero, orderOf_one,
    Nat.lcm_one_right]
  have hu' : ¬ (2 : ℤ) ∣ (u : ℤ) := by
    rw [← even_iff_two_dvd, Int.not_even_iff_odd]
    exact_mod_cast hu
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_natCast] using
    orderOf_one_add_mul_prime_pow Nat.prime_two v (by omega) (u : ℤ) hu' s

/-- For any natural numbers `a` and `n` (including `n = 0`), the residue of `a` modulo `n` has
positive multiplicative order if and only if `a` and `n` are coprime. -/
theorem orderOf_natCast_pos_iff {n a : ℕ} :
    0 < orderOf (a : ZMod n) ↔ a.Coprime n := by
  have : Finite (ZMod n)ˣ := by
    obtain rfl | _ := eq_zero_or_neZero n
    · exact inferInstanceAs (Finite ℤˣ)
    · infer_instance
  rw [orderOf_pos_iff, isOfFinOrder_iff_isUnit, isUnit_iff_coprime]

/-- If a prime `p` does not divide `m`, then the residue of `p` modulo `m` has positive
multiplicative order. -/
theorem orderOf_natCast_pos_of_not_dvd {m p : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    0 < orderOf (p : ZMod m) :=
  orderOf_natCast_pos_iff.mpr (hp.coprime_iff_not_dvd.mpr hm)

/-- For `m ∣ n`, the order of a natural number `a` modulo `m` divides its order modulo `n`, since
reduction modulo `m` is a ring homomorphism `ZMod n →+* ZMod m`. -/
theorem orderOf_natCast_dvd_orderOf_natCast {m n : ℕ} (h : m ∣ n) (a : ℕ) :
    orderOf (a : ZMod m) ∣ orderOf (a : ZMod n) := by
  simpa using orderOf_map_dvd (ZMod.castHom h (ZMod m)).toMonoidHom (a : ZMod n)

/-- For a positive natural number `q` and any modulus `n`, `n` divides `q ^ k - 1` if and only if
the order of `q` modulo `n` divides `k`. -/
theorem dvd_pow_sub_one_iff_orderOf_natCast_dvd {n q : ℕ} (hq : 0 < q) (k : ℕ) :
    n ∣ q ^ k - 1 ↔ orderOf (q : ZMod n) ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one, ← natCast_eq_zero_iff]
  simp [Nat.cast_sub (Nat.one_le_pow _ _ hq), sub_eq_zero]

/-- If a positive power of an integer `a > 1` is one modulo `2^(s+1)`, then the exponent
times `a + 1` is at least `2^s`. -/
theorem two_pow_le_mul_succ_of_pow_eq_one {a n s : ℕ} (ha : 1 < a) (hn : 0 < n)
    (h : (a : ZMod (2 ^ (s + 1))) ^ n = 1) : 2 ^ s ≤ n * (a + 1) := by
  have hd : 2 ^ (s + 1) ∣ a ^ n - 1 :=
    (dvd_pow_sub_one_iff_orderOf_natCast_dvd (by omega) n).2 (orderOf_dvd_of_pow_eq_one h)
  have hpow : 1 < a ^ n := Nat.one_lt_pow hn.ne' ha
  have hao : Odd a := by
    refine Nat.not_even_iff_odd.mp fun he => ?_
    have h₁ := (dvd_pow_self 2 (by omega : s + 1 ≠ 0)).trans hd
    have h₂ := dvd_pow (even_iff_two_dvd.1 he) hn.ne'
    omega
  have hle := (Nat.pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1)
    (Nat.sub_ne_zero_of_lt hpow)).1 hd
  have hminus : 2 ^ multiplicity 2 (a - 1) ≤ a - 1 :=
    Nat.le_of_dvd (by omega) (pow_multiplicity_dvd _ _)
  by_cases hne : Even n
  swap
  · have hv := Nat.multiplicity_pow_two_sub_pow_of_odd hao odd_one (Nat.not_even_iff_odd.mp hne)
    rw [one_pow] at hv
    rw [hv] at hle
    calc
      2 ^ s ≤ 2 ^ multiplicity 2 (a - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ a + 1 := hminus.trans (by omega)
      _ ≤ n * (a + 1) := Nat.le_mul_of_pos_left _ hn
  have hv := Nat.multiplicity_pow_two_sub_one ha hao.not_two_dvd_nat hn.ne' hne
  have hlow : multiplicity 2 (a + 1) ≤ 1 ∨ multiplicity 2 (a - 1) ≤ 1 := by
    have hcases : ¬4 ∣ a + 1 ∨ ¬4 ∣ a - 1 := by omega
    have hval (b : ℕ) (hb : b ≠ 0) (h4 : ¬4 ∣ b) : multiplicity 2 b ≤ 1 := by
      have hnot : ¬2 ≤ multiplicity 2 b := fun hh =>
        h4 ((Nat.pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hb).2 hh)
      omega
    exact hcases.imp (hval _ (by omega)) (hval _ (by omega))
  have hn' : 2 ^ multiplicity 2 n ≤ n := Nat.le_of_dvd hn (pow_multiplicity_dvd _ _)
  rcases hlow with hl | hl
  · calc
      2 ^ s ≤ 2 ^ (multiplicity 2 n + multiplicity 2 (a - 1)) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n * (a + 1) := by rw [pow_add]; gcongr; omega
  · have hplus : 2 ^ multiplicity 2 (a + 1) ≤ a + 1 :=
      Nat.le_of_dvd (by omega) (pow_multiplicity_dvd _ _)
    calc
      2 ^ s ≤ 2 ^ (multiplicity 2 n + multiplicity 2 (a + 1)) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n * (a + 1) := by rw [pow_add]; gcongr

/-- The case of `eventually_pow_dvd_orderOf_natCast` where `ℓ` is a prime not dividing `a`. -/
private theorem eventually_pow_dvd_orderOf_natCast_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ}
    (ha : a ≠ 1) (hdvd : ¬ ℓ ∣ a) (j : ℕ) :
    ∀ᶠ r in Filter.atTop, ℓ ^ j ∣ orderOf (a : ZMod (ℓ ^ r)) := by
  -- The order modulo `ℓ ^ r` divides the order modulo `ℓ ^ r'` for `r ≤ r'`, so one level
  -- suffices.
  suffices h : ∃ R, ℓ ^ j ∣ orderOf (a : ZMod (ℓ ^ R)) by
    obtain ⟨R, hR⟩ := h
    exact Filter.eventually_atTop.2 ⟨R, fun r hr =>
      hR.trans (orderOf_natCast_dvd_orderOf_natCast (pow_dvd_pow ℓ hr) a)⟩
  -- Here `a > 1` (as `ℓ ∣ 0`), and the order modulo `ℓ ^ r` divides `φ (ℓ ^ r)`; the level
  -- `r = a ^ B`, with `B = ℓ ^ (j - 1) * (ℓ - 1)`, is too large for `a ^ B ≡ 1 (mod ℓ ^ r)`.
  have ha : 1 < a := Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨fun h ↦ hdvd (h ▸ dvd_zero ℓ), ha⟩
  set B := ℓ ^ (j - 1) * (ℓ - 1)
  have hB : 0 < B := Nat.mul_pos (pow_pos hℓ.pos _) (Nat.sub_pos_of_lt hℓ.one_lt)
  have haB : 0 < a ^ B - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hB.ne' ha)
  set r := a ^ B
  have hr : 0 < r := pow_pos (by omega) B
  refine ⟨r, ?_⟩
  by_contra hnot
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r hℓ.ne_zero⟩
  have hcop : a.Coprime (ℓ ^ r) :=
    Nat.Coprime.pow_right r (Nat.Coprime.symm ((hℓ.coprime_iff_not_dvd).2 hdvd))
  have hoφ : orderOf (a : ZMod (ℓ ^ r)) ∣ ℓ ^ (r - 1) * (ℓ - 1) := by
    rw [← ZMod.coe_unitOfCoprime a hcop, orderOf_units, ← Nat.totient_prime_pow hℓ hr,
      ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  -- Write the order as `ℓ ^ e * t` with `t ∣ ℓ - 1`; then `e < j`, so the order divides `B`.
  obtain ⟨_, t, hd, ht, ho⟩ := dvd_mul.1 hoφ
  obtain ⟨e, -, rfl⟩ := (Nat.dvd_prime_pow hℓ).1 hd
  have he : e < j := by
    by_contra! hje
    exact hnot (ho ▸ (pow_dvd_pow ℓ hje).trans (dvd_mul_right _ _))
  have hoB : orderOf (a : ZMod (ℓ ^ r)) ∣ B := by
    rw [ho]
    exact mul_dvd_mul (pow_dvd_pow ℓ (by omega)) ht
  -- Hence `ℓ ^ r ∣ a ^ B - 1`, which is positive and smaller than `r < ℓ ^ r`.
  have := Nat.le_of_dvd haB ((dvd_pow_sub_one_iff_orderOf_natCast_dvd (by omega) B).2 hoB)
  have hlt : r < ℓ ^ r := Nat.lt_pow_self hℓ.one_lt
  omega

/-- For natural numbers `ℓ` and `a ≠ 1`, every power `ℓ ^ j` divides the multiplicative order of
`a` modulo `ℓ ^ r` for all large `r`. For a prime `ℓ` not dividing `a`, this order is positive, so
its `ℓ`-adic valuation is unbounded as `r` grows. When `a` and `ℓ` are not coprime (for a prime `ℓ`:
when `ℓ ∣ a`), the order is instead `0` from `r = 1` on. The hypothesis `a ≠ 1` is needed, since
`1` has order `1`. -/
theorem eventually_pow_dvd_orderOf_natCast (ℓ : ℕ) {a : ℕ} (ha : a ≠ 1) (j : ℕ) :
    ∀ᶠ r in Filter.atTop, ℓ ^ j ∣ orderOf (a : ZMod (ℓ ^ r)) := by
  by_cases hcop : a.Coprime ℓ
  swap
  · -- From `r = 1` on, the residue of `a` is not a unit, so its order is `0`.
    filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    have h0 : orderOf (a : ZMod (ℓ ^ r)) = 0 := Nat.eq_zero_of_not_pos <| by
      rwa [orderOf_natCast_pos_iff, Nat.coprime_pow_right_iff hr]
    exact h0 ▸ dvd_zero _
  -- Otherwise `ℓ ≠ 0`, and it suffices that for each prime `p ∣ ℓ` the part
  -- `p ^ (ℓ ^ j).factorization p` of `ℓ ^ j` divides the order modulo `p ^ r`, which divides
  -- the order modulo `ℓ ^ r`.
  have hℓ : ℓ ≠ 0 := by
    rintro rfl
    exact ha (Nat.coprime_zero_right _ |>.1 hcop)
  have hfac (p : ℕ) (hp : p ∈ ℓ.primeFactors) : ∀ᶠ r in Filter.atTop,
      p ^ (ℓ ^ j).factorization p ∣ orderOf (a : ZMod (ℓ ^ r)) := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpℓ := Nat.dvd_of_mem_primeFactors hp
    have hpa : ¬ p ∣ a := hpp.coprime_iff_not_dvd.1 (hcop.coprime_dvd_right hpℓ).symm
    filter_upwards [eventually_pow_dvd_orderOf_natCast_of_prime hpp ha hpa _] with r hr
    exact hr.trans (orderOf_natCast_dvd_orderOf_natCast (pow_dvd_pow_of_dvd hpℓ r) a)
  filter_upwards [(Filter.eventually_all_finset _).2 hfac] with r hr
  have ho : orderOf (a : ZMod (ℓ ^ r)) ≠ 0 := (orderOf_natCast_pos_iff.2 (hcop.pow_right r)).ne'
  rw [← Nat.factorization_prime_le_iff_dvd (pow_ne_zero j hℓ) ho]
  intro p hpp
  by_cases hpℓ : p ∣ ℓ
  · exact (hpp.pow_dvd_iff_le_factorization ho).1 (hr p (Nat.mem_primeFactors.2 ⟨hpp, hpℓ, hℓ⟩))
  · -- A prime not dividing `ℓ` does not occur in `ℓ ^ j`.
    simp [Nat.factorization_eq_zero_of_not_dvd hpℓ]

/-- Unless `n` is `1` or `2`, the residue `-1` has order `2` in `(ℤ/n)ˣ` (for `n = 0` this is
`ℤˣ = {±1}`), so `2` divides the exponent of the unit group. -/
theorem two_dvd_exponent_units {n : ℕ} (h1 : n ≠ 1) (h2 : n ≠ 2) :
    2 ∣ Monoid.exponent (ZMod n)ˣ := by
  have : Nontrivial (ZMod n) := nontrivial_iff.2 h1
  simpa [ringChar_zmod_n, h2] using Monoid.order_dvd_exponent (-1 : (ZMod n)ˣ)

/-! ### Primitive roots -/

/-- A residue modulo `n` whose order is `φ(n)` is a unit. -/
theorem isUnit_of_orderOf_eq_totient {n : ℕ} [NeZero n] {x : ZMod n}
    (h : orderOf x = n.totient) : IsUnit x :=
  (orderOf_pos_iff.mp (h ▸ Nat.totient_pos.mpr (NeZero.pos n))).isUnit

/-- A unit modulo `n` whose order is `φ(n)` generates `(ℤ/n)ˣ`. -/
theorem zpowers_eq_top_of_orderOf_eq_totient {n : ℕ} {u : (ZMod n)ˣ}
    (h : orderOf u = n.totient) : Subgroup.zpowers u = ⊤ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · -- `ℤˣ` is finite, so the order of `u` is positive, while `φ 0 = 0`.
    have : Finite (ZMod 0)ˣ := inferInstanceAs (Finite ℤˣ)
    exact absurd (h.trans Nat.totient_zero) (orderOf_pos u).ne'
  · have : NeZero n := ⟨hn.ne'⟩
    exact (Subgroup.card_eq_iff_eq_top _).mp <| by
      rw [Nat.card_zpowers, h, Nat.card_eq_fintype_card, card_units_eq_totient]

/-- If `(ℤ/n)ˣ` is cyclic, some natural number has order `φ(n)` modulo `n`, that is, is a primitive
root modulo `n` when `n ≠ 0`. For `n = 0` the statement holds with the junk witness `g = 0`, since
`φ 0 = 0`; it says nothing about generators of `ℤˣ`. -/
theorem exists_orderOf_natCast_eq_totient {n : ℕ} [IsCyclic (ZMod n)ˣ] :
    ∃ g : ℕ, orderOf (g : ZMod n) = n.totient := by
  rcases n.eq_zero_or_pos with rfl | hn
  · -- `φ 0 = 0` and `0 : ℤ` has order `0`.
    exact ⟨0, by simp [Nat.totient_zero]⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨u, hu⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp ‹IsCyclic (ZMod n)ˣ›
  refine ⟨(u : ZMod n).val, ?_⟩
  rw [natCast_zmod_val, orderOf_units, hu, Nat.card_eq_fintype_card, card_units_eq_totient]

/-- A primitive root modulo `n` is a primitive root modulo every divisor `d` of `n`. -/
theorem orderOf_natCast_eq_totient_of_dvd {d n g : ℕ} [NeZero n] (hdn : d ∣ n)
    (hg : orderOf (g : ZMod n) = n.totient) : orderOf (g : ZMod d) = d.totient := by
  have : NeZero d := ⟨fun hd ↦ NeZero.ne n (Nat.eq_zero_of_zero_dvd (hd ▸ hdn))⟩
  -- Reduction `(ℤ/n)ˣ → (ℤ/d)ˣ` is surjective, so it carries a generator to a generator.
  have hu := isUnit_of_orderOf_eq_totient hg
  have htop : Subgroup.zpowers hu.unit = ⊤ :=
    zpowers_eq_top_of_orderOf_eq_totient (by rw [← orderOf_units, hu.unit_spec, hg])
  have htop' : Subgroup.zpowers (unitsMap hdn hu.unit) = ⊤ := by
    rw [← MonoidHom.map_zpowers, htop, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (unitsMap_surjective hdn)]
  have hcoe : ((unitsMap hdn hu.unit : (ZMod d)ˣ) : ZMod d) = g := by
    simp [unitsMap_def]
  rw [← hcoe, orderOf_units, orderOf_eq_card_of_zpowers_eq_top htop', Nat.card_eq_fintype_card,
    card_units_eq_totient]

/-- **A primitive root modulo `p ²` is a primitive root modulo every power of `p`**, for an odd
prime `p`. -/
theorem orderOf_natCast_prime_pow_eq_totient {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = (p ^ 2).totient) (e : ℕ) :
    orderOf (g : ZMod (p ^ e)) = (p ^ e).totient := by
  -- Writing `g ^ (p - 1) = 1 + p a`, the integer `a` is prime to `p` because `g` has order
  -- `p (p - 1)` modulo `p ²`; so `g ^ (p - 1)` has order `p ^ (e - 1)` modulo `p ^ e`, while the
  -- order of `g` is a multiple of its order `p (p - 1)` modulo `p ²`.
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  obtain he | ⟨n, rfl⟩ : e ≤ 2 ∨ ∃ n, e = n + 2 :=
    (le_or_gt e 2).imp_right fun h ↦ ⟨e - 2, by omega⟩
  · exact orderOf_natCast_eq_totient_of_dvd (pow_dvd_pow p he) hg
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have htot : (p ^ 2).totient = p * (p - 1) := by
    rw [Nat.totient_prime_pow hp two_pos]
    simp
  -- `g` is prime to `p`, so Fermat's little theorem writes `g ^ (p - 1) = 1 + p a`.
  have hcop : IsCoprime (g : ℤ) p := Nat.isCoprime_iff_coprime.mpr <|
    Nat.Coprime.coprime_dvd_right (dvd_pow_self p two_ne_zero)
      ((isUnit_iff_coprime g (p ^ 2)).mp (isUnit_of_orderOf_eq_totient hg))
  obtain ⟨a, ha⟩ := (Int.ModEq.pow_card_sub_one_eq_one hp hcop).symm.dvd
  have hga : ((g ^ (p - 1) : ℕ) : ℤ) = 1 + p * a := by push_cast; linarith
  -- The integer `a` is prime to `p`, since otherwise `g ^ (p - 1) ≡ 1` modulo `p ²`.
  have hpa : ¬ (p : ℤ) ∣ a := by
    rintro ⟨b, rfl⟩
    have h1 : (g : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
      have := congrArg (fun z : ℤ ↦ (z : ZMod (p ^ 2))) hga
      push_cast at this
      rw [this, ← mul_assoc, ← pow_two, ← Nat.cast_pow, natCast_self, zero_mul, add_zero]
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hp1) (orderOf_dvd_of_pow_eq_one h1)
    rw [hg, htot] at this
    have := Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hp1)
    omega
  have hpow : orderOf ((g : ZMod (p ^ (n + 2))) ^ (p - 1)) = p ^ (n + 1) := by
    have := orderOf_one_add_mul_prime hp hp2 a hpa (n + 1)
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod (p ^ (n + 1 + 1)))) hga
    push_cast at hcast
    rwa [← hcast] at this
  have hdvd : p - 1 ∣ orderOf (g : ZMod (p ^ (n + 2))) :=
    (Dvd.intro_left p (htot ▸ hg).symm).trans
      (orderOf_natCast_dvd_orderOf_natCast (pow_dvd_pow p (by omega)) g)
  rw [orderOf_pow_of_dvd hp1 hdvd] at hpow
  rw [Nat.totient_prime_pow_succ hp, ← hpow, Nat.div_mul_cancel hdvd]

end ZMod

namespace TauCeti.ZMod

/-- For `1 < p`, the order of `p` modulo `p ^ f - 1` is `f`. At `f = 0` the modulus is `0`, and
the order `0` in `ZMod 0 = ℤ` means that `p` has infinite multiplicative order. -/
@[simp]
theorem orderOf_natCast_pow_sub_one {p : ℕ} (hp : 1 < p) (f : ℕ) :
    orderOf (p : ZMod (p ^ f - 1)) = f := by
  have hdvd := (ZMod.dvd_pow_sub_one_iff_orderOf_natCast_dvd (n := p ^ f - 1) (by omega) f).1
    dvd_rfl
  have ho := (ZMod.dvd_pow_sub_one_iff_orderOf_natCast_dvd (n := p ^ f - 1) (q := p) (by omega)
    (orderOf (p : ZMod (p ^ f - 1)))).2 dvd_rfl
  exact Nat.dvd_antisymm hdvd ((Nat.pow_sub_one_dvd_pow_sub_one_iff hp).mp ho)

end TauCeti.ZMod

/-! ### Divisibility of `a ^ k + b ^ k` -/

namespace Nat.Prime

/-- Suppose that `a / b` has order `2 * m` modulo a prime `p`, with `m ≠ 0`. Then `p` divides
`a ^ k + b ^ k` exactly for the odd multiples `k` of `m`. The inverse is that of `ZMod p`, which is
the field inverse since `p` is prime; the hypothesis on the order forces `p ∤ b`. -/
theorem dvd_pow_add_pow_iff_of_orderOf_eq_two_mul {p a b m : ℕ} (hp : p.Prime)
    (h : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = 2 * m) (hm : m ≠ 0) (k : ℕ) :
    p ∣ a ^ k + b ^ k ↔ m ∣ k ∧ ¬ 2 * m ∣ k := by
  have := Fact.mk hp
  -- If `b` vanished modulo `p`, the residue `a / b` would be `0`, which has order `0`.
  have hb : (b : ZMod p) ≠ 0 := by
    rintro hb
    rw [hb, inv_zero, mul_zero, orderOf_zero] at h
    omega
  -- Both sides say that `a ^ k = -b ^ k` modulo `p`.
  rw [← TauCeti.pow_eq_neg_one_iff_of_orderOf_eq_two_mul h hm, ← ZMod.natCast_eq_zero_iff,
    ← div_eq_mul_inv, div_pow, div_eq_iff (pow_ne_zero k hb)]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- If `q` has order `2 * m` modulo a prime `p`, with `m ≠ 0`, then `p` divides `q ^ k + 1`
exactly for the odd multiples `k` of `m`. -/
theorem dvd_pow_add_one_iff_of_orderOf_natCast_eq_two_mul {p q m : ℕ} (hp : p.Prime)
    (h : orderOf (q : ZMod p) = 2 * m) (hm : m ≠ 0) (k : ℕ) :
    p ∣ q ^ k + 1 ↔ m ∣ k ∧ ¬ 2 * m ∣ k := by
  have := Fact.mk hp
  simpa using hp.dvd_pow_add_pow_iff_of_orderOf_eq_two_mul (b := 1) (by simpa using h) hm k

end Nat.Prime
