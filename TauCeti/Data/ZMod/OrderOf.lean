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

/-!
# Orders of residues

Let `ℓ` be a prime and `a > 1` a natural number. The multiplicative order of `a` modulo `ℓ ^ r`
has unbounded `ℓ`-adic valuation as `r` grows: for every `j`, the power `ℓ ^ j` divides it for all
large `r` (`ZMod.eventually_pow_dvd_orderOf_natCast`).

When `ℓ ∣ a` the residue of `a` is not a unit and its order is `0` from `r = 1` on. Otherwise the
order divides `φ(ℓ ^ r) = ℓ ^ (r - 1) (ℓ - 1)`, so if `ℓ ^ j` did not divide it, it would divide
the number `ℓ ^ (j - 1) (ℓ - 1)`, which does not depend on `r`; then `ℓ ^ r` would divide the
positive number `a ^ (ℓ ^ (j - 1) (ℓ - 1)) - 1` for every `r`, which is absurd.

For the residue `a = 𝔑𝔭` of a prime `𝔭 ∤ ℓ` of a number field, this order is the residue degree
of `𝔭` in the cyclotomic extension of level `ℓ ^ r`, so the statement says that these residue
degrees become divisible by any given power of `ℓ` along the cyclotomic tower.

A residue whose order is `φ(n)` is a primitive root modulo `n`. A primitive root modulo `n` is
one modulo every divisor of `n`, and for an odd prime `p` a primitive root modulo `p ²` is one
modulo every power of `p`.

The order of `q` modulo `n` decides which of the numbers `q ^ k - 1` are divisible by `n`: those
with `k` a multiple of the order. Modulo a prime `p`, an element of even order `2 * m` has `m`-th
power `-1`, so if `a / b` has order `2 * m` then `p` divides `a ^ k + b ^ k` exactly for the odd
multiples `k` of `m`; for `b = 1` this decides which `q ^ k + 1` are divisible by `p`.

## Main results

* `ZMod.orderOf_natCast_dvd_orderOf_natCast`: for `m ∣ n`, the order of `a` modulo `m` divides its
  order modulo `n`.
* `ZMod.eventually_pow_dvd_orderOf_natCast`: for every `j`, `ℓ ^ j` divides the order of `a`
  modulo `ℓ ^ r` for all large `r`.
* `ZMod.isUnit_of_orderOf_eq_totient`, `ZMod.zpowers_eq_top_of_orderOf_eq_totient`: a residue of
  order `φ(n)` is a unit, and generates `(ℤ/n)ˣ`.
* `ZMod.exists_orderOf_natCast_eq_totient`: if `(ℤ/n)ˣ` is cyclic, some natural number is a
  primitive root modulo `n`.
* `ZMod.orderOf_natCast_eq_totient_of_dvd`: a primitive root modulo `n` is a primitive root
  modulo every divisor of `n`.
* `ZMod.orderOf_natCast_prime_pow_eq_totient`: for odd `p`, a primitive root modulo `p ²` is a
  primitive root modulo every `p ^ e`.
* `ZMod.dvd_pow_sub_one_iff_orderOf_natCast_dvd`: for `q > 0`, `n ∣ q ^ k - 1` iff the order of
  `q` modulo `n` divides `k`.
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

/-- For `m ∣ n`, the order of a natural number `a` modulo `m` divides its order modulo `n`, since
reduction modulo `m` is a ring homomorphism `ZMod n →+* ZMod m`. -/
theorem orderOf_natCast_dvd_orderOf_natCast {m n : ℕ} (h : m ∣ n) (a : ℕ) :
    orderOf (a : ZMod m) ∣ orderOf (a : ZMod n) := by
  simpa using orderOf_map_dvd (ZMod.castHom h (ZMod m)).toMonoidHom (a : ZMod n)

/-- For a prime `ℓ` and a natural number `a > 1`, every power `ℓ ^ j` divides the multiplicative
order of `a` modulo `ℓ ^ r` for all large `r`. -/
theorem eventually_pow_dvd_orderOf_natCast {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ} (ha : 1 < a) (j : ℕ) :
    ∀ᶠ r in Filter.atTop, ℓ ^ j ∣ orderOf (a : ZMod (ℓ ^ r)) := by
  -- The order modulo `ℓ ^ r` divides the order modulo `ℓ ^ r'` for `r ≤ r'`, so one level
  -- suffices.
  suffices h : ∃ R, ℓ ^ j ∣ orderOf (a : ZMod (ℓ ^ R)) by
    obtain ⟨R, hR⟩ := h
    exact Filter.eventually_atTop.2 ⟨R, fun r hr =>
      hR.trans (orderOf_natCast_dvd_orderOf_natCast (pow_dvd_pow ℓ hr) a)⟩
  by_cases hdvd : ℓ ∣ a
  · -- The residue of `a` modulo `ℓ` is `0`, of order `0`.
    have : Fact (1 < ℓ ^ 1) := ⟨by simpa using hℓ.one_lt⟩
    refine ⟨1, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff a (ℓ ^ 1)).2 (by simpa using hdvd), orderOf_zero]
    exact dvd_zero _
  -- Otherwise the order modulo `ℓ ^ r` divides `φ (ℓ ^ r)`; the level `r = a ^ B`, with
  -- `B = ℓ ^ (j - 1) * (ℓ - 1)`, is too large for `a ^ B ≡ 1 (mod ℓ ^ r)`.
  set B := ℓ ^ (j - 1) * (ℓ - 1) with hB_def
  have hB : 0 < B := Nat.mul_pos (pow_pos hℓ.pos _) (Nat.sub_pos_of_lt hℓ.one_lt)
  have haB : 0 < a ^ B - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hB.ne' ha)
  set r := a ^ B with hr_def
  have hr : 0 < r := pow_pos (by omega) B
  refine ⟨r, ?_⟩
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r hℓ.ne_zero⟩
  have hcop : a.Coprime (ℓ ^ r) :=
    Nat.Coprime.pow_right r (Nat.Coprime.symm ((hℓ.coprime_iff_not_dvd).2 hdvd))
  set o := orderOf (a : ZMod (ℓ ^ r)) with ho_def
  have hoφ : o ∣ ℓ ^ (r - 1) * (ℓ - 1) := by
    rw [ho_def, ← ZMod.coe_unitOfCoprime a hcop, orderOf_units, ← Nat.totient_prime_pow hℓ hr,
      ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have ho : o ≠ 0 := by
    rw [ho_def, ← ZMod.coe_unitOfCoprime a hcop, orderOf_units]
    exact (orderOf_pos _).ne'
  by_contra hnot
  -- Write `o = ℓ ^ e * t` with `ℓ ∤ t`; then `e < j` and `t ∣ ℓ - 1`, so `o ∣ B`.
  obtain ⟨e, t, ht, hot⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho ℓ hℓ.ne_one
  have he : e < j := by
    by_contra hje
    exact hnot (hot ▸ (pow_dvd_pow ℓ (not_lt.1 hje)).trans (dvd_mul_right _ _))
  have htcop : t.Coprime (ℓ ^ (r - 1)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.symm ((hℓ.coprime_iff_not_dvd).2 ht))
  have hoB : o ∣ B := by
    rw [hot, hB_def]
    exact mul_dvd_mul (pow_dvd_pow ℓ (by omega))
      (htcop.dvd_of_dvd_mul_left ((dvd_mul_left t (ℓ ^ e)).trans (hot ▸ hoφ)))
  -- Hence `ℓ ^ r ∣ a ^ B - 1`, which is positive and smaller than `r < ℓ ^ r`.
  have hpow : ((a ^ B : ℕ) : ZMod (ℓ ^ r)) = ((1 : ℕ) : ZMod (ℓ ^ r)) := by
    rw [Nat.cast_pow, Nat.cast_one]
    exact orderOf_dvd_iff_pow_eq_one.1 hoB
  have hdvd' : ℓ ^ r ∣ a ^ B - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1
      ((ZMod.natCast_eq_natCast_iff _ _ _).1 hpow).symm
  have hlt : r < ℓ ^ r := Nat.lt_pow_self hℓ.one_lt
  have := Nat.le_of_dvd haB hdvd'
  omega

/-! ### Primitive roots -/

/-- A residue modulo `n` whose order is `φ(n)` is a unit. -/
theorem isUnit_of_orderOf_eq_totient {n : ℕ} [NeZero n] {x : ZMod n}
    (h : orderOf x = n.totient) : IsUnit x :=
  (orderOf_pos_iff.mp (h ▸ Nat.totient_pos.mpr (NeZero.pos n))).isUnit

/-- A unit modulo `n` whose order is `φ(n)` generates `(ℤ/n)ˣ`. -/
theorem zpowers_eq_top_of_orderOf_eq_totient {n : ℕ} [NeZero n] {u : (ZMod n)ˣ}
    (h : orderOf u = n.totient) : Subgroup.zpowers u = ⊤ :=
  (Subgroup.card_eq_iff_eq_top _).mp <| by
    rw [Nat.card_zpowers, h, Nat.card_eq_fintype_card, card_units_eq_totient]

/-- If `(ℤ/n)ˣ` is cyclic, some natural number is a primitive root modulo `n`. -/
theorem exists_orderOf_natCast_eq_totient {n : ℕ} [NeZero n] [IsCyclic (ZMod n)ˣ] :
    ∃ g : ℕ, orderOf (g : ZMod n) = n.totient := by
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

/-! ### Divisibility of `q ^ k - 1` and `q ^ k + 1` -/

/-- For a positive natural number `q` and any modulus `n`, `n` divides `q ^ k - 1` if and only if
the order of `q` modulo `n` divides `k`. -/
theorem dvd_pow_sub_one_iff_orderOf_natCast_dvd {n q : ℕ} (hq : 0 < q) (k : ℕ) :
    n ∣ q ^ k - 1 ↔ orderOf (q : ZMod n) ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one, ← natCast_eq_zero_iff]
  simp [Nat.cast_sub (Nat.one_le_pow _ _ hq), sub_eq_zero]

end ZMod

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
