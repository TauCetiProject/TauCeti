/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import TauCeti.Data.ZMod.Divisibility
import TauCeti.Data.ZMod.OrderOf

/-!
# Generators of the unit groups modulo prime powers

By the Chinese remainder theorem the unit group `(ℤ/n)ˣ` is the product of the unit groups modulo
the prime powers `p ^ v_p(n)` exactly dividing `n` (`ZMod.unitsEquivPi`). Each factor has an
explicit generating set:

* for an odd prime `p`, an integer that is a primitive root modulo `p ²` is a primitive root modulo
  every power of `p` (`ZMod.orderOf_natCast_prime_pow_eq_totient`);
* modulo `2 ^ (e + 2)`, every unit is uniquely `± 5 ^ a` with `a` modulo `2 ^ e`
  (`ZMod.unitsTwoPowEquiv`).

These are the coordinates in which characters modulo `n` are written down explicitly, as in the
Conrey labelling of Dirichlet characters.

## Main definitions

* `ZMod.unitsEquivPi`: the Chinese remainder isomorphism
  `(ℤ/n)ˣ ≃* Π p ∣ n, (ℤ/p ^ v_p(n))ˣ`.
* `ZMod.unitsTwoPowEquiv e`: the isomorphism `ℤ/2 × ℤ/2 ^ e ≃ (ℤ/2 ^ (e + 2))ˣ`,
  `(x, a) ↦ (-1) ^ x 5 ^ a`, written multiplicatively.

## Main results

* `ZMod.unitsEquivPi_apply`: the components are the reductions.
* `ZMod.orderOf_natCast_eq_totient_of_dvd`: a primitive root modulo `n` is a primitive root
  modulo every divisor of `n`.
* `ZMod.orderOf_natCast_prime_pow_eq_totient`: for odd `p`, a primitive root modulo `p ²` is a
  primitive root modulo every `p ^ e`.
* `ZMod.coe_unitsTwoPowEquiv_ofAdd_natCast`: the formula `(x, a) ↦ (-1) ^ x 5 ^ a`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 4, §1,
  Theorems 2 and 2'.
-/

public section

open Multiplicative

namespace ZMod

/-! ### The Chinese remainder theorem for units -/

/-- **The Chinese remainder theorem for units**: `(ℤ/n)ˣ` is the product of the unit groups
modulo the prime powers exactly dividing `n`. -/
noncomputable def unitsEquivPi {n : ℕ} (hn : n ≠ 0) :
    (ZMod n)ˣ ≃* Π p : n.primeFactors, (ZMod (p ^ n.factorization p))ˣ :=
  (Units.mapEquiv (equivPi n hn).toMulEquiv).trans MulEquiv.piUnits

/-- The component at `p` of `ZMod.unitsEquivPi` is reduction modulo `p ^ v_p(n)`. -/
@[simp]
theorem unitsEquivPi_apply {n : ℕ} (hn : n ≠ 0) (u : (ZMod n)ˣ) (p : n.primeFactors) :
    unitsEquivPi hn u p = unitsMap (Nat.ordProj_dvd n p) u := by
  ext
  simp [unitsEquivPi, MulEquiv.piUnits, unitsMap_def]

/-! ### Primitive roots modulo odd prime powers -/

/-- A primitive root modulo `n` is a primitive root modulo every divisor `d` of `n`: reduction
`(ℤ/n)ˣ → (ℤ/d)ˣ` is surjective, so it carries a generator to a generator. -/
theorem orderOf_natCast_eq_totient_of_dvd {d n g : ℕ} [NeZero n] (hdn : d ∣ n)
    (hg : orderOf (g : ZMod n) = n.totient) : orderOf (g : ZMod d) = d.totient := by
  have : NeZero d := ⟨fun hd ↦ NeZero.ne n (Nat.eq_zero_of_zero_dvd (hd ▸ hdn))⟩
  have hu : IsUnit (g : ZMod n) :=
    (orderOf_pos_iff.mp (hg ▸ Nat.totient_pos.mpr (NeZero.pos n))).isUnit
  have htop : Subgroup.zpowers hu.unit = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp <| by
    rw [Nat.card_zpowers, ← orderOf_units, hu.unit_spec, hg, Nat.card_eq_fintype_card,
      card_units_eq_totient]
  have htop' : Subgroup.zpowers (unitsMap hdn hu.unit) = ⊤ := by
    rw [← MonoidHom.map_zpowers, htop, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (unitsMap_surjective hdn)]
  have hcoe : ((unitsMap hdn hu.unit : (ZMod d)ˣ) : ZMod d) = g := by
    simp [unitsMap_def]
  rw [← hcoe, orderOf_units, orderOf_eq_card_of_zpowers_eq_top htop', Nat.card_eq_fintype_card,
    card_units_eq_totient]

/-- **A primitive root modulo `p ²` is a primitive root modulo every power of `p`**, for an odd
prime `p`.

Writing `g ^ (p - 1) = 1 + p a`, the integer `a` is prime to `p` because `g` has order
`p (p - 1)` modulo `p ²`; so `g ^ (p - 1)` has order `p ^ (e - 1)` modulo `p ^ e`, while the order
of `g` is a multiple of its order `p (p - 1)` modulo `p ²`. -/
theorem orderOf_natCast_prime_pow_eq_totient {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : orderOf (g : ZMod (p ^ 2)) = (p ^ 2).totient) (e : ℕ) :
    orderOf (g : ZMod (p ^ e)) = (p ^ e).totient := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  obtain he | ⟨n, rfl⟩ : e ≤ 2 ∨ ∃ n, e = n + 2 :=
    (le_or_gt e 2).imp_right fun h ↦ ⟨e - 2, by omega⟩
  · exact orderOf_natCast_eq_totient_of_dvd (pow_dvd_pow p he) hg
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have htot : (p ^ 2).totient = p * (p - 1) := by
    rw [Nat.totient_prime_pow hp two_pos]
    simp
  -- `g` is prime to `p`, so Fermat's little theorem writes `g ^ (p - 1) = 1 + p a`.
  have hunit : IsUnit (g : ZMod (p ^ 2)) :=
    (orderOf_pos_iff.mp (hg ▸ Nat.totient_pos.mpr (pow_pos hp.pos 2))).isUnit
  have hcop : IsCoprime (g : ℤ) p := Nat.isCoprime_iff_coprime.mpr <|
    Nat.Coprime.coprime_dvd_right (dvd_pow_self p two_ne_zero)
      ((isUnit_iff_coprime g (p ^ 2)).mp hunit)
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

/-! ### The units modulo powers of two -/

/-- The homomorphism `ℤ / n → G`, `a ↦ x ^ a`, for an element `x` of order `n`. -/
private noncomputable def powValHom {G : Type*} [Monoid G] (x : G) (n : ℕ) [NeZero n]
    (hx : orderOf x = n) : Multiplicative (ZMod n) →* G where
  toFun a := x ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    have := pow_mod_orderOf x (a.toAdd.val + b.toAdd.val)
    rw [hx] at this
    simp only [toAdd_mul, val_add, this, pow_add]

private theorem powValHom_ofAdd_natCast {G : Type*} [Monoid G] (x : G) (n : ℕ) [NeZero n]
    (hx : orderOf x = n) (k : ℕ) : powValHom x n hx (ofAdd (k : ZMod n)) = x ^ k := by
  have := pow_mod_orderOf x k
  rw [hx] at this
  simp [powValHom, val_natCast, this]

private theorem powValHom_injective {G : Type*} [Group G] (x : G) (n : ℕ) [NeZero n]
    (hx : orderOf x = n) : Function.Injective (powValHom x n hx) := by
  refine (injective_iff_map_eq_one _).mpr fun a ha ↦ ?_
  change x ^ a.toAdd.val = 1 at ha
  rw [← toAdd_eq_zero, ← natCast_zmod_val a.toAdd, natCast_eq_zero_iff]
  have := orderOf_dvd_of_pow_eq_one ha
  rwa [hx] at this

private theorem coprime_five_two_pow (k : ℕ) : Nat.Coprime 5 (2 ^ k) :=
  Nat.Coprime.pow_right k (by norm_num)

private theorem orderOf_neg_one_units_two_pow (e : ℕ) :
    orderOf (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 2 := by
  have : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right two_pos (by omega)
  have : Fact (1 < 2 ^ (e + 2)) := ⟨by omega⟩
  rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ringChar.eq (ZMod _) _]
  simp only [ite_eq_right_iff]
  omega

private theorem orderOf_five_units_two_pow (e : ℕ) :
    orderOf (unitOfCoprime 5 (coprime_five_two_pow (e + 2))) = 2 ^ e := by
  rw [← orderOf_units, coe_unitOfCoprime, Nat.cast_ofNat, orderOf_five]

/-- The homomorphism `ℤ/2 × ℤ/2 ^ e → (ℤ/2 ^ (e + 2))ˣ`, `(x, a) ↦ (-1) ^ x 5 ^ a`. -/
private noncomputable def unitsTwoPowHom (e : ℕ) :
    Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ e)) →* (ZMod (2 ^ (e + 2)))ˣ :=
  (powValHom _ 2 (orderOf_neg_one_units_two_pow e)).coprod
    (powValHom _ (2 ^ e) (orderOf_five_units_two_pow e))

private theorem unitsTwoPowHom_bijective (e : ℕ) : Function.Bijective (unitsTwoPowHom e) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_one _).mpr fun ⟨x, a⟩ h ↦ ?_
    simp only [unitsTwoPowHom, MonoidHom.coprod_apply] at h
    -- Modulo `4` the factor `5 ^ a` disappears, which forces `x = 0`.
    have hx : x = 1 := by
      have h4 := congrArg (fun u : (ZMod (2 ^ (e + 2)))ˣ ↦
        castHom (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)) (ZMod (2 ^ 2)) u) h
      simp only [powValHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, coe_unitOfCoprime, map_mul,
        map_pow, map_neg, map_one,
        map_natCast] at h4
      obtain ⟨x, rfl⟩ := ofAdd.surjective x
      have h5 : ((5 : ℕ) : ZMod (2 ^ 2)) = 1 := by decide
      rw [h5, one_pow, mul_one] at h4
      fin_cases x
      · rfl
      · exact absurd h4 (by decide)
    subst hx
    simp only [map_one, one_mul] at h
    exact Prod.ext rfl (powValHom_injective _ _ _ (h.trans (map_one _).symm))
  · simp only [Fintype.card_prod, Fintype.card_multiplicative, card, card_units_eq_totient,
      Nat.totient_prime_pow_succ Nat.prime_two]
    ring

/-- **The units modulo `2 ^ (e + 2)`**: every unit is uniquely `(-1) ^ x 5 ^ a` with `x` modulo
`2` and `a` modulo `2 ^ e`, so `(ℤ/2 ^ (e + 2))ˣ ≃ ℤ/2 × ℤ/2 ^ e`. -/
noncomputable def unitsTwoPowEquiv (e : ℕ) :
    Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ e)) ≃* (ZMod (2 ^ (e + 2)))ˣ :=
  MulEquiv.ofBijective (unitsTwoPowHom e) (unitsTwoPowHom_bijective e)

private theorem unitsTwoPowEquiv_ofAdd_natCast (e x a : ℕ) :
    unitsTwoPowEquiv e (ofAdd (x : ZMod 2), ofAdd (a : ZMod (2 ^ e))) =
      (-1) ^ x * unitOfCoprime 5 (coprime_five_two_pow (e + 2)) ^ a := by
  simp [unitsTwoPowEquiv, unitsTwoPowHom, powValHom_ofAdd_natCast]

/-- `ZMod.unitsTwoPowEquiv` sends `(x, a)` to `(-1) ^ x 5 ^ a`. -/
theorem coe_unitsTwoPowEquiv_ofAdd_natCast (e x a : ℕ) :
    (unitsTwoPowEquiv e (ofAdd (x : ZMod 2), ofAdd (a : ZMod (2 ^ e))) : ZMod (2 ^ (e + 2))) =
      (-1) ^ x * 5 ^ a := by
  simp [unitsTwoPowEquiv_ofAdd_natCast]

/-- The coordinates of `-1` are `(1, 0)`. -/
@[simp]
theorem unitsTwoPowEquiv_symm_neg_one (e : ℕ) :
    (unitsTwoPowEquiv e).symm (-1) = (ofAdd 1, 1) := by
  rw [MulEquiv.symm_apply_eq, ← Nat.cast_one, ← ofAdd_zero, ← Nat.cast_zero,
    unitsTwoPowEquiv_ofAdd_natCast]
  simp

/-- The coordinates of `5` are `(0, 1)`. -/
theorem unitsTwoPowEquiv_symm_of_coe_eq_five {e : ℕ} {u : (ZMod (2 ^ (e + 2)))ˣ}
    (hu : (u : ZMod (2 ^ (e + 2))) = 5) : (unitsTwoPowEquiv e).symm u = (1, ofAdd 1) := by
  rw [MulEquiv.symm_apply_eq, ← ofAdd_zero, ← Nat.cast_zero, ← Nat.cast_one (R := ZMod (2 ^ e))]
  ext
  rw [coe_unitsTwoPowEquiv_ofAdd_natCast, hu]
  simp

end ZMod
