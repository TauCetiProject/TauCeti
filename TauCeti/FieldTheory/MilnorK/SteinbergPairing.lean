/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Steinberg pairings on commutative rings and fields

This file defines `TauCeti.IsSteinbergPairing`, proves the standard field identities
(skew-symmetry, `c a (-a) = 0`, `c a a = c a (-1)`, and `2 • c a a = 0`), establishes the
cyclic-unit annihilator criterion, and deduces that every Steinberg pairing on a finite field
vanishes identically.

## Main definitions

* `TauCeti.IsSteinbergPairing`: predicate expressing that a map `c : Rˣ → Rˣ → A` is biadditive
  (multiplicative in each unit argument) and satisfies the Steinberg relation `c a b = 0` whenever
  `(a : R) + b = 1`.

## Main results

* `TauCeti.IsSteinbergPairing.map_neg_self`: `c a (-a) = 0` over a field.
* `TauCeti.IsSteinbergPairing.map_comm`: `c a b = -c b a` over a field.
* `TauCeti.IsSteinbergPairing.map_self`: `c a a = c a (-1)` over a field.
* `TauCeti.IsSteinbergPairing.two_nsmul_map_self`: `2 • c a a = 0` over a field.
* `TauCeti.IsSteinbergPairing.eq_zero_of_isCyclic_of_ringChar_ne_zero`: vanishing when `Fˣ` is
  cyclic and `ringChar F ≠ 0`.
* `TauCeti.IsSteinbergPairing.eq_zero_of_finite`: every Steinberg pairing on a finite field is
  identically zero.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §III.6.1, Lemma III.6.1,
  Corollary III.6.1.1, and Lemma III.6.3.
-/

public section

namespace TauCeti

/-- A map `c : Rˣ → Rˣ → A` from pairs of units of a commutative semiring `R` to an additive
commutative monoid `A` is a *Steinberg pairing* if it is bimultiplicative (sending multiplication
in each unit slot to addition in `A`) and satisfies the Steinberg relation `c a b = 0` whenever
`(a : R) + b = 1`. -/
structure IsSteinbergPairing {R : Type*} [CommSemiring R] {A : Type*} [AddCommMonoid A]
    (c : Rˣ → Rˣ → A) : Prop where
  /-- Multiplicativity in the left unit argument. -/
  map_mul_left : ∀ a₁ a₂ b : Rˣ, c (a₁ * a₂) b = c a₁ b + c a₂ b
  /-- Multiplicativity in the right unit argument. -/
  map_mul_right : ∀ a b₁ b₂ : Rˣ, c a (b₁ * b₂) = c a b₁ + c a b₂
  /-- The Steinberg relation: complementary units pairing to `0`. -/
  steinberg : ∀ {a b : Rˣ}, (a : R) + b = 1 → c a b = 0

namespace IsSteinbergPairing

section CommSemiring

variable {R : Type*} [CommSemiring R] {A : Type*} [AddCommGroup A] {c : Rˣ → Rˣ → A}

/-- A Steinberg pairing vanishes when the left argument is `1`. -/
theorem map_one_left (hc : IsSteinbergPairing c) (b : Rˣ) : c 1 b = 0 := by
  simpa using (hc.map_mul_left 1 1 b).symm

/-- A Steinberg pairing vanishes when the right argument is `1`. -/
theorem map_one_right (hc : IsSteinbergPairing c) (a : Rˣ) : c a 1 = 0 := by
  simpa using (hc.map_mul_right a 1 1).symm

/-- Inverting the left unit negates the pairing value. -/
theorem map_inv_left (hc : IsSteinbergPairing c) (a b : Rˣ) : c a⁻¹ b = -c a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← hc.map_mul_left, inv_mul_cancel, hc.map_one_left]

/-- Inverting the right unit negates the pairing value. -/
theorem map_inv_right (hc : IsSteinbergPairing c) (a b : Rˣ) : c a b⁻¹ = -c a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← hc.map_mul_right, inv_mul_cancel, hc.map_one_right]

/-- Raising the left unit to a natural power scales the pairing value. -/
theorem map_pow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) :
    c (a ^ n) b = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_left]
  | succ n ih => rw [pow_succ, hc.map_mul_left, ih, succ_nsmul]

/-- Raising the right unit to a natural power scales the pairing value. -/
theorem map_pow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℕ) :
    c a (b ^ n) = n • c a b := by
  induction n with
  | zero => simp [hc.map_one_right]
  | succ n ih => rw [pow_succ, hc.map_mul_right, ih, succ_nsmul]

/-- Raising the left unit to an integer power scales the pairing value. -/
theorem map_zpow_left (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c (a ^ n) b = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_left a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_left, hc.map_pow_left, negSucc_zsmul]

/-- Raising the right unit to an integer power scales the pairing value. -/
theorem map_zpow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c a (b ^ n) = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_right a b n
  | negSucc n => rw [zpow_negSucc, hc.map_inv_right, hc.map_pow_right, negSucc_zsmul]

/-- Post-composing a Steinberg pairing with an additive homomorphism gives a Steinberg pairing. -/
theorem comp_addMonoidHom {B : Type*} [AddCommMonoid B] {c : Rˣ → Rˣ → B}
    (hc : IsSteinbergPairing c) {C : Type*} [AddCommMonoid C] (f : B →+ C) :
    IsSteinbergPairing (fun a b ↦ f (c a b)) where
  map_mul_left a₁ a₂ b := by rw [hc.map_mul_left, map_add]
  map_mul_right a b₁ b₂ := by rw [hc.map_mul_right, map_add]
  steinberg hab := by rw [hc.steinberg hab, map_zero]

/-- Pulling back a Steinberg pairing along a ring homomorphism gives a Steinberg pairing. -/
theorem comp_ringHom {S : Type*} [CommSemiring S] {B : Type*} [AddCommMonoid B]
    {c : Sˣ → Sˣ → B} (hc : IsSteinbergPairing c) (f : R →+* S) :
    IsSteinbergPairing (fun a b : Rˣ ↦ c (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b))
    where
  map_mul_left a₁ a₂ b := by rw [map_mul, hc.map_mul_left]
  map_mul_right a b₁ b₂ := by rw [map_mul, hc.map_mul_right]
  steinberg {a b} hab := hc.steinberg (by
    change f (a : R) + f (b : R) = 1
    rw [← map_add, hab, map_one])

end CommSemiring

section Field

variable {F : Type*} [Field F] {A : Type*} [AddCommGroup A] {c : Fˣ → Fˣ → A}

/-- Over a field, every Steinberg pairing satisfies `c a (-a) = 0`. -/
theorem map_neg_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a (-a) = 0 := by
  by_cases ha : (a : F) = 1
  · rw [show a = 1 from Units.ext ha, hc.map_one_left]
  · let u : Fˣ := Units.mk0 (1 - (a : F)) (sub_ne_zero.mpr (Ne.symm ha))
    have h1 : c a u = 0 := hc.steinberg (by simp [u])
    have h2 : c a⁻¹ (-(a⁻¹ * u)) = 0 := hc.steinberg (by
      have ha0 : (a : F) ≠ 0 := a.ne_zero
      simp only [Units.val_inv_eq_inv_val, Units.val_neg, Units.val_mul, u, Units.val_mk0]
      field_simp; ring)
    have hneg : -a = u * (-(a⁻¹ * u))⁻¹ := Units.ext (by
      have ha0 : (a : F) ≠ 0 := a.ne_zero
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val, u, Units.val_mk0]
      field_simp)
    rw [hneg, hc.map_mul_right, h1, zero_add, hc.map_inv_right, ← neg_neg (c a _),
      ← hc.map_inv_left, h2, neg_zero, neg_zero]

/-- Over a field, every Steinberg pairing satisfies `c a a = c a (-1)`. -/
theorem map_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a a = c a (-1 : Fˣ) := by
  have h0 : c a (-1 : Fˣ) + c a a = 0 := by
    rw [← hc.map_mul_right, show (-1 : Fˣ) * a = -a by ext; simp, hc.map_neg_self]
  have h1 : c a (-1 : Fˣ) + c a (-1 : Fˣ) = 0 := by
    rw [← hc.map_mul_right, show (-1 : Fˣ) * (-1 : Fˣ) = 1 by ext; simp, hc.map_one_right]
  exact add_left_cancel (h0.trans h1.symm)

/-- Over a field, every Steinberg pairing is skew-symmetric: `c a b = -c b a`. -/
theorem map_comm (hc : IsSteinbergPairing c) (a b : Fˣ) : c a b = -c b a := by
  have hab : c (a * b) (-(a * b)) = 0 := hc.map_neg_self (a * b)
  rw [show -(a * b) = (-a) * b by ext; simp, hc.map_mul_left, hc.map_mul_right,
    hc.map_mul_right, hc.map_neg_self, zero_add, show -a = (-1 : Fˣ) * a by ext; simp,
    hc.map_mul_right, hc.map_self b] at hab
  have hneg1 : c b (-1 : Fˣ) + c b (-1 : Fˣ) = 0 := by
    rw [← hc.map_mul_right, show (-1 : Fˣ) * (-1 : Fˣ) = 1 by ext; simp, hc.map_one_right]
  exact eq_neg_of_add_eq_zero_left <| by
    have : c a b + c b a = c a b + ((c b (-1 : Fˣ) + c b a) + c b (-1 : Fˣ)) -
        (c b (-1 : Fˣ) + c b (-1 : Fˣ)) := by abel
    rw [this, hab, hneg1, sub_zero]

/-- Over a field, diagonal values `c a a` are 2-torsion. -/
theorem two_nsmul_map_self (hc : IsSteinbergPairing c) (a : Fˣ) : 2 • c a a = 0 := by
  rw [two_nsmul, hc.map_self, ← hc.map_mul_right,
    show (-1 : Fˣ) * (-1 : Fˣ) = 1 by ext; simp, hc.map_one_right]

/-- In characteristic `2`, diagonal values of a Steinberg pairing vanish. -/
theorem map_self_of_charTwo [CharP F 2] (hc : IsSteinbergPairing c) (a : Fˣ) : c a a = 0 := by
  rw [hc.map_self, show (-1 : Fˣ) = 1 by ext; exact CharTwo.neg_eq 1, hc.map_one_right]

/-! ### Cyclic-unit annihilator and finite-field vanishing -/

/-- If `Fˣ` is generated by `g` and `c g g = 0`, then `c` is identically zero. -/
theorem eq_zero_of_generator_map_self_eq_zero (hc : IsSteinbergPairing c) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) (hgg : c g g = 0) (a b : Fˣ) :
    c a b = 0 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [hc.map_zpow_left, hc.map_zpow_right, hgg, smul_zero, smul_zero]

/-- If `Fˣ` is cyclic and `char F = 2`, every Steinberg pairing on `F` vanishes identically. -/
theorem eq_zero_of_isCyclic_of_charTwo [IsCyclic Fˣ] [CharP F 2] (hc : IsSteinbergPairing c)
    (a b : Fˣ) : c a b = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  exact hc.eq_zero_of_generator_map_self_eq_zero hg (hc.map_self_of_charTwo g) a b

/-- Cyclic-unit annihilator criterion: if `g` generates `Fˣ` and there exist complementary units
`a = g ^ (2 * k + 1)` and `b = g ^ (2 * l + 1)` with odd exponents relative to `g`, then `c` is
identically zero. -/
theorem eq_zero_of_odd_complementary (hc : IsSteinbergPairing c) {g : Fˣ}
    (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) {k l : ℤ}
    (hab : ((g ^ (2 * k + 1) : Fˣ) : F) + ((g ^ (2 * l + 1) : Fˣ) : F) = 1) (a b : Fˣ) :
    c a b = 0 := by
  have h0 : ((2 * k + 1) * (2 * l + 1)) • c g g = 0 := by
    rw [mul_zsmul, ← hc.map_zpow_right, ← hc.map_zpow_left]
    exact hc.steinberg hab
  have htwo : (2 : ℤ) • c g g = 0 := by
    simpa only [Nat.cast_ofNat] using (natCast_zsmul (c g g) 2).trans (hc.two_nsmul_map_self g)
  have hgg : c g g = 0 := by
    rw [show (2 * k + 1) * (2 * l + 1) = (2 * k * l + k + l) * 2 + 1 by ring,
      add_zsmul, mul_zsmul, htwo, smul_zero, zero_add, one_zsmul] at h0
    exact h0
  exact hc.eq_zero_of_generator_map_self_eq_zero hg hgg a b

private theorem not_isSquare_mul_inv_of_isSquare {s t : Fˣ} (hs : IsSquare s) (ht : ¬ IsSquare t) :
    ¬ IsSquare (s * t⁻¹) := by
  intro h; apply ht; simpa using hs.div h

private theorem exists_odd_zpow_of_not_isSquare {g : Fˣ} (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g)
    {a : Fˣ} (ha : ¬ IsSquare a) : ∃ k : ℤ, g ^ (2 * k + 1) = a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact absurd ⟨g ^ k, by rw [← zpow_add]⟩ ha
  · exact ⟨k, rfl⟩

private theorem exists_not_isSquare_complementary_of_ringChar_ne_zero
    (hchar : ringChar F ≠ 0) (hchar2 : ¬ CharP F 2) {g : Fˣ} (hg_nsq : ¬ IsSquare g) :
    ∃ a b : Fˣ, ¬ IsSquare a ∧ ¬ IsSquare b ∧ (a : F) + b = 1 := by
  have hprime := (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hchar
  have hp2 : ringChar F ≠ 2 := fun h2 ↦ hchar2 (h2 ▸ ringChar.charP F)
  have h1g_ne : 1 - (g : F) ≠ 0 := fun h0 ↦
    hg_nsq ⟨1, by simp [show g = 1 from Units.ext (sub_eq_zero.mp h0).symm]⟩
  let u : Fˣ := Units.mk0 (1 - (g : F)) h1g_ne
  by_cases hu : IsSquare u
  · by_cases hneg1 : IsSquare (-1 : Fˣ)
    · have hnegu : IsSquare (-u) := by simpa using hneg1.mul hu
      refine ⟨(-u) * g⁻¹, g⁻¹, not_isSquare_mul_inv_of_isSquare hnegu hg_nsq,
        mt isSquare_inv.mp hg_nsq, ?_⟩
      have hg0 : (g : F) ≠ 0 := g.ne_zero
      simp only [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, u, Units.val_mk0]
      field_simp; ring
    · have : CharP F (ringChar F) := ringChar.charP F
      have hp3 : 3 ≤ ringChar F := by have := hprime.two_le; omega
      have hcast_ne : ∀ n : ℕ, 0 < n → n < ringChar F → (n : F) ≠ 0 := fun n hn0 hnp h0 ↦
        Nat.not_lt_of_ge (Nat.le_of_dvd hn0 ((CharP.cast_eq_zero_iff F (ringChar F) n).mp h0)) hnp
      let P : ℕ → Prop := fun n ↦ ∃ h : (n : F) ≠ 0, ¬ IsSquare (Units.mk0 (n : F) h)
      have hp1_prop : P (ringChar F - 1) := by
        refine ⟨hcast_ne (ringChar F - 1) (by omega) (by omega), ?_⟩
        rwa [show Units.mk0 ((ringChar F - 1 : ℕ) : F) _ = (-1 : Fˣ) by
          ext; exact eq_neg_of_add_eq_zero_left (by
            simp only [Units.val_mk0, Units.val_one]
            rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ ringChar F),
              CharP.cast_eq_zero F (ringChar F)])]
      have hex : ∃ n, P n := ⟨ringChar F - 1, hp1_prop⟩
      classical
      set m := Nat.find hex
      have hm_spec : P m := Nat.find_spec hex
      obtain ⟨hm_ne, hm_nsq⟩ := hm_spec
      have hm_ge2 : 2 ≤ m := by
        by_contra hlt
        rcases (by omega : m = 0 ∨ m = 1) with hm0 | hm1
        · exact hm_ne (by rw [hm0, Nat.cast_zero])
        · exact hm_nsq ⟨1, Units.ext (by simp [hm1])⟩
      have hm1_ne : ((m - 1 : ℕ) : F) ≠ 0 :=
        hcast_ne (m - 1) (by omega) (by have := Nat.find_min' hex hp1_prop; omega)
      have hm1_sq : IsSquare (Units.mk0 ((m - 1 : ℕ) : F) hm1_ne) :=
        by_contra fun hnsq ↦ Nat.find_min hex (by omega : m - 1 < m) ⟨hm1_ne, hnsq⟩
      refine ⟨Units.mk0 ((m - 1 : ℕ) : F) hm1_ne * (Units.mk0 (m : F) hm_ne)⁻¹,
        (Units.mk0 (m : F) hm_ne)⁻¹, not_isSquare_mul_inv_of_isSquare hm1_sq hm_nsq,
        mt isSquare_inv.mp hm_nsq, ?_⟩
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [← add_one_mul, ← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ m),
        mul_inv_cancel₀ hm_ne]
  · exact ⟨g, u, hg_nsq, hu, by simp [u]⟩

/-- Every Steinberg pairing on a field with cyclic unit group and positive characteristic vanishes
identically. -/
theorem eq_zero_of_isCyclic_of_ringChar_ne_zero [IsCyclic Fˣ] (hchar : ringChar F ≠ 0)
    (hc : IsSteinbergPairing c) (a b : Fˣ) : c a b = 0 := by
  by_cases hchar2 : CharP F 2
  · exact hc.eq_zero_of_isCyclic_of_charTwo a b
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    by_cases hg_sq : IsSquare g
    · obtain ⟨u, hu⟩ := hg_sq
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have hpow : g ^ (2 * k - 1) = 1 := by
        rw [zpow_sub, zpow_one, two_mul, zpow_add, hk, ← hu, mul_inv_cancel]
      have h0 : (2 * k - 1) • c g g = 0 := by rw [← hc.map_zpow_left, hpow, hc.map_one_left]
      have htwo : (2 : ℤ) • c g g = 0 := by
        simpa only [Nat.cast_ofNat] using (natCast_zsmul (c g g) 2).trans (hc.two_nsmul_map_self g)
      have hgg : c g g = 0 := by
        rw [← one_zsmul (c g g), show (1 : ℤ) = k * 2 + -(2 * k - 1) by ring,
          add_zsmul, mul_zsmul, neg_zsmul, htwo, h0, smul_zero, neg_zero, add_zero]
      exact hc.eq_zero_of_generator_map_self_eq_zero hg hgg a b
    · obtain ⟨x, y, hx, hy, hxy⟩ :=
        exists_not_isSquare_complementary_of_ringChar_ne_zero hchar hchar2 hg_sq
      obtain ⟨k, rfl⟩ := exists_odd_zpow_of_not_isSquare hg hx
      obtain ⟨l, rfl⟩ := exists_odd_zpow_of_not_isSquare hg hy
      exact hc.eq_zero_of_odd_complementary hg hxy a b

/-- Every Steinberg pairing on a finite field is identically zero. -/
theorem eq_zero_of_finite [Finite F] (hc : IsSteinbergPairing c) (a b : Fˣ) : c a b = 0 :=
  hc.eq_zero_of_isCyclic_of_ringChar_ne_zero (CharP.ringChar_ne_zero_of_finite F) a b

end Field

end IsSteinbergPairing

end TauCeti
