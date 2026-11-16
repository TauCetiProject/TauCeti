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
  have h : c 1 b + 0 = c 1 b + c 1 b := by
    simpa only [add_zero, one_mul] using hc.map_mul_left 1 1 b
  exact (add_left_cancel h).symm

/-- A Steinberg pairing vanishes when the right argument is `1`. -/
theorem map_one_right (hc : IsSteinbergPairing c) (a : Rˣ) : c a 1 = 0 := by
  have h : c a 1 + 0 = c a 1 + c a 1 := by
    simpa only [add_zero, one_mul] using hc.map_mul_right a 1 1
  exact (add_left_cancel h).symm

/-- Inverting the left unit negates the pairing value. -/
theorem map_inv_left (hc : IsSteinbergPairing c) (a b : Rˣ) : c a⁻¹ b = -c a b := by
  apply eq_neg_of_add_eq_zero_left
  rw [← hc.map_mul_left, inv_mul_cancel, hc.map_one_left]

/-- Inverting the right unit negates the pairing value. -/
theorem map_inv_right (hc : IsSteinbergPairing c) (a b : Rˣ) : c a b⁻¹ = -c a b := by
  apply eq_neg_of_add_eq_zero_left
  rw [← hc.map_mul_right, inv_mul_cancel, hc.map_one_right]

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
  | negSucc n =>
    rw [zpow_negSucc, hc.map_inv_left, hc.map_pow_left, negSucc_zsmul]

/-- Raising the right unit to an integer power scales the pairing value. -/
theorem map_zpow_right (hc : IsSteinbergPairing c) (a b : Rˣ) (n : ℤ) :
    c a (b ^ n) = n • c a b := by
  cases n with
  | ofNat n => simpa using hc.map_pow_right a b n
  | negSucc n =>
    rw [zpow_negSucc, hc.map_inv_right, hc.map_pow_right, negSucc_zsmul]

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
  steinberg {a b} hab := by
    apply hc.steinberg
    change f (a : R) + f (b : R) = 1
    rw [← map_add, hab, map_one]

end CommSemiring

section Field

variable {F : Type*} [Field F] {A : Type*} [AddCommGroup A] {c : Fˣ → Fˣ → A}

/-- Over a field, every Steinberg pairing satisfies `c a (-a) = 0`. -/
theorem map_neg_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a (-a) = 0 := by
  by_cases ha : (a : F) = 1
  · have ha1 : a = 1 := Units.ext ha
    rw [ha1, hc.map_one_left]
  · have h1a : 1 - (a : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
    let u : Fˣ := Units.mk0 (1 - (a : F)) h1a
    have hu1 : (a : F) + u = 1 := by simp [u]
    have h1 : c a u = 0 := hc.steinberg hu1
    have h2 : c a⁻¹ (-(a⁻¹ * u)) = 0 := by
      apply hc.steinberg
      have ha0 : (a : F) ≠ 0 := a.ne_zero
      simp only [Units.val_inv_eq_inv_val, Units.val_neg, Units.val_mul, u, Units.val_mk0]
      field_simp
      ring
    have hneg_eq : -a = u * (-(a⁻¹ * u))⁻¹ := by
      ext
      have ha0 : (a : F) ≠ 0 := a.ne_zero
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val, u, Units.val_mk0]
      field_simp
    rw [hneg_eq, hc.map_mul_right, h1, zero_add, hc.map_inv_right]
    have h3 : c a (-(a⁻¹ * u)) = -c a⁻¹ (-(a⁻¹ * u)) := by
      rw [hc.map_inv_left, neg_neg]
    rw [h3, h2, neg_zero, neg_zero]

/-- Over a field, every Steinberg pairing satisfies `c a a = c a (-1)`. -/
theorem map_self (hc : IsSteinbergPairing c) (a : Fˣ) : c a a = c a (-1 : Fˣ) := by
  have h : -a = (-1 : Fˣ) * a := by ext; simp
  have h0 : c a (-1 : Fˣ) + c a a = 0 := by
    rw [← hc.map_mul_right, ← h, hc.map_neg_self]
  have h1 : c a (-1 : Fˣ) + c a (-1 : Fˣ) = 0 := by
    rw [← hc.map_mul_right, show (-1 : Fˣ) * (-1 : Fˣ) = 1 by ext; simp, hc.map_one_right]
  have heq : c a (-1 : Fˣ) + c a a = c a (-1 : Fˣ) + c a (-1 : Fˣ) := h0.trans h1.symm
  exact add_left_cancel heq

/-- Over a field, every Steinberg pairing is skew-symmetric: `c a b = -c b a`. -/
theorem map_comm (hc : IsSteinbergPairing c) (a b : Fˣ) : c a b = -c b a := by
  have hab : c (a * b) (-(a * b)) = 0 := hc.map_neg_self (a * b)
  have hprod : -(a * b) = (-a) * b := by ext; simp
  rw [hprod, hc.map_mul_left, hc.map_mul_right, hc.map_mul_right, hc.map_neg_self, zero_add] at hab
  have hba : c b (-a) = c b (-1 : Fˣ) + c b a := by
    rw [show -a = (-1 : Fˣ) * a by ext; simp, hc.map_mul_right]
  have hbb : c b b = c b (-1 : Fˣ) := hc.map_self b
  have hneg1 : c b (-1 : Fˣ) + c b (-1 : Fˣ) = 0 := by
    rw [← hc.map_mul_right, show (-1 : Fˣ) * (-1 : Fˣ) = 1 by ext; simp, hc.map_one_right]
  rw [hba, hbb] at hab
  have hsum : c a b + c b a = 0 := by
    calc
      c a b + c b a = c a b + ((c b (-1 : Fˣ) + c b a) + c b (-1 : Fˣ)) -
          (c b (-1 : Fˣ) + c b (-1 : Fˣ)) := by abel
      _ = 0 - 0 := by rw [hab, hneg1]
      _ = 0 := sub_zero 0
  exact eq_neg_of_add_eq_zero_left hsum

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
  have h0 : c (g ^ (2 * k + 1)) (g ^ (2 * l + 1)) = 0 := hc.steinberg hab
  rw [hc.map_zpow_left, hc.map_zpow_right, ← mul_zsmul] at h0
  have htwo : (2 : ℤ) • c g g = 0 := by
    change ((2 : ℕ) : ℤ) • c g g = 0
    rw [natCast_zsmul]
    exact hc.two_nsmul_map_self g
  have hgg : c g g = 0 := by
    have hmul : (2 * k + 1) * (2 * l + 1) = (2 * k * l + k + l) * 2 + 1 := by ring
    rw [hmul, add_zsmul, mul_zsmul, htwo, smul_zero, zero_add, one_zsmul] at h0
    exact h0
  exact hc.eq_zero_of_generator_map_self_eq_zero hg hgg a b

private theorem not_isSquare_mul_inv_of_isSquare {s t : Fˣ} (hs : IsSquare s) (ht : ¬ IsSquare t) :
    ¬ IsSquare (s * t⁻¹) := by
  rintro ⟨w, hw⟩
  obtain ⟨u, rfl⟩ := hs
  refine ht ⟨u * w⁻¹, ?_⟩
  have h1 : u * u = w * w * t := mul_inv_eq_iff_eq_mul.mp hw
  have h2 : t = (u * u) * (w * w)⁻¹ := by
    rw [h1, mul_comm (w * w) t, mul_inv_cancel_right]
  rw [h2, mul_inv_rev]
  ac_rfl

private theorem not_isSquare_inv {t : Fˣ} (ht : ¬ IsSquare t) : ¬ IsSquare t⁻¹ := by
  rintro ⟨w, hw⟩
  refine ht ⟨w⁻¹, ?_⟩
  have := congrArg Inv.inv hw
  simpa [mul_inv_rev] using this

private theorem exists_odd_zpow_of_not_isSquare {g : Fˣ} (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g)
    {a : Fˣ} (ha : ¬ IsSquare a) : ∃ k : ℤ, g ^ (2 * k + 1) = a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  rcases Int.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact absurd ⟨g ^ k, by rw [← zpow_add]⟩ ha
  · exact ⟨k, rfl⟩

private theorem exists_not_isSquare_complementary_of_ringChar_ne_zero [IsCyclic Fˣ]
    (hchar : ringChar F ≠ 0) (hchar2 : ¬ CharP F 2) {g : Fˣ}
    (hg_nsq : ¬ IsSquare g) :
    ∃ a b : Fˣ, ¬ IsSquare a ∧ ¬ IsSquare b ∧ (a : F) + b = 1 := by
  have hprime : Nat.Prime (ringChar F) :=
    (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hchar
  have hp2 : ringChar F ≠ 2 := by
    intro h2
    exact hchar2 (h2 ▸ ringChar.charP F)
  have h1g_ne : 1 - (g : F) ≠ 0 := by
    intro h0
    have hg1 : g = 1 := Units.ext (sub_eq_zero.mp h0).symm
    exact hg_nsq ⟨1, by simp [hg1]⟩
  let u : Fˣ := Units.mk0 (1 - (g : F)) h1g_ne
  by_cases hu : IsSquare u
  · by_cases hneg1 : IsSquare (-1 : Fˣ)
    · have hnegu : IsSquare (-u) := by
        obtain ⟨x, hx⟩ := hneg1
        obtain ⟨y, hy⟩ := hu
        refine ⟨x * y, ?_⟩
        have h : -u = (-1 : Fˣ) * u := by ext; simp
        rw [h, hx, hy]
        ac_rfl
      refine ⟨(-u) * g⁻¹, g⁻¹, not_isSquare_mul_inv_of_isSquare hnegu hg_nsq,
        not_isSquare_inv hg_nsq, ?_⟩
      have hg0 : (g : F) ≠ 0 := g.ne_zero
      simp only [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, u, Units.val_mk0]
      field_simp
      ring
    · have : CharP F (ringChar F) := ringChar.charP F
      have hp3 : 3 ≤ ringChar F := by
        have := hprime.two_le
        omega
      have hcast_ne : ∀ n : ℕ, 0 < n → n < ringChar F → (n : F) ≠ 0 := by
        intro n hn0 hnp h0
        have hdvd : ringChar F ∣ n := (CharP.cast_eq_zero_iff F (ringChar F) n).mp h0
        exact Nat.not_lt_of_ge (Nat.le_of_dvd hn0 hdvd) hnp
      let P : ℕ → Prop := fun n ↦
        ∃ h : (n : F) ≠ 0, ¬ IsSquare (Units.mk0 (n : F) h)
      have hp1_prop : P (ringChar F - 1) := by
        have hne : ((ringChar F - 1 : ℕ) : F) ≠ 0 :=
          hcast_ne (ringChar F - 1) (by omega) (by omega)
        refine ⟨hne, ?_⟩
        have hval : Units.mk0 ((ringChar F - 1 : ℕ) : F) hne = (-1 : Fˣ) := by
          ext
          have hadd : ((ringChar F - 1 : ℕ) : F) + 1 = 0 := by
            rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ ringChar F),
              CharP.cast_eq_zero F (ringChar F)]
          exact eq_neg_of_add_eq_zero_left hadd
        rwa [hval]
      have hex : ∃ n, P n := ⟨ringChar F - 1, hp1_prop⟩
      classical
      set m := Nat.find hex
      have hm_spec : P m := Nat.find_spec hex
      obtain ⟨hm_ne, hm_nsq⟩ := hm_spec
      have hm_ge2 : 2 ≤ m := by
        by_contra hlt
        have hm01 : m = 0 ∨ m = 1 := by omega
        rcases hm01 with hm0 | hm1
        · exact hm_ne (by rw [hm0, Nat.cast_zero])
        · apply hm_nsq
          refine ⟨1, ?_⟩
          ext
          simp only [Units.val_mk0, hm1, Nat.cast_one, mul_one, Units.val_one]
      have hm1_ne : ((m - 1 : ℕ) : F) ≠ 0 := by
        intro h0
        have hdvd : ringChar F ∣ (m - 1) := (CharP.cast_eq_zero_iff F (ringChar F) (m - 1)).mp h0
        have hle : ringChar F ≤ m - 1 := Nat.le_of_dvd (by omega) hdvd
        have hfind : m ≤ ringChar F - 1 := Nat.find_min' hex hp1_prop
        omega
      have hm1_sq : IsSquare (Units.mk0 ((m - 1 : ℕ) : F) hm1_ne) := by
        by_contra hnsq
        exact Nat.find_min hex (by omega : m - 1 < m) ⟨hm1_ne, hnsq⟩
      let s := Units.mk0 ((m - 1 : ℕ) : F) hm1_ne
      let t := Units.mk0 (m : F) hm_ne
      refine ⟨s * t⁻¹, t⁻¹, not_isSquare_mul_inv_of_isSquare hm1_sq hm_nsq,
        not_isSquare_inv hm_nsq, ?_⟩
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, s, t, Units.val_mk0]
      have hst : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
        rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ m)]
      calc
        ((m - 1 : ℕ) : F) * (m : F)⁻¹ + (m : F)⁻¹
            = (((m - 1 : ℕ) : F) + 1) * (m : F)⁻¹ := by ring
        _ = (m : F) * (m : F)⁻¹ := by rw [hst]
        _ = 1 := mul_inv_cancel₀ hm_ne
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
        have h2k : g ^ (2 * k) = g := by
          rw [two_mul, zpow_add, hk, ← hu]
        rw [zpow_sub, zpow_one, h2k, mul_inv_cancel]
      have h0 : (2 * k - 1) • c g g = 0 := by
        rw [← hc.map_zpow_left, hpow, hc.map_one_left]
      have htwo : (2 : ℤ) • c g g = 0 := by
        change ((2 : ℕ) : ℤ) • c g g = 0
        rw [natCast_zsmul]
        exact hc.two_nsmul_map_self g
      have hgg : c g g = 0 := by
        calc
          c g g = (1 : ℤ) • c g g := (one_zsmul _).symm
          _ = (k * 2 + -(2 * k - 1)) • c g g := by congr 1; ring
          _ = (k * 2) • c g g + -((2 * k - 1) • c g g) := by rw [add_zsmul, neg_zsmul]
          _ = k • ((2 : ℤ) • c g g) + -((2 * k - 1) • c g g) := by rw [mul_zsmul]
          _ = 0 := by rw [htwo, smul_zero, h0, neg_zero, add_zero]
      exact hc.eq_zero_of_generator_map_self_eq_zero hg hgg a b
    · obtain ⟨x, y, hx, hy, hxy⟩ :=
        exists_not_isSquare_complementary_of_ringChar_ne_zero hchar hchar2 hg_sq
      obtain ⟨k, rfl⟩ := exists_odd_zpow_of_not_isSquare hg hx
      obtain ⟨l, rfl⟩ := exists_odd_zpow_of_not_isSquare hg hy
      exact hc.eq_zero_of_odd_complementary hg hxy a b

/-- Every Steinberg pairing on a finite field is identically zero. -/
theorem eq_zero_of_finite [Finite F] (hc : IsSteinbergPairing c) (a b : Fˣ) :
    c a b = 0 := by
  have hchar : ringChar F ≠ 0 := by
    intro h0
    have : CharP F 0 := h0 ▸ ringChar.charP F
    have : CharZero F := CharP.charP_to_charZero F
    exact not_infinite_iff_finite.mpr ‹Finite F›
      (Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective)
  exact hc.eq_zero_of_isCyclic_of_ringChar_ne_zero hchar a b

end Field

end IsSteinbergPairing

end TauCeti
