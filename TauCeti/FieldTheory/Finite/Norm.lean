/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import TauCeti.FieldTheory.Finite.PowNeOne

/-!
# The norm `b ↦ b * b ^ q` and `q`-power fixed elements in a field of order `q²`

Let `K` be a field with `Nat.card K = q ^ 2`. Without choosing a subfield of order `q`, the
elements fixed by the `q`-power map satisfy `c ^ q = c`, and the quadratic norm is
`b ↦ b * b ^ q = b ^ (q + 1)`. This file proves three elementary facts needed for the generation
of finite special unitary groups by unitary transvections:

* `TauCeti.FiniteField.exists_mul_pow_eq`: every `c : K` with `c ^ q = c` is of the form
  `b * b ^ q` for some `b : K`. For `c ≠ 0` this comes from the cyclicity of `Kˣ` of order
  `q ^ 2 - 1 = (q + 1) * (q - 1)`: writing `c = g ^ m` and raising to `q - 1` shows `q + 1 ∣ m`.
* `TauCeti.FiniteField.exists_pow_ne_self`: some element `a : K` satisfies `a ^ q ≠ a`.
* `TauCeti.FiniteField.exists_ne_zero_and_ne_one_and_pow_eq_self`: when `3 ≤ q`, some element
  `c : K` satisfies `c ≠ 0`, `c ≠ 1`, and `c ^ q = c`, obtained as `b ^ (q + 1)` for a unit `b` of
  order not dividing `q + 1`.

Mathlib's `FiniteField.norm_surjective` proves surjectivity of `Algebra.norm L` for an explicit
extension `K / L`; the formulation here avoids constructing the fixed subfield `L` when the
involution is given directly as `x ↦ x ^ q`, matching `TauCeti.FiniteField.PowAddSelf`.
-/

public section

namespace TauCeti.FiniteField

variable {K : Type*} [Field K] {q : ℕ}

/-- **The quadratic norm is onto the `q`-power fixed elements.** In a field `K` with
`Nat.card K = q ^ 2`, every `c : K` satisfying `c ^ q = c` has the form `b * b ^ q`. -/
theorem exists_mul_pow_eq (hK : Nat.card K = q ^ 2) {c : K} (hc : c ^ q = c) :
    ∃ b : K, b * b ^ q = c := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨1, by simpa using hc⟩
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨0, by simp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 hq)
  have hq1 : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Finite.one_lt_card)
  -- Express `c ∈ Kˣ` as a power `g ^ m` of a generator `g` of the cyclic unit group `Kˣ`.
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr (hg (.mk0 c hc0))
  dsimp only at hm
  have hc_pow : c ^ (q - 1) = 1 := by
    refine mul_right_cancel₀ hc0 ?_
    rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hc]
  have hgm : g ^ (m * (q - 1)) = 1 := by
    rw [pow_mul, hm]
    exact Units.ext (by simpa using hc_pow)
  have hord : orderOf g = (q + 1) * (q - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    have hcard := Nat.card_eq_card_units_add_one K
    rw [hK] at hcard
    zify [hq1.le] at hcard ⊢
    linarith
  have hdvd : q + 1 ∣ m := by
    refine (Nat.mul_dvd_mul_iff_right (Nat.sub_pos_of_lt hq1)).mp ?_
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hgm
  obtain ⟨k, rfl⟩ := hdvd
  refine ⟨((g ^ k : Kˣ) : K), ?_⟩
  have hval : (((g ^ ((q + 1) * k) : Kˣ) : K)) = c := by
    simpa using congrArg Units.val hm
  rw [← pow_succ', ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm k, hval]

/-- **The `q`-power map on a field of order `q²` is nontrivial.** -/
theorem exists_pow_ne_self (hK : Nat.card K = q ^ 2) : ∃ a : K, a ^ q ≠ a := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 hq)
  have hq1 : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Finite.one_lt_card)
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_pow_ne_one (k := q - 1) (by omega)
    (by rw [hK, Nat.sub_add_cancel hq1.le]; nlinarith)
  refine ⟨a, fun h ↦ ha1 (mul_right_cancel₀ ha0 ?_)⟩
  rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, h]

/-- **A field of order `q²` with `3 ≤ q` has a `q`-power fixed element other than `0` and `1`.** -/
theorem exists_ne_zero_and_ne_one_and_pow_eq_self (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 ∧ c ^ q = c := by
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 (by omega))
  let _ := Fintype.ofFinite K
  obtain ⟨b, hb0, hb1⟩ := exists_ne_zero_pow_ne_one (k := q + 1) (by omega)
    (by rw [hK]; nlinarith)
  have hb_card : b ^ q ^ 2 = b := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact _root_.FiniteField.pow_card b
  refine ⟨b ^ (q + 1), pow_ne_zero _ hb0, hb1, ?_⟩
  rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, hb_card, ← pow_succ',
    Nat.add_comm]

end TauCeti.FiniteField
