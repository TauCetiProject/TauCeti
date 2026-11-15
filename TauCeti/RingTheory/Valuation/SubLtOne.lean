/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Congruence subrings and subfields of a valuation

Let `v` be a valuation on a ring `B` taking values in a nontrivial linearly ordered commutative
monoid with zero `Γ₀`, and let `f, c : A →+* B` be ring homomorphisms with `v (c a) ≤ 1` for all
`a : A`. The elements `a : A` satisfying `v (f a - c a) < 1` form a subring of `A`:

* closure under addition and negation comes from the ultrametric inequality on `f - c`;
* closure under multiplication rewrites `f (a * b) - c (a * b)` as
  `(f a - c a) * f b + c a * (f b - c b)` and bounds `v (f b) ≤ max (v (f b - c b)) (v (c b)) ≤ 1`.

When `A` is a division ring `K`, this subring is a subfield: for `a ≠ 0`, `v (c a) * v (c a⁻¹) = 1`
together with `v ∘ c ≤ 1` forces `v (c a) = 1`, ultrametricity gives `v (f a) = 1` and hence
`v (f a⁻¹) = 1`, and `f a⁻¹ - c a⁻¹ = f a⁻¹ * (c a - f a) * c a⁻¹` keeps valuation `< 1`.

## Main definitions

* `Valuation.subLtOneSubring`: the subring `{a : A | v (f a - c a) < 1}` of `A`.
* `Valuation.subLtOneSubfield`: the subfield `{a : K | v (f a - c a) < 1}` of a division ring `K`.
-/

public section

namespace Valuation

variable {B Γ₀ : Type*} [Ring B] [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]

section Subring

variable {A : Type*} [Ring A]

/-- **The congruence subring of two ring homomorphisms at a valuation**: for `f, c : A →+* B` with
`v (c a) ≤ 1` for every `a`, the set `{a : A | v (f a - c a) < 1}` is a subring of `A`. -/
def subLtOneSubring (v : Valuation B Γ₀) (f c : A →+* B) (hc : ∀ a, v (c a) ≤ 1) : Subring A where
  carrier := {a : A | v (f a - c a) < 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have hfb : v (f b) ≤ 1 := by
      rw [← sub_add_cancel (f b) (c b)]
      exact (v.map_add _ _).trans (max_le hb.le (hc b))
    have hmul : f (a * b) - c (a * b) = (f a - c a) * f b + c a * (f b - c b) := by
      rw [map_mul, map_mul, sub_mul, mul_sub, sub_add_sub_cancel]
    rw [hmul]
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_right' hfb).trans_lt ha
    · rw [map_mul]
      exact (mul_le_of_le_one_left' (hc a)).trans_lt hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have hadd : f (a + b) - c (a + b) = (f a - c a) + (f b - c b) := by
      rw [map_add, map_add, add_sub_add_comm]
    rw [hadd]
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rwa [f.map_neg, c.map_neg, neg_sub_neg, v.map_sub_swap]

/-- An element lies in `v.subLtOneSubring f c hc` if and only if `v (f a - c a) < 1`. -/
@[simp]
theorem mem_subLtOneSubring {v : Valuation B Γ₀} {f c : A →+* B} {hc : ∀ a, v (c a) ≤ 1} {a : A} :
    a ∈ v.subLtOneSubring f c hc ↔ v (f a - c a) < 1 :=
  Iff.rfl

/-- The underlying set of `v.subLtOneSubring f c hc` is `{a : A | v (f a - c a) < 1}`. -/
@[simp]
theorem coe_subLtOneSubring (v : Valuation B Γ₀) (f c : A →+* B) (hc : ∀ a, v (c a) ≤ 1) :
    (v.subLtOneSubring f c hc : Set A) = {a : A | v (f a - c a) < 1} :=
  Set.ext fun _ ↦ mem_subLtOneSubring

end Subring

section Subfield

variable {K : Type*} [DivisionRing K]

/-- **The congruence subfield of two ring homomorphisms out of a division ring**: for
`f, c : K →+* B` with `v (c a) ≤ 1` for every `a`, `{a : K | v (f a - c a) < 1}` is a subfield of
`K`. -/
def subLtOneSubfield (v : Valuation B Γ₀) (f c : K →+* B) (hc : ∀ a, v (c a) ≤ 1) : Subfield K :=
  { v.subLtOneSubring f c hc with
    inv_mem' := fun {a} ha ↦ by
      rw [Subring.mem_carrier, mem_subLtOneSubring] at ha ⊢
      rcases eq_or_ne a 0 with rfl | ha0
      · simp
      have hmul_c : v (c a) * v (c a⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
      have hvca : v (c a) = 1 :=
        le_antisymm (hc a) (by rw [← hmul_c]; exact mul_le_of_le_one_right' (hc a⁻¹))
      have hvfa : v (f a) = 1 := by
        rw [← sub_add_cancel (f a) (c a), v.map_add_eq_of_lt_right (hvca ▸ ha), hvca]
      have hvfa_inv : v (f a⁻¹) = 1 := by
        have h : v (f a) * v (f a⁻¹) = 1 := by
          rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
        rwa [hvfa, one_mul] at h
      have hinv : f a⁻¹ - c a⁻¹ = f a⁻¹ * (c a - f a) * c a⁻¹ := by
        calc f a⁻¹ - c a⁻¹
          _ = f a⁻¹ * c (a * a⁻¹) - f (a⁻¹ * a) * c a⁻¹ := by
              rw [mul_inv_cancel₀ ha0, inv_mul_cancel₀ ha0, map_one, map_one, mul_one, one_mul]
          _ = f a⁻¹ * (c a * c a⁻¹) - f a⁻¹ * f a * c a⁻¹ := by rw [map_mul, map_mul]
          _ = f a⁻¹ * (c a - f a) * c a⁻¹ := by rw [← mul_assoc, ← sub_mul, ← mul_sub]
      rw [hinv, map_mul, map_mul, hvfa_inv, one_mul, v.map_sub_swap]
      exact (mul_le_of_le_one_right' (hc a⁻¹)).trans_lt ha }

/-- An element lies in `v.subLtOneSubfield f c hc` if and only if `v (f a - c a) < 1`. -/
@[simp]
theorem mem_subLtOneSubfield {v : Valuation B Γ₀} {f c : K →+* B} {hc : ∀ a, v (c a) ≤ 1} {a : K} :
    a ∈ v.subLtOneSubfield f c hc ↔ v (f a - c a) < 1 :=
  Iff.rfl

/-- The underlying set of `v.subLtOneSubfield f c hc` is `{a : K | v (f a - c a) < 1}`. -/
@[simp]
theorem coe_subLtOneSubfield (v : Valuation B Γ₀) (f c : K →+* B) (hc : ∀ a, v (c a) ≤ 1) :
    (v.subLtOneSubfield f c hc : Set K) = {a : K | v (f a - c a) < 1} :=
  Set.ext fun _ ↦ mem_subLtOneSubfield

/-- The underlying subring of `v.subLtOneSubfield f c hc` is `v.subLtOneSubring f c hc`. -/
@[simp]
theorem toSubring_subLtOneSubfield (v : Valuation B Γ₀) (f c : K →+* B) (hc : ∀ a, v (c a) ≤ 1) :
    (v.subLtOneSubfield f c hc).toSubring = v.subLtOneSubring f c hc :=
  Subring.ext fun _ ↦ Iff.rfl

end Subfield

end Valuation

end
