/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Agreement locus of two ring homomorphisms modulo a valuation

Let `v : Valuation L Γ₀` be a valuation on a ring `L` with nontrivial value monoid `Γ₀` (so that
`0 < 1`), and let `f, g : R →+* L` be two ring homomorphisms with `v (g x) ≤ 1` for all `x : R`.
The set `{x : R | v (f x - g x) < 1}` of elements on which `f` and `g` agree modulo `v < 1` is a
subring of `R` (`Valuation.eqModSubring`). Notably, `f` is not assumed bounded by `1` in advance:
for `x` in this locus, `v (f x) ≤ 1` follows from `v (f x - g x) < 1` and `v (g x) ≤ 1` by the
ultrametric inequality.

When the domain `E` is a division ring, `v (g x) ≤ 1` forces `v (g x) = 1` for every nonzero `x`,
hence `v (f x) = 1` on the locus; applying `v` to the identity
`f x * (f x⁻¹ - g x⁻¹) * g x = -(f x - g x)` then gives closure under inverses, so the locus is a
subfield (`Valuation.eqModSubfield`). For a field extension `E / F` on whose base `f` and `g`
agree modulo `v < 1`, this promotes to an intermediate field (`Valuation.eqModIntermediateField`),
allowing agreement modulo `v < 1` on all of `E` to be checked on field generators over `F`.

## Main definitions

* `Valuation.eqModSubring`: the subring `{x : R | v (f x - g x) < 1}` where `f` and `g` agree
  modulo `v < 1`.
* `Valuation.eqModSubfield`: the subfield `{x : E | v (f x - g x) < 1}` for a division ring `E`.
* `Valuation.eqModIntermediateField`: the intermediate field `{x : E | v (f x - g x) < 1}` of
  `E / F` when `f` and `g` agree modulo `v < 1` on `F`.

## References

* Mathlib's `RingHom.eqLocus`, `RingHom.eqLocusField`, and `Valuation.ltAddSubgroup`.
-/

public section

namespace Valuation

variable {L Γ₀ : Type*} [Ring L] [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀]

/-- The subring of elements of `R` where two ring homomorphisms `f, g : R →+* L` agree modulo
`v < 1`, assuming `v (g x) ≤ 1` for all `x : R`. -/
def eqModSubring {R : Type*} [Ring R] (v : Valuation L Γ₀) (f g : R →+* L)
    (hg : ∀ x : R, v (g x) ≤ 1) : Subring R where
  carrier := {x : R | v (f x - g x) < 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq, map_add, map_add, add_sub_add_comm]
    exact v.map_add_lt hx hy
  neg_mem' {x} hx := by
    rw [Set.mem_ofPred_eq, _root_.map_neg, _root_.map_neg, neg_sub_neg, ← neg_sub, v.map_neg]
    exact hx
  mul_mem' {x y} hx hy := by
    have hfx : v (f x) ≤ 1 := by
      simpa only [sub_add_cancel] using
        (v.map_add (f x - g x) (g x)).trans (max_le hx.le (hg x))
    have hmul : f x * f y - g x * g y = (f x - g x) * g y + f x * (f y - g y) := by
      rw [sub_mul, mul_sub, add_comm, sub_add_sub_cancel]
    rw [Set.mem_ofPred_eq, map_mul, map_mul, hmul]
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_right' (hg y)).trans_lt hx
    · rw [map_mul]
      exact (mul_le_of_le_one_left' hfx).trans_lt hy

/-- Membership in `Valuation.eqModSubring` is characterized by `v (f x - g x) < 1`. -/
@[simp]
theorem mem_eqModSubring {R : Type*} [Ring R] {v : Valuation L Γ₀} {f g : R →+* L}
    {hg : ∀ x : R, v (g x) ≤ 1} {x : R} :
    x ∈ v.eqModSubring f g hg ↔ v (f x - g x) < 1 :=
  Iff.rfl

/-- The underlying set of `Valuation.eqModSubring` is `{x | v (f x - g x) < 1}`. -/
@[simp]
theorem coe_eqModSubring {R : Type*} [Ring R] (v : Valuation L Γ₀) (f g : R →+* L)
    (hg : ∀ x : R, v (g x) ≤ 1) :
    (v.eqModSubring f g hg : Set R) = {x : R | v (f x - g x) < 1} :=
  Set.ext fun _ ↦ mem_eqModSubring

/-- The subfield of elements of a division ring `E` where two ring homomorphisms `f, g : E →+* L`
agree modulo `v < 1`, assuming `v (g x) ≤ 1` for all `x : E`. -/
def eqModSubfield {E : Type*} [DivisionRing E] (v : Valuation L Γ₀) (f g : E →+* L)
    (hg : ∀ x : E, v (g x) ≤ 1) : Subfield E where
  __ := v.eqModSubring f g hg
  inv_mem' x hx := by
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hx' : v (f x - g x) < 1 := hx
    have hgx : v (g x) = 1 := by
      refine le_antisymm (hg x) ?_
      have h1 : (1 : Γ₀) = v (g x) * v (g x⁻¹) := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
      exact h1.trans_le (mul_le_of_le_one_right' (hg x⁻¹))
    have hfx : v (f x) = 1 := by
      simpa only [sub_add_cancel, hgx] using
        Valuation.map_add_eq_of_lt_right v (hx'.trans_eq hgx.symm)
    have hinv : f x * (f x⁻¹ - g x⁻¹) * g x = -(f x - g x) := by
      rw [mul_sub, sub_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul,
        mul_assoc, ← map_mul, inv_mul_cancel₀ hx0, map_one, mul_one, neg_sub]
    have hval := congrArg v hinv
    rw [map_mul, map_mul, hfx, hgx, one_mul, mul_one, v.map_neg] at hval
    exact hval.trans_lt hx'

/-- Membership in `Valuation.eqModSubfield` is characterized by `v (f x - g x) < 1`. -/
@[simp]
theorem mem_eqModSubfield {E : Type*} [DivisionRing E] {v : Valuation L Γ₀} {f g : E →+* L}
    {hg : ∀ x : E, v (g x) ≤ 1} {x : E} :
    x ∈ v.eqModSubfield f g hg ↔ v (f x - g x) < 1 :=
  Iff.rfl

/-- The underlying set of `Valuation.eqModSubfield` is `{x | v (f x - g x) < 1}`. -/
@[simp]
theorem coe_eqModSubfield {E : Type*} [DivisionRing E] (v : Valuation L Γ₀) (f g : E →+* L)
    (hg : ∀ x : E, v (g x) ≤ 1) :
    (v.eqModSubfield f g hg : Set E) = {x : E | v (f x - g x) < 1} :=
  Set.ext fun _ ↦ mem_eqModSubfield

/-- The underlying subring of `Valuation.eqModSubfield` is `Valuation.eqModSubring`. -/
@[simp]
theorem toSubring_eqModSubfield {E : Type*} [DivisionRing E] (v : Valuation L Γ₀) (f g : E →+* L)
    (hg : ∀ x : E, v (g x) ≤ 1) :
    (v.eqModSubfield f g hg).toSubring = v.eqModSubring f g hg := by
  ext x
  rw [Subfield.mem_toSubring, mem_eqModSubfield, mem_eqModSubring]

/-- The intermediate field of `E / F` consisting of elements where two ring homomorphisms
`f, g : E →+* L` agree modulo `v < 1`, assuming `v (g x) ≤ 1` for all `x : E` and that `f` and
`g` agree modulo `v < 1` on `F`. -/
def eqModIntermediateField (v : Valuation L Γ₀) (F : Type*) {E : Type*} [Field F] [Field E]
    [Algebra F E] (f g : E →+* L) (hg : ∀ x : E, v (g x) ≤ 1)
    (hF : ∀ c : F, v (f (algebraMap F E c) - g (algebraMap F E c)) < 1) :
    IntermediateField F E :=
  (v.eqModSubfield f g hg).toIntermediateField hF

/-- Membership in `Valuation.eqModIntermediateField` is characterized by `v (f x - g x) < 1`. -/
@[simp]
theorem mem_eqModIntermediateField {F E : Type*} [Field F] [Field E] [Algebra F E]
    {v : Valuation L Γ₀} {f g : E →+* L} {hg : ∀ x : E, v (g x) ≤ 1}
    {hF : ∀ c : F, v (f (algebraMap F E c) - g (algebraMap F E c)) < 1} {x : E} :
    x ∈ v.eqModIntermediateField F f g hg hF ↔ v (f x - g x) < 1 :=
  Iff.rfl

/-- The underlying set of `Valuation.eqModIntermediateField` is `{x | v (f x - g x) < 1}`. -/
@[simp]
theorem coe_eqModIntermediateField (v : Valuation L Γ₀) (F : Type*) {E : Type*} [Field F]
    [Field E] [Algebra F E] (f g : E →+* L) (hg : ∀ x : E, v (g x) ≤ 1)
    (hF : ∀ c : F, v (f (algebraMap F E c) - g (algebraMap F E c)) < 1) :
    (v.eqModIntermediateField F f g hg hF : Set E) = {x : E | v (f x - g x) < 1} :=
  Set.ext fun _ ↦ mem_eqModIntermediateField

/-- The underlying subfield of `Valuation.eqModIntermediateField` is `Valuation.eqModSubfield`. -/
@[simp]
theorem toSubfield_eqModIntermediateField (v : Valuation L Γ₀) (F : Type*) {E : Type*} [Field F]
    [Field E] [Algebra F E] (f g : E →+* L) (hg : ∀ x : E, v (g x) ≤ 1)
    (hF : ∀ c : F, v (f (algebraMap F E c) - g (algebraMap F E c)) < 1) :
    (v.eqModIntermediateField F f g hg hF).toSubfield = v.eqModSubfield f g hg := by
  ext x
  rw [IntermediateField.mem_toSubfield, mem_eqModIntermediateField, mem_eqModSubfield]

end Valuation

end
