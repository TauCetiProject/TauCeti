/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.PrimitiveReduced

/-!
# Negative definite forms and the sign transport

The form–ideal dictionary at a negative discriminant `-n` is stated for positive definite forms
(`posDefProperClassEquivPic`). A negative definite form enters it through negation: `f ↦ -f`
preserves the discriminant (`BinaryQuadraticForm.discrim_neg`), the content
(`BinaryQuadraticForm.content_neg`) and the proper automorphs (`MulAction.stabilizer_neg`), and
it commutes with the proper action of `SL(2, ℤ)`. It therefore exchanges the primitive positive
definite forms of discriminant `-n` with the primitive negative definite ones
(`negDef n`), and induces an equivalence between their proper classes,
`posDefProperClassEquivNegDefProperClass`, whose inverse is again negation. The count of the
negative definite classes is the count of the positive definite ones
(`nat_card_negDefProperClass`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.negDef`: the negative definite forms of discriminant `-n`.
* `TauCeti.BinaryQuadraticForm.NegDefProperClass`: their primitive proper classes.
* `TauCeti.BinaryQuadraticForm.posDefProperClassEquivNegDefProperClass`: negation of proper
  classes.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2.
-/

public section

open scoped MatrixGroups Finset

namespace TauCeti.BinaryQuadraticForm

/-- A form has discriminant `-D` and positive leading coefficient exactly when its negative has
discriminant `-D` and negative leading coefficient. -/
private theorem neg_discrim_eq_and_lt_zero_iff {D : ℕ} {f : BinaryQuadraticForm ℤ} :
    ((-f).discrim = -D ∧ (-f).a < 0) ↔ (f.discrim = -D ∧ 0 < f.a) := by
  rw [discrim_neg, neg_a, neg_lt_zero]

/-- The negative definite integral binary quadratic forms of discriminant `-D`, for `D ≠ 0`, as a
sub-action of `SL(2, ℤ)`: the forms of discriminant `-D` whose leading coefficient is negative.
They are the negatives of the positive definite forms (`neg_mem_negDef_iff`). -/
def negDef (D : ℕ) [NeZero D] : SubMulAction SL(2, ℤ) (BinaryQuadraticForm ℤ) where
  carrier := {f | f.discrim = -D ∧ f.a < 0}
  smul_mem' γ f hf := by
    have h := (posDef D).smul_mem γ
      (mem_posDef.mpr (neg_discrim_eq_and_lt_zero_iff.mp (by rwa [neg_neg])))
    rw [mem_posDef, ← neg_discrim_eq_and_lt_zero_iff, smul_neg, neg_neg] at h
    exact h

/-- A form lies in `negDef D` exactly when its discriminant is `-D` and its leading coefficient is
negative. -/
@[simp]
theorem mem_negDef {D : ℕ} [NeZero D] {f : BinaryQuadraticForm ℤ} :
    f ∈ negDef D ↔ f.discrim = -D ∧ f.a < 0 :=
  Iff.rfl

/-- The negative of a form is negative definite of discriminant `-D` exactly when the form is
positive definite of discriminant `-D`. -/
theorem neg_mem_negDef_iff {D : ℕ} [NeZero D] {f : BinaryQuadraticForm ℤ} :
    -f ∈ negDef D ↔ f ∈ posDef D := by
  rw [mem_negDef, mem_posDef]
  exact neg_discrim_eq_and_lt_zero_iff

/-- The negative of a form is positive definite of discriminant `-D` exactly when the form is
negative definite of discriminant `-D`. -/
theorem neg_mem_posDef_iff {D : ℕ} [NeZero D] {f : BinaryQuadraticForm ℤ} :
    -f ∈ posDef D ↔ f ∈ negDef D := by
  rw [← neg_mem_negDef_iff, neg_neg]

/-- A form is primitive negative definite of discriminant `-n` exactly when it has discriminant
`-n`, negative leading coefficient and coprime coefficients. -/
theorem mem_negDef_inf_primitiveForms (n : ℕ) [NeZero n] {f : BinaryQuadraticForm ℤ} :
    f ∈ negDef n ⊓ primitiveForms (-n) ↔ f.discrim = -n ∧ f.a < 0 ∧ f.IsPrimitive :=
  calc f ∈ negDef n ⊓ primitiveForms (-n) ↔ f ∈ negDef n ∧ f ∈ primitiveForms (-n) := Iff.rfl
    _ ↔ _ := by rw [mem_negDef, mem_primitiveForms]; tauto

/-- Negation exchanges the primitive positive definite forms of discriminant `-n` with the
primitive negative definite ones. -/
theorem neg_mem_negDef_inf_primitiveForms_iff (n : ℕ) [NeZero n] {f : BinaryQuadraticForm ℤ} :
    -f ∈ negDef n ⊓ primitiveForms (-n) ↔ f ∈ posDef n ⊓ primitiveForms (-n) := by
  rw [mem_negDef_inf_primitiveForms, mem_posDef_inf_primitiveForms, isPrimitive_iff,
    isPrimitive_iff, content_neg, discrim_neg, neg_a, neg_lt_zero]

/-- Negation exchanges the primitive negative definite forms of discriminant `-n` with the
primitive positive definite ones. -/
theorem neg_mem_posDef_inf_primitiveForms_iff (n : ℕ) [NeZero n] {f : BinaryQuadraticForm ℤ} :
    -f ∈ posDef n ⊓ primitiveForms (-n) ↔ f ∈ negDef n ⊓ primitiveForms (-n) := by
  rw [← neg_mem_negDef_inf_primitiveForms_iff, neg_neg]

/-- The proper equivalence classes of primitive negative definite forms of discriminant `-n`. -/
abbrev NegDefProperClass (n : ℕ) [NeZero n] :=
  MulAction.orbitRel.Quotient SL(2, ℤ) ↥(negDef n ⊓ primitiveForms (-n))

/-- Negation, from the primitive positive definite forms of discriminant `-n` to the primitive
negative definite ones. -/
private def negPosDefEquiv (n : ℕ) [NeZero n] :
    ↥(posDef n ⊓ primitiveForms (-n)) ≃ ↥(negDef n ⊓ primitiveForms (-n)) where
  toFun f := ⟨-f, (neg_mem_negDef_inf_primitiveForms_iff n).mpr f.property⟩
  invFun f := ⟨-f, (neg_mem_posDef_inf_primitiveForms_iff n).mpr f.property⟩
  left_inv f := Subtype.ext (neg_neg f.val)
  right_inv f := Subtype.ext (neg_neg f.val)

/-- **Negation of forms identifies the positive and negative definite proper classes.** The map
`f ↦ -f` preserves the discriminant and primitivity and commutes with the proper action, so it
induces a bijection from the proper classes of primitive positive definite forms of discriminant
`-n` to those of primitive negative definite forms. Its inverse is again negation
(`posDefProperClassEquivNegDefProperClass_symm_mk`). -/
def posDefProperClassEquivNegDefProperClass (n : ℕ) [NeZero n] :
    PosDefProperClass n ≃ NegDefProperClass n :=
  Quotient.congr (negPosDefEquiv n) fun f g ↦ by
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.ext_iff,
      SubMulAction.val_smul, negPosDefEquiv, Equiv.coe_fn_mk, smul_neg, neg_inj]

/-- Negation sends the proper class of a primitive positive definite form to the proper class of
its negative. -/
@[simp]
theorem posDefProperClassEquivNegDefProperClass_mk (n : ℕ) [NeZero n]
    (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    posDefProperClassEquivNegDefProperClass n (Quotient.mk'' f) =
      Quotient.mk'' ⟨-f, (neg_mem_negDef_inf_primitiveForms_iff n).mpr f.property⟩ :=
  (rfl)

/-- The inverse of `posDefProperClassEquivNegDefProperClass` is again negation. -/
@[simp]
theorem posDefProperClassEquivNegDefProperClass_symm_mk (n : ℕ) [NeZero n]
    (f : ↥(negDef n ⊓ primitiveForms (-n))) :
    (posDefProperClassEquivNegDefProperClass n).symm (Quotient.mk'' f) =
      Quotient.mk'' ⟨-f, (neg_mem_posDef_inf_primitiveForms_iff n).mpr f.property⟩ :=
  (rfl)

/-- There are finitely many proper classes of primitive negative definite forms of discriminant
`-n`. -/
instance finite_negDefProperClass (n : ℕ) [NeZero n] : Finite (NegDefProperClass n) :=
  .of_equiv _ (posDefProperClassEquivNegDefProperClass n)

/-- **The number of proper classes of primitive negative definite forms** of discriminant `-n` is
the number of primitive reduced (positive definite) forms of discriminant `-n`. -/
theorem nat_card_negDefProperClass (n : ℕ) [NeZero n] :
    Nat.card (NegDefProperClass n) = #(primitiveReducedForms n) := by
  rw [← Nat.card_congr (posDefProperClassEquivNegDefProperClass n), nat_card_posDefProperClass]

end TauCeti.BinaryQuadraticForm
