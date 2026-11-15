/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ClassNumber
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Composition
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Reflection
public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-!
# Positive definite proper classes and the ring class field

Let `n > 0` with `-n ≡ 0, 1 mod 4`, let `K = ℚ(√(-n))` and let `O` be the quadratic order of
discriminant `-n`, with ring class field `H_O`. Composing the bijection between proper classes of
primitive positive definite forms of discriminant `-n` and the Picard group of `O`
(`posDefProperClassEquivPic`) with ring-class reciprocity `Pic O ≃* Gal(H_O / K)`
(`TauCeti.ClassFieldTheory.ringClassArtinEquiv`) gives

```text
Gal(H_O / K) ≃ Pic O ≃ proper classes of primitive positive definite forms of discriminant -n.
```

The composite sends the proper class of `f = (a, b, c)` to the Artin symbol in `H_O` of the
ideal `aℤ + ((-b + √(-n))/2)ℤ` of `O` (`posDefProperClassEquivGal_mk`). It carries the class of
the principal form to the identity and only that class (`posDefProperClassEquivGal_eq_one_iff`),
the opposite form to the inverse (`posDefProperClassEquivGal_mk_eq_inv_of_eq_reflected`), and a
Dirichlet composition to the product (`posDefProperClassEquivGal_mk_mul_of_united`); every product
in the Galois group arises this way
(`exists_posDefProperClassEquivGal_mul_posDefProperClassEquivGal_eq`). So Gauss composition of
forms is the group law of `Gal(H_O / K)`.

Since each proper class contains exactly one primitive reduced form, the Artin symbols of the
ideals of the primitive reduced forms of discriminant `-n` list the elements of `Gal(H_O / K)`
without repetition (`ringClassArtinMap_primitiveReducedForms_bijective`), and the degree
`[H_O : K]` is the number of primitive reduced forms
(`finrank_ringClassField_eq_card_primitiveReducedForms`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.posDefProperClassEquivGal`: proper classes of primitive positive
  definite forms of discriminant `-n` are in bijection with the Galois group of the ring class
  field of the order of discriminant `-n`.

## Main results

* `TauCeti.BinaryQuadraticForm.posDefProperClassEquivGal_mk`: the bijection sends the class of a
  form to the Artin symbol of its ideal.
* `TauCeti.BinaryQuadraticForm.posDefProperClassEquivGal_mk_mul_of_united` and
  `TauCeti.BinaryQuadraticForm.exists_posDefProperClassEquivGal_mul_posDefProperClassEquivGal_eq`:
  composition of forms is multiplication in the Galois group.
* `TauCeti.BinaryQuadraticForm.posDefProperClassEquivGal_eq_one_iff`: the principal class is the
  only class with trivial Artin symbol.
* `TauCeti.BinaryQuadraticForm.posDefProperClassEquivGal_mk_eq_inv_of_eq_reflected`: the opposite
  form has the inverse Artin symbol.
* `TauCeti.BinaryQuadraticForm.ringClassArtinMap_primitiveReducedForms_bijective`: the Artin
  symbols of the ideals of the primitive reduced forms enumerate the Galois group.
* `TauCeti.BinaryQuadraticForm.finrank_ringClassField_eq_card_primitiveReducedForms`: the degree
  of the ring class field is the number of primitive reduced forms.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7, and §9, Theorem 9.18.
-/

public section
noncomputable section

open Finset

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields ClassFieldTheory

variable (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)

/-- **Proper classes of forms and the Galois group of the ring class field.** The proper classes
of primitive positive definite forms of discriminant `-n` are in bijection with the Galois group
of the ring class field of the quadratic order of discriminant `-n` over `ℚ(√(-n))`: the
bijection with the Picard group of the order, followed by ring-class reciprocity. -/
def posDefProperClassEquivGal :
    PosDefProperClass n ≃
      Gal(ringClassField (QuadraticOrder.numberFieldOrder (-n) hn) /
        QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) :=
  (posDefProperClassEquivPic n hn).trans
    (ringClassArtinEquiv (QuadraticOrder.numberFieldOrder (-n) hn)).toEquiv

/-- The bijection with the Galois group is ring-class reciprocity applied to the Picard class. -/
theorem posDefProperClassEquivGal_apply (q : PosDefProperClass n) :
    posDefProperClassEquivGal n hn q =
      ringClassArtinEquiv (QuadraticOrder.numberFieldOrder (-n) hn)
        (posDefProperClassToPic n hn q) := by
  -- `Equiv.trans_apply` does not rewrite here: the target of `posDefProperClassEquivPic` spells
  -- the field `ℚ(√(-n))` differently, up to a cast that is only definitionally equal.
  unfold posDefProperClassEquivGal
  exact congrArg (ringClassArtinEquiv (QuadraticOrder.numberFieldOrder (-n) hn))
    (posDefProperClassEquivPic_apply n hn q)

/-- **The Artin symbol of a form.** The proper class of a primitive positive definite form
`(a, b, c)` of discriminant `-n` corresponds to the Artin symbol in the ring class field of the
ideal `aℤ + ((-b + √(-n))/2)ℤ` of the order of discriminant `-n`. -/
theorem posDefProperClassEquivGal_mk (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    posDefProperClassEquivGal n hn (Quotient.mk _ f) =
      ringClassArtinMap (QuadraticOrder.numberFieldOrder (-n) hn)
        ((f : BinaryQuadraticForm ℤ).invertibleFractionalIdeal (-n)
          ((mem_posDef_inf_primitiveForms n).mp f.2).1
          ((mem_posDef_inf_primitiveForms n).mp f.2).2.2) := by
  rw [posDefProperClassEquivGal_apply, posDefProperClassToPic_mk, picClass_def,
    ringClassArtinMap_apply]

/-- **Dirichlet composition is multiplication in the Galois group.** If primitive positive
definite forms `f = (a, B, a'C)` and `g = (a', B, aC)` of discriminant `-n` have Dirichlet
composition `h = (aa', B, C)`, then the Artin symbol of the class of `h` is the product of those
of `f` and `g`. -/
theorem posDefProperClassEquivGal_mk_mul_of_united {a a' B C : ℤ}
    {f g h : ↥(posDef n ⊓ primitiveForms (-n))}
    (hf : (f : BinaryQuadraticForm ℤ) = ⟨a, B, a' * C⟩)
    (hg : (g : BinaryQuadraticForm ℤ) = ⟨a', B, a * C⟩)
    (hh : (h : BinaryQuadraticForm ℤ) = ⟨a * a', B, C⟩) :
    posDefProperClassEquivGal n hn (Quotient.mk _ f) *
        posDefProperClassEquivGal n hn (Quotient.mk _ g) =
      posDefProperClassEquivGal n hn (Quotient.mk _ h) := by
  simp only [posDefProperClassEquivGal_apply, ← map_mul,
    posDefProperClassToPic_mk_mul_of_united n hn hf hg hh]

/-- **Every product in the Galois group is a Dirichlet composition.** Any two proper classes of
primitive positive definite forms of discriminant `-n` have representatives `f = (a, B, a'C)` and
`g = (a', B, aC)`; their composition `h = (aa', B, C)` is again primitive positive definite, and
its Artin symbol is the product of the Artin symbols of the two classes. -/
theorem exists_posDefProperClassEquivGal_mul_posDefProperClassEquivGal_eq
    (q₁ q₂ : PosDefProperClass n) :
    ∃ (a a' B C : ℤ) (f g h : ↥(posDef n ⊓ primitiveForms (-n))),
      Quotient.mk _ f = q₁ ∧ Quotient.mk _ g = q₂ ∧
      (f : BinaryQuadraticForm ℤ) = ⟨a, B, a' * C⟩ ∧ (g : BinaryQuadraticForm ℤ) = ⟨a', B, a * C⟩ ∧
      (h : BinaryQuadraticForm ℤ) = ⟨a * a', B, C⟩ ∧
      posDefProperClassEquivGal n hn q₁ * posDefProperClassEquivGal n hn q₂ =
        posDefProperClassEquivGal n hn (Quotient.mk _ h) := by
  obtain ⟨a, a', B, C, f, g, h, hfq, hgq, hf, hg, hh, -⟩ :=
    exists_posDefProperClassToPic_mul_posDefProperClassToPic_eq n hn q₁ q₂
  refine ⟨a, a', B, C, f, g, h, hfq, hgq, hf, hg, hh, ?_⟩
  rw [← hfq, ← hgq]
  exact posDefProperClassEquivGal_mk_mul_of_united n hn hf hg hh

/-- **The principal class has trivial Artin symbol.** -/
theorem posDefProperClassEquivGal_principalForm :
    posDefProperClassEquivGal n hn
      (Quotient.mk _ ⟨principalForm (-n), principalForm_mem_posDef_inf_primitiveForms n hn⟩) =
        1 := by
  rw [posDefProperClassEquivGal_apply, posDefProperClassToPic_principalForm, map_one]

/-- **Only the principal class has trivial Artin symbol.** A proper class of primitive positive
definite forms of discriminant `-n` has trivial Artin symbol in the ring class field exactly when
it is the class of the principal form. -/
theorem posDefProperClassEquivGal_eq_one_iff (q : PosDefProperClass n) :
    posDefProperClassEquivGal n hn q = 1 ↔
      q = Quotient.mk _ ⟨principalForm (-n), principalForm_mem_posDef_inf_primitiveForms n hn⟩ := by
  rw [posDefProperClassEquivGal_apply, MulEquiv.map_eq_one_iff,
    posDefProperClassToPic_eq_one_iff]

/-- **The opposite form has the inverse Artin symbol.** -/
theorem posDefProperClassEquivGal_mk_eq_inv_of_eq_reflected
    {f g : ↥(posDef n ⊓ primitiveForms (-n))}
    (hg : (g : BinaryQuadraticForm ℤ) = (f : BinaryQuadraticForm ℤ).reflected) :
    posDefProperClassEquivGal n hn (Quotient.mk _ g) =
      (posDefProperClassEquivGal n hn (Quotient.mk _ f))⁻¹ := by
  rw [posDefProperClassEquivGal_apply, posDefProperClassEquivGal_apply,
    posDefProperClassToPic_mk_eq_inv_of_eq_reflected n hn hg, map_inv]

/-- **The Galois group of the ring class field from reduced forms.** The Artin symbols in the ring
class field of the ideals `aℤ + ((-b + √(-n))/2)ℤ` of the primitive reduced forms `(a, b, c)` of
discriminant `-n` are all the elements of its Galois group over `ℚ(√(-n))`, each exactly once. -/
theorem ringClassArtinMap_primitiveReducedForms_bijective :
    Function.Bijective fun f : primitiveReducedForms n ↦
      ringClassArtinMap (QuadraticOrder.numberFieldOrder (-n) hn)
        ((f : BinaryQuadraticForm ℤ).invertibleFractionalIdeal (-n)
          ((mem_posDef_inf_primitiveForms n).mp
            (mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2)).1
          ((mem_posDef_inf_primitiveForms n).mp
            (mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2)).2.2) := by
  simpa only [Function.comp_def, picClass_def, ringClassArtinMap_apply] using
    (ringClassArtinEquiv (QuadraticOrder.numberFieldOrder (-n) hn)).bijective.comp
      (picClass_primitiveReducedForms_bijective n hn)

/-- **The degree of the ring class field is the number of reduced forms.** The ring class field of
the quadratic order of discriminant `-n` has degree over `ℚ(√(-n))` equal to the number of
primitive reduced forms of discriminant `-n`. -/
theorem finrank_ringClassField_eq_card_primitiveReducedForms :
    Module.finrank (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)
        (ringClassField (QuadraticOrder.numberFieldOrder (-n) hn)) =
      #(primitiveReducedForms n) := by
  rw [finrank_ringClassField, nat_card_pic]

section Examples

/-- **The ring class field of discriminant `-23` is cubic.** The order of discriminant `-23` is
the ring of integers of `ℚ(√(-23))`, and its ring class field has degree three over `ℚ(√(-23))`,
certified by the three primitive reduced forms `x² + x y + 6 y²` and `2 x² ± x y + 3 y²`. -/
theorem finrank_ringClassField_neg_twenty_three_eq_three :
    Module.finrank (QuadraticAlgebra ℚ ((-(23 : ℕ) : ℤ) : ℚ) 0)
        (ringClassField (QuadraticOrder.numberFieldOrder (-(23 : ℕ)) (by decide))) = 3 := by
  rw [finrank_ringClassField_eq_card_primitiveReducedForms]
  decide +kernel

/-- **A ring class field of a nonmaximal order.** The order `ℤ[3i]` of discriminant `-36` has a
ring class field of degree two over `ℚ(√(-36)) = ℚ(i)`, certified by the two primitive reduced forms
`x² + 9 y²` and `2 x² + 2 x y + 5 y²`, although `ℚ(i)` itself has class number one. -/
theorem finrank_ringClassField_neg_thirty_six_eq_two :
    Module.finrank (QuadraticAlgebra ℚ ((-(36 : ℕ) : ℤ) : ℚ) 0)
        (ringClassField (QuadraticOrder.numberFieldOrder (-(36 : ℕ)) (by decide))) = 2 := by
  rw [finrank_ringClassField_eq_card_primitiveReducedForms]
  decide +kernel

end Examples

end TauCeti.BinaryQuadraticForm
