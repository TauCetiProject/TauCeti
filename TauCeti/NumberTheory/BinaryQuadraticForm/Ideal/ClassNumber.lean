/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.PicEquivalence
public import TauCeti.NumberTheory.BinaryQuadraticForm.PrimitiveReduced
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.OrderOfConductor
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Examples
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger
import TauCeti.NumberTheory.NumberField.Global.Orders.Maximal
import TauCeti.NumberTheory.QuadraticOrder.Embedding
import TauCeti.NumberTheory.QuadraticOrder.NormOne

/-!
# Class numbers of imaginary quadratic orders from reduced forms

Proper classes of primitive positive definite forms of discriminant `-n` are in bijection with the
Picard group of the quadratic order of discriminant `-n` (`posDefProperClassEquivPic`), and each
such class contains exactly one primitive reduced form
(`posDefProperClass_mk_primitiveReducedForms_bijective`). Composing the two, the ideals
`aℤ + ((-b + √(-n))/2)ℤ` of the primitive reduced forms `(a, b, c)` represent every Picard class
exactly once, and the order of the Picard group is the number of primitive reduced forms.
Weighting each primitive reduced form as in the Hurwitz class number gives `2 h / w`, for `h` the
order of the Picard group and `w` the number of units of the order, so that `w` accounts for the
exceptional weights at the discriminants `-3` and `-4`.

When `-n` is a fundamental discriminant the order is the maximal order of `ℚ(√(-n))`
(`QuadraticOrder.numberFieldOrder_eq_maximal_iff`), whose Picard group is the ideal class group
(`GlobalNumberFields.maximalOrderPicEquiv`). The class number of
`ℚ(√(-n))` is then the number of primitive reduced forms of discriminant `-n`, a finite set the
kernel can enumerate.

The same count applies to the order `ℤ + f 𝓞 K` of conductor `f` in any quadratic field `K` of
discriminant `D` with `f² D = -n`. Evaluation at `f √D` identifies the order of discriminant `-n`
of `ℚ(√(-n))` with the canonical order of discriminant `-n` in `K`
(`QuadraticOrder.equivNumberFieldOrderOfSqrt`), and that order is `ℤ + f 𝓞 K`
(`QuadraticOrder.numberFieldOrderOfSqrt_eq_intAddMulOrder`). So `#Pic(ℤ + f 𝓞 K)` is the
number of primitive reduced forms of discriminant `f² D`. At `f = 1` this is the class number of
`K`. As a certified example, `ℚ(√(-20)) = ℚ(√(-5))` has class number two, so its ring of integers
is not a unique factorization domain.

## Main definitions and results

* `TauCeti.BinaryQuadraticForm.picClass_primitiveReducedForms_bijective`: the Picard classes of
  the primitive reduced forms of discriminant `-n` enumerate the Picard group of the order of
  discriminant `-n` without repetition.
* `TauCeti.BinaryQuadraticForm.nat_card_pic`: that Picard group has
  `#(primitiveReducedForms n)` elements.
* `sum_reducedFormWeight_primitiveReducedForms_eq_card_pic_div_card_units`: the weighted count of
  the primitive reduced forms of discriminant `-n`, their contribution to the Hurwitz class
  number, is twice the order of that Picard group divided by the number of units of the order.
* `TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms`: for fundamental `-n`,
  the class number of `ℚ(√(-n))` is `#(primitiveReducedForms n)`.
* `TauCeti.BinaryQuadraticForm.card_pic_intAddMulOrder_eq_card_primitiveReducedForms`: if
  `f² D = -n`, the Picard group of the order `ℤ + f 𝓞 K` of conductor `f` in a quadratic field of
  discriminant `D` has `#(primitiveReducedForms n)` elements.
* `TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms_of_discr_eq`: the class
  number of any quadratic field of discriminant `-n` is `#(primitiveReducedForms n)`.
* `TauCeti.BinaryQuadraticForm.classNumber_neg_twenty_eq_two`: the class number of `ℚ(√(-20))` is
  `2`; `not_uniqueFactorizationMonoid_neg_twenty` records the failure of unique factorization there.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2, Theorem 2.8, and §7, Theorem 7.7.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.3.
-/

public section
noncomputable section

open Finset
open scoped NumberField

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

section Order

variable (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)

/-- **Ideal representatives of the Picard group.** The Picard classes of the ideals
`aℤ + ((-b + √(-n))/2)ℤ` of the primitive reduced forms `(a, b, c)` of discriminant `-n` are all
the elements of the Picard group of the order of discriminant `-n`, each exactly once. -/
theorem picClass_primitiveReducedForms_bijective :
    Function.Bijective fun f : primitiveReducedForms n ↦
      picClass (-n) hn ⟨f, inf_le_right (a := posDef n)
        (mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2)⟩ := by
  have h := Function.Bijective.comp
    ⟨posDefProperClassToPic_injective n hn, posDefProperClassToPic_surjective n hn⟩
    posDefProperClass_mk_primitiveReducedForms_bijective
  simpa only [Function.comp_def, Quotient.mk''_eq_mk, posDefProperClassToPic_mk] using h

/-- **The order of the Picard group** of the quadratic order of discriminant `-n` is the number of
primitive reduced forms of discriminant `-n`. -/
theorem nat_card_pic :
    Nat.card (Pic (QuadraticOrder.numberFieldOrder (-n) hn)) = #(primitiveReducedForms n) :=
  (Nat.card_eq_of_bijective _ (picClass_primitiveReducedForms_bijective n hn)).symm.trans
    (Nat.card_eq_finsetCard _)

/-- **The weighted count of the primitive reduced forms as class number over units.** The
weighted count of the primitive reduced forms of discriminant `-n` is `2 h / w`, for `h` the order
of the Picard group and `w` the number of units of the quadratic order of discriminant `-n`: the
weights `1/3` of `x² + x y + y²` and `1/2` of `x² + y²` are the exceptional unit counts `6` and `4`
at `n = 3` and `n = 4`. This is the term of discriminant `-n` in
`TauCeti.hurwitzClassNumber_eq_sum_card_primitiveReducedForms`. -/
theorem sum_reducedFormWeight_primitiveReducedForms_eq_card_pic_div_card_units :
    ∑ f ∈ primitiveReducedForms n, reducedFormWeight f =
      2 * Nat.card (Pic (QuadraticOrder.numberFieldOrder (-n) hn)) /
        Nat.card (QuadraticOrder.numberFieldOrder (-n) hn).toSubalgebraˣ := by
  rw [sum_reducedFormWeight_primitiveReducedForms, nat_card_pic,
    QuadraticOrder.numberFieldOrder_toSubalgebra,
    QuadraticOrder.card_units_of_neg _ _ (by simpa using NeZero.pos n)]
  simp only [neg_inj, Nat.cast_ite, Nat.cast_ofNat]
  norm_cast

end Order

section Fundamental

variable (n : ℕ) [NeZero n]

/-- **The class number of an imaginary quadratic field counts primitive reduced forms.** For a
fundamental discriminant `-n`, the class number of `ℚ(√(-n))` is the number of primitive reduced
forms of discriminant `-n`. -/
theorem classNumber_eq_card_primitiveReducedForms (hfund : Int.IsFundamentalDiscr (-n)) :
    NumberField.classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) =
      #(primitiveReducedForms n) := by
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (maximalOrderPicEquiv _).toEquiv,
    ← (QuadraticOrder.numberFieldOrder_eq_maximal_iff _ hfund.emod_four_eq_zero_or_one).2 hfund,
    nat_card_pic]

end Fundamental

section Conductor

variable {K : Type*} [Field K] [NumberField K]

/-- **Class numbers of imaginary quadratic orders from reduced forms.** Let `K` be a quadratic
field of discriminant `D` and `f ≥ 1` with `f² D = -n`. The Picard group of the order
`ℤ + f 𝓞 K` of conductor `f` has `#(primitiveReducedForms n)` elements. -/
theorem card_pic_intAddMulOrder_eq_card_primitiveReducedForms (hK : Module.finrank ℚ K = 2)
    {f : ℕ} [NeZero f] {n : ℕ} (hn : (f : ℤ) ^ 2 * NumberField.discr K = -n) :
    Nat.card (Pic (intAddMulOrder K f)) = #(primitiveReducedForms n) := by
  have : NeZero n := ⟨by
    rintro rfl
    simp [NeZero.ne f, NumberField.discr_ne_zero K] at hn⟩
  have hn4 : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1 := by
    rw [← hn, Int.mul_emod, Int.sq_emod_four]
    rcases TauCeti.NumberField.discr_emod_four_eq_zero_or_one K with h | h <;>
      rcases Int.emod_two_eq_zero_or_one (f : ℤ) with h' | h' <;> simp [h, h']
  -- `f` times a square root of `D` is a square root of `-n = f² D`.
  obtain ⟨δ, hδ⟩ := Multiquadratic.exists_sq_eq_discr hK
  have hfδ : ((f : K) * δ) ^ 2 = ((-n : ℤ) : K) := by
    rw [mul_pow, hδ, ← hn]
    push_cast
    ring
  rw [← QuadraticOrder.numberFieldOrderOfSqrt_eq_intAddMulOrder hK hn4 hn.symm _ hfδ,
    ← nat_card_pic n hn4]
  exact Nat.card_congr (ClassGroup.mulEquiv ((Subalgebra.equivOfEq _ _
    (QuadraticOrder.numberFieldOrder_toSubalgebra (-n) hn4)).trans
      (QuadraticOrder.equivNumberFieldOrderOfSqrt (-n) hn4 _ hfδ hK)).toRingEquiv).toEquiv.symm

/-- **Class numbers of quadratic fields of negative discriminant from reduced forms.** A
quadratic number field of discriminant `-n` has class number `#(primitiveReducedForms n)`, the
count for its model `ℚ(√(-n))`. -/
theorem classNumber_eq_card_primitiveReducedForms_of_discr_eq (hK : Module.finrank ℚ K = 2)
    {n : ℕ} (hn : NumberField.discr K = -n) :
    NumberField.classNumber K = #(primitiveReducedForms n) := by
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card,
    ← NumberFieldOrder.card_pic_intAddMulOrder_one,
    card_pic_intAddMulOrder_eq_card_primitiveReducedForms hK (by simpa using hn)]

end Conductor

section Examples

/-- **`ℚ(√(-5))` has class number two**, certified by its two primitive reduced forms
`x² + 5 y²` and `2 x² + 2 x y + 3 y²` of discriminant `-20`. -/
theorem classNumber_neg_twenty_eq_two :
    NumberField.classNumber (QuadraticAlgebra ℚ ((-(20 : ℕ) : ℤ) : ℚ) 0) = 2 := by
  rw [classNumber_eq_card_primitiveReducedForms 20
    (by simpa using Multiquadratic.isFundamentalDiscr_neg_twenty)]
  decide +kernel

/-- **Unique factorization fails in `ℚ(√(-5))`**: its ring of integers, of class number two, is
not a unique factorization domain. -/
theorem not_uniqueFactorizationMonoid_neg_twenty :
    ¬ UniqueFactorizationMonoid (𝓞 (QuadraticAlgebra ℚ ((-(20 : ℕ) : ℤ) : ℚ) 0)) := by
  rw [← NumberField.classNumber_eq_one_iff_uniqueFactorizationMonoid,
    classNumber_neg_twenty_eq_two]
  decide

end Examples

end TauCeti.BinaryQuadraticForm
