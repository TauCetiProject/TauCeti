/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.PicEquivalence
public import TauCeti.NumberTheory.BinaryQuadraticForm.PrimitiveReduced
public import TauCeti.NumberTheory.QuadraticOrder.ClassGroup
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.PID
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Examples

/-!
# Class numbers of imaginary quadratic orders from reduced forms

Proper classes of primitive positive definite forms of discriminant `-n` are in bijection with the
Picard group of the quadratic order of discriminant `-n` (`posDefProperClassEquivPic`), and each
such class contains exactly one primitive reduced form
(`posDefProperClass_mk_primitiveReducedForms_bijective`). Composing the two, the ideals
`aℤ + ((-b + √(-n))/2)ℤ` of the primitive reduced forms `(a, b, c)` represent every Picard class
exactly once, and the order of the Picard group is the number of primitive reduced forms.

When `-n` is a fundamental discriminant the order is the ring of integers of `ℚ(√(-n))` and its
Picard group is the ideal class group (`QuadraticOrder.picEquivClassGroup`). The class number of
`ℚ(√(-n))` is then the number of primitive reduced forms of discriminant `-n`, a finite set the
kernel can enumerate. As certified examples, `ℚ(√(-4)) = ℚ(i)` has class number one, while
`ℚ(√(-20)) = ℚ(√(-5))` has class number two, so its ring of integers is not a unique factorization
domain.

## Main definitions and results

* `TauCeti.BinaryQuadraticForm.picClass_primitiveReducedForms_bijective`: the Picard classes of
  the primitive reduced forms of discriminant `-n` enumerate the Picard group of the order of
  discriminant `-n` without repetition.
* `TauCeti.BinaryQuadraticForm.nat_card_pic`: that Picard group has
  `#(primitiveReducedForms n)` elements.
* `TauCeti.BinaryQuadraticForm.posDefProperClassEquivClassGroup`: for fundamental `-n`, proper
  classes of primitive positive definite forms are in bijection with the class group of
  `𝓞 ℚ(√(-n))`.
* `TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms`: for fundamental `-n`,
  the class number of `ℚ(√(-n))` is `#(primitiveReducedForms n)`.
* `TauCeti.BinaryQuadraticForm.classNumber_neg_four` and
  `TauCeti.BinaryQuadraticForm.classNumber_neg_twenty`: the class numbers of `ℚ(√(-4))` and
  `ℚ(√(-20))` are `1` and `2`; `not_uniqueFactorizationMonoid_neg_twenty` records the failure of
  unique factorization in the latter.

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

end Order

section Fundamental

variable (n : ℕ) [NeZero n]

/-- **Forms and ideal classes of an imaginary quadratic field.** For a fundamental discriminant
`-n`, proper classes of primitive positive definite forms of discriminant `-n` are in bijection
with the ideal class group of `𝓞 ℚ(√(-n))`. The class of `(a, b, c)` goes to the ideal class of
`aℤ + ((-b + √(-n))/2)ℤ` (`posDefProperClassEquivClassGroup_apply`). -/
def posDefProperClassEquivClassGroup (hfund : Int.IsFundamentalDiscr (-n)) :
    PosDefProperClass n ≃ ClassGroup (𝓞 (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)) :=
  have hn := hfund.emod_four_eq_zero_or_one
  Equiv.ofBijective _ <| (QuadraticOrder.picEquivClassGroup (-n) hn hfund).bijective.comp
    ⟨posDefProperClassToPic_injective n hn, posDefProperClassToPic_surjective n hn⟩

/-- `posDefProperClassEquivClassGroup` is the Picard class of a form class, followed by the
identification of the Picard group with the class group. -/
theorem posDefProperClassEquivClassGroup_apply (hfund : Int.IsFundamentalDiscr (-n))
    (q : PosDefProperClass n) :
    posDefProperClassEquivClassGroup n hfund q =
      QuadraticOrder.picEquivClassGroup (-n) _ hfund
        (posDefProperClassToPic n hfund.emod_four_eq_zero_or_one q) := by
  rw [posDefProperClassEquivClassGroup, Equiv.ofBijective_apply, Function.comp_apply]

/-- **The class number of an imaginary quadratic field counts primitive reduced forms.** For a
fundamental discriminant `-n`, the class number of `ℚ(√(-n))` is the number of primitive reduced
forms of discriminant `-n`. -/
theorem classNumber_eq_card_primitiveReducedForms (hfund : Int.IsFundamentalDiscr (-n)) :
    NumberField.classNumber (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0) =
      #(primitiveReducedForms n) := by
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (posDefProperClassEquivClassGroup n hfund), nat_card_posDefProperClass]

end Fundamental

section Examples

/-- **`ℚ(i)` has class number one**, certified by its single primitive reduced form `x² + y²` of
discriminant `-4`. -/
theorem classNumber_neg_four :
    NumberField.classNumber (QuadraticAlgebra ℚ ((-(4 : ℕ) : ℤ) : ℚ) 0) = 1 := by
  have hfund : Int.IsFundamentalDiscr (-(4 : ℕ) : ℤ) := by
    simpa using (Int.isFundamentalDiscr_four_mul (m := -1)).mpr
      ⟨isUnit_neg_one.squarefree, by decide⟩
  rw [classNumber_eq_card_primitiveReducedForms 4 hfund]
  decide +kernel

/-- **`ℚ(√(-5))` has class number two**, certified by its two primitive reduced forms
`x² + 5 y²` and `2 x² + 2 x y + 3 y²` of discriminant `-20`. -/
theorem classNumber_neg_twenty :
    NumberField.classNumber (QuadraticAlgebra ℚ ((-(20 : ℕ) : ℤ) : ℚ) 0) = 2 := by
  rw [classNumber_eq_card_primitiveReducedForms 20
    (by simpa using Multiquadratic.isFundamentalDiscr_neg_twenty)]
  decide +kernel

/-- **Unique factorization fails in `ℚ(√(-5))`**: its ring of integers, of class number two, is
not a unique factorization domain. -/
theorem not_uniqueFactorizationMonoid_neg_twenty :
    ¬ UniqueFactorizationMonoid (𝓞 (QuadraticAlgebra ℚ ((-(20 : ℕ) : ℤ) : ℚ) 0)) := by
  intro h
  -- a Dedekind domain with unique factorization is a principal ideal domain, of class number one
  have h1 := NumberField.classNumber_eq_one_iff.mpr <|
    IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
      (𝓞 (QuadraticAlgebra ℚ ((-(20 : ℕ) : ℤ) : ℚ) 0))
  rw [classNumber_neg_twenty] at h1
  exact absurd h1 (by decide)

end Examples

end TauCeti.BinaryQuadraticForm
