/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Class
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Normalization

/-!
# Positive definite proper classes and the Picard group

Normalization expresses an invertible ideal as a positive rational multiple of the
ideal of a primitive form with positive leading coefficient. At negative discriminant
this gives a positive definite form. The principal factor vanishes in the Picard group,
so `posDefProperClassToPic` is surjective. Its injectivity then gives the equivalence.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section
noncomputable section

open QuadraticAlgebra FractionalIdeal
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

/-- Every Picard class of the order of discriminant `-n` has a primitive positive
definite form representative. -/
theorem posDefProperClassToPic_surjective (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    Function.Surjective (posDefProperClassToPic n hn) := by
  let O := QuadraticOrder.numberFieldOrder (-n : ℤ) hn
  intro c
  obtain ⟨I, hIc⟩ := O.mkPic_surjective c
  obtain ⟨f, hf, hp, ha, -, u, -, -, hI⟩ :=
    exists_pos_primitive_form_invertibleFractionalIdeal_eq (-n : ℤ) hn I
  let g : ↥(posDef n ⊓ primitiveForms (-n : ℤ)) :=
    ⟨f, (mem_posDef_inf_primitiveForms n).mpr ⟨hf, ha, hp⟩⟩
  have hmap := congrArg O.mkPic hI
  simp only [O, NumberFieldOrder.mkPic, map_mul,
    ClassGroup.mk_toPrincipalIdeal, one_mul] at hmap
  refine ⟨Quotient.mk _ g, ?_⟩
  rw [posDefProperClassToPic_mk, picClass_def]
  exact hmap.symm.trans hIc

/-- Proper classes of primitive positive definite forms of discriminant `-n` are in
bijection with the Picard group of the quadratic order of discriminant `-n`. -/
def posDefProperClassEquivPic (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    PosDefProperClass n ≃ @Pic (QuadraticAlgebra ℚ (-((n : ℤ) : ℚ)) 0)
      (inferInstanceAs (Field (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)))
      (inferInstanceAs (NumberField (QuadraticAlgebra ℚ ((-n : ℤ) : ℚ) 0)))
      (QuadraticOrder.numberFieldOrder (-n : ℤ) hn) :=
  Equiv.ofBijective (posDefProperClassToPic n hn)
    ⟨posDefProperClassToPic_injective n hn, posDefProperClassToPic_surjective n hn⟩

/-- The forward function of the equivalence is the form-ideal Picard class map. -/
@[simp] theorem posDefProperClassEquivPic_apply (n : ℕ) [NeZero n]
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) (q : PosDefProperClass n) :
    posDefProperClassEquivPic n hn q = posDefProperClassToPic n hn q := (rfl)

end TauCeti.BinaryQuadraticForm
