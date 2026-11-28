/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.GenusField
public import TauCeti.NumberTheory.Multiquadratic.Three.GenusField
import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Quadratic
import TauCeti.NumberTheory.Multiquadratic.Three.TwoRank

/-!
# The Hilbert and narrow Hilbert class fields of `ℚ(√3)`

The ordinary Hilbert class field of `ℚ(√3)` is the base field itself, whereas the narrow
Hilbert class field is `ℚ(i, √3)`. We use the quadratic base embedded in its prime-discriminant
compositum, as in the analogous calculation for `ℚ(√-5)`. The narrow identification holds for
every embedding of the compositum into the separable closure of the base.

The class number is one and the narrow class number is two. The compositum associated to
`12 = (-4)·(-3)` is abelian and unramified at every finite prime and has relative degree two,
so its image exhausts the narrow Hilbert class field. Its nontriviality, contrasted with the
ordinary Hilbert class field, records why real places must be retained in the ordinary
unramifiedness condition.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A (genus fields).
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6 (Hilbert class fields).
-/

public noncomputable section

open IntermediateField NumberField Polynomial
open TauCeti.Multiquadratic

namespace TauCeti.ClassFieldTheory

variable (hd : Squarefree (3 : ℤ))

-- Supply the canonical base actions directly: generic intermediate-field instance search
-- otherwise explores actions of the compositum on the separable closure of its base.
/-- The canonical action of the quadratic base on its separable closure. -/
local instance : Algebra (candidateGenusFieldBase hd)
    (SeparableClosure (candidateGenusFieldBase hd)) :=
  (separableClosure (candidateGenusFieldBase hd)
    (AlgebraicClosure (candidateGenusFieldBase hd))).toSubalgebra.algebra

/-- The canonical base action on subfields of the separable closure. -/
local instance (F : IntermediateField (candidateGenusFieldBase hd)
    (SeparableClosure (candidateGenusFieldBase hd))) : Algebra (candidateGenusFieldBase hd) F :=
  F.toSubalgebra.algebra

/-- The module structure from the canonical base action. -/
local instance (F : IntermediateField (candidateGenusFieldBase hd)
    (SeparableClosure (candidateGenusFieldBase hd))) : Module (candidateGenusFieldBase hd) F :=
  Algebra.toModule

/-- **The ordinary Hilbert class field of `ℚ(√3)` is trivial.** Every ideal class of the base
is principal, and real places are required to remain unramified. -/
theorem hilbertClassField_sqrt_three_eq_bot :
    hilbertClassField (candidateGenusFieldBase hd) = ⊥ := by
  rw [hilbertClassField_eq_bot_iff]
  exact TauCeti.NumberField.classNumber_eq_one_of_minpoly_eq_X_sq_sub_three
    (minpoly_candidateGenusFieldBaseGen hd TauCeti.NumberField.not_isSquare_three_rat)
    (adjoin_candidateGenusFieldBaseGen_eq_top hd)

/-- The narrow Hilbert class field of `ℚ(√3)` has degree two. -/
theorem finrank_narrowHilbertClassField_sqrt_three :
    Module.finrank (candidateGenusFieldBase hd)
      (narrowHilbertClassField (candidateGenusFieldBase hd)) = 2 := by
  rw [finrank_narrowHilbertClassField]
  exact natCard_narrowClassGroup_eq_two_of_minpoly_eq_X_sq_sub_three
    (minpoly_candidateGenusFieldBaseGen hd TauCeti.NumberField.not_isSquare_three_rat)
    (adjoin_candidateGenusFieldBaseGen_eq_top hd)

/-- **The narrow Hilbert class field of `ℚ(√3)` is its prime-discriminant compositum.**
The equality holds for every embedding over the quadratic base into its separable closure. -/
theorem fieldRange_candidateGenusField_three_eq_narrowHilbertClassField
    (ι : candidateGenusField hd →ₐ[candidateGenusFieldBase hd]
      SeparableClosure (candidateGenusFieldBase hd)) :
    ι.fieldRange = narrowHilbertClassField (candidateGenusFieldBase hd) := by
  apply fieldRange_candidateGenusField_eq_narrowHilbertClassField hd ?_ ι
  rw [← finrank_narrowHilbertClassField, finrank_narrowHilbertClassField_sqrt_three,
    genusPrimeDiscriminants_three]
  norm_num

/-- **`H⁺(ℚ(√3)) ≃ ℚ(i, √3)`.** This identifies the canonical narrow Hilbert class field
from global reciprocity with its concrete complex presentation. -/
theorem nonempty_algEquiv_narrowHilbertClassField_sqrt_three :
    Nonempty (narrowHilbertClassField (candidateGenusFieldBase hd) ≃ₐ[ℚ]
      adjoin ℚ ({Complex.I, (Real.sqrt 3 : ℂ)} : Set ℂ)) := by
  let ι : candidateGenusField hd →ₐ[candidateGenusFieldBase hd]
      SeparableClosure (candidateGenusFieldBase hd) := IsSepClosed.lift
  let e := (IntermediateField.equivOfEq
    (fieldRange_candidateGenusField_three_eq_narrowHilbertClassField hd ι)).symm.trans
      ι.equivFieldRange.symm
  exact ⟨e.toRingEquiv.toRatAlgEquiv.trans
    (IntermediateField.equivOfEq (candidateGenusField_three_eq hd))⟩

/-- The ordinary and narrow Hilbert class fields of `ℚ(√3)` differ: the former has degree one
and the latter degree two. -/
theorem narrowHilbertClassField_sqrt_three_ne_hilbertClassField :
    narrowHilbertClassField (candidateGenusFieldBase hd) ≠
      hilbertClassField (candidateGenusFieldBase hd) := by
  intro h
  have hdeg := finrank_narrowHilbertClassField_sqrt_three hd
  rw [h, hilbertClassField_sqrt_three_eq_bot, IntermediateField.finrank_bot] at hdeg
  norm_num at hdeg

/-- **The narrow Hilbert class field of `ℚ(√3)` ramifies at infinity.** Thus finite-prime
unramifiedness alone does not characterize the ordinary Hilbert class field. -/
theorem not_isUnramifiedAtInfinitePlaces_narrowHilbertClassField_sqrt_three :
    ¬ IsUnramifiedAtInfinitePlaces (candidateGenusFieldBase hd)
      (narrowHilbertClassField (candidateGenusFieldBase hd)) := by
  intro h
  have hle := (fieldRange_le_hilbertClassField_iff
    (narrowHilbertClassField (candidateGenusFieldBase hd)).val).2
      ⟨isUnramifiedAt_narrowHilbertClassField _, h⟩
  rw [IntermediateField.fieldRange_val, hilbertClassField_sqrt_three_eq_bot] at hle
  have hdeg := finrank_narrowHilbertClassField_sqrt_three hd
  rw [le_bot_iff.mp hle, IntermediateField.finrank_bot] at hdeg
  norm_num at hdeg

end TauCeti.ClassFieldTheory
