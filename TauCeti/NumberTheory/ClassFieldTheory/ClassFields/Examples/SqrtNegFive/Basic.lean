/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.GenusField
public import TauCeti.NumberTheory.Multiquadratic.MinusFive.GenusField
import TauCeti.NumberTheory.Multiquadratic.MinusFive.ClassNumber

/-!
# The Hilbert class field of `ℚ(√-5)`

The Hilbert class field of `ℚ(√-5)` is `ℚ(i, √5)`. We use the embedded quadratic base
`candidateGenusFieldBase hd`, with `hd : Squarefree (-5 : ℤ)`, so the comparison is an equality
of subfields of its separable closure, for every embedding of the genus field. The proof combines
the everywhere-unramified genus-field extension with the class number two computation: its degree
already exhausts the degree of the Hilbert class field.

`nonempty_algEquiv_hilbertClassField_sqrt_neg_five` gives the concrete complex presentation as an
algebra equivalence over `ℚ`. The narrow Hilbert class field has the same presentation
(`nonempty_algEquiv_narrowHilbertClassField_sqrt_neg_five`), since the base has no real places.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A (the genus field of discriminant `-20`).
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6 (the Hilbert class field).
-/

public noncomputable section

open IntermediateField NumberField
open TauCeti.Multiquadratic

namespace TauCeti.ClassFieldTheory

variable (hd : Squarefree (-5 : ℤ))

-- The generic intermediate-field shortcuts search for an action of the genus field on the
-- separable closure of its base. Supply the intended base action directly to avoid that search.
-- These shortcuts are definitionally equal to the corresponding global instances.
/-- The canonical action of the quadratic base on its separable closure. -/
local instance : Algebra (candidateGenusFieldBase hd)
    (SeparableClosure (candidateGenusFieldBase hd)) :=
  (separableClosure (candidateGenusFieldBase hd)
    (AlgebraicClosure (candidateGenusFieldBase hd))).toSubalgebra.algebra

/-- The canonical base algebra structure on subfields of the separable closure. -/
local instance (F : IntermediateField (candidateGenusFieldBase hd)
    (SeparableClosure (candidateGenusFieldBase hd))) : Algebra (candidateGenusFieldBase hd) F :=
  F.toSubalgebra.algebra

/-- The module structure induced by the canonical base algebra structure. -/
local instance (F : IntermediateField (candidateGenusFieldBase hd)
    (SeparableClosure (candidateGenusFieldBase hd))) : Module (candidateGenusFieldBase hd) F :=
  Algebra.toModule

/-- The Hilbert class field of the embedded copy of `ℚ(√-5)` has degree two. -/
theorem finrank_hilbertClassField_sqrt_neg_five :
    Module.finrank (candidateGenusFieldBase hd)
      (hilbertClassField (candidateGenusFieldBase hd)) = 2 := by
  rw [finrank_hilbertClassField]
  exact TauCeti.NumberField.classNumber_eq_two_of_minpoly_eq_X_sq_add_five
    (minpoly_candidateGenusFieldBaseGen hd (by norm_num))
    (adjoin_candidateGenusFieldBaseGen_eq_top hd)

/-- **The Hilbert class field of `ℚ(√-5)` is its genus field.** For every embedding of that
field into the separable closure of its quadratic base, its image is the canonical Hilbert
class field, not just an unramified subextension. -/
theorem fieldRange_candidateGenusField_neg_five_eq_hilbertClassField
    (ι : candidateGenusField hd →ₐ[candidateGenusFieldBase hd]
      SeparableClosure (candidateGenusFieldBase hd)) :
    ι.fieldRange = hilbertClassField (candidateGenusFieldBase hd) := by
  apply fieldRange_candidateGenusField_eq_hilbertClassField hd (by norm_num) ?_ ι
  rw [← finrank_hilbertClassField, finrank_hilbertClassField_sqrt_neg_five,
    genusPrimeDiscriminants_neg_five]
  norm_num

/-- **`H(ℚ(√-5)) ≃ ℚ(i, √5)`.** The abstract Hilbert class field, defined by global class-field
correspondence, has the concrete complex presentation as the compositum of `i` and `√5`. -/
theorem nonempty_algEquiv_hilbertClassField_sqrt_neg_five :
    Nonempty (hilbertClassField (candidateGenusFieldBase hd) ≃ₐ[ℚ]
      adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ)) := by
  let ι : candidateGenusField hd →ₐ[candidateGenusFieldBase hd]
      SeparableClosure (candidateGenusFieldBase hd) := IsSepClosed.lift
  let e := (IntermediateField.equivOfEq
    (fieldRange_candidateGenusField_neg_five_eq_hilbertClassField hd ι)).symm.trans
      ι.equivFieldRange.symm
  exact ⟨(e.toRingEquiv.toRatAlgEquiv).trans
    (IntermediateField.equivOfEq (candidateGenusField_neg_five_eq hd))⟩

/-- The narrow Hilbert class field of `ℚ(√-5)` is also `ℚ(i, √5)`: allowing ramification at
real places changes nothing for this imaginary quadratic base. -/
theorem nonempty_algEquiv_narrowHilbertClassField_sqrt_neg_five :
    Nonempty (narrowHilbertClassField (candidateGenusFieldBase hd) ≃ₐ[ℚ]
      adjoin ℚ ({Complex.I, (Real.sqrt 5 : ℂ)} : Set ℂ)) := by
  have := isTotallyComplex_candidateGenusFieldBase hd (by norm_num)
  rw [narrowHilbertClassField_eq_hilbertClassField]
  exact nonempty_algEquiv_hilbertClassField_sqrt_neg_five hd

end TauCeti.ClassFieldTheory
