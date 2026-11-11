/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Degree
import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.GaloisGroup
import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.InfinitePlace
import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Ramification

/-!
# When an imaginary quadratic genus field is the Hilbert class field

For squarefree `d < 0`, the canonical genus field is everywhere unramified over its quadratic
base. If the class number of that base equals the genus-field degree `2 ^ (t - 1)`, where `t`
is the number of prime discriminants, every embedding of the genus field into the separable
closure of the base has image equal to the Hilbert class field.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
-/

public noncomputable section

open IsDedekindDomain NumberField
open TauCeti.Multiquadratic

namespace TauCeti.ClassFieldTheory

/-- The genus field of an imaginary quadratic field is its Hilbert class field when its relative
degree exhausts the class number. The equality holds for every embedding over the quadratic base. -/
theorem fieldRange_candidateGenusField_eq_hilbertClassField {d : ℤ} (hd : Squarefree d)
    (hneg : d < 0)
    (hclass : classNumber (candidateGenusFieldBase hd) =
      2 ^ ((genusPrimeDiscriminants hd).card - 1))
    (ι : candidateGenusField hd →ₐ[candidateGenusFieldBase hd]
      SeparableClosure (candidateGenusFieldBase hd)) :
    ι.fieldRange = hilbertClassField (candidateGenusFieldBase hd) := by
  have hnsq : ¬ IsSquare (d : ℚ) := not_isSquare_of_neg (by exact_mod_cast hneg)
  apply fieldRange_eq_hilbertClassField_of_unramified_of_finrank_eq_classNumber ι
  · intro w
    exact isUnramifiedIn_candidateGenusField hd hnsq
      (w.asIdeal.under (𝓞 (candidateGenusFieldBase hd))) w.asIdeal inferInstance inferInstance
  · exact isUnramifiedAtInfinitePlaces_candidateGenusField hd hneg
  · rw [finrank_candidateGenusField_over_candidateGenusFieldBase hd hnsq, hclass]

end TauCeti.ClassFieldTheory
