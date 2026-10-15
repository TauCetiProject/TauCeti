/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange
public import TauCeti.Algebra.Quaternion.BaseChange

/-!
# Scalar extension of the Hasse invariant

The Brauer-valued Hasse invariant commutes with extension of scalars: the invariant of an
extended quadratic space is the image of its original invariant under the scalar-extension
homomorphism on Brauer groups. This permits the same invariant to be compared over different
fields without choosing compatible diagonalizations.

The convention is Lam's `s(q) = ∏_{i<j} [(aᵢ,aⱼ)]`, with the empty product in ranks zero
and one. Scalar extension preserves each quaternion symbol by
`TauCeti.BrauerGroup.baseChange_quaternionClass`, and hence preserves the product. No
finiteness or separability assumption on the field extension is needed.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3, Definition 3.17
  and Proposition 3.18.
-/

public section

namespace TauCeti.RegularFormClass

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Invertible (2 : K)] [Invertible (2 : L)]

/-- The Hasse invariant of a scalar extension is the scalar extension of the original
Brauer class. -/
@[simp]
theorem hasseInvariant_baseChange (q : RegularFormClass K) :
    hasseInvariant (baseChange L q) = BrauerGroup.baseChange K L (hasseInvariant q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    rw [baseChange_mk, RegularFormPresentation.baseChange_def,
      hasseInvariant_mk, hasseInvariant_mk]
    simp [map_prod]

end TauCeti.RegularFormClass
