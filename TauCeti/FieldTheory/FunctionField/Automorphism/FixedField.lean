/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.Galois.FixedField

/-!
# Fixed fields of finite automorphism groups of function fields

If a finite group of automorphisms acts on an algebraic function field `F / k`, its fixed field
is again an algebraic function field over `k`. The extension of the fixed field is finite Galois,
and its Galois group is the acting group. This is the field-theoretic input to applying
Riemann--Hurwitz to a quotient by a finite automorphism group.

Algebraic-extension descent is `TauCeti.IsFunctionField.of_isAlgebraic_top`.
`FixedPoints.finrank_eq_card` gives the degree,
`IsGalois.of_fixed_field` gives the Galois extension, and
`FixedPoints.toAlgAutMulEquiv` identifies the Galois group.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section III.7.
-/

public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The fixed field of a finite group of `k`-automorphisms of a function field is itself a
function field over `k`. `IsGalois.of_fixed_field` makes `F` Galois over
this field, and `FixedPoints.toAlgAutMulEquiv` identifies its Galois group
with `H`. -/
theorem IsFunctionField.fixedField (hF : IsFunctionField k F)
    (H : Subgroup (F ≃ₐ[k] F)) [Finite H] :
    IsFunctionField k (IntermediateField.fixedField H) := by
  exact hF.of_isAlgebraic_top (E := IntermediateField.fixedField H)

end TauCeti
