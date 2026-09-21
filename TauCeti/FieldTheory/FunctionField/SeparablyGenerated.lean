/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.Separable.TranscendenceDegreeOne

/-!
# Separably generated algebraic function fields

An algebraic function field over a perfect field admits a separating element: a transcendental
element `x` over which the function field is finite and separable.  This supplies the parameter
needed for the differential calculus of an algebraic function field in arbitrary characteristic,
while keeping the more general results over imperfect fields stated with an explicit separating
element.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2 and
Section IV.1.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace IsFunctionField

/-- **A function field over a perfect field is separably generated** (Stichtenoth,
Proposition 3.10.2): it has a transcendental element `x` such that `F / k(x)` is separable.
Finiteness over `k(x)` follows separately from
`TauCeti.IsFunctionField.finiteDimensional_adjoin`. -/
theorem exists_transcendental_and_isSeparable_adjoin_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  exact TauCeti.exists_transcendental_and_isSeparable_adjoin_of_perfectField hF.trdeg_eq_one

end IsFunctionField

end TauCeti
