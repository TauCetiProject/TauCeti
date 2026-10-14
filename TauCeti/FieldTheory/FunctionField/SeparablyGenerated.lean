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

Over an imperfect field a separating element need not exist. An element of `F` outside `k` with a
`p`-power in `k`, such as `t^{1/p}` in `𝔽_p(t^{1/p})(X)` over `𝔽_p(t)`, would be both separable
and purely inseparable over `k(x)` for a separating `x`, hence a constant of `k(x)`, which it is
not.

## Main results

* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_perfectField`: a
  function field over a perfect field has a separating element.
* `TauCeti.not_isSeparable_adjoin_of_pow_mem`: an element outside `k` with a power
  `α ^ q ^ n` in `k` rules out every separating element.

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
