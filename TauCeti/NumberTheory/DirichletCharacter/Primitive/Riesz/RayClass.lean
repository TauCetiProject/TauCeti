/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder

/-!
# Zero-freeness of rational ray class characters

The rational character dictionary identifies the Dirichlet and ideal-theoretic first Riesz
remainders (`PrimitiveDirichletCharacter.rieszRemainder_toPrimitiveRayClassCharacter`). This
file transports zero-freeness right of a line between the two L-functions, so that explicit
formulas for Dirichlet characters apply to prime-ideal sums over `ℚ`.
-/

public section

open TauCeti.LFunctions

namespace TauCeti.PrimitiveDirichletCharacter

/-- A Dirichlet L-function and the Hecke L-function of the corresponding rational ray class
character have the same zeros right of any line. -/
@[simp] theorem zeroFreeRightOf_heckeLFunctionC_toPrimitiveRayClassCharacter_iff
    (ψ : PrimitiveDirichletCharacter) (σ : ℝ) :
    ZeroFreeRightOf σ (heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character) ↔
      ZeroFreeRightOf σ ψ.character.LFunction :=
  zeroFreeRightOf_congr fun s _ ↦ ψ.heckeLFunctionC_toPrimitiveRayClassCharacter_eventuallyEq s

end TauCeti.PrimitiveDirichletCharacter
