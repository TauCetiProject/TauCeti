/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule

/-!
# The group ring of the determinant-`n` matrix module

Popa and Zagier carry out their proof of the Eichler–Selberg trace formula in the group ring
`ℛₙ = ℚ[ℳₙ]` of the projective determinant-`n` matrix module `ℳₙ`, which is
`TauCeti.TraceFormulaMatrixModule n`. No new type is introduced for it: `ℛₙ` is Mathlib's
`MonoidAlgebra ℚ (TraceFormulaMatrixModule n)`, the free `ℚ`-module on `ℳₙ`, which is the space
of every permutation representation `Representation.ofMulAction ℚ G ℳₙ`. The three actions of
`PSL(2, ℤ)` on `ℳₙ` give three such representations on `ℛₙ`:

* the left action `Representation.ofMulAction ℚ PSL(2, ℤ) ℳₙ`, with `ρ g [M] = [g M]`;
* the right action `Representation.ofMulAction ℚ PSL(2, ℤ)ᵐᵒᵖ ℳₙ`, with
  `ρ (MulOpposite.op g) [M] = [M g]`, so that Popa–Zagier's product `ξ · g` is
  `Representation.ofMulAction ℚ PSL(2, ℤ)ᵐᵒᵖ ℳₙ (MulOpposite.op g) ξ`;
* the conjugation action `Representation.ofMulAction ℚ (ConjAct PSL(2, ℤ)) ℳₙ`, with
  `ρ (ConjAct.toConjAct g) [M] = [g M g⁻¹]`.

This file records how they fit together, over an arbitrary coefficient semiring `k`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.ofMulAction_coe`: the left representation of the class of a
  determinant-one matrix `g` is the left representation of `g` itself.
* `TauCeti.TraceFormulaMatrixModule.ofMulAction_toConjAct`: the conjugation representation of `g`
  is the left representation of `g` after the right representation of `g⁻¹`.

The left and right representations commute, so `ℛₙ` is a bimodule. This is the general
`Representation.commute_ofMulAction` (in `TauCeti.RepresentationTheory.OfMulAction`), applied to
the instance `SMulCommClass PSL(2, ℤ) PSL(2, ℤ)ᵐᵒᵖ ℳₙ` saying that left and right
multiplication on `ℳₙ` commute.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1.
-/

public section

open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} [Semiring k] {n : ℤ}

/-- The left representation of the projective class of a determinant-one matrix `g` on
`k[ℳₙ]` is the left representation of `g`. -/
@[simp]
theorem ofMulAction_coe (g : SL(2, ℤ)) :
    Representation.ofMulAction k PSL(2, ℤ) (TraceFormulaMatrixModule n) g =
      Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) g := rfl

/-- Conjugation by `g` on `k[ℳₙ]` is left multiplication by `g` after right multiplication by
`g⁻¹`. -/
@[simp]
theorem ofMulAction_toConjAct (g : PSL(2, ℤ)) :
    Representation.ofMulAction k (ConjAct PSL(2, ℤ)) (TraceFormulaMatrixModule n)
        (ConjAct.toConjAct g) =
      Representation.ofMulAction k PSL(2, ℤ) (TraceFormulaMatrixModule n) g *
        Representation.ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
          (MulOpposite.op g)⁻¹ := by
  ext
  simp

end TauCeti.TraceFormulaMatrixModule
