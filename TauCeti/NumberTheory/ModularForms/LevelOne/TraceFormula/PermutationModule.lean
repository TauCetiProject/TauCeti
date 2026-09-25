/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
public import TauCeti.RepresentationTheory.OfMulAction

/-!
# The permutation module of the determinant-`n` matrix module

Popa and Zagier carry out their proof of the Eichler–Selberg trace formula in `ℛₙ = ℚ[ℳₙ]`, the
free `ℚ`-module on the projective determinant-`n` matrix module `ℳₙ`, which is
`TauCeti.TraceFormulaMatrixModule n`. For `n ≠ 1` the set `ℳₙ` is not a group, since it does
not contain the identity matrix, of determinant `1`; `ℛₙ` is the free `ℚ`-module on `ℳₙ`, with
an action of the group ring `ℚ[PSL(2, ℤ)]` on each side. No new type is
introduced for it: `ℛₙ` is Mathlib's `MonoidAlgebra ℚ (TraceFormulaMatrixModule n)`, which is
the space of every permutation representation `Representation.ofMulAction ℚ G ℳₙ`. The three
actions of `PSL(2, ℤ)` on `ℳₙ` give three such representations on `ℛₙ`:

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
* `TauCeti.TraceFormulaMatrixModule.ofMulAction_S_sq`,
  `TauCeti.TraceFormulaMatrixModule.ofMulAction_T_mul_S_pow_three`: on `k[ℳₙ]`, `S² = 1` and
  `U³ = 1` for `U = T S`, since `S² = U³ = -1` in `SL(2, ℤ)` and `-1` acts trivially.

The left and right representations commute, so `ℛₙ` is a `ℚ[PSL(2, ℤ)]`-bimodule. This is the
general `TauCeti.commute_ofMulAction` (in `TauCeti.RepresentationTheory.OfMulAction`), applied to
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
      Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) g := by
  -- on basis vectors both sides are `single (g • x) r`, by `coe_smul`
  ext
  simp [coe_smul]

/-- The central sign `-1 ∈ SL(2, ℤ)` acts trivially on `k[ℳₙ]`. -/
@[simp]
theorem ofMulAction_neg_one :
    Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) (-1) = 1 := by
  ext
  simp

open ModularGroup in
/-- Left multiplication by `S` on `k[ℳₙ]` is an involution: `S² = 1`. -/
@[simp]
theorem ofMulAction_S_sq :
    Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) S ^ 2 = 1 := by
  -- `S² = -1` in `SL(2, ℤ)`, which acts trivially on `ℳₙ`
  rw [← map_pow, sq, show S * S = -1 from Subtype.ext S_mul_S_eq, ofMulAction_neg_one]

open ModularGroup in
/-- Left multiplication by `U = T S` on `k[ℳₙ]` satisfies `U³ = 1`. -/
theorem ofMulAction_T_mul_S_pow_three :
    Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) (T * S) ^ 3 = 1 := by
  -- `U³ = -1` in `SL(2, ℤ)`, which acts trivially on `ℳₙ`
  rw [← map_pow, show (T * S) ^ 3 = -1 by decide +kernel, ofMulAction_neg_one]

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
