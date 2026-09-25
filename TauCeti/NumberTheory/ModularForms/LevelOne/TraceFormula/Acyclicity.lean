/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PermutationModule
import TauCeti.NumberTheory.Modular.Acyclicity

/-!
# Acyclicity of the permutation module of `ℳₙ`

For `n ≠ 0`, the left action of `PSL(2, ℤ)` on the projective determinant-`n` matrix module
`ℳₙ` is free (`TauCeti.TraceFormulaMatrixModule.isCancelSMul`). Hence the acyclicity of
permutation modules of free `PSL(2, ℤ)`-sets
(`TauCeti.ModularGroup.disjoint_ker_one_add_S_ker_one_add_T_mul_S_add_sq`) applies to `k[ℳₙ]`:
no nonzero element is killed by both `1 + S` and `1 + U + U²`, where `U = T * S`. Popa and
Zagier state this (their Lemma 2) for `ℚ[ℳ]`, with `ℳ` the integral matrices of positive
determinant modulo sign; its summands `ℛₙ = ℚ[ℳₙ]` are the case needed for the trace formula.
The right action of `PSL(2, ℤ)` on `ℳₙ` is free as well
(`TauCeti.TraceFormulaMatrixModule.isCancelSMul_mulOpposite`), so the same holds for `S` and `U`
acting on `k[ℳₙ]` by right multiplication.

The hypothesis `n ≠ 0` is needed. On `ℳ₀` the left action is not free (`T` fixes the class of
`(1 0; 0 0)`), and acyclicity for the left action fails for a nontrivial ring `k`: `S` swaps the
classes of `(1 0; 0 0)` and `(0 0; 1 0)`, and `U` permutes them cyclically with the class of
`(1 0; 1 0)`, so `[(0 0; 1 0)] - [(1 0; 0 0)]` is a nonzero element of both kernels on `k[ℳ₀]`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.disjoint_ker_one_add_S_ker_one_add_T_mul_S_add_sq`: for
  `n ≠ 0`, acyclicity of `k[ℳₙ]`, stated with the `SL(2, ℤ)` permutation representation.
* `TauCeti.TraceFormulaMatrixModule.disjoint_ker_one_add_op_S_ker_one_add_op_T_mul_S_add_sq`: for
  `n ≠ 0`, acyclicity of `k[ℳₙ]` for the right action of `PSL(2, ℤ)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, §3, Lemma 2.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

open _root_.ModularGroup

variable {n : ℤ}

/-- **Acyclicity of `k[ℳₙ]`** (Popa--Zagier, Lemma 2): for `n ≠ 0`, on the permutation module
`k[ℳₙ]` of the left action of `SL(2, ℤ)`, the kernels of `1 + S` and `1 + U + U²`, with
`U = T * S`, are disjoint. -/
theorem disjoint_ker_one_add_S_ker_one_add_T_mul_S_add_sq {k : Type*} [Ring k] (hn : n ≠ 0) :
    Disjoint
      (LinearMap.ker (1 + Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) S))
      (LinearMap.ker (1 +
        Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) (T * S) +
        Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) (T * S) ^ 2)) := by
  have := isCancelSMul hn
  simpa only [← ofMulAction_coe, QuotientGroup.mk_mul] using
    ModularGroup.disjoint_ker_one_add_S_ker_one_add_T_mul_S_add_sq

/-- **Acyclicity of `k[ℳₙ]` for the right action** (Popa--Zagier, Lemma 2): for `n ≠ 0`, on the
permutation module `k[ℳₙ]` of the right action of `PSL(2, ℤ)`, the kernels of `1 + S` and
`1 + U + U²`, with `S` and `U = T * S` acting by right multiplication, are disjoint. -/
theorem disjoint_ker_one_add_op_S_ker_one_add_op_T_mul_S_add_sq {k : Type*} [Ring k] (hn : n ≠ 0) :
    Disjoint
      (LinearMap.ker
        (1 + Representation.ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (.op S)))
      (LinearMap.ker (1 +
        Representation.ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
          (.op ((T : PSL(2, ℤ)) * S)) +
        Representation.ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
          (.op ((T : PSL(2, ℤ)) * S)) ^ 2)) :=
  have := isCancelSMul_mulOpposite hn
  ModularGroup.disjoint_ker_one_add_op_S_ker_one_add_op_T_mul_S_add_sq

end TauCeti.TraceFormulaMatrixModule
