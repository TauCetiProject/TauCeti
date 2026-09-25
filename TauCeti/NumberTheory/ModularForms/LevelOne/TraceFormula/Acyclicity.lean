/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
import TauCeti.NumberTheory.Modular.Acyclicity

/-!
# Acyclicity of the permutation module of `ℳₙ`

For `n ≠ 0`, the left action of `PSL(2, ℤ)` on the projective determinant-`n` matrix module
`ℳₙ` is free: a determinant-`n` matrix is invertible over `ℚ`, so `g A = ±A` forces `g = ±1`.
Hence the acyclicity of permutation modules of free `PSL(2, ℤ)`-sets
(`TauCeti.ModularGroup.ker_one_add_S_inf_ker_one_add_T_mul_S_add_sq_eq_bot`) applies to `k[ℳₙ]`:
no nonzero element is killed by both `1 + S` and `1 + U + U²`, where `U = T * S`. Popa and
Zagier state this (their Lemma 2) for `ℚ[ℳ]`, with `ℳ` the integral matrices of positive
determinant modulo sign; its summands `ℛₙ = ℚ[ℳₙ]` are the case needed for the trace formula.

The hypothesis `n ≠ 0` is needed. On `ℳ₀` the action is not free (`T` fixes the class of
`(1 0; 0 0)`), and acyclicity fails for a nontrivial ring `k`: `S` swaps the classes of
`(1 0; 0 0)` and `(0 0; 1 0)`, and `U` permutes them cyclically with the class of `(1 0; 1 0)`,
so `[(0 0; 1 0)] - [(1 0; 0 0)]` is a nonzero element of both kernels on `k[ℳ₀]`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.eq_one_or_eq_neg_one_of_smul_eq`: for `n ≠ 0`, only `±1`
  in `SL(2, ℤ)` fixes an element of `ℳₙ`.
* `TauCeti.TraceFormulaMatrixModule.isCancelSMul`: for `n ≠ 0`, `PSL(2, ℤ)` acts freely on `ℳₙ`.
* `TauCeti.TraceFormulaMatrixModule.ker_one_add_S_inf_ker_one_add_T_mul_S_add_sq_eq_bot`: for
  `n ≠ 0`, acyclicity of `k[ℳₙ]`, stated with the `SL(2, ℤ)` permutation representation.

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

/-- For `n ≠ 0`, only `±1` in `SL(2, ℤ)` fixes an element of `ℳₙ`. -/
theorem eq_one_or_eq_neg_one_of_smul_eq (hn : n ≠ 0) {g : SL(2, ℤ)} {x : TraceFormulaMatrixModule n}
    (h : g • x = x) : g = 1 ∨ g = -1 := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  -- `A` is cancellable on the right, as its determinant `n` is nonzero
  have hA := (isRegular_of_isLeftRegular_det (A.2 ▸ IsRegular.of_ne_zero hn).left).right
  rw [smul_mk, mk_eq_iff] at h
  rcases h with h | h <;> [left; right] <;>
    exact Subtype.ext <| hA <| by simpa [FixedDetMatrices.smul_coe] using congrArg Subtype.val h

/-- For `n ≠ 0`, `PSL(2, ℤ)` acts freely on `ℳₙ`. -/
theorem isCancelSMul (hn : n ≠ 0) : IsCancelSMul PSL(2, ℤ) (TraceFormulaMatrixModule n) := by
  refine isCancelSMul_iff_eq_one_of_smul_eq.mpr fun g x h ↦ ?_
  induction g using QuotientGroup.induction_on with | H g => ?_
  rw [QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact eq_one_or_eq_neg_one_of_smul_eq hn ((coe_smul g x).symm.trans h)

/-- **Acyclicity of `k[ℳₙ]`** (Popa--Zagier, Lemma 2): for `n ≠ 0`, on the permutation module
`k[ℳₙ]` of the left action of `SL(2, ℤ)`, the kernels of `1 + S` and `1 + U + U²`, with
`U = T * S`, meet in `0`. -/
theorem ker_one_add_S_inf_ker_one_add_T_mul_S_add_sq_eq_bot {k : Type*} [Ring k] (hn : n ≠ 0) :
    LinearMap.ker (1 + Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) S) ⊓
      LinearMap.ker (1 +
        Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) (T * S) +
        Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) (T * S) ^ 2) = ⊥ := by
  have := isCancelSMul hn
  -- `g ∈ SL(2, ℤ)` acts on `k[ℳₙ]` as its class in `PSL(2, ℤ)`
  have hρ (g : SL(2, ℤ)) : Representation.ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) g =
      Representation.ofMulAction k PSL(2, ℤ) (TraceFormulaMatrixModule n) g := by
    simp [Representation.ofMulAction_def]
  simpa only [hρ] using ModularGroup.ker_one_add_S_inf_ker_one_add_T_mul_S_add_sq_eq_bot

end TauCeti.TraceFormulaMatrixModule
