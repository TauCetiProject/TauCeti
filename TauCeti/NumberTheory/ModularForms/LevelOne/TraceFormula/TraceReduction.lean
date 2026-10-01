/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodAction
import TauCeti.LinearAlgebra.Trace.Exchange
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The trace reduction to the ambient space of binary forms

Let `K` be a field of characteristic zero, `w` a positive even natural number and
`ξ ∈ K[ℳₙ]` an element satisfying Popa and Zagier's exchange relations (B). On the space `V_w`
of binary forms of degree `w`, the action of `ξ` maps each of the subspaces `A = ker (1 + S)` and
`B = ker (1 + U + U²)`, with `U = T S`, into the other, and `A + B = V_w`. Its trace on the
period-polynomial space `W_w = A ∩ B` is therefore its trace on `V_w`. This is Popa and Zagier's
reduction `tr(ξ | W_w) = tr(ξ | V_w)` of the trace on period polynomials to the trace on all
binary forms.

## Main results

* `TauCeti.TraceFormulaMatrixModule.ExchangeRelations.trace_periodActionRestrict_eq_trace`: the
  trace of `ξ` on `W_w` is its trace on `V_w`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2, Proposition 3.
-/

public section

open MonoidAlgebra MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

variable {K : Type*} [Field K] {n : ℤ} {w : ℕ}

/-- The trace of `ξ` on the period polynomials, computed on `ker (1 + S) ⊓ ker (1 + U + U²)`. -/
private theorem ExchangeRelations.trace_periodActionRestrict_eq_trace_restrict_inf (hw : Even w)
    {ξ : K[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations K n ξ) :
    LinearMap.trace K (periodPolynomials K w) (hξ.periodActionRestrict hw) =
      LinearMap.trace K
        ↥(LinearMap.ker (1 + binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) ⊓
          LinearMap.ker
            (1 + binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
              binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2))
        ((periodAction (R := K) hw ξ).restrict fun _ hP ↦
          ⟨hξ.periodAction_mem_ker_one_add_S hw hP.2,
            hξ.periodAction_mem_ker_one_add_U_add_U_sq hw hP.1⟩) := by
  have h : hξ.periodActionRestrict hw = (periodAction (R := K) hw ξ).restrict
      fun _ hP ↦ hξ.periodAction_mem_periodPolynomials hw hP :=
    LinearMap.ext fun P ↦ Subtype.ext (hξ.coe_periodActionRestrict_apply hw P)
  rw [h]
  exact LinearMap.trace_restrict_congr periodPolynomials_def _ _ _

/-- **The trace reduction** (Popa–Zagier, §2, Proposition 3): over a field of characteristic zero
and for positive even `w`, the action of an element `ξ` satisfying the exchange relations has the
same trace on the period polynomials `W_w` as on the binary forms `V_w`. -/
theorem ExchangeRelations.trace_periodActionRestrict_eq_trace [CharZero K] (hw : Even w)
    (hw₀ : w ≠ 0) {ξ : K[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations K n ξ) :
    LinearMap.trace K (periodPolynomials K w) (hξ.periodActionRestrict hw) =
      LinearMap.trace K (homogeneousSubmodule (Fin 2) K w) (periodAction (R := K) hw ξ) := by
  rw [hξ.trace_periodActionRestrict_eq_trace_restrict_inf hw]
  exact LinearMap.trace_restrict_inf_eq_trace
    (codisjoint_ker_one_add_S_ker_one_add_U_add_U_sq hw hw₀)
    (fun _ ↦ hξ.periodAction_mem_ker_one_add_U_add_U_sq hw)
    (fun _ ↦ hξ.periodAction_mem_ker_one_add_S hw)

end TauCeti.TraceFormulaMatrixModule
