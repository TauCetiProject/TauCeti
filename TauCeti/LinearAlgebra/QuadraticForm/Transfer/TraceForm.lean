/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
import TauCeti.FieldTheory.Trace
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

/-!
# Trace transfer in a quadratic extension

If `L/K` has degree two and `x² = d` for `x ∉ K`, then the square-root basis `(1,x)`
diagonalizes the trace transfer of the unit line as `⟨2, 2d⟩`. This gives a form-level
description of the trace form used in computations of transferred invariants.

The trace calculation uses `TauCeti.Algebra.trace_eq_zero_of_sq_algebraMap_of_not_mem_range`;
the basis uses `TauCeti.linearIndependent_one_of_notMem_range_algebraMap`.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
-/

public section

namespace TauCeti

open QuadraticMap QuadraticForm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The trace transfer of the unit line of a quadratic extension is diagonal in the
square-root basis. -/
theorem traceTransfer_sq_equivalent_weightedSumSquares
    (hfin : Module.finrank K L = 2) {x : L} {d : K}
    (hx2 : x ^ 2 = algebraMap K L d) (hx : x ∉ Set.range (algebraMap K L)) :
    ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Equivalent
      (weightedSumSquares K ![(2 : K), 2 * d]) := by
  let b : Module.Basis (Fin 2) K L :=
    basisOfLinearIndependentOfCardEqFinrank
      (b := ![1, x]) (linearIndependent_one_of_notMem_range_algebraMap K L hx)
      (by simpa using hfin.symm)
  have hb : (b : Fin 2 → L) = ![1, x] := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have htrace : Algebra.trace K L x = 0 :=
    Algebra.trace_eq_zero_of_sq_algebraMap_of_not_mem_range hx2 hx
  have hform :
      ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).comp
          (b.equivFun.symm : (Fin 2 → K) →ₗ[K] L) =
        weightedSumSquares K ![(2 : K), 2 * d] := by
    ext v
    rw [QuadraticMap.comp_apply, QuadraticMap.traceTransfer_apply]
    have hrepr : b.equivFun.symm v =
        algebraMap K L (v 0) + algebraMap K L (v 1) * x := by
      rw [b.equivFun_symm_apply]
      simp [Fin.sum_univ_two, hb, Algebra.smul_def]
    simp only [QuadraticMap.sq_apply, LinearEquiv.coe_coe]
    rw [hrepr, ← pow_two]
    rw [show (algebraMap K L (v 0) + algebraMap K L (v 1) * x) ^ 2 =
        algebraMap K L ((v 0) ^ 2 + d * (v 1) ^ 2) +
          (algebraMap K L (2 * (v 0) * (v 1))) * x by
      simp only [map_add, map_pow, map_mul]
      rw [← hx2, map_ofNat]
      ring]
    rw [map_add, Algebra.trace_algebraMap, ← Algebra.smul_def, map_smul, htrace]
    simp [hfin, weightedSumSquares_apply, Fin.sum_univ_two]
    ring
  refine ⟨{ toLinearEquiv := b.equivFun, map_app' := fun z => ?_ }⟩
  have h := congrArg (fun Q : QuadraticForm K (Fin 2 → K) => Q (b.equivFun z)) hform
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    b.equivFun.symm_apply_apply] at h
  convert h.symm using 1

end TauCeti
