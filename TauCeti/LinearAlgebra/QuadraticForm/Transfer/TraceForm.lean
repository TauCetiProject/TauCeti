/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.Algebra.QuadraticAlgebra.NormTrace

/-!
# Trace transfer in a quadratic algebra

For `QuadraticAlgebra K d 0`, the basis `(1, ω)` diagonalizes the trace transfer of
the unit line as `⟨2, 2d⟩`, including when the algebra is split.

The trace calculation uses `QuadraticAlgebra.algebraTrace_eq_trace`.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
-/

public section

namespace TauCeti

open QuadraticMap QuadraticForm

variable {K : Type*} [Field K]

/-- The trace transfer of the unit line of a quadratic algebra is diagonal in the
canonical basis `(1, ω)`, including for a split algebra. -/
theorem traceTransfer_sq_equivalent_weightedSumSquares (d : K) :
    ((QuadraticMap.sq (R := QuadraticAlgebra K d 0)
      (A := QuadraticAlgebra K d 0)).traceTransfer K).Equivalent
      (weightedSumSquares K ![(2 : K), 2 * d]) := by
  let b : Module.Basis (Fin 2) K (QuadraticAlgebra K d 0) := QuadraticAlgebra.basis d 0
  have hfin : Module.finrank K (QuadraticAlgebra K d 0) = 2 := by
    rw [Module.finrank_eq_card_basis b]
    simp
  have htrace : Algebra.trace K (QuadraticAlgebra K d 0) QuadraticAlgebra.omega = 0 := by
    rw [QuadraticAlgebra.algebraTrace_eq_trace, QuadraticAlgebra.trace_omega]
  have hω : (QuadraticAlgebra.omega : QuadraticAlgebra K d 0) ^ 2 =
      algebraMap K (QuadraticAlgebra K d 0) d := by
    simpa [Algebra.smul_def] using
      (QuadraticAlgebra.omega_pow_two_eq_add (R := K) (a := d) (b := 0))
  have hform :
      ((QuadraticMap.sq (R := QuadraticAlgebra K d 0)
        (A := QuadraticAlgebra K d 0)).traceTransfer K).comp
          (b.equivFun.symm : (Fin 2 → K) →ₗ[K] QuadraticAlgebra K d 0) =
        weightedSumSquares K ![(2 : K), 2 * d] := by
    ext v
    rw [QuadraticMap.comp_apply, QuadraticMap.traceTransfer_apply]
    have hrepr : b.equivFun.symm v =
        algebraMap K (QuadraticAlgebra K d 0) (v 0) +
          algebraMap K (QuadraticAlgebra K d 0) (v 1) * QuadraticAlgebra.omega := by
      rw [b.equivFun_symm_apply]
      simp [Fin.sum_univ_two, b, Algebra.smul_def]
    simp only [QuadraticMap.sq_apply, LinearEquiv.coe_coe]
    rw [hrepr, ← pow_two]
    rw [show (algebraMap K (QuadraticAlgebra K d 0) (v 0) +
          algebraMap K (QuadraticAlgebra K d 0) (v 1) * QuadraticAlgebra.omega) ^ 2 =
        algebraMap K (QuadraticAlgebra K d 0) ((v 0) ^ 2 + d * (v 1) ^ 2) +
          (algebraMap K (QuadraticAlgebra K d 0) (2 * (v 0) * (v 1))) *
            QuadraticAlgebra.omega by
      simp only [map_add, map_pow, map_mul]
      rw [← hω, map_ofNat]
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
