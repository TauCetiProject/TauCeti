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

This gives a concrete presentation for calculating invariants of transferred quadratic forms.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
-/

public section

namespace TauCeti

open QuadraticMap QuadraticForm

variable {K : Type*} [CommRing K]

/-- The coordinate map in the basis `(1, ω)` identifies the trace transfer of the unit
line with `⟨2, 2d⟩`. -/
noncomputable def traceTransferSqIsometryEquivWeightedSumSquares (d : K) :
    ((QuadraticMap.sq (R := QuadraticAlgebra K d 0)
      (A := QuadraticAlgebra K d 0)).traceTransfer K).IsometryEquiv
      (weightedSumSquares K ![(2 : K), 2 * d]) := by
  let b : Module.Basis (Fin 2) K (QuadraticAlgebra K d 0) := QuadraticAlgebra.basis d 0
  have hω : (QuadraticAlgebra.omega : QuadraticAlgebra K d 0) ^ 2 =
      algebraMap K (QuadraticAlgebra K d 0) d := by
    simpa [Algebra.smul_def] using
      (QuadraticAlgebra.omega_pow_two_eq_add (R := K) (a := d) (b := 0))
  have hform :
      ((QuadraticMap.sq (R := QuadraticAlgebra K d 0)
        (A := QuadraticAlgebra K d 0)).traceTransfer K).basisRepr b =
        weightedSumSquares K ![(2 : K), 2 * d] := by
    ext v
    rw [QuadraticMap.basisRepr, QuadraticMap.comp_apply,
      QuadraticMap.traceTransfer_apply]
    have hrepr : b.equivFun.symm v =
        algebraMap K (QuadraticAlgebra K d 0) (v 0) +
          algebraMap K (QuadraticAlgebra K d 0) (v 1) * QuadraticAlgebra.omega := by
      rw [b.equivFun_symm_apply]
      simp [Fin.sum_univ_two, b, Algebra.smul_def]
    simp only [QuadraticMap.sq_apply, LinearEquiv.coe_coe]
    rw [hrepr, ← pow_two]
    -- Expand the square in coordinates so the explicit quadratic-algebra trace can simplify it.
    rw [show (algebraMap K (QuadraticAlgebra K d 0) (v 0) +
          algebraMap K (QuadraticAlgebra K d 0) (v 1) * QuadraticAlgebra.omega) ^ 2 =
        algebraMap K (QuadraticAlgebra K d 0) ((v 0) ^ 2 + d * (v 1) ^ 2) +
          (algebraMap K (QuadraticAlgebra K d 0) (2 * (v 0) * (v 1))) *
            QuadraticAlgebra.omega by
      simp only [map_add, map_pow, map_mul]
      rw [← hω, map_ofNat]
      ring]
    rw [QuadraticAlgebra.algebraTrace_eq_trace]
    simp [QuadraticAlgebra.trace_def, weightedSumSquares_apply, Fin.sum_univ_two]
    simp only [← map_pow, QuadraticAlgebra.algebraMap_re]
    ring
  let e := ((QuadraticMap.sq (R := QuadraticAlgebra K d 0)
    (A := QuadraticAlgebra K d 0)).traceTransfer K).isometryEquivBasisRepr b
  refine { toLinearEquiv := e.toLinearEquiv, map_app' := fun z => ?_ }
  rw [← hform]
  exact e.map_app z

/-- The isometry's underlying linear equivalence is the coordinate equivalence
for the basis `(1, ω)`. -/
private theorem traceTransferSqIsometryEquivWeightedSumSquares_toLinearEquiv (d : K) :
    (traceTransferSqIsometryEquivWeightedSumSquares d).toLinearEquiv =
      (QuadraticAlgebra.basis d 0).equivFun := by
  rfl

/-- The canonical isometry sends an element to its coordinates in `(1, ω)`. -/
@[simp]
theorem traceTransferSqIsometryEquivWeightedSumSquares_apply (d : K)
    (z : QuadraticAlgebra K d 0) :
    traceTransferSqIsometryEquivWeightedSumSquares d z =
      (QuadraticAlgebra.basis d 0).equivFun z := by
  change (traceTransferSqIsometryEquivWeightedSumSquares d).toLinearEquiv z = _
  rw [traceTransferSqIsometryEquivWeightedSumSquares_toLinearEquiv]

/-- The inverse canonical isometry reconstructs an element from its coordinates. -/
@[simp]
theorem traceTransferSqIsometryEquivWeightedSumSquares_symm_apply (d : K)
    (v : Fin 2 → K) :
    (traceTransferSqIsometryEquivWeightedSumSquares d).symm v =
      (QuadraticAlgebra.basis d 0).equivFun.symm v := by
  change (traceTransferSqIsometryEquivWeightedSumSquares d).toLinearEquiv.symm v = _
  rw [traceTransferSqIsometryEquivWeightedSumSquares_toLinearEquiv]

/-- The trace transfer of the unit line of a quadratic algebra is equivalent to
`⟨2, 2d⟩`, including for a split algebra. -/
theorem equivalent_traceTransfer_sq_weightedSumSquares (d : K) :
    ((QuadraticMap.sq (R := QuadraticAlgebra K d 0)
      (A := QuadraticAlgebra K d 0)).traceTransfer K).Equivalent
      (weightedSumSquares K ![(2 : K), 2 * d]) :=
  ⟨traceTransferSqIsometryEquivWeightedSumSquares d⟩

end TauCeti
