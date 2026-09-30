/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

/-!
# Trace transfer in a quadratic algebra

If `x` generates a degree-two algebra over a field and `x² = d`, the basis `(1, x)`
identifies the trace transfer of the unit line with `⟨2, 2d⟩`. This supplies the
general degree-two version of the trace-form calculation, with an explicit isometry
whose coordinates can be used to compute invariants of transferred forms.

The trace of `x` vanishes by computing the diagonal of its multiplication matrix
in `(1, x)`; this also covers split and nonreduced algebras.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
-/

public section

namespace TauCeti

open QuadraticMap QuadraticForm

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

/-- In square-root coordinates, the trace transfer of the unit line is `⟨2, 2d⟩`. -/
theorem traceTransfer_sq_basisRepr {x : L} {d : K}
    (hfin : Module.finrank K L = 2) (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L d) :
    ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).basisRepr
      (quadraticExtensionBasis K L hx hfin) =
      weightedSumSquares K ![(2 : K), 2 * d] := by
  have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (by omega)
  let b := quadraticExtensionBasis K L hx hfin
  have htrace : Algebra.trace K L x = 0 := by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_two]
    have hzero : Algebra.leftMulMatrix b x 0 0 = 0 := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, quadraticExtensionBasis_zero, mul_one]
      simp [show x = b 1 from (quadraticExtensionBasis_one K L hx hfin).symm]
    have hone : Algebra.leftMulMatrix b x 1 1 = 0 := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, quadraticExtensionBasis_one, ← pow_two, hx2]
      simp [show algebraMap K L d = d • b 0 by
        rw [quadraticExtensionBasis_zero, Algebra.smul_def, mul_one]]
    simp [hzero, hone]
  ext v
  rw [QuadraticMap.basisRepr, QuadraticMap.comp_apply,
    QuadraticMap.traceTransfer_sq, LinearMap.BilinMap.toQuadraticMap_apply,
    Algebra.traceForm_apply]
  simp only [LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    Fin.sum_univ_two, quadraticExtensionBasis_zero, quadraticExtensionBasis_one,
    Algebra.smul_def]
  have hpoly :
      ((algebraMap K L) (v 0) * 1 + (algebraMap K L) (v 1) * x) *
          ((algebraMap K L) (v 0) * 1 + (algebraMap K L) (v 1) * x) =
        (algebraMap K L) ((v 0) ^ 2 + d * (v 1) ^ 2) +
          (algebraMap K L) (2 * (v 0) * (v 1)) * x := by
    simp only [map_add, map_pow, map_mul]
    calc
      _ = (algebraMap K L) (v 0) ^ 2 +
            (algebraMap K L) (v 1) ^ 2 * x ^ 2 +
            (algebraMap K L) (2 * v 0 * v 1) * x := by
          simp only [map_mul, map_ofNat]
          ring
      _ = _ := by rw [hx2]; simp only [map_mul]; ring
  have hcross :
      (Algebra.trace K L) ((algebraMap K L) (2 * v 0 * v 1) * x) = 0 := by
    rw [← Algebra.smul_def, map_smul, htrace, smul_zero]
  rw [hpoly, map_add, Algebra.trace_algebraMap, hfin]
  rw [hcross]
  simp [weightedSumSquares_apply, Fin.sum_univ_two, nsmul_eq_mul]
  ring

/-- The square-root coordinate map is an isometry from the transferred unit line
to the diagonal form `⟨2, 2d⟩`. -/
noncomputable def traceTransferSqIsometryEquivWeightedSumSquaresOfSq
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) :
    ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).IsometryEquiv
      (weightedSumSquares K ![(2 : K), 2 * d]) := by
  let b := quadraticExtensionBasis K L hx hfin
  let e := ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).isometryEquivBasisRepr b
  refine { e with map_app' := fun z => ?_ }
  rw [← traceTransfer_sq_basisRepr hfin hx hx2]
  exact e.map_app z

/-- The isometry's underlying linear equivalence is the coordinate equivalence
for the square-root basis. -/
private theorem traceTransferSqIsometryEquivWeightedSumSquaresOfSq_toLinearEquiv
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) :
    (traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2).toLinearEquiv =
      (quadraticExtensionBasis K L hx hfin).equivFun := by
  rfl

/-- The isometry uses coordinates in the square-root basis. -/
@[simp]
theorem traceTransferSqIsometryEquivWeightedSumSquaresOfSq_apply
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d)
    (z : L) :
    traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2 z =
      (quadraticExtensionBasis K L hx hfin).equivFun z := by
  simpa only [IsometryEquiv.coe_toLinearEquiv] using
    LinearEquiv.congr_fun
      (traceTransferSqIsometryEquivWeightedSumSquaresOfSq_toLinearEquiv hfin hx hx2) z

/-- The inverse isometry reconstructs an element from its square-root coordinates. -/
@[simp]
theorem traceTransferSqIsometryEquivWeightedSumSquaresOfSq_symm_apply
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d)
    (v : Fin 2 → K) :
    (traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2).symm v =
      (quadraticExtensionBasis K L hx hfin).equivFun.symm v := by
  simpa only [IsometryEquiv.coe_symm_toLinearEquiv, IsometryEquiv.coe_toLinearEquiv] using
    LinearEquiv.congr_fun
      (congrArg LinearEquiv.symm
        (traceTransferSqIsometryEquivWeightedSumSquaresOfSq_toLinearEquiv hfin hx hx2)) v

/-- The trace transfer of the unit line in a degree-two algebra generated by
`x² = d` is equivalent to `⟨2, 2d⟩`. -/
theorem equivalent_traceTransfer_sq_weightedSumSquares_of_sq
    {x : L} {d : K} (hfin : Module.finrank K L = 2)
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L d) :
    ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Equivalent
      (weightedSumSquares K ![(2 : K), 2 * d]) :=
  ⟨traceTransferSqIsometryEquivWeightedSumSquaresOfSq hfin hx hx2⟩

end TauCeti
