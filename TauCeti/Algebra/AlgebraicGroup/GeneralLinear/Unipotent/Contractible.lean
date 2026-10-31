/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.OneParameter
public import TauCeti.Analysis.Normed.Algebra.NilpotentExponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Contractibility of unipotent algebraic matrix groups

Let `K` be a field with a ring topology and continuous real scalar multiplication, for
example `ℝ` or `ℂ`, and let `I` define a closed subgroup of `GLₙ` over `K`. If every
`K`-point of the subgroup is unipotent, its point group is contractible, hence simply connected. No
connectedness or smoothness assumption is needed.

The contraction is `g ↦ exp ((1 - t) log g)`. The polynomial one-parameter subgroup
through a unipotent point stays in the algebraic subgroup, and Cayley–Hamilton gives
a common nilpotency bound. Thus continuity follows from the finite polynomial formulas
for exponential and logarithm, including at the identity and for empty matrices.

The algebraic input is `expSMulHom_log_mem_hopfIdealPointsSubgroup`; the topological
input is `Subgroup.contractibleSpace_of_expSMulHom_log_mem`. The resulting topology is
the subgroup topology inherited from the units of the matrix algebra.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (2015), §2.3.
-/

public section

namespace TauCeti.GeneralLinear

open IsNilpotent

variable {K : Type*} [Field K] [Algebra ℝ K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousSMul ℝ K] (n : ℕ)

/-- Over a field with a ring topology and continuous real scalar multiplication, a closed algebraic
subgroup of `GLₙ` whose points are all unipotent is contractible. In particular this
applies to real and complex unipotent algebraic matrix groups. -/
theorem contractibleSpace_hopfIdealPointsSubgroup
    (I : HopfIdeal K (coordinateHopfAlgebra K n))
    (hu : ∀ g ∈ hopfIdealPointsSubgroup n I K,
      IsNilpotent ((g : Matrix (Fin n) (Fin n) K) - 1)) :
    ContractibleSpace (hopfIdealPointsSubgroup n I K) := by
  let : CharZero K := Algebra.charZero_of_charZero ℝ K
  refine Subgroup.contractibleSpace_of_expSMulHom_log_mem
    (hopfIdealPointsSubgroup n I K) (n := n) ?_ ?_
  · intro g hg
    have hc : ((g : Matrix (Fin n) (Fin n) K) - 1).charpoly = Polynomial.X ^ n := by
      simpa only [Fintype.card_fin] using sub_eq_zero.mp
        (isNilpotent_iff_eq_zero.mp
          (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent (hu g hg)))
    have heval := congrArg
      (Polynomial.aeval ((g : Matrix (Fin n) (Fin n) K) - 1)) hc
    rw [Matrix.aeval_self_charpoly, Polynomial.aeval_X_pow] at heval
    exact heval.symm
  · intro g t
    have h := expSMulHom_log_mem_hopfIdealPointsSubgroup n I g
      (hu g g.property) g.property (algebraMap ℝ K t)
    simpa only [Algebra.algebraMap_self, RingHom.mapMatrix_id,
      expSMulHom_apply, toAdd_ofAdd, IsScalarTower.algebraMap_smul] using h

end TauCeti.GeneralLinear
