/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.OneParameter
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.PolynomialCurve
import TauCeti.LinearAlgebra.Matrix.Exponential.Polynomial

/-!
# Logarithms of unipotent points are subgroup tangent vectors

Over a rational domain, the finite logarithm of a unipotent matrix in a closed subgroup
belongs to the subgroup's actual tangent Lie algebra. The polynomial curve
`t ↦ exp(t log g)` already factors through the subgroup by
`expSMulHom_ofAdd_X_mem_hopfIdealPointsSubgroup`. Its velocity is `log g`, so that
velocity annihilates the defining Hopf ideal.

No smoothness, reducedness, connectedness or unipotence assumption on the whole subgroup
is needed. Only the chosen point must be unipotent. The theorem is expressed through
`HopfIdeal.lieSubalgebra` and `tangentLieEquivMatrix`, so it uses the existing
closed-subgroup differential rather than a separate matrix tangent predicate.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
* The finite logarithm and its inverse identity are `IsNilpotent.log` and
  `Units.nilpotentExpUnit_log`.
-/

public section

namespace TauCeti.GeneralLinear

open Polynomial WithConv

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] (n : ℕ)
variable {X : Matrix (Fin n) (Fin n) R}

/-- The polynomial exponential curve starts at the identity of `GLₙ`. -/
-- Use this as a named rewrite: the general evaluation simp lemma simplifies its left side first.
theorem aeval_zero_comp_nilpotentOneParameterCoordinateMap (hX : IsNilpotent X) :
    (aeval (0 : R)).comp (nilpotentOneParameterCoordinateMap n hX) =
      _root_.Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n) := by
  rw [aeval_comp_nilpotentOneParameterCoordinateMap]
  have hzero : expSMulHom R hX (Multiplicative.ofAdd (0 : R)) = 1 := map_one _
  rw [hzero, ← pointsMulEquiv_symm_apply, map_one]
  rfl

/-- The velocity of the polynomial exponential curve is its nilpotent matrix parameter. -/
@[simp]
theorem tangentMatrix_polynomialCurveTangent_nilpotentOneParameterCoordinateMap
    (hX : IsNilpotent X) :
    tangentMatrix n (Bialgebra.polynomialCurveTangent
      (nilpotentOneParameterCoordinateMap n hX)
      (aeval_zero_comp_nilpotentOneParameterCoordinateMap n hX)) = X := by
  ext i j
  rw [tangentMatrix_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Bialgebra.polynomialCurveTangent_apply,
    nilpotentOneParameterCoordinateMap_apply_X]
  exact Matrix.coeff_one_exp_X_smul_map_C hX i j

variable [IsDomain R]

/-- If the exponential of a nilpotent matrix belongs to a closed subgroup, the matrix
belongs to its tangent Lie algebra. -/
theorem tangentLieEquivMatrix_symm_mem_lieSubalgebra_of_exp_mem
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (hX : IsNilpotent X)
    (hI : nilpotentExpUnit hX ∈ hopfIdealPointsSubgroup n I R) :
    (tangentLieEquivMatrix (R := R) (B := R) n).symm X ∈ I.lieSubalgebra := by
  let d := Bialgebra.polynomialCurveTangent
    (nilpotentOneParameterCoordinateMap n hX)
    (aeval_zero_comp_nilpotentOneParameterCoordinateMap n hX)
  have hd : tangentLieEquivMatrix n d = X := by
    simpa only [tangentLieEquivMatrix_apply] using
      tangentMatrix_polynomialCurveTangent_nilpotentOneParameterCoordinateMap n hX
  rw [← hd, LieEquiv.symm_apply_apply, HopfIdeal.mem_lieSubalgebra_iff]
  intro a ha
  apply (Bialgebra.CounitAlgebra.algEquivSelf R (coordinateHopfAlgebra R n) R).injective
  rw [map_zero, Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Bialgebra.polynomialCurveTangent_apply]
  have hcurve := (mem_hopfIdealPointsSubgroup_iff n I R[X] _).mp
    (expSMulHom_ofAdd_X_mem_hopfIdealPointsSubgroup n I hX hI) a ha
  rw [pointsMulEquiv_symm_apply,
    ← toConv_nilpotentOneParameterCoordinateMap n hX, ofConv_toConv] at hcurve
  rw [hcurve, coeff_zero]

/-- The finite logarithm of a unipotent point of any closed subgroup of `GLₙ` lies in
that subgroup's tangent Lie algebra. -/
theorem log_mem_lieSubalgebra
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (g : Matrix.GeneralLinearGroup (Fin n) R)
    (hg : IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1))
    (hI : g ∈ hopfIdealPointsSubgroup n I R) :
    (tangentLieEquivMatrix (R := R) (B := R) n).symm
      (IsNilpotent.log (g : Matrix (Fin n) (Fin n) R)) ∈ I.lieSubalgebra := by
  apply tangentLieEquivMatrix_symm_mem_lieSubalgebra_of_exp_mem n I
    (IsNilpotent.isNilpotent_log hg)
  simpa only [Units.nilpotentExpUnit_log g hg] using hI

end TauCeti.GeneralLinear
