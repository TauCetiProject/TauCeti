/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic
public import TauCeti.RingTheory.Nilpotent.Log
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial one-parameter subgroups through unipotent matrices

Over a rational algebra, a nilpotent matrix `X` defines the polynomial one-parameter subgroup
`t ↦ exp(tX)`. Over a rational domain, if `exp X` belongs to a closed subgroup of
`GLₙ`, the whole polynomial curve factors through that subgroup. In particular, for a unipotent
matrix `g` in a closed subgroup, the curve `t ↦ exp(t log g)` remains in the subgroup, even on
points valued in nonreduced algebras.

The restriction is scheme-theoretic: every element of the subgroup's defining Hopf ideal is
sent to the zero polynomial. Integer parameters give powers of `exp X`, so infinitely many
roots force each pulled-back equation to vanish. No smoothness, connectedness or reducedness
assumption on the subgroup is required. This is the polynomial-curve input to showing that
`log g` belongs to its tangent Lie algebra.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
* The finite exponential and logarithm are `IsNilpotent.exp` and `IsNilpotent.log`.
-/

public section

open WithConv
open scoped Polynomial

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] [Algebra ℚ R] (n : ℕ)
variable {X : Matrix (Fin n) (Fin n) R}

/-- The polynomial coordinate map of the curve `t ↦ exp(tX)`.
Its direction is opposite to the morphism from the affine line into `GLₙ`. -/
noncomputable def nilpotentOneParameterCoordinateMap (hX : IsNilpotent X) :
    coordinateHopfAlgebra R n →ₐ[R] R[X] :=
  (generalLinearToPoint n
    (expSMulHom R[X] (hX.map Polynomial.C.mapMatrix)
      (Multiplicative.ofAdd Polynomial.X))).ofConv

/-- The coordinate map represents the polynomial-valued exponential point. -/
@[simp]
theorem toConv_nilpotentOneParameterCoordinateMap (hX : IsNilpotent X) :
    toConv (nilpotentOneParameterCoordinateMap n hX) =
      generalLinearToPoint n
        (expSMulHom R[X] (hX.map Polynomial.C.mapMatrix)
          (Multiplicative.ofAdd Polynomial.X)) :=
  (rfl)

/-- A generic matrix entry pulls back to the corresponding entry of the polynomial
exponential matrix. These entries determine the coordinate map. -/
@[simp]
theorem nilpotentOneParameterCoordinateMap_apply_X (hX : IsNilpotent X) (i j : Fin n) :
    nilpotentOneParameterCoordinateMap n hX
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      IsNilpotent.exp ((Polynomial.X : R[X]) • Polynomial.C.mapMatrix X) i j := by
  rw [nilpotentOneParameterCoordinateMap, generalLinearToPoint_apply]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) R[X] ↦ M i j)
    (coe_expSMulHom R[X] (hX.map Polynomial.C.mapMatrix)
      (Multiplicative.ofAdd Polynomial.X))

/-- Evaluating the polynomial curve at `t` gives the corresponding one-parameter-group value. -/
@[simp]
theorem aeval_comp_nilpotentOneParameterCoordinateMap (hX : IsNilpotent X) (t : R) :
    (Polynomial.aeval t).comp (nilpotentOneParameterCoordinateMap n hX) =
      (generalLinearToPoint n (expSMulHom R hX (Multiplicative.ofAdd t))).ofConv := by
  apply WithConv.toConv_injective
  rw [nilpotentOneParameterCoordinateMap, toConv_comp_generalLinearToPoint_ofConv,
    Matrix.GeneralLinearGroup.map,
    map_expSMulHom R[X] _ _ _ (fun r a ↦ Matrix.map_smul' _ r a (map_mul _))]
  rw [toConv_ofConv]
  apply congrArg (generalLinearToPoint n)
  apply Units.ext
  simp only [coe_expSMulHom, toAdd_ofAdd]
  congr 1
  ext i j
  simp

section ClosedSubgroup

variable [IsDomain R]
variable {Y : Matrix (Fin n) (Fin n) R}

/-- The polynomial exponential curve through a point of a closed subgroup is itself a
polynomial-valued point of that subgroup. -/
theorem expSMulHom_ofAdd_X_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (hY : IsNilpotent Y)
    (hI : nilpotentExpUnit hY ∈ hopfIdealPointsSubgroup n I R) :
    expSMulHom R[X] (hY.map Polynomial.C.mapMatrix)
        (Multiplicative.ofAdd Polynomial.X) ∈ hopfIdealPointsSubgroup n I R[X] := by
  rw [mem_hopfIdealPointsSubgroup_iff]
  intro a ha
  rw [pointsMulEquiv_symm_apply]
  rw [← toConv_nilpotentOneParameterCoordinateMap n hY, ofConv_toConv]
  have : CharZero R := Algebra.charZero_of_charZero ℚ R
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := R))).mono
  rintro _ ⟨m, rfl⟩
  have hm := (mem_hopfIdealPointsSubgroup_iff n I R
    (expSMulHom R hY (Multiplicative.ofAdd (m : R)))).mp
      (expSMulHom_ofAdd_natCast R hY m ▸
        (hopfIdealPointsSubgroup n I R).pow_mem hI m) a ha
  rw [pointsMulEquiv_symm_apply] at hm
  have heval := AlgHom.congr_fun (aeval_comp_nilpotentOneParameterCoordinateMap n hY (m : R)) a
  simpa only [Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_id,
    Algebra.algebraMap_self, AlgHom.comp_apply, pointsMulEquiv_symm_apply] using heval.trans hm

/-- Every algebra-valued parameter of `t ↦ exp(t log g)` stays in a closed subgroup containing
the unipotent point `g`. The value algebra may be nonreduced. -/
theorem map_aeval_expSMulHom_log_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (g : Matrix.GeneralLinearGroup (Fin n) R)
    (hg : IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1))
    (hI : g ∈ hopfIdealPointsSubgroup n I R)
    {A : Type v} [CommRing A] [Algebra R A] (t : A) :
    Matrix.GeneralLinearGroup.map (Polynomial.aeval (R := R) t).toRingHom
        (expSMulHom R[X]
          ((IsNilpotent.isNilpotent_log hg).map Polynomial.C.mapMatrix)
          (Multiplicative.ofAdd Polynomial.X)) ∈ hopfIdealPointsSubgroup n I A :=
  map_mem_hopfIdealPointsSubgroup n I (Polynomial.aeval t)
    (expSMulHom_ofAdd_X_mem_hopfIdealPointsSubgroup n I (IsNilpotent.isNilpotent_log hg)
      (by simpa only [Units.nilpotentExpUnit_log g hg] using hI))

end ClosedSubgroup

end TauCeti.GeneralLinear
