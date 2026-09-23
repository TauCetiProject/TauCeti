/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.CAR.Isotypic
public import TauCeti.Algebra.Lie.GeneralLinear.CAR.WeightMultiplicity
public import TauCeti.Algebra.Lie.GeneralLinear.CompleteReducibility
public import TauCeti.Algebra.Lie.UniversalEnveloping.Multiplicity
import TauCeti.Algebra.Lie.Weights.Multiplicity
import TauCeti.Data.Nat.Choose
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# The numerical CAR isotypic decomposition

The left-regular Clifford algebra for the trace form on `M_N` is already known to be isotypic of
type `glIrreducible N (glHalfStaircase K N)`.  Its top weight space is one-dimensional in the
named irreducible and has dimension `2 ^ (N * (N + 1) / 2)` in the CAR module.  This file turns
those two facts into the numerical multiplicity, the dimension of the simple type, and the
resulting direct-sum decomposition.

The dimension calculation also records the complementary exponent identity
`N * (N + 1) / 2 + N * (N - 1) / 2 = N * N`, matching the total Clifford dimension.

The construction uses the multiplicity and isotypic-component APIs rather than unfolding either
the CAR occupation calculation or the chosen carrier for `glIrreducible`.

## Main results

* `isotypicMultiplicity_glIrreducible_car`: the CAR multiplicity is
  `2 ^ (N * (N + 1) / 2)`.
* `finrank_glIrreducible_glHalfStaircase`: the named simple carrier has dimension
  `2 ^ (N * (N - 1) / 2)`.
* `nonempty_lieModuleEquiv_directSum_glIrreducible_car`: the left-regular CAR module is the
  direct sum of the stated number of copies of that simple carrier.

The mathematical decomposition is the `gl_N` instance described by Panyushev, *The exterior
algebra and "spin" of an orthogonal g-module*, Proposition 2.4 and Example 2.5(1).
-/

public section

open scoped BigOperators DirectSum TauCeti

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.decEq

noncomputable section

/-! ### Multiplicity and simple dimension -/

/-- The half-staircase simple occurs in the left-regular CAR module with multiplicity
`2 ^ (N * (N + 1) / 2)`. -/
@[simp]
theorem isotypicMultiplicity_glIrreducible_car
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (N : ℕ) :
    _root_.LieModule.isotypicMultiplicity K (Matrix (Fin N) (Fin N) K)
      (CliffordAlgebra (traceQuadraticForm K (Fin N)))
      (glIrreducible N (glHalfStaircase K N)) =
      2 ^ (N * (N + 1) / 2) := by
  let _ := isIrreducible_glIrreducible (K := K)
    (isGlDominantIntegral_glHalfStaircase (F := K) N)
  let _ : Module.Finite K (CliffordAlgebra (traceQuadraticForm K (Fin N))) := inferInstance
  let _ := complementedLattice_lieSubmodule_car K (Fin N)
  calc
    _ = Module.finrank K (LieModule.weightSpace
        (CliffordAlgebra (traceQuadraticForm K (Fin N)))
        ((glWeightEquiv K (Fin N) (glHalfStaircase K N) :
          Module.Dual K (diagonalCartan K (Fin N))) : diagonalCartan K (Fin N) → K)) :=
      (isIsotypicOfType_glIrreducible_car K N).isotypicMultiplicity_eq_finrank_weightSpace _
        (finrank_weightSpace_glIrreducible
          (isGlDominantIntegral_glHalfStaircase (F := K) N))
    _ = _ := finrank_weightSpace_glHalfStaircase_car N

/-- The half-staircase simple has dimension `2 ^ (N * (N - 1) / 2)`. -/
@[simp]
theorem finrank_glIrreducible_glHalfStaircase
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (N : ℕ) :
    Module.finrank K (glIrreducible N (glHalfStaircase K N)) =
      2 ^ (N * (N - 1) / 2) := by
  let _ := isIrreducible_glIrreducible (K := K)
    (isGlDominantIntegral_glHalfStaircase (F := K) N)
  let _ : Module.Finite K (CliffordAlgebra (traceQuadraticForm K (Fin N))) := inferInstance
  let _ := complementedLattice_lieSubmodule_car K (Fin N)
  have hdim := LieModule.finrank_of_isIsotypicOfType
    (M := CliffordAlgebra (traceQuadraticForm K (Fin N)))
    (S := glIrreducible N (glHalfStaircase K N))
    (isIsotypicOfType_glIrreducible_car K N)
  rw [finrank_cliffordAlgebra_traceQuadraticForm] at hdim
  simp only [isotypicMultiplicity_glIrreducible_car K N, Fintype.card_fin] at hdim
  have hexp : N * (N + 1) / 2 + N * (N - 1) / 2 = N * N := by
    calc
      N * (N + 1) / 2 + N * (N - 1) / 2 =
          N * (N + 1) / 2 + N.choose 2 := by
        rw [Nat.choose_two_right]
      _ = N.choose 2 + N * (N + 1) / 2 := Nat.add_comm _ _
      _ = N * N := Nat.choose_two_add_mul_succ_div_two N
  have hpos : 0 < 2 ^ (N * (N + 1) / 2) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← pow_add, hexp]
  exact hdim.symm

/-! ### The direct-sum endpoint -/

/-- The left-regular CAR module is the direct sum of
`2 ^ (N * (N + 1) / 2)` copies of the half-staircase simple. -/
theorem nonempty_lieModuleEquiv_directSum_glIrreducible_car
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (N : ℕ) :
    Nonempty ((CliffordAlgebra (traceQuadraticForm K (Fin N))) ≃ₗ⁅K, Matrix (Fin N) (Fin N) K⁆
      (DirectSum (Fin (2 ^ (N * (N + 1) / 2)))
        (fun _ => glIrreducible N (glHalfStaircase K N)))) := by
  let _ := isIrreducible_glIrreducible (K := K)
    (isGlDominantIntegral_glHalfStaircase (F := K) N)
  let _ : Module.Finite K (CliffordAlgebra (traceQuadraticForm K (Fin N))) := inferInstance
  let _ := complementedLattice_lieSubmodule_car K (Fin N)
  have e := LieModule.nonempty_lieModuleEquiv_of_isIsotypicOfType
    (M := CliffordAlgebra (traceQuadraticForm K (Fin N)))
    (S := glIrreducible N (glHalfStaircase K N))
    (isIsotypicOfType_glIrreducible_car K N)
  rw [isotypicMultiplicity_glIrreducible_car K N] at e
  exact e

end
end TauCeti
