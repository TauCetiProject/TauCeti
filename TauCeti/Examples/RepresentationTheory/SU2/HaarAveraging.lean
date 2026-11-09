/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.LieAlgebra
public import TauCeti.RepresentationTheory.Compact.BilinearForm
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Topology.Algebra.Module.BilinearForm
/-!
# The weighted compact SU(2) metric example

This example uses the native Lie algebra of the special unitary subgroup of GL₂. Its Pauli
coordinates have the actual native group adjoint, as proved in
`TauCeti.SU2.adjointRepresentation_pauliLieAlgebraEquiv`. Averaging a diagonal form gives the
mean of its weights times the standard form.

The weighted example's basis is z, x, y, so its weights (1, 2, 3) become (2, 3, 1) in native
Pauli order.
The weighted form pairs ⁅e₁, e₂⁆ with e₃ to minus six and e₂ with ⁅e₁, e₃⁆ to four. Twice the
standard form gives minus four and four; `su2_integral_pauliForm` identifies it with the Haar
average. The Killing form takes minus eight on the first basis vector.

## Main definitions

* `TauCeti.Examples.LieGroups.su2PauliForm`: the starting diagonal form on the native Lie algebra.

## Main results

* `TauCeti.Examples.LieGroups.su2PauliForm_apply`: evaluation in native Pauli coordinates.
* `TauCeti.Examples.LieGroups.su2PauliForm_isSymm` and `su2PauliForm_posDef`: symmetry and
  positivity for strictly positive weights.
* `TauCeti.Examples.LieGroups.su2_integral_weightedPauliBasis`: the specified Gram matrix.
* `TauCeti.Examples.LieGroups.su2_integral_pauliForm`: the native inverse-adjoint Haar integral.
* `TauCeti.Examples.LieGroups.su2_weightedPauliForm_skew_values`: the explicit adjoint
  pairings and Killing-form value.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), Lemma 10.4.14, for Haar averaging.
-/

public noncomputable section

open Matrix TauCeti TauCeti.Lie MeasureTheory
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
namespace TauCeti.Examples.LieGroups

-- Cache the canonical group properties with the matrix operator norm in scope.
private local instance : IsTopologicalGroup SU2 :=
  TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti

private local instance : CompactSpace SU2 :=
  TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti

local notation "S" => lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
  (GLSpecialUnitary (Fin 2) ℂ)

/-- A diagonal Pauli form, transported to the native real SU(2) Lie algebra. -/
def su2PauliForm (weights : Fin 3 → ℝ) : LinearMap.BilinForm ℝ S :=
  (Matrix.toBilin' (Matrix.diagonal weights)).compl₁₂
    SU2.pauliLieAlgebraEquiv.symm.toLinearMap SU2.pauliLieAlgebraEquiv.symm.toLinearMap

/-- Evaluation of a Pauli form on native Pauli Lie-algebra elements. -/
@[simp]
theorem su2PauliForm_apply (weights x y : Fin 3 → ℝ) :
    su2PauliForm weights (SU2.pauliLieAlgebraEquiv x) (SU2.pauliLieAlgebraEquiv y) =
      ∑ i, weights i * x i * y i := by
  simp [su2PauliForm, LinearMap.compl₁₂_apply, Matrix.toBilin'_apply', dotProduct,
    Matrix.mulVec_diagonal, mul_comm, mul_left_comm]

/-- Every diagonal Pauli form is symmetric. -/
theorem su2PauliForm_isSymm (weights : Fin 3 → ℝ) : (su2PauliForm weights).IsSymm := by
  constructor
  intro X Y
  exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr (Matrix.isSymm_diagonal weights)).eq _ _

/-- Strictly positive coordinate weights give a positive-definite native form. -/
theorem su2PauliForm_posDef (weights : Fin 3 → ℝ) (hweights : ∀ i, 0 < weights i) :
    (su2PauliForm weights).toQuadraticMap.PosDef := by
  intro X hX
  have hx : SU2.pauliLieAlgebraEquiv.symm X ≠ 0 :=
    (map_ne_zero_iff SU2.pauliLieAlgebraEquiv.symm
      SU2.pauliLieAlgebraEquiv.symm.injective).mpr hX
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply, su2PauliForm,
    LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Matrix.toBilin'_apply', star_trivial] using
    (Matrix.posDef_diagonal_iff.mpr hweights).dotProduct_mulVec_pos hx

local notation "A" => LeftInvariantDerivation
  𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) (Matrix (Fin 2) (Fin 2) ℂ)ˣ

-- Keep the canonical native norms in the local instance cache for the nested operator spaces.
private local instance : NormedAddCommGroup A := LeftInvariantDerivation.instNormedAddCommGroup
private local instance : NormedSpace ℝ A := LeftInvariantDerivation.instNormedSpace
private local instance : NormedAddCommGroup S := inferInstance
private local instance : NormedSpace ℝ S := inferInstance

private local instance : NormedAddCommGroup (S →L[ℝ] S →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (S →L[ℝ] S →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance : FiniteDimensional ℝ S :=
  FiniteDimensional.of_injective SU2.pauliLieAlgebraEquiv.symm.toLinearMap
    SU2.pauliLieAlgebraEquiv.symm.injective

private local instance : MeasurableSpace SU2 := borel SU2
private local instance : BorelSpace SU2 := ⟨rfl⟩

private def pauliFormL (weights : Fin 3 → ℝ) : S →L[ℝ] S →L[ℝ] ℝ :=
  (su2PauliForm weights).toContinuousBilinearMap

private theorem pauliFormL_apply (weights : Fin 3 → ℝ) (X Y : S) :
    pauliFormL weights X Y = su2PauliForm weights X Y := by
  rw [pauliFormL, ← ContinuousLinearMap.toBilinForm_apply,
    LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap]

private def cycle : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0; 0,0,1; 1,0,0]

private theorem cycle_mem : cycle ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  constructor
  · apply (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [cycle, Matrix.mul_apply, Fin.sum_univ_three]
  · norm_num [cycle, Matrix.det_fin_three]

private theorem form_one_invariant :
    Representation.IsInvariantForm SU2.adjointRepresentation.toRepresentation
      (pauliFormL (fun _ ↦ 1)).toBilinForm := by
  apply Representation.isInvariantForm_iff.mpr
  intro g X Y
  obtain ⟨x, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective X
  obtain ⟨y, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective Y
  simp only [ContRepresentation.toRepresentation_apply, ContinuousLinearMap.toBilinForm_apply,
    pauliFormL_apply,
    SU2.adjointRepresentation_pauliLieAlgebraEquiv, su2PauliForm_apply, one_mul]
  simpa only [dotProduct, SU2.coe_toSO3] using
    dotProduct_pauliRotation_mulVec
      (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup g) x y

private theorem cycle_sum_apply (weights : Fin 3 → ℝ) (g : SU2)
    (hgc : (SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) = cycle)
    (hgcc : (SU2.toSO3 (g * g) : Matrix (Fin 3) (Fin 3) ℝ) = cycle * cycle) (X Y : S) :
    su2PauliForm weights X Y + su2PauliForm weights
        (SU2.adjointRepresentation g X) (SU2.adjointRepresentation g Y) +
      su2PauliForm weights (SU2.adjointRepresentation (g * g) X)
        (SU2.adjointRepresentation (g * g) Y) =
      (weights 0 + weights 1 + weights 2) * su2PauliForm (fun _ ↦ 1) X Y := by
  obtain ⟨x, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective X
  obtain ⟨y, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective Y
  simp only [SU2.adjointRepresentation_pauliLieAlgebraEquiv, su2PauliForm_apply,
    hgc, hgcc, Fin.sum_univ_three]
  simp [cycle, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem cycle_sum (weights : Fin 3 → ℝ) :
    ∃ g : SU2, pauliFormL weights + (pauliFormL weights).bilinearComp
        (SU2.adjointRepresentation g) (SU2.adjointRepresentation g) +
      (pauliFormL weights).bilinearComp (SU2.adjointRepresentation (g * g))
        (SU2.adjointRepresentation (g * g)) =
        (weights 0 + weights 1 + weights 2) • pauliFormL (fun _ ↦ 1) := by
  obtain ⟨g, hg⟩ := SU2.toSO3_surjective ⟨cycle, cycle_mem⟩
  have hgc : (SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) = cycle :=
    congrArg Subtype.val hg
  have hgcc : (SU2.toSO3 (g * g) : Matrix (Fin 3) (Fin 3) ℝ) = cycle * cycle := by
    simp [hgc]
  refine ⟨g, ?_⟩
  ext X Y
  simpa only [add_apply, smul_apply, ContinuousLinearMap.bilinearComp_apply,
    pauliFormL_apply, smul_eq_mul] using cycle_sum_apply weights g hgc hgcc X Y

-- Keep the native operator packaged, so scalar identities do not elaborate its norm data again.
private def nativeAverage : (S →L[ℝ] S →L[ℝ] ℝ) →L[ℝ] S →L[ℝ] S →L[ℝ] ℝ :=
  ContRepresentation.averageBilinearForm SU2.adjointRepresentation
    SU2.continuous_adjointRepresentation

private theorem average_pauliForm (weights : Fin 3 → ℝ) (X Y : S) :
    nativeAverage (pauliFormL weights) X Y =
      (weights 0 + weights 1 + weights 2) / 3 * su2PauliForm (fun _ ↦ 1) X Y := by
  obtain ⟨g, hg⟩ := cycle_sum weights
  have h := congrArg nativeAverage hg
  simp only [nativeAverage, map_add, map_smul,
    ContRepresentation.averageBilinearForm_bilinearComp,
    ContRepresentation.averageBilinearForm_eq_self SU2.adjointRepresentation
      SU2.continuous_adjointRepresentation _ form_one_invariant] at h
  have he := congrArg (fun B ↦ B X Y) h
  simp only [add_apply, smul_apply, smul_eq_mul, pauliFormL_apply] at he
  dsimp only [nativeAverage]
  linarith

/-- The pairings of ⁅e₁, e₂⁆ with e₃ and of e₂ with ⁅e₁, e₃⁆ are minus six and four for the
weighted form, and minus four and four for twice the standard form.
The Killing value is minus eight.
-/
theorem su2_weightedPauliForm_skew_values :
    let e₁ := SU2.pauliLieAlgebraEquiv (Pi.single 2 1)
    let e₂ := SU2.pauliLieAlgebraEquiv (Pi.single 0 1)
    let e₃ := SU2.pauliLieAlgebraEquiv (Pi.single 1 1)
    su2PauliForm ![2, 3, 1] ⁅e₁, e₂⁆ e₃ = -6 ∧
      su2PauliForm ![2, 3, 1] e₂ ⁅e₁, e₃⁆ = 4 ∧
      (2 • su2PauliForm (fun _ ↦ 1)) ⁅e₁, e₂⁆ e₃ = -4 ∧
      (2 • su2PauliForm (fun _ ↦ 1)) e₂ ⁅e₁, e₃⁆ = 4 ∧
      killingForm ℝ S e₁ e₁ = -8 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [SU2.lie_pauliLieAlgebraEquiv, su2PauliForm_apply,
      SU2.killingForm_pauliLieAlgebraEquiv, cross_apply, dotProduct, Fin.sum_univ_three]

/-- The normalized Haar integral of the actual native inverse-adjoint pullbacks is the mean
weight times the standard native Pauli form. -/
theorem su2_integral_pauliForm (weights : Fin 3 → ℝ) (X Y : S) :
    letI : IsTopologicalGroup SU2 :=
      TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : CompactSpace SU2 :=
      TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : MeasurableSpace SU2 := borel SU2
    letI : BorelSpace SU2 := ⟨rfl⟩
    (∫ g : SU2, su2PauliForm weights
      (SU2.adjointRepresentation g⁻¹ X) (SU2.adjointRepresentation g⁻¹ Y) ∂haarProb SU2) =
      (weights 0 + weights 1 + weights 2) / 3 * su2PauliForm (fun _ ↦ 1) X Y := by
  have h := average_pauliForm weights X Y
  rw [nativeAverage, ContRepresentation.averageBilinearForm_apply] at h
  simpa only [pauliFormL_apply] using h

/-- In the ordered basis z, x, y and with starting weights (1, 2, 3), the actual normalized
Haar average has Gram matrix twice the identity. -/
theorem su2_integral_weightedPauliBasis (j k : Fin 3) :
    letI : IsTopologicalGroup SU2 :=
      TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : CompactSpace SU2 :=
      TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : MeasurableSpace SU2 := borel SU2
    letI : BorelSpace SU2 := ⟨rfl⟩
    let X := SU2.pauliLieAlgebraEquiv (Pi.single (![(2 : Fin 3), 0, 1] j) 1)
    let Y := SU2.pauliLieAlgebraEquiv (Pi.single (![(2 : Fin 3), 0, 1] k) 1)
    (∫ g : SU2, su2PauliForm ![2, 3, 1]
      (SU2.adjointRepresentation g⁻¹ X) (SU2.adjointRepresentation g⁻¹ Y) ∂haarProb SU2) =
      if j = k then 2 else 0 := by
  dsimp only
  rw [su2_integral_pauliForm]
  fin_cases j <;> fin_cases k <;> norm_num [su2PauliForm_apply, Fin.sum_univ_three]

end TauCeti.Examples.LieGroups
