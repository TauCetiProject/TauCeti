/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary
public import TauCeti.RepresentationTheory.SU2.Adjoint
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import Mathlib.Algebra.Lie.TraceForm
import TauCeti.RepresentationTheory.Continuous.Subrepresentation
import TauCeti.Topology.Algebra.Star.Unitary

/-!
# Pauli coordinates on the native Lie algebra of SU(2)

Multiplication by the imaginary unit identifies the real Pauli coordinates with the native
Lie subalgebra of the special unitary subgroup of the general linear group. This equivalence
retains the actual left-invariant derivation carrier. It intertwines its bracket with minus twice
the cross product and its group adjoint with the native double cover `SU2.toSO3`.

The coordinate order is x, y, z.

## Main definitions

* `TauCeti.SU2.pauliLieAlgebraEquiv`: real coordinates on the native subgroup Lie algebra.
* `TauCeti.SU2.adjointRepresentation`: the actual native adjoint restricted to that Lie algebra.

## Main results

* `TauCeti.SU2.unitsLieAlgebraLieEquiv_pauliLieAlgebraEquiv`: native matrix evaluation.
* `TauCeti.SU2.coe_adjointRepresentation_apply`: the restricted action in the ambient algebra.
* `TauCeti.SU2.continuous_adjointRepresentation`: continuity of the native adjoint.
* `TauCeti.SU2.adjointRepresentation_pauliLieAlgebraEquiv`: the adjoint in Pauli coordinates.
* `TauCeti.SU2.lie_pauliLieAlgebraEquiv`: the native Lie bracket in these coordinates.
* `TauCeti.SU2.Ad_pauliLieAlgebraEquiv`: compatibility with the actual group adjoint.
* `TauCeti.SU2.killingForm_pauliLieAlgebraEquiv`: the Killing form is minus eight times the
  standard coordinate dot product.
* `TauCeti.SU2.killingForm_self_neg`: the Killing form is strictly negative on nonzero vectors.

## References

* `TauCeti.LinearAlgebra.Matrix.Pauli`, for the Pauli map and its commutator identity.
* `TauCeti.Geometry.Lie.Subgroup.SpecialUnitary`, for the native subgroup Lie algebra.
-/

public noncomputable section

open Matrix TauCeti TauCeti.Lie Complex
open scoped ContDiff Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

namespace TauCeti.SU2

local notation "𝔰𝔲₂" => lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
  (GLSpecialUnitary (Fin 2) ℂ)

private def skewPauli : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • pauli

private theorem skewPauli_apply (x : Fin 3 → ℝ) : skewPauli x = I • pauli x := rfl

private theorem skewPauli_mem (x : Fin 3 → ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).symm (skewPauli x) ∈ 𝔰𝔲₂ := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff]
  constructor
  · rw [skewPauli_apply, Matrix.conjTranspose_smul,
      (isHermitian_pauli x).eq, Complex.star_def, Complex.conj_I, neg_smul]
  · simp [skewPauli_apply]

private def coords : (Fin 3 → ℝ) →ₗ[ℝ] 𝔰𝔲₂ :=
  (((unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).symm.toLinearMap).comp
    skewPauli).codRestrict (𝔰𝔲₂).toSubmodule skewPauli_mem

private theorem coords_apply (x : Fin 3 → ℝ) :
    unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ) (coords x).1 = skewPauli x :=
  (unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).apply_symm_apply _

private theorem coords_injective : Function.Injective coords := by
  intro x y h
  have h' := congrArg (fun X : 𝔰𝔲₂ ↦
    unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ) X.1) h
  simp only [coords_apply, skewPauli_apply] at h'
  exact pauli_injective ((smul_right_injective _ Complex.I_ne_zero) h')

private theorem coords_surjective : Function.Surjective coords := by
  intro X
  let A := unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ) X.1
  have hm : (unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).symm A ∈ 𝔰𝔲₂ := by
    simpa only [A, LieEquiv.symm_apply_apply] using X.2
  obtain ⟨hA, ht⟩ :=
    (unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff A).mp hm
  have hH : (-I • A).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA]
  have hT : (-I • A).trace = 0 := by simp [ht]
  obtain ⟨x, hx⟩ := exists_pauli_eq_iff.mpr ⟨hH, hT⟩
  refine ⟨x, Subtype.ext ?_⟩
  have he : unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ) (coords x).1 = A := by
    rw [coords_apply, skewPauli_apply, hx, smul_smul]
    simp
  exact (unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).injective he

/-- Pauli coordinates on the native real Lie algebra of the special unitary subgroup of GL₂. -/
def pauliLieAlgebraEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] 𝔰𝔲₂ :=
  LinearEquiv.ofBijective coords ⟨coords_injective, coords_surjective⟩

private theorem skewPauli_lie (x y : Fin 3 → ℝ) :
    ⁅skewPauli x, skewPauli y⁆ = skewPauli ((-2 : ℝ) • (x ⨯₃ y)) := by
  simp only [skewPauli_apply, LieRing.of_associative_ring_bracket,
    smul_mul_smul, ← smul_sub, pauli_mul_sub_mul_pauli, map_smul, smul_smul]
  ext i j
  simp [smul_eq_mul]
  ring
/-- In ambient matrix coordinates, a native Pauli Lie-algebra element is `i` times its Pauli
matrix. -/
-- Normalize the Pauli image before the generic units equivalence expands to evaluation.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_pauliLieAlgebraEquiv (x : Fin 3 → ℝ) :
    unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ) (pauliLieAlgebraEquiv x).1 =
      I • pauli x := coords_apply x

/-- The native SU(2) Lie bracket corresponds to minus twice the coordinate cross product. -/
@[simp]
theorem lie_pauliLieAlgebraEquiv (x y : Fin 3 → ℝ) :
    ⁅pauliLieAlgebraEquiv x, pauliLieAlgebraEquiv y⁆ =
      pauliLieAlgebraEquiv ((-2 : ℝ) • (x ⨯₃ y)) := by
  apply Subtype.ext
  have he : unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)
      (⁅pauliLieAlgebraEquiv x, pauliLieAlgebraEquiv y⁆ : 𝔰𝔲₂).1 =
      unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)
        (pauliLieAlgebraEquiv ((-2 : ℝ) • (x ⨯₃ y))).1 := by
    calc
      _ = ⁅unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ) (pauliLieAlgebraEquiv x).1,
          unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ) (pauliLieAlgebraEquiv y).1⁆ :=
        (unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).map_lie _ _
      _ = _ := by
        simpa only [unitsLieAlgebraLieEquiv_pauliLieAlgebraEquiv, skewPauli_apply] using
          skewPauli_lie x y
  exact (unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).injective he

/-- The actual group adjoint in the ambient general linear group is the Pauli rotation. -/
@[simp]
theorem Ad_pauliLieAlgebraEquiv (g : SU2) (x : Fin 3 → ℝ) :
    Ad (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
      (Unitary.toUnits (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup g))
      (pauliLieAlgebraEquiv x).1 =
      (pauliLieAlgebraEquiv ((toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x)).1 := by
  have he : unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)
      (Ad (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
        (Unitary.toUnits (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup g))
        (pauliLieAlgebraEquiv x).1) =
      unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)
        (pauliLieAlgebraEquiv ((SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x)).1 := by
    rw [unitsLieAlgebraLieEquiv_pauliLieAlgebraEquiv, unitsLieAlgebraLieEquiv_apply,
      unitsLieAlgebraEquiv_Ad,
      ← unitsLieAlgebraLieEquiv_apply, unitsLieAlgebraLieEquiv_pauliLieAlgebraEquiv]
    simp only [SU2.coe_toSO3, pauli_pauliRotation_mulVec]
    simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  exact (unitsLieAlgebraLieEquiv (R := Matrix (Fin 2) (Fin 2) ℂ)).injective he


private def unitsHom : SU2 →* (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  Unitary.toUnits.comp (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup)

private theorem unitsHom_apply (g : SU2) :
    unitsHom g = Unitary.toUnits
      (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup g) := by
  rfl

private theorem unitsHom_mem (g : SU2) : unitsHom g ∈ GLSpecialUnitary (Fin 2) ℂ :=
  GLSpecialUnitary.mem_iff_mem_specialUnitaryGroup.mpr g.2

private theorem stable (g : SU2) (X : LeftInvariantDerivation
    𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (hX : X ∈ 𝔰𝔲₂) :
    ((continuousAdjointRepresentation (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
      (G := (Matrix (Fin 2) (Fin 2) ℂ)ˣ)).restrict unitsHom) g X ∈ 𝔰𝔲₂ := by
  simpa only [ContRepresentation.restrict_apply_apply, continuousAdjointRepresentation_apply]
    using Ad_mem_lieSubalgebraOfSubgroup (Subgroup.le_normalizer (unitsHom_mem g)) hX

/-- The adjoint representation of SU(2) restricted to its native Lie subalgebra. -/
def adjointRepresentation : ContRepresentation ℝ SU2 𝔰𝔲₂ :=
  ((continuousAdjointRepresentation (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
    (G := (Matrix (Fin 2) (Fin 2) ℂ)ˣ)).restrict unitsHom).subrepresentation
    (𝔰𝔲₂).toSubmodule stable

/-- Coercing the restricted action recovers the native ambient group adjoint. -/
@[simp]
theorem coe_adjointRepresentation_apply (g : SU2) (X : 𝔰𝔲₂) :
    (adjointRepresentation g X : LeftInvariantDerivation
      𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) (Matrix (Fin 2) (Fin 2) ℂ)ˣ) =
      Ad (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
        (Unitary.toUnits (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup g))
        X := by
  rw [adjointRepresentation, ContRepresentation.coe_subrepresentation_apply,
    ContRepresentation.restrict_apply_apply, continuousAdjointRepresentation_apply,
    unitsHom_apply]

/-- The native SU(2) adjoint representation is continuous in its group argument. -/
@[fun_prop]
theorem continuous_adjointRepresentation : Continuous adjointRepresentation := by
  apply ContRepresentation.continuous_subrepresentation
  have hu : Continuous unitsHom := Unitary.continuous_toUnits.comp
    (continuous_inclusion Matrix.specialUnitaryGroup_le_unitaryGroup)
  exact (contMDiff_continuousAdjointRepresentation
    (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
    (G := (Matrix (Fin 2) (Fin 2) ℂ)ˣ)).continuous.comp hu

/-- The Pauli coordinate equivalence intertwines the native adjoint and rotation actions. -/
@[simp]
theorem adjointRepresentation_pauliLieAlgebraEquiv (g : SU2) (x : Fin 3 → ℝ) :
    adjointRepresentation g (SU2.pauliLieAlgebraEquiv x) =
      SU2.pauliLieAlgebraEquiv ((SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) := by
  apply Subtype.ext
  rw [coe_adjointRepresentation_apply]
  exact SU2.Ad_pauliLieAlgebraEquiv g x

private def basis : Module.Basis (Fin 3) ℝ 𝔰𝔲₂ :=
  (Pi.basisFun ℝ (Fin 3)).map SU2.pauliLieAlgebraEquiv
private theorem ad_matrix (x : Fin 3 → ℝ) :
    LinearMap.toMatrix basis basis (LieAlgebra.ad ℝ 𝔰𝔲₂ (SU2.pauliLieAlgebraEquiv x)) =
      !![0, 2*x 2, -2*x 1; -2*x 2, 0, 2*x 0; 2*x 1, -2*x 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, basis, LieAlgebra.ad_apply,
      SU2.lie_pauliLieAlgebraEquiv, cross_apply]
/-- The Killing form on the native SU(2) Lie algebra is minus eight times the Pauli dot form. -/
@[simp]
theorem killingForm_pauliLieAlgebraEquiv (x y : Fin 3 → ℝ) :
    killingForm ℝ 𝔰𝔲₂ (SU2.pauliLieAlgebraEquiv x) (SU2.pauliLieAlgebraEquiv y) =
      -8 * (x ⬝ᵥ y) := by
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℝ basis,
    LinearMap.toMatrix_comp basis basis basis, ad_matrix, ad_matrix]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The native real Lie algebra of SU(2) has negative-definite Killing form. -/
theorem killingForm_self_neg (X : 𝔰𝔲₂) (hX : X ≠ 0) :
    killingForm ℝ 𝔰𝔲₂ X X < 0 := by
  obtain ⟨x, rfl⟩ := pauliLieAlgebraEquiv.surjective X
  rw [killingForm_pauliLieAlgebraEquiv]
  have hx : x ≠ 0 := (map_ne_zero_iff _ pauliLieAlgebraEquiv.injective).mp hX
  exact mul_neg_of_neg_of_pos (by norm_num)
    (by simpa only [star_trivial] using Matrix.dotProduct_star_self_pos_iff.mpr hx)

end TauCeti.SU2
