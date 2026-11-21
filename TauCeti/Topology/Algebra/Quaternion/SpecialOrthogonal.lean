/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Quaternion
public import TauCeti.Topology.Algebra.Quaternion.Unitary
import TauCeti.RepresentationTheory.SU2.Adjoint

/-!
# `SO(3)` is the unit quaternions modulo `±1`, which is `ℝP³`

A unit quaternion `q` acts on `ℝ³`, viewed as the pure quaternions `v₀ i + v₁ j + v₂ k`, by the
rotation `v ↦ q * v * star q` (`Quaternion.unitaryToSpecialOrthogonalGroup`). This file shows that
every rotation arises in this way (`Quaternion.unitaryToSpecialOrthogonalGroup_surjective`) and that
the action is continuous, so it is a covering map with fibres `{q, -q}`
(`Quaternion.isCoveringMap_unitaryToSpecialOrthogonalGroup`).

The unit quaternions are the unit sphere `S³` of `ℝ⁴`
(`Quaternion.unitaryHomeomorphEuclideanSphere`), and identifying antipodal points of `S³` gives
real projective space `ℝP³`. Since two unit quaternions give the same rotation exactly when they
agree up to sign, the action descends to a continuous bijection from the compact space `ℝP³` onto
the Hausdorff space `SO(3)`, hence a homeomorphism
`TauCeti.RealProjectiveSpace.homeomorphSpecialOrthogonalGroup : ℝP³ ≃ₜ SO(3)`. It sends the class
of a unit vector `x = (a, b, c, d)` to the rotation by conjugation with the quaternion
`a + b i + c j + d k`, and the class of `(1, 0, 0, 0)` to the identity.

Surjectivity is deduced from that of the Pauli double cover `TauCeti.SU2.toSO3`: through
`Quaternion.toComplexMatrix`, conjugation by `q` on pure quaternions is conjugation by the matrix
of `q` on traceless Hermitian matrices, read in coordinates permuted by
`(v₀, v₁, v₂) ↦ (v₂, v₁, v₀)`.

## Main definitions

* `TauCeti.RealProjectiveSpace.homeomorphSpecialOrthogonalGroup`: the homeomorphism
  `ℝP³ ≃ₜ SO(3)`.

## Main results

* `Quaternion.unitaryToSpecialOrthogonalGroup_surjective`: every rotation of `ℝ³` is conjugation
  by a unit quaternion.
* `Quaternion.continuous_unitaryToSpecialOrthogonalGroup` and
  `Quaternion.isCoveringMap_unitaryToSpecialOrthogonalGroup`: `S³ → SO(3)` is a covering map.
* `TauCeti.RealProjectiveSpace.homeomorphSpecialOrthogonalGroup_mk` and
  `TauCeti.RealProjectiveSpace.homeomorphSpecialOrthogonalGroup_symm_apply`: the homeomorphism and
  its inverse on representatives.

## References

* J. Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008, §2.3.
* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, Chapter 3.
-/

public section

open Matrix Metric
open scoped Quaternion

namespace Quaternion

/-! ### Surjectivity through the Pauli double cover -/

/-- The permutation matrix of `(v₀, v₁, v₂) ↦ (v₂, v₁, v₀)`. -/
private def swapZeroTwo : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private theorem swapZeroTwo_mulVec (v : Fin 3 → ℝ) : swapZeroTwo *ᵥ v = ![v 2, v 1, v 0] := by
  ext i
  fin_cases i <;> simp [swapZeroTwo, mulVec, dotProduct, Fin.sum_univ_three]

private theorem swapZeroTwo_mul_self : swapZeroTwo * swapZeroTwo = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapZeroTwo, Matrix.mul_apply, Fin.sum_univ_three]

/-- The matrix of the pure quaternion `v₀ i + v₁ j + v₂ k` is `i` times the Pauli matrix of
`(v₂, v₁, v₀)`. -/
private theorem toComplexMatrix_mk_zero (v : Fin 3 → ℝ) :
    toComplexMatrix ⟨0, v 0, v 1, v 2⟩ = Complex.I • TauCeti.pauli (swapZeroTwo *ᵥ v) := by
  rw [toComplexMatrix_apply, TauCeti.pauli_apply, swapZeroTwo_mulVec]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp

/-- Conjugation by a unit quaternion is the Pauli rotation of its special unitary matrix, in
coordinates permuted by `swapZeroTwo`. -/
private theorem rotationMatrix_eq_swapZeroTwo_mul (q : unitary ℍ[ℝ]) :
    rotationMatrix (q : ℍ[ℝ]) = swapZeroTwo *
      (TauCeti.SU2.toSO3 (unitaryEquivSpecialUnitaryGroup q) : Matrix (Fin 3) (Fin 3) ℝ) *
        swapZeroTwo := by
  refine rotationMatrix_eq_iff.mpr fun v ↦ toComplexMatrix_injective ?_
  have hv := TauCeti.pauli_pauliRotation_mulVec
    (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup
      (unitaryEquivSpecialUnitaryGroup q)) (swapZeroTwo *ᵥ v)
  simp only [Submonoid.coe_inclusion, coe_unitaryEquivSpecialUnitaryGroup_apply] at hv
  rw [map_mul, map_mul, map_star, toComplexMatrix_mk_zero, toComplexMatrix_mk_zero,
    TauCeti.SU2.coe_toSO3, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_mulVec (M := swapZeroTwo) (N := swapZeroTwo),
    swapZeroTwo_mul_self, one_mulVec, hv, mul_smul_comm, smul_mul_assoc]

/-- **Every rotation of `ℝ³` is conjugation by a unit quaternion.** -/
theorem unitaryToSpecialOrthogonalGroup_surjective :
    Function.Surjective (unitaryToSpecialOrthogonalGroup (R := ℝ)) := by
  intro A
  have hP : swapZeroTwo * (A : Matrix (Fin 3) (Fin 3) ℝ) * swapZeroTwo ∈
      specialOrthogonalGroup (Fin 3) ℝ := by
    obtain ⟨hA, hdet⟩ := mem_specialOrthogonalGroup_iff.mp A.2
    have hS : swapZeroTwo ∈ orthogonalGroup (Fin 3) ℝ := by
      rw [mem_orthogonalGroup_iff']
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapZeroTwo, Matrix.mul_apply, Fin.sum_univ_three]
    refine mem_specialOrthogonalGroup_iff.mpr ⟨mul_mem (mul_mem hS hA) hS, ?_⟩
    rw [det_mul, det_mul, mul_right_comm, ← det_mul, swapZeroTwo_mul_self, det_one, one_mul]
    exact hdet
  obtain ⟨g, hg⟩ := TauCeti.SU2.toSO3_surjective ⟨_, hP⟩
  refine ⟨unitaryEquivSpecialUnitaryGroup.symm g, Subtype.ext ?_⟩
  rw [coe_unitaryToSpecialOrthogonalGroup_apply, rotationMatrix_eq_swapZeroTwo_mul,
    MulEquiv.apply_symm_apply, hg, Subtype.coe_mk]
  simp only [← mul_assoc, swapZeroTwo_mul_self, one_mul]
  rw [mul_assoc, swapZeroTwo_mul_self, mul_one]

/-! ### Continuity and the covering map -/

/-- Conjugation by a quaternion depends continuously on the quaternion. -/
@[fun_prop]
theorem continuous_rotationMatrix :
    Continuous (rotationMatrix : ℍ[ℝ] → Matrix (Fin 3) (Fin 3) ℝ) := by
  have := continuous_re; have := continuous_imI; have := continuous_imJ; have := continuous_imK
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;> simp only [rotationMatrix_def] <;> fun_prop

/-- The action of the unit quaternions on `ℝ³` by conjugation is continuous. -/
theorem continuous_unitaryToSpecialOrthogonalGroup :
    Continuous (unitaryToSpecialOrthogonalGroup (R := ℝ)) :=
  continuous_induced_rng.mpr <| by
    simpa only [Function.comp_def, coe_unitaryToSpecialOrthogonalGroup_apply] using
      continuous_rotationMatrix.comp continuous_subtype_val

end Quaternion

namespace TauCeti.RealProjectiveSpace

open Quaternion

/-- The rotation attached to a point `x` of `S³`: conjugation by the unit quaternion with
coordinates `x`. -/
private noncomputable def sphereToSpecialOrthogonalGroup
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : specialOrthogonalGroup (Fin 3) ℝ :=
  unitaryToSpecialOrthogonalGroup (unitaryHomeomorphEuclideanSphere.symm x)

private theorem sphereToSpecialOrthogonalGroup_neg (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    sphereToSpecialOrthogonalGroup (-x) = sphereToSpecialOrthogonalGroup x :=
  unitaryToSpecialOrthogonalGroup_eq_iff.mpr
    (Or.inr (unitaryHomeomorphEuclideanSphere_symm_neg x))

private theorem bijective_lift_sphereToSpecialOrthogonalGroup :
    Function.Bijective (RealProjectiveSpace.lift 3 sphereToSpecialOrthogonalGroup
      sphereToSpecialOrthogonalGroup_neg) := by
  constructor
  · intro a b h
    obtain ⟨x, rfl⟩ := mk_surjective 3 a
    obtain ⟨y, rfl⟩ := mk_surjective 3 b
    rw [RealProjectiveSpace.lift_mk, RealProjectiveSpace.lift_mk, sphereToSpecialOrthogonalGroup,
      sphereToSpecialOrthogonalGroup, unitaryToSpecialOrthogonalGroup_eq_iff,
      ← unitaryHomeomorphEuclideanSphere_symm_neg,
      unitaryHomeomorphEuclideanSphere.symm.injective.eq_iff,
      unitaryHomeomorphEuclideanSphere.symm.injective.eq_iff] at h
    exact (mk_eq_mk_iff 3 x y).mpr h
  · intro A
    obtain ⟨q, rfl⟩ := unitaryToSpecialOrthogonalGroup_surjective A
    refine ⟨mk 3 (unitaryHomeomorphEuclideanSphere q), ?_⟩
    rw [RealProjectiveSpace.lift_mk, sphereToSpecialOrthogonalGroup, Homeomorph.symm_apply_apply]

/-- The bijection `ℝP³ ≃ SO(3)` induced by conjugation. -/
private noncomputable def equivSpecialOrthogonalGroup :
    RealProjectiveSpace 3 ≃ specialOrthogonalGroup (Fin 3) ℝ :=
  Equiv.ofBijective _ bijective_lift_sphereToSpecialOrthogonalGroup

private theorem equivSpecialOrthogonalGroup_mk (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    equivSpecialOrthogonalGroup (mk 3 x) = sphereToSpecialOrthogonalGroup x := by
  rw [equivSpecialOrthogonalGroup, Equiv.ofBijective_apply, RealProjectiveSpace.lift_mk]

/-- **`ℝP³` is homeomorphic to `SO(3)`.** The class of a unit vector `x = (a, b, c, d)` of `ℝ⁴`
goes to the rotation `v ↦ q * v * star q` of the pure quaternions by `q = a + b i + c j + d k`;
this is well defined because `q` and `-q` give the same rotation. -/
noncomputable def homeomorphSpecialOrthogonalGroup :
    RealProjectiveSpace 3 ≃ₜ specialOrthogonalGroup (Fin 3) ℝ :=
  Continuous.homeoOfEquivCompactToT2 (f := equivSpecialOrthogonalGroup) <|
    (isQuotientMap_mk 3).continuous_iff.mpr <| by
      simpa only [Function.comp_def, equivSpecialOrthogonalGroup_mk,
        sphereToSpecialOrthogonalGroup] using
        continuous_unitaryToSpecialOrthogonalGroup.comp
          unitaryHomeomorphEuclideanSphere.symm.continuous

/-- The class of a unit vector `x` goes to conjugation by the unit quaternion with coordinates
`x`. -/
@[simp]
theorem homeomorphSpecialOrthogonalGroup_mk (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    homeomorphSpecialOrthogonalGroup (mk 3 x) =
      unitaryToSpecialOrthogonalGroup (unitaryHomeomorphEuclideanSphere.symm x) := by
  rw [homeomorphSpecialOrthogonalGroup, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, equivSpecialOrthogonalGroup_mk,
    sphereToSpecialOrthogonalGroup]

/-- The point of `ℝP³` attached to conjugation by a unit quaternion `q` is the class of the
coordinate vector of `q`. -/
@[simp]
theorem homeomorphSpecialOrthogonalGroup_symm_apply (q : unitary ℍ[ℝ]) :
    homeomorphSpecialOrthogonalGroup.symm (unitaryToSpecialOrthogonalGroup q) =
      mk 3 (unitaryHomeomorphEuclideanSphere q) := by
  rw [Homeomorph.symm_apply_eq, homeomorphSpecialOrthogonalGroup_mk, Homeomorph.symm_apply_apply]

/-- The identity rotation corresponds to the class of the unit quaternion `1`, that is, of
`(1, 0, 0, 0)`. -/
theorem homeomorphSpecialOrthogonalGroup_symm_one :
    homeomorphSpecialOrthogonalGroup.symm 1 = mk 3 (unitaryHomeomorphEuclideanSphere 1) := by
  rw [← map_one unitaryToSpecialOrthogonalGroup, homeomorphSpecialOrthogonalGroup_symm_apply]

end TauCeti.RealProjectiveSpace

namespace Quaternion

/-- **`S³ → SO(3)` is a covering map**: the action of the unit quaternions on `ℝ³` by conjugation
is the antipodal quotient `S³ → ℝP³` followed by the homeomorphism `ℝP³ ≃ₜ SO(3)`. -/
theorem isCoveringMap_unitaryToSpecialOrthogonalGroup :
    IsCoveringMap (unitaryToSpecialOrthogonalGroup (R := ℝ)) := by
  have h := ((TauCeti.RealProjectiveSpace.isCoveringMap_mk 3).comp_homeomorph
    unitaryHomeomorphEuclideanSphere).homeomorph_comp
      TauCeti.RealProjectiveSpace.homeomorphSpecialOrthogonalGroup
  convert h using 1
  ext q : 1
  simp

end Quaternion
