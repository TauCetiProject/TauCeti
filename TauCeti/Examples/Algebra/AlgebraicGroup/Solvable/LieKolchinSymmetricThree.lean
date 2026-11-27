/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Representation
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.SchemeProperties
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
public import TauCeti.RepresentationTheory.Symmetric.Standard

import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Check: Lie–Kolchin needs connectedness

The constant group scheme `S₃` over `ℂ` has solvable group of points
(`TauCeti.Examples.LieKolchinSymmetricThree.isSolvable`) and is not connected
(`TauCeti.Examples.LieKolchinSymmetricThree.not_connectedSpace`), and its two-dimensional standard
representation `TauCeti.standardRepresentation ℂ (Fin 3)`, on the sum-zero vectors of `ℂ[Fin 3]`
with `S₃` permuting the coordinates, is irreducible
(`TauCeti.isIrreducible_standardRepresentation_fin_three`) and has no nonzero weight vector
(`TauCeti.Examples.LieKolchinSymmetricThree.not_hasNonzeroWeightVector`): a weight vector would be
a common eigenvector of the transposition `(0 1)` and the cycle `(0 1 2)`, and these have none on
the sum-zero plane. So the conclusion of the Lie–Kolchin
theorem (`TauCeti.Comodule.hasNonzeroWeightVector_of_nonzeroJointWeight_commutator` and its
corollaries need a connected group) fails for this disconnected solvable group.
-/

public section

open Equiv TauCeti

noncomputable section

namespace TauCeti.Examples.LieKolchinSymmetricThree

/-- `S₃` is solvable, as is every permutation group on at most four points. -/
theorem isSolvable : Group.IsSolvable (Perm (Fin 3)) :=
  Equiv.Perm.isSolvable (by simp)

/-- The constant group scheme `S₃` over `ℂ` is not connected. -/
theorem not_connectedSpace :
    ¬ConnectedSpace (ConstantGroup.groupScheme ℂ (Perm (Fin 3))).X.left :=
  ConstantGroup.not_connectedSpace_groupScheme (G := Perm (Fin 3)) ℂ

/-- The two-dimensional standard representation of `S₃` over `ℂ` is irreducible. -/
example : (standardRepresentation ℂ (Fin 3)).IsIrreducible :=
  isIrreducible_standardRepresentation_fin_three (by norm_num)

/-- The transposition `(0 1)` and the cycle `(0 1 2)` have no common eigenvector on the sum-zero
vectors. -/
theorem eq_zero_of_forall_exists_smul
    {v : (augmentationSubrepresentation ℂ (Perm (Fin 3)) (Fin 3)).toSubmodule}
    (hv : ∀ σ : Perm (Fin 3), ∃ a : ℂ, standardRepresentation ℂ (Fin 3) σ v = a • v) :
    v = 0 := by
  obtain ⟨a, ha⟩ := hv (swap 0 1)
  obtain ⟨b, hb⟩ := hv (finRotate 3)
  have hs : (v : MonoidAlgebra ℂ (Fin 3)).coeff 0 + (v : MonoidAlgebra ℂ (Fin 3)).coeff 1 +
      (v : MonoidAlgebra ℂ (Fin 3)).coeff 2 = 0 := by
    have := mem_augmentationSubrepresentation_iff.mp v.property
    rw [Module.Basis.coe_sumCoords_of_fintype] at this
    simpa [Fin.sum_univ_three] using this
  have ha' (i : Fin 3) := congrArg (fun w : MonoidAlgebra ℂ (Fin 3) ↦ w.coeff i)
    (congrArg Subtype.val ha)
  have hb' (i : Fin 3) := congrArg (fun w : MonoidAlgebra ℂ (Fin 3) ↦ w.coeff i)
    (congrArg Subtype.val hb)
  simp only [coe_standardRepresentation_apply, Representation.coeff_ofMulAction, Perm.smul_def,
    SetLike.val_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at ha' hb'
  have a0 := ha' 0
  have a1 := ha' 1
  have a2 := ha' 2
  have b0 := hb' 0
  have b1 := hb' 1
  have b2 := hb' 2
  have s0 : (swap (0 : Fin 3) 1)⁻¹ 0 = 1 := by decide
  have s1 : (swap (0 : Fin 3) 1)⁻¹ 1 = 0 := by decide
  have s2 : (swap (0 : Fin 3) 1)⁻¹ 2 = 2 := by decide
  have r0 : (finRotate 3)⁻¹ 0 = 2 := by decide
  have r1 : (finRotate 3)⁻¹ 1 = 0 := by decide
  have r2 : (finRotate 3)⁻¹ 2 = 1 := by decide
  rw [s0] at a0
  rw [s1] at a1
  rw [s2] at a2
  rw [r0] at b0
  rw [r1] at b1
  rw [r2] at b2
  have hx : (v : MonoidAlgebra ℂ (Fin 3)).coeff 0 = 0 := by
    by_contra hx
    have e1 : 1 + b + b ^ 2 = 0 :=
      mul_left_cancel₀ hx (by linear_combination hs - b0 - b2 - b * b0)
    have ea : a = b ^ 2 := mul_left_cancel₀ hx (by linear_combination -a0 + b2 + b * b0)
    have eb : b = a * b := mul_left_cancel₀ hx (by linear_combination -b0 + a2 + a * b0)
    have hb0 : b ≠ 0 := by
      rintro rfl
      norm_num at e1
    have ha1 : a = 1 := (mul_left_cancel₀ hb0 (by linear_combination eb : b * 1 = b * a)).symm
    have hb : b = -2 := by linear_combination e1 + ea - ha1
    have h3 : (3 : ℂ) = 0 := by linear_combination (ha1 - ea) - (b - 2) * hb
    norm_num at h3
  have hz : (v : MonoidAlgebra ℂ (Fin 3)).coeff 2 = 0 := by rw [b0, hx, mul_zero]
  have hy : (v : MonoidAlgebra ℂ (Fin 3)).coeff 1 = 0 := by rw [b2, hz, mul_zero]
  ext i
  fin_cases i <;> simp [hx, hy, hz]

/-- **The two-dimensional representation of `S₃` has no weight vector.** As a comodule over the
coordinate ring of the constant group `S₃` over `ℂ`, the sum-zero vectors of `ℂ[Fin 3]` have no
nonzero weight vector, although the group of points `S₃` is solvable: the constant group is not
connected. -/
theorem not_hasNonzeroWeightVector :
    letI := ConstantGroup.representationComodule ℂ (standardRepresentation ℂ (Fin 3))
    ¬Comodule.HasNonzeroWeightVector ℂ (ConstantGroup.coordinateRing ℂ (Perm (Fin 3)))
      (augmentationSubrepresentation ℂ (Perm (Fin 3)) (Fin 3)).toSubmodule := by
  let := ConstantGroup.representationComodule ℂ (standardRepresentation ℂ (Fin 3))
  rw [Comodule.hasNonzeroWeightVector_iff]
  rintro ⟨v, c, hv, -, hcoact⟩
  refine hv (eq_zero_of_forall_exists_smul fun σ ↦ ⟨(ConstantGroup.toPoints ℂ _ σ).ofConv c, ?_⟩)
  rw [← ConstantGroup.basePointsRepresentation_toPoints, Comodule.basePointsRepresentation_apply,
    Comodule.endOfPoint_tmul, hcoact]
  simp

end TauCeti.Examples.LieKolchinSymmetricThree
