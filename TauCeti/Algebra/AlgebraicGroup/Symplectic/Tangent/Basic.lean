/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
public import TauCeti.Algebra.Lie.Symplectic.Basic

/-!
# The tangent Lie algebra of the symplectic group scheme

The closed immersion `Sp₂ₘ → GL₂ₘ` identifies counit-valued tangent derivations
with matrices satisfying `X J + J Xᵀ = 0`. Reindexing these matrices in
`Fin m ⊕ Fin m` coordinates identifies the convolution Lie bracket with the
commutator bracket in Mathlib's `LieAlgebra.Symplectic.sp`.

The equivalence works over every commutative base ring and every commutative
coefficient algebra. In particular it includes characteristic two, nilpotents,
and rank zero. It supplies matrix coordinates for root-subgroup differentials
and adjoint root spaces of the symplectic group.

The construction follows `SpecialLinear.tangentLieEquivSl`, using
`ConstantForm.mem_lieSubalgebra_definingHopfIdeal_iff` and the existing
`GeneralLinear.tangentLieEquivMatrix` and `HopfIdeal.quotientLieEquiv`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 24.6.
-/

public section

open Matrix

namespace TauCeti.Symplectic

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  (m : ℕ)

/-- An ambient tangent derivation lies in the symplectic subgroup's Lie algebra
exactly when its matrix, in paired coordinates, lies in the classical symplectic Lie algebra. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R (m + m))
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R (m + m)) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R m) ↔
      (GeneralLinear.tangentMatrix (m + m) d).submatrix finSumFinEquiv finSumFinEquiv ∈
        LieAlgebra.Symplectic.sp (Fin m) B := by
  rw [ConstantForm.mem_lieSubalgebra_definingHopfIdeal_iff, JFin_map,
    LieAlgebra.Symplectic.mem_sp_iff_mul_J_add_J_mul_transpose_eq_zero]
  rw [← (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective.eq_iff]
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_add, Pi.add_apply,
    ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _, Matrix.transpose_submatrix,
    JFin_submatrix, Matrix.submatrix_zero, Pi.zero_apply]

/-- The symplectic tangent matrix, written in paired coordinates and restricted
to the classical symplectic Lie algebra. -/
noncomputable def tangentMatrix :
    Derivation R (coordinateHopfAlgebra R m)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B) →ₗ[B]
      LieAlgebra.Symplectic.sp (Fin m) B :=
  let ambient :=
    (Matrix.reindexLinearEquiv B B finSumFinEquiv.symm finSumFinEquiv.symm).toLinearMap.comp
    ((GeneralLinear.tangentMatrix (R := R) (B := B) (m + m)).comp
      (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R m)).toLinearMap)
  ambient.codRestrict (LieAlgebra.Symplectic.sp (Fin m) B) fun d => by
    -- Expose the new composite linear map before its public computation rule is available.
    change (GeneralLinear.tangentMatrix (m + m)
      (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R m) d)).submatrix
        finSumFinEquiv finSumFinEquiv ∈ LieAlgebra.Symplectic.sp (Fin m) B
    simpa only [HopfIdeal.quotientLieEquiv_apply_coe] using
      (mem_lieSubalgebra_definingHopfIdeal_iff m _).mp
        (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R m) d).property

/-- Forgetting the symplectic condition recovers the ambient tangent matrix,
reindexed along the canonical equivalence between paired and unpaired coordinates. -/
@[simp]
theorem tangentMatrix_apply_coe
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B)) :
    (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) =
      (GeneralLinear.tangentMatrix (m + m)
        (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R m) d)).submatrix
          finSumFinEquiv finSumFinEquiv := (rfl)

private theorem tangentMatrix_injective :
    Function.Injective (tangentMatrix (R := R) (B := B) m) := by
  intro d e h
  apply HopfIdeal.quotientLieHom_injective (B := B) (definingHopfIdeal R m)
  apply (GeneralLinear.tangentLinearEquivMatrix (R := R) (B := B) (m + m)).injective
  rw [GeneralLinear.tangentLinearEquivMatrix_apply, GeneralLinear.tangentLinearEquivMatrix_apply]
  apply (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm).injective
  simpa only [tangentMatrix_apply_coe (R := R) (B := B),
    Matrix.reindex_apply, Equiv.symm_symm] using congrArg Subtype.val h

private theorem tangentMatrix_surjective :
    Function.Surjective (tangentMatrix (R := R) (B := B) m) := by
  intro X
  let Y := X.val.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  let d := (GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (m + m)).symm Y
  have hd : GeneralLinear.tangentMatrix (m + m) d = Y := by
    rw [← GeneralLinear.tangentLieEquivMatrix_apply]
    exact (GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (m + m)).apply_symm_apply Y
  have hmem : d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R m) := by
    rw [mem_lieSubalgebra_definingHopfIdeal_iff, hd]
    simpa only [Y, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] using X.property
  let e : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B) :=
    (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R m)).symm ⟨d, hmem⟩
  refine ⟨e, Subtype.ext ?_⟩
  have he : HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R m) e = d := by
    rw [← HopfIdeal.quotientLieEquiv_apply_coe]
    exact congrArg Subtype.val
      ((HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R m)).apply_symm_apply ⟨d, hmem⟩)
  simp only [tangentMatrix_apply_coe (R := R) (B := B), he, hd, Y, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id]

/-- The symplectic tangent-matrix map preserves the convolution Lie bracket. -/
@[simp]
theorem tangentMatrix_lie
    (d e : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B)) :
    tangentMatrix m ⁅d, e⁆ = ⁅tangentMatrix m d, tangentMatrix m e⁆ := by
  apply Subtype.ext
  simp only [tangentMatrix_apply_coe (R := R) (B := B), LieHom.map_lie,
    GeneralLinear.tangentMatrix_lie, LieSubalgebra.coe_bracket,
    LieRing.of_associative_ring_bracket, Matrix.submatrix_sub, Pi.sub_apply,
    ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv _]

/-- The tangent Lie algebra of `Sp₂ₘ` is the classical symplectic Lie algebra,
over any commutative coefficient algebra, including in characteristic two. -/
noncomputable def tangentLieEquivSp :
    Derivation R (coordinateHopfAlgebra R m)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B) ≃ₗ⁅B⁆
      LieAlgebra.Symplectic.sp (Fin m) B :=
  LieEquiv.ofBijective
    { tangentMatrix (R := R) (B := B) m with
      map_lie' := fun {d e} ↦ tangentMatrix_lie m d e }
    ⟨tangentMatrix_injective m, tangentMatrix_surjective m⟩

/-- The Lie equivalence computes by the symplectic tangent-matrix map. -/
@[simp]
theorem tangentLieEquivSp_apply
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B)) :
    tangentLieEquivSp m d = tangentMatrix m d := (rfl)

end TauCeti.Symplectic
