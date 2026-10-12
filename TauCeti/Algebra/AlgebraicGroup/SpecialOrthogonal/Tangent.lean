/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Orthogonal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic
public import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# The tangent Lie algebra of the special orthogonal group

When `2` is invertible, differentiating the orthogonality and determinant-one equations identifies
the tangent Lie algebra of `SOₙ` with the skew-symmetric matrices. This is the classical
orthogonal Lie algebra and gives a concrete model for studying representations of `SOₙ` in
characteristic zero.

The proof combines the existing tangent criteria for a constant-form subgroup and `SLₙ`. The
orthogonality equation forces trace zero when `2` is invertible, so the determinant condition adds
no further tangent vectors.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 21.
-/

public section

open LieAlgebra Matrix

namespace TauCeti.SpecialOrthogonal

universe u w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
variable (n : ℕ)

/-- Every special-orthogonal tangent derivation has a skew-symmetric tangent matrix,
without any restriction on the characteristic. -/
theorem transpose_tangentMatrix_eq_neg_of_mem
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B))
    (hd : d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n)) :
    (GeneralLinear.tangentMatrix n d)ᵀ = -GeneralLinear.tangentMatrix n d := by
  rw [definingHopfIdeal_def, HopfIdeal.mem_lieSubalgebra_sup_iff] at hd
  simpa using congrArg Matrix.transpose
    (add_eq_zero_iff_eq_neg.mp
      ((Orthogonal.mem_lieSubalgebra_definingHopfIdeal_iff n d).mp hd.1))

/-- An ambient tangent derivation belongs to the special-orthogonal Lie algebra exactly when its
tangent matrix is skew-symmetric. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff [Invertible (2 : B)]
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n) ↔
      (GeneralLinear.tangentMatrix n d)ᵀ = -GeneralLinear.tangentMatrix n d := by
  constructor
  · exact transpose_tangentMatrix_eq_neg_of_mem n d
  · intro hskew
    rw [definingHopfIdeal_def, HopfIdeal.mem_lieSubalgebra_sup_iff,
      Orthogonal.mem_lieSubalgebra_definingHopfIdeal_iff,
      SpecialLinear.mem_lieSubalgebra_definingHopfIdeal_iff]
    exact ⟨by rw [hskew, add_neg_cancel],
      Matrix.trace_eq_zero_of_transpose_eq_neg _ hskew⟩

/-- The tangent matrix of `SOₙ`, as a skew-symmetric matrix in Mathlib's orthogonal Lie algebra. -/
noncomputable def tangentMatrix :
    Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) →ₗ[B]
      LieAlgebra.Orthogonal.so (Fin n) B :=
  let ambient := (GeneralLinear.tangentMatrix (R := R) (B := B) n).comp
    (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n)).toLinearMap
  ambient.codRestrict (LieAlgebra.Orthogonal.so (Fin n) B) fun d => by
    -- Expose the composite before its public computation rule is available.
    change GeneralLinear.tangentMatrix n
      (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) d) ∈
        LieAlgebra.Orthogonal.so (Fin n) B
    rw [LieAlgebra.Orthogonal.mem_so]
    simpa only [HopfIdeal.quotientLieEquiv_apply_coe] using
      transpose_tangentMatrix_eq_neg_of_mem n _
        (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R n) d).property

/-- The underlying matrix of `tangentMatrix` is the ambient tangent matrix after quotienting by
the special-orthogonal defining ideal. -/
@[simp]
theorem tangentMatrix_apply_coe
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    (tangentMatrix n d : Matrix (Fin n) (Fin n) B) =
      GeneralLinear.tangentMatrix n
        (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) d) := (rfl)

/-- The special-orthogonal tangent-matrix map preserves the convolution Lie bracket. -/
@[simp]
theorem tangentMatrix_lie
    (d e : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    tangentMatrix n ⁅d, e⁆ = ⁅tangentMatrix n d, tangentMatrix n e⁆ := by
  apply Subtype.ext
  simp only [tangentMatrix_apply_coe (R := R) (B := B), LieHom.map_lie,
    GeneralLinear.tangentMatrix_lie, LieSubalgebra.coe_bracket]

/-- The general-linear tangent equivalence carries the special-orthogonal tangent image
onto the skew-symmetric matrix Lie algebra when `2` is invertible. -/
theorem map_lieSubalgebra_definingHopfIdeal [Invertible (2 : B)] :
    (HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n)).map
        (GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) n).toLieHom =
      LieAlgebra.Orthogonal.so (Fin n) B := by
  ext X
  rw [LieSubalgebra.mem_map, LieAlgebra.Orthogonal.mem_so]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa only [LieEquiv.coe_coe, GeneralLinear.tangentLieEquivMatrix_apply] using
      (mem_lieSubalgebra_definingHopfIdeal_iff n d).mp hd
  · intro hX
    refine ⟨(GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) n).symm X, ?_,
      (GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) n).apply_symm_apply X⟩
    rw [mem_lieSubalgebra_definingHopfIdeal_iff,
      ← GeneralLinear.tangentLieEquivMatrix_apply, LieEquiv.apply_symm_apply]
    exact hX

/-- The tangent Lie algebra of `SOₙ` is the classical orthogonal Lie algebra, whenever `2` is
invertible in the coefficient algebra. -/
noncomputable def tangentLieEquivSo [Invertible (2 : B)] :
    Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃ₗ⁅B⁆
      LieAlgebra.Orthogonal.so (Fin n) B :=
  (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R n)).trans
    ((GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) n).ofSubalgebras _ _
      (map_lieSubalgebra_definingHopfIdeal n))

/-- The orthogonal Lie equivalence computes by the tangent-matrix map. -/
@[simp]
theorem tangentLieEquivSo_apply [Invertible (2 : B)]
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    tangentLieEquivSo n d = tangentMatrix n d := by
  apply Subtype.ext
  simp only [tangentLieEquivSo, LieEquiv.trans_apply, LieEquiv.ofSubalgebras_apply,
    HopfIdeal.quotientLieEquiv_apply_coe, GeneralLinear.tangentLieEquivMatrix_apply,
    tangentMatrix_apply_coe (R := R) (B := B)]

end TauCeti.SpecialOrthogonal
