/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic

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

/-- A skew-symmetric matrix has trace zero when `2` is invertible. -/
private theorem trace_eq_zero_of_transpose_eq_neg [Invertible (2 : B)]
    (X : Matrix (Fin n) (Fin n) B) (hX : Xᵀ = -X) : Matrix.trace X = 0 := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro i hi
  have hdiag : X i i = -X i i := by
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using congrFun (congrFun hX i) i
  have htwo : (2 : B) * X i i = 0 := by linear_combination hdiag
  calc
    X i i = ⅟(2 : B) * ((2 : B) * X i i) := by simp
    _ = 0 := by rw [htwo]; simp

/-- An ambient tangent derivation belongs to the special-orthogonal Lie algebra exactly when its
tangent matrix is skew-symmetric. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff [Invertible (2 : B)]
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n) ↔
      (GeneralLinear.tangentMatrix n d)ᵀ = -GeneralLinear.tangentMatrix n d := by
  have hspan : (definingHopfIdeal R n).toIdeal =
      Ideal.span (Orthogonal.relationSet R n ∪
        {(GeneralLinear.determinantGroupLike R n :
          GeneralLinear.coordinateHopfAlgebra R n) - 1}) := by
    rw [definingHopfIdeal_toIdeal, ← Ideal.span_union]
  have hO_iff : (∀ x ∈ Orthogonal.relationSet R n, d x = 0) ↔
      GeneralLinear.tangentMatrix n d + (GeneralLinear.tangentMatrix n d)ᵀ = 0 := by
    change (∀ x ∈ ConstantForm.relationSet R n 1, d x = 0) ↔ _
    rw [← HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span
      (ConstantForm.definingHopfIdeal R n 1)
      (ConstantForm.definingHopfIdeal_toIdeal R n 1) d]
    simpa [Matrix.map_one] using ConstantForm.mem_lieSubalgebra_definingHopfIdeal_iff
      (C := (1 : Matrix (Fin n) (Fin n) R)) (n := n) d
  have hSL_iff : (∀ x ∈ ({(GeneralLinear.determinantGroupLike R n :
      GeneralLinear.coordinateHopfAlgebra R n) - 1} :
        Set (GeneralLinear.coordinateHopfAlgebra R n)), d x = 0) ↔
        Matrix.trace (GeneralLinear.tangentMatrix n d) = 0 := by
    rw [← HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span
      (SpecialLinear.definingHopfIdeal R n)
      (SpecialLinear.definingHopfIdeal_toIdeal R n) d]
    exact SpecialLinear.mem_lieSubalgebra_definingHopfIdeal_iff n d
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ hspan,
    Set.forall_mem_union, hO_iff, hSL_iff]
  constructor
  · rintro ⟨hform, _⟩
    have hsum : GeneralLinear.tangentMatrix n d +
        (GeneralLinear.tangentMatrix n d)ᵀ = 0 := by simpa using hform
    simpa using congrArg Matrix.transpose
      (add_eq_zero_iff_eq_neg.mp hsum)
  · intro hskew
    refine ⟨?_, ?_⟩
    · apply Matrix.ext
      intro i j
      have hij : GeneralLinear.tangentMatrix n d j i =
          -GeneralLinear.tangentMatrix n d i j := by
        simpa only [Matrix.transpose_apply, Matrix.neg_apply] using
          congrFun (congrFun hskew i) j
      change GeneralLinear.tangentMatrix n d i j +
        GeneralLinear.tangentMatrix n d j i = 0
      rw [hij]
      ring
    · exact trace_eq_zero_of_transpose_eq_neg n _ hskew

/-- The tangent matrix of `SOₙ`, as a skew-symmetric matrix in Mathlib's orthogonal Lie algebra. -/
noncomputable def tangentMatrix [Invertible (2 : B)] :
    Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) →ₗ[B]
      LieAlgebra.Orthogonal.so (Fin n) B :=
  let ambient := (GeneralLinear.tangentMatrix (R := R) (B := B) n).comp
    (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n)).toLinearMap
  ambient.codRestrict (LieAlgebra.Orthogonal.so (Fin n) B) fun d => by
    change ambient d ∈ LieAlgebra.Orthogonal.so (Fin n) B
    rw [LieAlgebra.Orthogonal.mem_so]
    apply (mem_lieSubalgebra_definingHopfIdeal_iff n _).mp
    change HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) d ∈
      HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n)
    simpa only [HopfIdeal.quotientLieEquiv_apply_coe] using
      (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R n) d).property

/-- The underlying matrix of `tangentMatrix` is the ambient tangent matrix after quotienting by
the special-orthogonal defining ideal. -/
@[simp]
theorem tangentMatrix_apply_coe [Invertible (2 : B)]
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    (tangentMatrix n d : Matrix (Fin n) (Fin n) B) =
      GeneralLinear.tangentMatrix n
        (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) d) := by
  rw [tangentMatrix]
  change GeneralLinear.tangentMatrix n
    (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) d) = _
  rfl

private theorem tangentMatrix_injective [Invertible (2 : B)] :
    Function.Injective (tangentMatrix (R := R) (B := B) n) := by
  intro d e hde
  apply HopfIdeal.quotientLieHom_injective (B := B) (definingHopfIdeal R n)
  apply (GeneralLinear.tangentLinearEquivMatrix (R := R) (B := B) n).injective
  simpa only [GeneralLinear.tangentLinearEquivMatrix_apply, tangentMatrix_apply_coe n] using
    congrArg Subtype.val hde

private theorem tangentMatrix_surjective [Invertible (2 : B)] :
    Function.Surjective (tangentMatrix (R := R) (B := B) n) := by
  intro X
  let d := (GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) n).symm X.val
  have hd : GeneralLinear.tangentMatrix n d = X.val := by
    rw [← GeneralLinear.tangentLieEquivMatrix_apply]
    exact (GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) n).apply_symm_apply X.val
  have hmem : d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n) := by
    apply (mem_lieSubalgebra_definingHopfIdeal_iff n d).mpr
    rw [hd]
    exact (LieAlgebra.Orthogonal.mem_so (n := Fin n) (R := B) X.val).mp X.property
  let d' : HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n) := ⟨d, hmem⟩
  let e := (HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R n)).symm d'
  refine ⟨e, Subtype.ext ?_⟩
  rw [tangentMatrix_apply_coe]
  have he : HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) e = d := by
    rw [← HopfIdeal.quotientLieEquiv_apply_coe]
    exact congrArg Subtype.val
      ((HopfIdeal.quotientLieEquiv (B := B) (definingHopfIdeal R n)).apply_symm_apply d')
  rw [he, hd]

/-- The tangent Lie algebra of `SOₙ` is the classical orthogonal Lie algebra, whenever `2` is
invertible in the coefficient algebra. -/
noncomputable def tangentLieEquivSo [Invertible (2 : B)] :
    Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B) ≃ₗ⁅B⁆
      LieAlgebra.Orthogonal.so (Fin n) B :=
  LieEquiv.ofBijective
    { tangentMatrix (R := R) (B := B) n with
      map_lie' := fun {d e} ↦ by
        apply Subtype.ext
        change GeneralLinear.tangentMatrix n
            (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) ⁅d, e⁆) =
          ⁅GeneralLinear.tangentMatrix n
              (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) d),
            GeneralLinear.tangentMatrix n
              (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R n) e)⁆
        rw [LieHom.map_lie, GeneralLinear.tangentMatrix_lie] }
    ⟨tangentMatrix_injective (R := R) (B := B) n,
      tangentMatrix_surjective (R := R) (B := B) n⟩

/-- The orthogonal Lie equivalence computes by the tangent-matrix map. -/
@[simp]
theorem tangentLieEquivSo_apply [Invertible (2 : B)]
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    tangentLieEquivSo n d = tangentMatrix n d := by
  rfl

end TauCeti.SpecialOrthogonal
