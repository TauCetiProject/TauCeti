/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Componentwise
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.Homology.ReidemeisterTorsion.SquareMinor

/-!
# A partially acyclic complex over the group ring of `ℤ/2`

Let `g` be the generator of `ℤ/2` and `ℤ[ℤ/2]` its integral group ring. The complex
`TauCeti.PartialAcyclicity.complex` is concentrated in degrees `1` and `0`, both of rank one, with
differential multiplication by `1 - g`. The rational group algebra of `ℤ/2` is the product `ℚ × ℚ`
of its two components, given by the characters `g ↦ 1` and `g ↦ -1`
(`TauCeti.PartialAcyclicity.characters`). Along these the differential becomes `0` and `2`, so the
scalar extension to the first component is not acyclic and the one to the second component is.
Accordingly the componentwise torsion with values in `ℚ × ℚ` is `(0, 1/2)`
(`TauCeti.PartialAcyclicity.reidemeisterTorsionComponentwise_complex`): the torsion records the
acyclic component even though the complex has a component that is not acyclic.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, §2.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex Module

namespace TauCeti.PartialAcyclicity

/-- The ranks of the complex: one in degrees `0` and `1`, zero elsewhere. -/
def rank (i : ℤ) : ℕ :=
  if i = 0 ∨ i = 1 then 1 else 0

/-- The generator `g` of `ℤ/2`, as an element of the group ring `ℤ[ℤ/2]`. -/
def gen : AddMonoidAlgebra ℤ (ZMod 2) :=
  AddMonoidAlgebra.single 1 1

/-- The matrices of the differentials, all of whose entries are `1 - g`. Only the differential
from degree `1` to degree `0` has entries: in every other degree the source or the target has
rank zero. -/
def matrix (i : ℤ) : Matrix (Fin (rank i)) (Fin (rank (i + 1))) (AddMonoidAlgebra ℤ (ZMod 2)) :=
  Matrix.of fun _ _ ↦ 1 - gen

/-- Consecutive products of the matrices vanish, since one of the factors has no rows or no
columns. -/
theorem matrix_mul_matrix (i : ℤ) : matrix i * matrix (i + 1) = 0 := by
  ext a b
  have ha := a.pos
  have hb := b.pos
  simp only [rank] at ha hb
  split_ifs at ha hb <;> omega

/-- The complex `ℤ[ℤ/2] → ℤ[ℤ/2]`, multiplication by `1 - g`, in degrees `1` and `0`. -/
abbrev complex : ChainComplex (ModuleCat (AddMonoidAlgebra ℤ (ZMod 2))) ℤ :=
  ChainComplex.ofMatrix matrix matrix_mul_matrix

/-- The character of `ℤ/2` sending `g` to `-1`. -/
def signChar : Multiplicative (ZMod 2) →* ℚ where
  toFun x := (-1) ^ x.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

/-- Evaluation of the group ring `ℤ[ℤ/2]` at the trivial character and at the sign character of
`ℤ/2`. These are the two components of the rational group algebra `ℚ[ℤ/2] ≅ ℚ × ℚ`. -/
def characters : AddMonoidAlgebra ℤ (ZMod 2) →+* ℚ × ℚ :=
  ((AddMonoidAlgebra.lift ℤ ℚ (ZMod 2) 1 : _ →+* ℚ)).prod
    (AddMonoidAlgebra.lift ℤ ℚ (ZMod 2) signChar : _ →+* ℚ)

/-- The torsion of the scalar extension of `complex` along a ring homomorphism
`φ : ℤ[ℤ/2] →+* K` to a field is the inverse of `φ (1 - g)`; it is `0` when `φ (1 - g) = 0`. -/
theorem reidemeisterTorsion_extendScalarsOfBasis_complex {K : Type*} [Field K]
    (φ : AddMonoidAlgebra ℤ (ZMod 2) →+* K) :
    (complex.extendScalarsOfBasis (ChainComplex.ofMatrixBasis _ _) φ).reidemeisterTorsion
      (ChainComplex.ofMatrixBasis _ _) = (φ (1 - gen))⁻¹ := by
  have hd (i : ℤ) : LinearMap.toMatrix (ChainComplex.ofMatrixBasis _ _ (i + 1))
      (ChainComplex.ofMatrixBasis _ _ i)
      ((complex.extendScalarsOfBasis (ChainComplex.ofMatrixBasis _ _) φ).d (i + 1) i).hom =
        Matrix.of fun _ _ ↦ φ (1 - gen) := by
    rw [ChainComplex.toMatrix_ofMatrix_d, ChainComplex.toMatrix_ofMatrix_d]
    rfl
  -- `rank (-1 + 1)` reduces to `1`.
  let _ : Unique (Fin (rank (-1 + 1))) := inferInstanceAs (Unique (Fin 1))
  by_cases h : (complex.extendScalarsOfBasis (ChainComplex.ofMatrixBasis _ _) φ).Acyclic
  · rw [reidemeisterTorsion_eq_det_zpow (j := -1) h fun i h0 h1 ↦ by simp_all [rank],
      Basis.det_apply, Matrix.det_unique, Basis.toMatrix_apply, ← LinearMap.toMatrix_apply, hd]
    simp
  · -- If `φ (1 - g) ≠ 0`, the complex is acyclic, its square minors being `φ (1 - g)` in degree
    -- `0` and empty elsewhere.
    rw [reidemeisterTorsion_of_not_acyclic _ _ h, eq_comm, inv_eq_zero]
    by_contra hne
    refine h (acyclic_of_det_torsionMinor_ne_zero (c := ChainComplex.ofMatrixBasis _ _)
      (q := fun j ↦ if j = 0 then 1 else 0)
      (p := fun j ↦ if j = 1 then 1 else 0) (hn := fun i ↦ by unfold rank; split_ifs <;> omega)
      (hpq := fun j ↦ by split_ifs <;> omega) fun j ↦ ?_)
    by_cases hj : j = 0
    · subst hj
      let _ : Unique (Fin (if (0 : ℤ) = 0 then 1 else 0)) := inferInstanceAs (Unique (Fin 1))
      rw [Matrix.det_unique, torsionMinor_apply, ← LinearMap.toMatrix_apply, hd]
      exact hne
    · have : IsEmpty (Fin (if j = 0 then 1 else 0)) := by simp [hj]
      rw [Matrix.det_isEmpty]
      exact one_ne_zero

/-- The complex is bounded. -/
theorem finite_rank_ne_zero : {i | rank i ≠ 0}.Finite :=
  (Set.toFinite {0, 1}).subset fun i hi ↦ by
    by_contra h
    simp_all [rank]

/-- The scalar extension of `complex` along a ring homomorphism `φ : ℤ[ℤ/2] →+* K` to a field is
acyclic if and only if `φ (1 - g) ≠ 0`. -/
theorem acyclic_extendScalarsOfBasis_complex_iff {K : Type*} [Field K]
    (φ : AddMonoidAlgebra ℤ (ZMod 2) →+* K) :
    (complex.extendScalarsOfBasis (ChainComplex.ofMatrixBasis _ _) φ).Acyclic ↔
      φ (1 - gen) ≠ 0 := by
  rw [← not_iff_not, ← reidemeisterTorsion_eq_zero_iff _ _ finite_rank_ne_zero,
    reidemeisterTorsion_extendScalarsOfBasis_complex, inv_eq_zero, not_not]

/-- **Partial acyclicity.** The componentwise torsion of `complex`, with values in `ℚ × ℚ` along
the two characters of `ℤ/2`, is `(0, 1/2)`: along the trivial character the differential becomes
`0` and the complex is not acyclic, while along the sign character it becomes `2`. -/
theorem reidemeisterTorsionComponentwise_complex :
    letI := characters.toAlgebra
    complex.reidemeisterTorsionComponentwise (ChainComplex.ofMatrixBasis _ _) (ℚ × ℚ) =
      (0, 1 / 2) := by
  let := characters.toAlgebra
  refine ((complex.eq_reidemeisterTorsionComponentwise_iff _ ![RingHom.fst ℚ ℚ, RingHom.snd ℚ ℚ]
    fun x y h ↦ Prod.ext (congrFun h 0) (congrFun h 1)).2 ?_).symm
  rw [Fin.forall_fin_two]
  constructor
  · rw [reidemeisterTorsion_extendScalarsOfBasis_complex]
    simp [RingHom.algebraMap_toAlgebra, characters, gen]
  · rw [reidemeisterTorsion_extendScalarsOfBasis_complex]
    norm_num [RingHom.algebraMap_toAlgebra, characters, gen, signChar, ZMod.val_one]

end TauCeti.PartialAcyclicity
