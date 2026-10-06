/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Adjoint weight spaces of the symplectic group

The paired diagonal torus acts on the `(i,j)` entry of a symplectic tangent matrix
through the difference of the standard weights `εₐ` and `-εₐ`. A cotangent-dual
vector has adjoint weight `α` exactly when its matrix entries of every other weight
vanish. This criterion uses the actual torus coaction and distinguishes characters
even in characteristic two and over rings with nilpotents. It provides the matrix
criterion for identifying the root lines and normalizing a symplectic pinning.

The universal-point argument follows
`TauCeti.SpecialLinear.mem_adjointWeightSpace_iff` and uses the symplectic
tangent Lie equivalence, quotient differential equivariance, and the general-linear
matrix conjugation formula. No field or reducedness assumption is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1 (root spaces and pinnings).
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.Symplectic

universe u

noncomputable section

variable {R : Type u} [CommRing R] {m : ℕ}

/-- The standard weights of the paired diagonal torus: `εᵢ` in the first block and
`-εᵢ` in the second block. These are integral characters, irrespective of the base ring. -/
def diagonalTorusWeight : (Fin m ⊕ Fin m) → ULift.{u} (Fin m) →₀ ℤ
  | .inl i => Finsupp.single (ULift.up i) 1
  | .inr i => -Finsupp.single (ULift.up i) 1

@[simp]
theorem diagonalTorusWeight_inl (i : Fin m) :
    diagonalTorusWeight (.inl i) = Finsupp.single (ULift.up i) (1 : ℤ) := (rfl)

@[simp]
theorem diagonalTorusWeight_inr (i : Fin m) :
    diagonalTorusWeight (.inr i) = -Finsupp.single (ULift.up i) (1 : ℤ) := (rfl)

private theorem ambientCounitPoint_universalDiagonalTorus :
    GeneralLinear.counitPointsMulEquiv (m + m)
      (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
        (GeneralLinear.coordinateHopfAlgebra R (m + m))
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))))
        (Bialgebra.Quotient.mkBialgHom (definingHopfIdeal R m).toIdeal)
        (Derivation.pointInCounitAlgebra
          (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))))
          (toConv (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom))) =
      diagGL (fun i => DiagonalizableGroup.charOfPoint
        (AlgHom.id R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))))
        (Multiplicative.ofAdd (diagonalTorusWeight (finSumFinEquiv.symm i)))) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinear.counitPointsMulEquiv_apply]
  -- The quotient and ambient counit indices denote the same coefficient algebra.
  erw [Bialgebra.CounitAlgebra.algEquivSelf_apply, AlgHom.mapDomain_apply_apply,
    Derivation.pointInCounitAlgebra_apply]
  rw [ofConv_toConv, ← CommHopfAlgCat.hom_mkQuotient, ← coordinateMap_def]
  by_cases hij : i = j
  · subst j
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i
    · erw [coordinateMap_comp_diagonalTorusCoordinateMap_X_castAdd (R := R) i]
      simp [diagGL_apply, finSumFinEquiv_apply_left]
    · rw [finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat]
      erw [coordinateMap_comp_diagonalTorusCoordinateMap_X_addNat (R := R) i]
      simp [diagGL_apply, ← Fin.natAdd_eq_addNat, finSumFinEquiv_symm_apply_natAdd,
        Finsupp.single_neg]
  · erw [coordinateMap_comp_diagonalTorusCoordinateMap_X_of_ne (R := R) i j hij]
    simp [diagGL_apply, hij]

/-- At the universal diagonal-torus point, each matrix entry is multiplied by its
integral character in the group-algebra basis. -/
theorem tangentMatrix_adDerivation_universalDiagonalTorus_apply
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) R))
    (i j : Fin m ⊕ Fin m) :
    (tangentMatrix m
      (Derivation.adDerivation
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)))
        (Derivation.pointInCounitAlgebra
          (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))))
          (toConv (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom))
        (Derivation.mapValue (Algebra.ofId R _) d)) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)))) i j =
      MonoidAlgebra.single
        (Multiplicative.ofAdd (diagonalTorusWeight i - diagonalTorusWeight j))
        ((tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) i j) := by
  rw [tangentMatrix_apply_coe, Matrix.submatrix_apply,
    HopfIdeal.quotientLieHom_adDerivation,
    GeneralLinear.tangentMatrix_adDerivation_apply_of_diagGL
      ambientCounitPoint_universalDiagonalTorus]
  simp only [Equiv.symm_apply_apply,
    DiagonalizableGroup.charOfPoint_apply_coe, DiagonalizableGroup.charOfPoint_apply_inv_coe,
    AlgHom.id_apply]
  have hmatrix := congrArg (fun X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) => X i j)
    (tangentMatrix_apply_coe (R := R) m (Derivation.mapValue (Algebra.ofId R _) d))
  rw [tangentMatrix_mapValue_coe, Matrix.map_apply, Algebra.ofId_apply] at hmatrix
  simp only [Matrix.submatrix_apply] at hmatrix
  -- The ambient tangent map retains the quotient-indexed coefficient structure.
  erw [← hmatrix]
  rw [mul_comm (MonoidAlgebra.single _ (1 : R)), mul_assoc,
    MonoidAlgebra.single_mul_single, one_mul]
  rw [← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]
  congr 1
  simp [ofAdd_sub, div_eq_mul_inv]

/-- A cotangent-dual vector has adjoint weight `α` exactly when every entry of a
different weight in its paired symplectic tangent matrix vanishes. -/
theorem mem_adjointWeightSpace_iff
    (α : Multiplicative (ULift.{u} (Fin m) →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R m))) :
    x ∈ Derivation.adjointWeightSpace (diagonalTorusCoordinateMap (R := R) (m := m)).hom α ↔
      ∀ i j : Fin m ⊕ Fin m,
        Multiplicative.ofAdd (diagonalTorusWeight i - diagonalTorusWeight j) ≠ α →
          (tangentMatrix m (Derivation.cotangentLinearEquiv (B := R) x) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) i j = 0 := by
  rw [Derivation.mem_adjointWeightSpace_iff_universalPointAction]
  let K := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))
  rw [← (Derivation.tangentScalarExtensionEquiv
    (R := R) (A := coordinateHopfAlgebra R m) (B := K)).injective.eq_iff]
  -- The scalar-extension action stores the coordinate algebra by its quotient presentation.
  erw [Derivation.tangentScalarExtensionEquiv_adjointAction (CommAlgCat.of R K)
      (toConv (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom),
    Derivation.tangentScalarExtensionEquiv_tmul, one_smul,
    Derivation.tangentScalarExtensionEquiv_tmul]
  have hentry (i j : Fin m ⊕ Fin m) :
      (tangentMatrix (B := K) m
          (MonoidAlgebra.single α (1 : R) •
            Derivation.mapValue (Algebra.ofId R K)
              (Derivation.cotangentLinearEquiv (B := R) x)) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) i j =
        MonoidAlgebra.single α
          ((tangentMatrix m (Derivation.cotangentLinearEquiv (B := R) x) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) i j) := by
    rw [map_smul, SetLike.val_smul, Matrix.smul_apply, smul_eq_mul,
      tangentMatrix_mapValue_coe, Matrix.map_apply, Algebra.ofId_apply]
    rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]
  constructor
  · intro h i j hij
    have he := congrArg (fun d =>
      (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) i j) h
    rw [tangentMatrix_adDerivation_universalDiagonalTorus_apply, hentry] at he
    by_contra hne
    exact hij (MonoidAlgebra.single_left_injective hne he)
  · intro h
    apply (tangentLieEquivSp (R := R) m).injective
    simp only [LieEquiv.coe_toLieHom]
    -- Injectivity exposes the quotient-indexed presentation of the coordinate algebra.
    erw [tangentLieEquivSp_apply, tangentLieEquivSp_apply]
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    rw [tangentMatrix_adDerivation_universalDiagonalTorus_apply, hentry]
    by_cases hij : Multiplicative.ofAdd (diagonalTorusWeight i - diagonalTorusWeight j) = α
    · rw [hij]
    · simp [h i j hij]

/-- A nonzero entry of a symplectic adjoint weight vector determines its character.
The assertion holds over every commutative base ring, including rings with zero divisors. -/
theorem ofAdd_diagonalTorusWeight_sub_eq_of_mem_adjointWeightSpace_of_apply_ne_zero
    {α : Multiplicative (ULift.{u} (Fin m) →₀ ℤ)}
    {x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R m))}
    (hx : x ∈ Derivation.adjointWeightSpace
      (diagonalTorusCoordinateMap (R := R) (m := m)).hom α)
    {i j : Fin m ⊕ Fin m}
    (hentry : (tangentMatrix m (Derivation.cotangentLinearEquiv (B := R) x) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) i j ≠ 0) :
    Multiplicative.ofAdd (diagonalTorusWeight i - diagonalTorusWeight j) = α := by
  by_contra hweight
  exact hentry ((mem_adjointWeightSpace_iff α x).mp hx i j hweight)

end

end TauCeti.Symplectic
