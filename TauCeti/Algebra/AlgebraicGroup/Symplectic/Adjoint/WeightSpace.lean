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
through `diagonalTorusWeight i - diagonalTorusWeight j`, where the standard weight
is `εᵢ` on the first block and `-εᵢ` on the second. A cotangent-dual vector has
adjoint weight `α` exactly when its matrix entries of every other weight
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

private theorem ambientCounitPoint_diagonalTorus {B : Type*} [CommRing B] [Algebra R B]
    (s : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] B)) :
    GeneralLinear.counitPointsMulEquiv (m + m)
      (AlgHom.mapDomain (A := Bialgebra.CounitAlgebra R
        (GeneralLinear.coordinateHopfAlgebra R (m + m)) B)
        (Bialgebra.Quotient.mkBialgHom (definingHopfIdeal R m).toIdeal)
        (Derivation.pointInCounitAlgebra B
          (toConv (s.ofConv.comp
            (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom)))) =
      diagGL (fun i => DiagonalizableGroup.charOfPoint s.ofConv
        (Multiplicative.ofAdd (diagonalTorusWeight (finSumFinEquiv.symm i)))) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinear.counitPointsMulEquiv_apply]
  -- `mapDomain` uses the ambient-indexed copy of B, whereas `pointInCounitAlgebra`
  -- uses the quotient-indexed copy. They reduce to the same coefficient algebra.
  erw [Bialgebra.CounitAlgebra.algEquivSelf_apply, AlgHom.mapDomain_apply_apply,
    Derivation.pointInCounitAlgebra_apply]
  rw [ofConv_toConv, AlgHom.comp_apply,
    ← CommHopfAlgCat.hom_mkQuotient, ← coordinateMap_def]
  -- The preceding point rules erase the category and matrix coercions; restate them
  -- with their full types so the coordinate-map comparison rewrites at ordinary transparency.
  change s.ofConv ((diagonalTorusCoordinateMap (R := R) (m := m)).hom
    ((coordinateMap R m).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
      (GeneralLinear.coordinateRingMap R (m + m) (MvPolynomial.X (i, j)))))) =
    (diagGL (fun k => DiagonalizableGroup.charOfPoint s.ofConv
      (Multiplicative.ofAdd (diagonalTorusWeight (finSumFinEquiv.symm k)))) :
        Matrix (Fin (m + m)) (Fin (m + m)) B) i j
  rw [← BialgHom.comp_apply, ← _root_.CommHopfAlgCat.hom_comp,
    coordinateMap_comp_diagonalTorusCoordinateMap, GeneralLinear.weightTorusCoordinateMap_X,
    Finsupp.equivFunOnFinite_symm_coe]
  by_cases hij : i = j <;>
    simp [diagGL_apply, hij, DiagonalizableGroup.charOfPoint_apply_coe]

/-- Over any coefficient algebra, a diagonal-torus point scales each tangent-matrix entry
by the difference of its two standard weights. -/
theorem tangentMatrix_adDerivation_diagonalTorus_apply
    {B : Type*} [CommRing B] [Algebra R B]
    (s : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] B))
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B))
    (i j : Fin m ⊕ Fin m) :
    (tangentMatrix m
      (Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra B
          (toConv (s.ofConv.comp
            (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom))) d) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) i j =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (Multiplicative.ofAdd (diagonalTorusWeight i - diagonalTorusWeight j)) : B) *
        (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) i j := by
  rw [tangentMatrix_apply_coe, Matrix.submatrix_apply,
    HopfIdeal.quotientLieHom_adDerivation,
    GeneralLinear.tangentMatrix_adDerivation_apply_of_diagGL
      (ambientCounitPoint_diagonalTorus s)]
  simp only [Equiv.symm_apply_apply]
  have hentry : GeneralLinear.tangentMatrix (m + m)
      (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal R m) d)
        (finSumFinEquiv i) (finSumFinEquiv j) =
      (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) i j := by
    rw [tangentMatrix_apply, GeneralLinear.tangentMatrix_apply,
      HopfIdeal.quotientLieHom_apply_apply, coordinateMap_def, CommHopfAlgCat.mkQuotient_apply]
    exact Bialgebra.CounitAlgebra.algEquivSelf_apply R _ B _
  rw [hentry]
  simp only [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv, Units.val_mul]
  ring

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
  have h := tangentMatrix_adDerivation_diagonalTorus_apply
    (toConv (AlgHom.id R _)) (Derivation.mapValue (Algebra.ofId R _) d) i j
  rw [ofConv_toConv, AlgHom.id_comp] at h
  rw [h, tangentMatrix_mapValue_coe, Matrix.map_apply,
    DiagonalizableGroup.charOfPoint_apply_coe, AlgHom.id_apply, Algebra.ofId_apply]
  rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]

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
