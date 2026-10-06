/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
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

private theorem diagonalTorus_weightTorusFactorization :
    (diagonalTorusCoordinateMap (R := R) (m := m)).hom.comp
        (Bialgebra.Quotient.mkBialgHom (definingHopfIdeal R m).toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap
        (fun i : Fin (m + m) => ⇑(diagonalTorusWeight (finSumFinEquiv.symm i)))).hom := by
  simpa only [CommHopfAlgCat.hom_comp, coordinateMap_def, CommHopfAlgCat.hom_mkQuotient] using
    congrArg (fun f => f.hom) (coordinateMap_comp_diagonalTorusCoordinateMap (R := R) (m := m))

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
  rw [tangentMatrix_apply_coe, tangentMatrix_apply_coe, Matrix.submatrix_apply,
    Matrix.submatrix_apply]
  simpa only [Equiv.symm_apply_apply, ← Finsupp.coe_sub, SplitTorus.weightCharacter_coe] using
    HopfIdeal.tangentMatrix_adDerivation_weightTorus_apply (definingHopfIdeal R m)
      (fun k : Fin (m + m) => ⇑(diagonalTorusWeight (finSumFinEquiv.symm k)))
      (diagonalTorusCoordinateMap (R := R) (m := m)).hom
      diagonalTorus_weightTorusFactorization s d (finSumFinEquiv i) (finSumFinEquiv j)

/-- At the universal diagonal-torus point, each matrix entry is multiplied by its
integral character in the group-algebra basis. -/
theorem tangentMatrix_adDerivation_universalDiagonalTorus_apply
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) R))
    (i j : Fin m ⊕ Fin m) :
    (tangentMatrix m
      (Derivation.adDerivation
        (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))))
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

/-- A symplectic tangent vector transforms by `α` at the universal torus point exactly
when every entry of a different character vanishes. -/
theorem adDerivation_universalDiagonalTorus_eq_iff
    (α : Multiplicative (ULift.{u} (Fin m) →₀ ℤ))
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) R)) :
    Derivation.adDerivation
        (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))))
        (Derivation.pointInCounitAlgebra
          (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))))
          (toConv (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom))
        (Derivation.mapValue (Algebra.ofId R _) d) =
      MonoidAlgebra.single α (1 : R) • Derivation.mapValue (Algebra.ofId R _) d ↔
      ∀ i j : Fin m ⊕ Fin m,
        Multiplicative.ofAdd (diagonalTorusWeight i - diagonalTorusWeight j) ≠ α →
          (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) i j = 0 := by
  rw [HopfIdeal.adDerivation_universalWeightTorus_eq_iff (definingHopfIdeal R m)
    (fun k : Fin (m + m) => ⇑(diagonalTorusWeight (finSumFinEquiv.symm k)))
    (diagonalTorusCoordinateMap (R := R) (m := m)).hom
    diagonalTorus_weightTorusFactorization]
  simp only [← Finsupp.coe_sub, SplitTorus.weightCharacter_coe]
  constructor
  · intro h i j hij
    rw [tangentMatrix_apply_coe, Matrix.submatrix_apply]
    apply h
    simpa only [Equiv.symm_apply_apply] using hij
  · intro h i j hij
    have hh := h (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) hij
    rw [tangentMatrix_apply_coe, Matrix.submatrix_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at hh
    exact hh

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
  rw [Derivation.tangentScalarExtensionEquiv_adjointAction (CommAlgCat.of R K)
      (toConv (diagonalTorusCoordinateMap (R := R) (m := m)).hom.toAlgHom),
    Derivation.tangentScalarExtensionEquiv_tmul, one_smul,
    Derivation.tangentScalarExtensionEquiv_tmul, adDerivation_universalDiagonalTorus_eq_iff]

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
