/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.ChangeBasis
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.ChangeBasis
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Finite-dimensional unitary comodules

A finite-dimensional inner product space with a native right coaction is unitary when its
coefficient matrix in an orthonormal basis is unitary. The coefficient algebra may be
noncommutative; matrix star is conjugate transpose, not entrywise star. No norm or positivity
on the coefficient algebra is required.

`OrthonormalBasis.coefficientMatrix_eq_conjTranspose_mul` gives the change-of-basis formula,
including bases with different finite index types. Consequently
`OrthonormalBasis.isUnitary_comodule_iff` tests unitarity in any orthonormal basis,
independently of the arbitrary standard basis used in the definition. For Hopf algebras,
unitarity is equivalent to the antipode acting on coefficients by transposed star.

These algebraic unitary objects are the finite coefficient objects used in unitarization
and reconstruction of compact quantum groups.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 1.3, for unitary corepresentations.
-/

public section

open Module TauCeti TauCeti.Comodule
open scoped Matrix

section Coalgebra

variable {𝕜 A M ι κ : Type*} [RCLike 𝕜] [Semiring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A] [Coalgebra 𝕜 A]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [Comodule 𝕜 A M]
  [Fintype ι] [Fintype κ]

namespace OrthonormalBasis

/-- An orthonormal change of basis conjugates the coefficient matrix by the scalar
change-of-basis matrix. The index types need not be the same. -/
theorem coefficientMatrix_eq_conjTranspose_mul
    (b : OrthonormalBasis ι 𝕜 M) (c : OrthonormalBasis κ 𝕜 M) :
    coefficientMatrix (C := A) c.toBasis =
      ((b.toBasis.toMatrix c.toBasis).map (algebraMap 𝕜 A))ᴴ *
        coefficientMatrix (C := A) b.toBasis *
          (b.toBasis.toMatrix c.toBasis).map (algebraMap 𝕜 A) := by
  classical
  rw [Matrix.mul_assoc, b.toBasis.coefficientMatrix_mul_toMatrix c.toBasis,
    ← Matrix.mul_assoc, c.coe_toBasis, b.toMatrix_map_conjTranspose_mul_self c,
    Matrix.one_mul]

/-- Transfer unitarity across an orthonormal change of coefficient basis. -/
private theorem coefficientMatrix_mem_unitary [DecidableEq ι] [DecidableEq κ]
    (b : OrthonormalBasis ι 𝕜 M) (c : OrthonormalBasis κ 𝕜 M)
    (h : coefficientMatrix (C := A) b.toBasis ∈ unitary (Matrix ι ι A)) :
    coefficientMatrix (C := A) c.toBasis ∈ unitary (Matrix κ κ A) := by
  rw [b.coefficientMatrix_eq_conjTranspose_mul c]
  exact Matrix.conjTranspose_mul_mul_mem_unitary _
    (b.toMatrix_map_conjTranspose_mul_self c) (b.toMatrix_map_self_mul_conjTranspose c) h

/-- Unitarity of the coefficient matrix is independent of the orthonormal basis, even when
the two bases use different finite index types. -/
theorem coefficientMatrix_mem_unitary_iff [DecidableEq ι] [DecidableEq κ]
    (b : OrthonormalBasis ι 𝕜 M) (c : OrthonormalBasis κ 𝕜 M) :
    coefficientMatrix (C := A) b.toBasis ∈ unitary (Matrix ι ι A) ↔
      coefficientMatrix (C := A) c.toBasis ∈ unitary (Matrix κ κ A) :=
  ⟨coefficientMatrix_mem_unitary b c, coefficientMatrix_mem_unitary c b⟩

end OrthonormalBasis

variable [FiniteDimensional 𝕜 M]

namespace TauCeti.Comodule

/-- A native finite-dimensional comodule on an inner product space is unitary if its
coefficient matrix in an orthonormal basis is unitary. By
`OrthonormalBasis.isUnitary_comodule_iff`, the choice of
orthonormal basis does not matter. -/
def IsUnitary (𝕜 A M : Type*) [RCLike 𝕜] [Semiring A] [StarRing A]
    [Algebra 𝕜 A] [Coalgebra 𝕜 A]
    [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [Comodule 𝕜 A M]
    [FiniteDimensional 𝕜 M] : Prop :=
  coefficientMatrix (C := A) (stdOrthonormalBasis 𝕜 M).toBasis ∈
    unitary (Matrix (Fin (finrank 𝕜 M)) (Fin (finrank 𝕜 M)) A)

end TauCeti.Comodule

namespace OrthonormalBasis

/-- Unitarity can be checked in any finite orthonormal basis. -/
theorem isUnitary_comodule_iff [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 M) :
    IsUnitary 𝕜 A M ↔ coefficientMatrix (C := A) b.toBasis ∈ unitary (Matrix ι ι A) :=
  (stdOrthonormalBasis 𝕜 M).coefficientMatrix_mem_unitary_iff b

end OrthonormalBasis

namespace TauCeti.Comodule

/-- In a unitary comodule the coefficient matrix of every orthonormal basis is unitary. -/
theorem IsUnitary.coefficientMatrix_mem_unitary (h : IsUnitary 𝕜 A M)
    [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 M) :
    coefficientMatrix (C := A) b.toBasis ∈ unitary (Matrix ι ι A) :=
  b.isUnitary_comodule_iff.mp h

end TauCeti.Comodule

end Coalgebra

namespace GroupLike

section GroupLike

variable {𝕜 A M : Type*} [RCLike 𝕜] [Semiring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A] [Coalgebra 𝕜 A]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]

/-- A unitary group-like element gives a unitary scalar coaction on every finite-dimensional
inner product space. In particular this includes the rank-one unitary corepresentations. -/
theorem isUnitary_comodule (g : GroupLike 𝕜 A) (hg : (g : A) ∈ unitary A) :
    letI : Comodule 𝕜 A M := groupLike (R := 𝕜) (C := A) (M := M) g
    IsUnitary 𝕜 A M := by
  classical
  let : Comodule 𝕜 A M := groupLike (R := 𝕜) (C := A) (M := M) g
  let b := stdOrthonormalBasis 𝕜 M
  rw [b.isUnitary_comodule_iff]
  have hmat : coefficientMatrix (C := A) b.toBasis = Matrix.diagonal (fun _ => (g : A)) := by
    ext i j
    simp [coefficientMatrix_apply, matrixCoefficient_groupLike, Basis.coord_apply,
      Matrix.diagonal_apply]
  rw [hmat, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  exact fun _ => hg

end GroupLike

end GroupLike

section Hopf

variable {𝕜 A M ι : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [HopfAlgebra 𝕜 A]
  [StarModule 𝕜 A] [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]
  [Comodule 𝕜 A M] [FiniteDimensional 𝕜 M] [Fintype ι]

namespace OrthonormalBasis

/-- For a Hopf comodule, unitarity means precisely that the antipode of its coefficient
matrix is its conjugate transpose. -/
theorem isUnitary_comodule_iff_map_antipode_eq_conjTranspose
    (b : OrthonormalBasis ι 𝕜 M) :
    IsUnitary 𝕜 A M ↔
      (coefficientMatrix (C := A) b.toBasis).map (HopfAlgebra.antipode 𝕜) =
        (coefficientMatrix (C := A) b.toBasis)ᴴ := by
  classical
  rw [b.isUnitary_comodule_iff]
  constructor
  · intro h
    exact left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b.toBasis) h.2
  · intro h
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, ← h]
    exact ⟨map_antipode_mul_coefficientMatrix b.toBasis,
      coefficientMatrix_mul_map_antipode b.toBasis⟩

end OrthonormalBasis

namespace TauCeti.Comodule

/-- The antipode of a coefficient of a unitary comodule is the star of the transposed
coefficient. -/
@[simp]
theorem IsUnitary.antipode_coefficientMatrix (h : IsUnitary 𝕜 A M)
    (b : OrthonormalBasis ι 𝕜 M) (i j : ι) :
    HopfAlgebra.antipode 𝕜 (coefficientMatrix (C := A) b.toBasis i j) =
      star (coefficientMatrix (C := A) b.toBasis j i) := by
  classical
  exact congrFun (congrFun (b.isUnitary_comodule_iff_map_antipode_eq_conjTranspose.mp h) i) j

end TauCeti.Comodule

end Hopf
