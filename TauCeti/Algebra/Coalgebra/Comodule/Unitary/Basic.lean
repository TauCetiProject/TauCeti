/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.ChangeBasis
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Dual
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.ChangeBasis
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Transport

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
unitarity is equivalent to the antipode acting on coefficients by transposed star, the explicit
right dual comodule in the dual basis has coefficient matrix given by the entrywise star
(`TauCeti.Comodule.coefficientMatrix_dualBasis_of_mem_unitary` and
`TauCeti.Comodule.IsUnitary.coefficientMatrix_dualBasis`), and any matrix `G` satisfying
`(u.map star)ᴴ * G * u.map star = G` for a unitary coefficient matrix `u` has `Gᵀ` intertwining
`u` with its double antipode `(u.map S).map S`.

These algebraic unitary objects—and the set `TauCeti.unitaryCoefficientSet` of matrix entries of
unitary `Fin n × Fin n` coefficient matrices over `ℂ`
(`Module.Basis.coefficientMatrix_mem_unitaryCoefficientSet`)—are the finite coefficient objects
used in unitarization and reconstruction of compact quantum groups.

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

namespace TauCeti

/-- The set of matrix entries of all finite-dimensional unitary matrix corepresentations on
`Fin n → ℂ` of a complex star coalgebra `A`. -/
noncomputable def unitaryCoefficientSet.{u} (A : Type u) [Semiring A] [Algebra ℂ A] [Coalgebra ℂ A]
    [StarRing A] : Set A :=
  {a : A | ∃ (n : ℕ) (ρ : Comodule ℂ A (Fin n → ℂ)), letI := ρ
    let U := coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n))
    U ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ ∃ i j, a = U i j}

/-- Membership in `unitaryCoefficientSet A` unfolds to being an entry of a unitary `Fin n × Fin n`
coefficient matrix. -/
theorem mem_unitaryCoefficientSet_iff.{u} {A : Type u} [Semiring A] [Algebra ℂ A] [Coalgebra ℂ A]
    [StarRing A] {a : A} : a ∈ unitaryCoefficientSet A ↔ ∃ (n : ℕ) (ρ : Comodule ℂ A (Fin n → ℂ)),
      letI := ρ
      let U := coefficientMatrix (C := A) (Pi.basisFun ℂ (Fin n))
      U ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ ∃ i j, a = U i j := Iff.rfl

end TauCeti

/-- Every entry of a unitary coefficient matrix in a finite basis belongs to
`unitaryCoefficientSet A`. -/
theorem Module.Basis.coefficientMatrix_mem_unitaryCoefficientSet {A M ι : Type*} [Semiring A]
    [Algebra ℂ A] [Coalgebra ℂ A] [StarRing A] [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ M)
    (hb : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j : ι) :
    coefficientMatrix (C := A) b i j ∈ unitaryCoefficientSet A := by
  let e := Fintype.equivFin ι
  let b' := b.reindex e
  have hmat : coefficientMatrix (C := A) b' =
      Matrix.reindexStarAlgEquiv ℂ A e (coefficientMatrix (C := A) b) := Matrix.ext fun p q ↦ by
    have hcoord : b'.coord p = b.coord (e.symm p) :=
      LinearMap.ext fun m ↦ by simp [b', Basis.coord_apply]
    simp [b', coefficientMatrix_apply, hcoord]
  have hb' : coefficientMatrix (C := A) b' ∈
      unitary (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A) := by
    rw [hmat]
    exact Unitary.map_mem (Matrix.reindexStarAlgEquiv ℂ A e) hb
  exact ⟨Fintype.card ι, Transport b'.equivFun,
    by rwa [b'.coefficientMatrix_basisFun_transport_equivFun], e i, e j,
    by simp [b'.coefficientMatrix_basisFun_transport_equivFun, hmat]⟩

namespace GroupLike

variable {𝕜 A M : Type*} [RCLike 𝕜] [Semiring A] [StarRing A]
  [Algebra 𝕜 A] [Coalgebra 𝕜 A]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]

/-- A unitary group-like element gives a unitary scalar coaction on every finite-dimensional
inner product space. In particular this includes the rank-one unitary corepresentations. -/
theorem isUnitary_comodule (g : GroupLike 𝕜 A) (hg : (g : A) ∈ unitary A) :
    letI : Comodule 𝕜 A M := groupLike (R := 𝕜) (C := A) (M := M) g
    IsUnitary 𝕜 A M := by
  classical
  let : Comodule 𝕜 A M := groupLike (R := 𝕜) (C := A) (M := M) g
  let b := stdOrthonormalBasis 𝕜 M
  rw [IsUnitary]
  have hmat : coefficientMatrix (C := A) b.toBasis = Matrix.diagonal (fun _ => (g : A)) := by
    ext i j
    simp [coefficientMatrix_apply, matrixCoefficient_groupLike, Basis.coord_apply,
      Matrix.diagonal_apply]
  rw [hmat, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  exact fun _ => hg

end GroupLike

section HopfDual

namespace TauCeti.Comodule

variable {R A M ι : Type*} [CommSemiring R] [Semiring A] [StarRing A]
  [HopfAlgebra R A] [AddCommMonoid M] [Module R M] [Comodule R A M]
  [Module.Finite R M] [Module.Projective R M] [Fintype ι] [DecidableEq ι]

attribute [local instance] Comodule.dual

/-- When `b` has unitary coefficient matrix `u`, the dual basis `b.dualBasis` of the explicit right
dual comodule has coefficient matrix `u.map star`, the entrywise star (conjugate matrix). -/
theorem coefficientMatrix_dualBasis_of_mem_unitary (b : Basis ι R M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    coefficientMatrix (C := A) b.dualBasis = (coefficientMatrix (C := A) b).map star := by
  have hu2 : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  have hS : (coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R) =
      (coefficientMatrix (C := A) b)ᴴ :=
    left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) hu2
  ext i j
  rw [coefficientMatrix_dualBasis, hS, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply]

end TauCeti.Comodule

end HopfDual

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

attribute [local instance] Comodule.dual in
/-- For a finite-dimensional unitary comodule in an orthonormal basis `b`, the dual basis
`b.toBasis.dualBasis` has coefficient matrix `(coefficientMatrix b.toBasis).map star`. -/
theorem IsUnitary.coefficientMatrix_dualBasis [DecidableEq ι] (hM : IsUnitary 𝕜 A M)
    (b : OrthonormalBasis ι 𝕜 M) :
    coefficientMatrix (C := A) b.toBasis.dualBasis =
      (coefficientMatrix (C := A) b.toBasis).map star :=
  coefficientMatrix_dualBasis_of_mem_unitary b.toBasis (hM.coefficientMatrix_mem_unitary b)

end TauCeti.Comodule

namespace Module.Basis

/-- If the coefficient matrix `u` of `b` is unitary and `(u.map star)ᴴ * G * u.map star = G`, then
`Gᵀ` intertwines `u` with its double antipode `(u.map S).map S`. -/
theorem map_antipode_map_antipode_mul_transpose_of_conjTranspose_map_star_mul_mul_eq
    {R A M ι : Type*} [CommSemiring R] [Semiring A] [StarRing A] [HopfAlgebra R A]
    [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι] [DecidableEq ι]
    (b : Basis ι R M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {G : Matrix ι ι R} (hG : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap R A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap R A)) :
    (((coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R)).map (HopfAlgebra.antipode R)) *
        Gᵀ.map (algebraMap R A) =
      Gᵀ.map (algebraMap R A) * coefficientMatrix (C := A) b := by
  set u := coefficientMatrix (C := A) b
  set S : A →ₗ[R] A := HopfAlgebra.antipode R
  obtain ⟨hu1, hu2⟩ := Matrix.mem_unitary_iff_conjTranspose.mp hu
  have huS : u.map S = uᴴ := left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) hu2
  have hmulS (X Y : Matrix ι ι A) : ((X * Y).map S)ᵀ = (Y.map S)ᵀ * (X.map S)ᵀ :=
    Matrix.ext fun _ _ ↦ by simp [Matrix.mul_apply, S, _root_.HopfAlgebra.antipode_mul_antidistrib]
  have hij (i j) : S (u i j) = star (u j i) := by simpa using congrFun (congrFun huS i) j
  have hf1 : ((u.map star).map S)ᵀ = (u.map S).map S := Matrix.ext fun _ _ ↦ by simp [← hij]
  have hf2 : ((G.map (algebraMap R A)).map S)ᵀ = Gᵀ.map (algebraMap R A) :=
    Matrix.ext fun _ _ ↦ by simp [S, Algebra.algebraMap_eq_smul_one]
  have hf3 : (((u.map star)ᴴ).map S)ᵀ = uᴴ := Matrix.ext fun _ _ ↦ by simp [hij]
  have h1 := congrArg (fun X : Matrix ι ι A ↦ (X.map S)ᵀ) hG
  rw [hmulS, hmulS, hf1, hf2, hf3, ← Matrix.mul_assoc] at h1
  simpa only [Matrix.mul_assoc _ uᴴ, hu1, Matrix.mul_one] using congrArg (· * u) h1

end Module.Basis

end Hopf
