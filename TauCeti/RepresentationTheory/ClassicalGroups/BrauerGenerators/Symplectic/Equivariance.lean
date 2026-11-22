/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Kronecker.Power
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action
-- Non-public: `Fintype.equivFin` transports finite coordinate index sets to `Fin n`, and
-- `Matrix.reindex_sumCongr_J` transports `Matrix.J` along that equivalence.
import Mathlib.Data.Fintype.EquivFin
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The Brauer algebra acts by intertwiners of the symplectic group

The action `TauCeti.brauerActionSymp` of the Brauer algebra `B_k(-2n)` on the tensor power
`((Fin n ⊕ Fin n) → R)^{⊗k}` commutes with the diagonal action `g ↦ g^{⊗k}` of every matrix `g`
preserving the standard alternating form `Matrix.J (Fin n) R`, that is, satisfying
`gᵀ * J * g = J`. Equivalently, the image of `B_k(-2n)` lies in the commutant of the symplectic
group acting on the tensor power (`TauCeti.range_brauerActionSymp_le_centralizer`); on two strands
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/TwoStrands.lean` upgrades
this inclusion to an equality (`TauCeti.range_brauerActionSymp_two_eq_centralizer`).

By `TauCeti.range_brauerActionSymp_eq_adjoin_union`, the image of `B_k(-2n)` is generated as an
`R`-algebra by the sign-twisted permutations `TauCeti.symplecticPermTensorAction` and the
distinct-strand cap-cup operators `TauCeti.symplecticCupCapAt`. Both families already commute with
`PiTensorProduct.map fun _ => A.mulVecLin`
(`PiTensorProduct.commute_signReindexRepresentation_map` and
`TauCeti.commute_symplecticCupCapAt_piTensorProductMap`), so the whole image lies in the
centralizer of `A^{⊗k}` (`TauCeti.commute_brauerActionSymp_piTensorProductMap`). Passing to
matrices in the monomial basis via `LinearMap.toMatrixAlgEquiv` and reindexing along
`Fintype.equivFin ι` via `Matrix.reindexAlgEquiv` then yields matrix-level equivariance for
`TauCeti.BrauerDiagram.symplecticActionMatrix` over any finite index type `ι`
(`TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`).

## Main results

* `TauCeti.commute_brauerActionSymp_piTensorProductMap`: every element of `B_k(-2n)` acts by an
  operator commuting with `A^{⊗k}` when `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_tensorPower` and
  `TauCeti.range_brauerActionSymp_le_centralizer`: equivariance under the tensor power of
  `TauCeti.stdSymplecticRep`, packaged as an inclusion into the commutant.
* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_permToBrauer_kroneckerPower`: the matrix of
  a permutation diagram commutes with the Kronecker power of any matrix.
* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`: the symplectic matrix of
  any Brauer diagram commutes with the Kronecker power of a matrix satisfying `Aᵀ * J * A = J`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Dipper, S. Doty, and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl
  duality*, Transactions of the American Mathematical Society 360 (2008), 189-213, §1.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

universe u

section CommRing

variable (R : Type u) [CommRing R] (n k : ℕ)

/-- **The symplectic Brauer action commutes with symplectic matrices.** Every element of `B_k(-2n)`
acts on `((Fin n ⊕ Fin n) → R)^{⊗k}` by an operator commuting with the diagonal action of each
matrix `A` preserving `Matrix.J (Fin n) R`. -/
theorem commute_brauerActionSymp_piTensorProductMap (x : BrauerAlgebra R (-(2 * n : R)) k)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hA : Aᵀ * Matrix.J (Fin n) R * A = Matrix.J (Fin n) R) :
    Commute (brauerActionSymp R n k x)
      (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  set T : Module.End R (⨂[R]^k ((Fin n ⊕ Fin n) → R)) :=
    PiTensorProduct.map fun _ : Fin k => A.mulVecLin
  have hle : (brauerActionSymp R n k).range ≤ Subalgebra.centralizer R {T} := by
    rw [range_brauerActionSymp_eq_adjoin_union]
    refine Algebra.adjoin_le ?_
    rintro _ (⟨σ, rfl⟩ | ⟨⟨⟨a, b⟩, hab⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff, Set.forall_mem_singleton,
        symplecticPermTensorAction_def]
      exact (PiTensorProduct.commute_signReindexRepresentation_map σ A.mulVecLin).symm.eq
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff, Set.forall_mem_singleton]
      exact (commute_symplecticCupCapAt_piTensorProductMap hA hab).symm.eq
  exact Commute.symm
    ((Subalgebra.mem_centralizer_iff R).mp (hle ⟨x, rfl⟩) T (Set.mem_singleton T))

/-- **The Brauer algebra acts by intertwiners of the symplectic group.** Every element of `B_k(-2n)`
acts on `((Fin n ⊕ Fin n) → R)^{⊗k}` by an operator commuting with the tensor power of the standard
symplectic representation `TauCeti.stdSymplecticRep`. -/
theorem commute_brauerActionSymp_tensorPower (x : BrauerAlgebra R (-(2 * n : R)) k)
    (g : Matrix.symplecticGroup (Fin n) R) :
    Commute (brauerActionSymp R n k x) ((stdSymplecticRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_brauerActionSymp_piTensorProductMap R n k x
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := R)).mp g.prop)

/-- **The image of `B_k(-2n)` lies in the commutant of the symplectic group** acting on
`((Fin n ⊕ Fin n) → R)^{⊗k}`. -/
theorem range_brauerActionSymp_le_centralizer :
    (brauerActionSymp R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdSymplecticRep R n).tensorPower k)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionSymp_tensorPower R n k x g).symm.eq

end CommRing

namespace BrauerDiagram

variable {k : ℕ} {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Transport operator-level commutation with `brauerActionSymp` on `Fin n` to matrix-level
commutation between `D.symplecticActionMatrix R ι` and `A.kroneckerPower (Fin k)` along an
equivalence `e : Fin n ≃ ι`. -/
private theorem commute_symplecticActionMatrix_kroneckerPower_of_brauerActionSymp
    {n : ℕ} (e : Fin n ≃ ι) (D : BrauerDiagram k) (A : Matrix (ι ⊕ ι) (ι ⊕ ι) R)
    (hop : Commute (brauerActionSymp R n k (BrauerAlgebra.of D))
      (PiTensorProduct.map fun _ : Fin k =>
        (Matrix.reindex (Equiv.sumCongr e.symm e.symm)
          (Equiv.sumCongr e.symm e.symm) A).mulVecLin)) :
    Commute (D.symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  let eSum : Fin n ⊕ Fin n ≃ ι ⊕ ι := Equiv.sumCongr e e
  let eFun : (Fin k → Fin n ⊕ Fin n) ≃ (Fin k → ι ⊕ ι) := Equiv.piCongrRight fun _ => eSum
  let A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
    Matrix.reindex (Equiv.sumCongr e.symm e.symm) (Equiv.sumCongr e.symm e.symm) A
  let B := Basis.piTensorProduct fun _ : Fin k => Pi.basisFun R (Fin n ⊕ Fin n)
  have hmat : Commute (D.symplecticActionMatrix R (Fin n)) (A₀.kroneckerPower (Fin k)) := by
    have hop' := hop.map (LinearMap.toMatrixAlgEquiv B)
    simp only [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
      toMatrix_brauerActionSymp_of, B] at hop'
    rwa [← piTensorPowerBasis_def, Matrix.toMatrix_piTensorProductMap_mulVecLin] at hop'
  have hA₀ : Matrix.reindex eSum eSum A₀ = A := by
    simp [A₀, eSum, ← Equiv.sumCongr_symm]
  simpa only [Matrix.coe_reindexAlgEquiv, eFun, eSum, reindex_symplecticActionMatrix R e,
    Matrix.reindex_kroneckerPower, hA₀] using
    hmat.map (Matrix.reindexAlgEquiv R R eFun)

/-- **The matrix of a permutation diagram commutes with every Kronecker power**, since reindexing
the factors of `∏ i, A (v i) (u i)` along `σ` leaves the product unchanged. -/
theorem commute_symplecticActionMatrix_permToBrauer_kroneckerPower
    (σ : Equiv.Perm (Fin k)) (A : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    Commute ((permToBrauer σ).symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  refine commute_symplecticActionMatrix_kroneckerPower_of_brauerActionSymp
    (Fintype.equivFin ι).symm (permToBrauer σ) A ?_
  rw [brauerActionSymp_of_permToBrauer, symplecticPermTensorAction_def]
  exact PiTensorProduct.commute_signReindexRepresentation_map σ _

/-- **The symplectic matrix of a Brauer diagram commutes with symplectic matrices.** For any matrix
`A` with `Aᵀ * Matrix.J ι R * A = Matrix.J ι R`, `TauCeti.BrauerDiagram.symplecticActionMatrix`
commutes with the Kronecker power `A.kroneckerPower (Fin k)`. -/
theorem commute_symplecticActionMatrix_kroneckerPower (D : BrauerDiagram k)
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (hA : Aᵀ * Matrix.J ι R * A = Matrix.J ι R) :
    Commute (D.symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine commute_symplecticActionMatrix_kroneckerPower_of_brauerActionSymp e D A ?_
  refine commute_brauerActionSymp_piTensorProductMap R (Fintype.card ι) k (BrauerAlgebra.of D) ?_
  have h := congrArg (Matrix.reindexAlgEquiv R R (Equiv.sumCongr e.symm e.symm)) hA
  simpa only [map_mul, Matrix.coe_reindexAlgEquiv, ← Matrix.transpose_reindex,
    Matrix.reindex_sumCongr_J] using h

end BrauerDiagram

end TauCeti
