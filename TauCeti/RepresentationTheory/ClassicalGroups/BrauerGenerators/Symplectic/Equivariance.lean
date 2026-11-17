/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TwoStrands

/-!
# The symplectic Brauer algebra acts by intertwiners of the symplectic group

The action `TauCeti.brauerActionSymp` of the Brauer algebra `B_k(-2n)` on the tensor power
`⨂[R]^k ((Fin n ⊕ Fin n) → R)` commutes with the diagonal action `A ↦ A^{⊗k}` of every matrix `A`
preserving the standard alternating form, that is, with `Aᵀ * J * A = J`. Equivalently, the image
of the Brauer algebra lies in the commutant of the symplectic group acting on the tensor power
(`TauCeti.range_brauerActionSymp_le_centralizer`).

The equivariance proof works one diagram at a time in the monomial basis, without appealing to
generators of the Brauer algebra. For a matrix `A` with `Aᵀ * J * A = J`, one also has
`A * J * Aᵀ = J`, so `A.kroneckerPower (Fin k)` leaves the symplectic boundary matrix
`TauCeti.BrauerDiagram.symplecticBoundaryMatrix` invariant under congruence
(`TauCeti.BrauerDiagram.kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose`). Since the
action matrix is the boundary matrix right-multiplied by `(Matrix.J ι R).kroneckerPower (Fin k)`
and `Kᵀ * K_J * K = K_J`, the action matrix commutes with `K = A.kroneckerPower (Fin k)`
(`TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`).

On two strands, combining `TauCeti.range_brauerActionSymp_two_eq_adjoin` with the two-strand
commutant characterization of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/TwoStrands.lean` shows
that the image of `B₂(-2n)` equals the full commutant of `Sp_{2n}` on `V ⊗ V` over any integral
domain containing a unit `t` with `t ^ m ≠ 1` for `0 < m ≤ 4`
(`TauCeti.range_brauerActionSymp_two_eq_centralizer`), and in particular over any field of
characteristic zero (`TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`).

## Main results

* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`: the symplectic action
  matrix of a Brauer diagram commutes with the Kronecker power of every matrix with
  `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_piTensorProductMap`: every element of `B_k(-2n)` acts by an
  operator commuting with `A^{⊗k}` when `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_tensorPower` and
  `TauCeti.range_brauerActionSymp_le_centralizer`: the image of `B_k(-2n)` lies in the commutant
  of the symplectic group acting diagonally on the `k`-th tensor power.
* `TauCeti.range_brauerActionSymp_two_eq_centralizer` and
  `TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`: on two strands, the image of
  `B₂(-2n)` equals the full commutant of the symplectic group.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

universe u

namespace BrauerDiagram

variable {k : ℕ} {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The symplectic action matrix of a Brauer diagram commutes with symplectic matrices.** For any
matrix `A` with `Aᵀ * J * A = J`, the action matrix `TauCeti.BrauerDiagram.symplecticActionMatrix`
of `D` commutes with `A.kroneckerPower (Fin k)`. -/
theorem commute_symplecticActionMatrix_kroneckerPower (D : BrauerDiagram k)
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (hA : Aᵀ * Matrix.J ι R * A = Matrix.J ι R) :
    Commute (D.symplecticActionMatrix R ι) (A.kroneckerPower (Fin k)) := by
  have hA' : A * Matrix.J ι R * Aᵀ = Matrix.J ι R :=
    SymplecticGroup.mem_iff.mp (SymplecticGroup.mem_iff'.mpr hA)
  set K := A.kroneckerPower (Fin k)
  set K_J := (Matrix.J ι R).kroneckerPower (Fin k)
  set B := D.symplecticBoundaryMatrix R ι
  have hB : K * B * Kᵀ = B :=
    D.kroneckerPower_mul_symplecticBoundaryMatrix_mul_transpose R ι hA'
  have hKJ : Kᵀ * K_J * K = K_J := by
    simp only [K, K_J, Matrix.transpose_kroneckerPower, ← Matrix.kroneckerPower_mul, hA]
  change D.symplecticActionMatrix R ι * K = K * D.symplecticActionMatrix R ι
  calc
    D.symplecticActionMatrix R ι * K = B * K_J * K := by rw [symplecticActionMatrix_def]
    _ = K * B * Kᵀ * K_J * K := by rw [hB]
    _ = K * B * (Kᵀ * K_J * K) := by simp only [Matrix.mul_assoc]
    _ = K * B * K_J := by rw [hKJ]
    _ = K * D.symplecticActionMatrix R ι := by rw [symplecticActionMatrix_def, Matrix.mul_assoc]

end BrauerDiagram

section CommRing

variable (R : Type u) [CommRing R] (n k : ℕ)

/-- **The symplectic Brauer algebra commutes with symplectic matrices.** Every element of
`B_k(-2n)` acts on `⨂[R]^k ((Fin n ⊕ Fin n) → R)` by an operator commuting with the diagonal action
of each matrix `A` satisfying `Aᵀ * J * A = J`. -/
theorem commute_brauerActionSymp_piTensorProductMap (x : BrauerAlgebra R (-(2 * n : R)) k)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hA : Aᵀ * Matrix.J (Fin n) R * A = Matrix.J (Fin n) R) :
    Commute (brauerActionSymp R n k x) (PiTensorProduct.map fun _ : Fin k => A.mulVecLin) := by
  let b := Basis.piTensorProduct fun _ : Fin k => Pi.basisFun R (Fin n ⊕ Fin n)
  set T := PiTensorProduct.map fun _ : Fin k => A.mulVecLin
  have hT : T = Matrix.toLin b b (A.kroneckerPower (Fin k)) := by
    rw [← A.toMatrix_piTensorProductMap_mulVecLin (κ := Fin k), Matrix.toLin_toMatrix]
  have hlin : (LinearMap.mulRight R T).comp (brauerActionSymp R n k).toLinearMap =
      (LinearMap.mulLeft R T).comp (brauerActionSymp R n k).toLinearMap :=
    (BrauerAlgebra.basis R (-(2 * n : R)) k).ext fun D => by
      simp only [LinearMap.comp_apply, BrauerAlgebra.basis_apply, AlgHom.toLinearMap_apply,
        LinearMap.mulRight_apply, LinearMap.mulLeft_apply, brauerActionSymp_of, hT]
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
        (D.commute_symplecticActionMatrix_kroneckerPower hA).eq]
  exact LinearMap.congr_fun hlin x

/-- **The symplectic Brauer algebra acts by intertwiners of the symplectic group.** Every element
of `B_k(-2n)` acts on `⨂[R]^k ((Fin n ⊕ Fin n) → R)` by an operator commuting with the tensor power
of the standard symplectic representation. -/
theorem commute_brauerActionSymp_tensorPower (x : BrauerAlgebra R (-(2 * n : R)) k)
    (g : Matrix.symplecticGroup (Fin n) R) :
    Commute (brauerActionSymp R n k x) ((stdSymplecticRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_brauerActionSymp_piTensorProductMap R n k x (SymplecticGroup.mem_iff'.mp g.prop)

/-- **The image of the symplectic Brauer algebra lies in the commutant of the symplectic group**
acting diagonally on `⨂[R]^k ((Fin n ⊕ Fin n) → R)`. -/
theorem range_brauerActionSymp_le_centralizer :
    (brauerActionSymp R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdSymplecticRep R n).tensorPower k)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionSymp_tensorPower R n k x g).symm.eq

end CommRing

section TwoStrands

/-- **Brauer duality for the symplectic group on two strands.** Over an integral domain containing
a unit `t` with `t ^ m ≠ 1` for `0 < m ≤ 4`, the image of `brauerActionSymp K n 2` equals the full
commutant of the symplectic group on `⨂[K]^2 ((Fin n ⊕ Fin n) → K)`. -/
theorem range_brauerActionSymp_two_eq_centralizer {K : Type u} [CommRing K] [IsDomain K] {n : ℕ}
    (ht : ∃ t : Kˣ, ∀ m : ℕ, 0 < m → m ≤ 4 → t ^ m ≠ 1) :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) := by
  rw [range_brauerActionSymp_two_eq_adjoin,
    adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer ht]

/-- **Brauer duality for the symplectic group on two strands in characteristic zero**, for instance
over `ℂ`: the image of `brauerActionSymp K n 2` equals the full commutant of the symplectic group
on `⨂[K]^2 ((Fin n ⊕ Fin n) → K)`. -/
theorem range_brauerActionSymp_two_eq_centralizer_of_charZero {K : Type u} [Field K] [CharZero K]
    {n : ℕ} :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) := by
  rw [range_brauerActionSymp_two_eq_adjoin,
    adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer_of_charZero]

end TwoStrands

end TauCeti
