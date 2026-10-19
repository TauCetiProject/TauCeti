/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Tangent.Basic

/-!
# Coordinates and a basis for the projective tangent Lie algebra

The tangent Lie algebra of `PGL_{r+1}` has a basis indexed by all matrix units except
`E_{rr}`. Its elements act on the matrix algebra by commutators with those matrix units.
The coordinates of a commutator with `X` are the entries of `X - X_{rr} I`, omitting
the zero last diagonal entry. Thus the tangent module is free over any commutative
coefficient algebra. More generally, the tangent module of `PGL_n` is finite and free
for every `n`. Over a nontrivial coefficient ring its rank is `n² - 1`, including
in characteristics dividing `n`.

These coordinates separate the off-diagonal directions from the diagonal directions
without choosing trace-zero representatives. They provide a matrix model for computing
the adjoint root spaces of the projective diagonal torus.

The construction combines `ProjectiveGeneralLinear.tangentLieEquivInnerDerivations`
with `Matrix.adRangeEquivPi`, the normalized coordinates for inner derivations.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.
* N. Jacobson, *Basic Algebra II*, derivations of matrix algebras.
-/

public section

namespace TauCeti.ProjectiveGeneralLinear

open Matrix

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable (r : ℕ) {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

/-- Coordinates on the tangent Lie algebra of `PGL_{r+1}`, obtained by setting the last
diagonal entry of an inner-derivation representative to zero. -/
def tangentEquivPi :
    Derivation R (coordinateHopfAlgebra (r + 1) R)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra (r + 1) R) B) ≃ₗ[B]
      ({ij : Fin (r + 1) × Fin (r + 1) // ij ≠ (Fin.last r, Fin.last r)} → B) :=
  (tangentLieEquivInnerDerivations (R := R) (B := B) (r + 1)).toLinearEquiv.trans
    (Matrix.adRangeEquivPi B (Fin (r + 1)) (Fin.last r))

/-- A matrix representing a projective tangent vector determines its normalized
coordinates by subtracting its last diagonal entry. -/
theorem tangentEquivPi_apply_of_tangentEnd_eq
    (d : Derivation R (coordinateHopfAlgebra (r + 1) R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra (r + 1) R) B))
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) B)
    (hX : tangentEnd (r + 1) d = LieAlgebra.ad B _ X)
    (ij : {ij : Fin (r + 1) × Fin (r + 1) // ij ≠ (Fin.last r, Fin.last r)}) :
    tangentEquivPi r d ij =
      X ij.1.1 ij.1.2 - if ij.1.1 = ij.1.2 then X (Fin.last r) (Fin.last r) else 0 := by
  have h : tangentLieEquivInnerDerivations (r + 1) d =
      (LieAlgebra.ad B (Matrix (Fin (r + 1)) (Fin (r + 1)) B)).rangeRestrict X := by
    apply Subtype.ext
    rw [tangentLieEquivInnerDerivations_apply (R := R) (B := B) (r + 1)]
    exact hX
  simp only [tangentEquivPi, LinearEquiv.trans_apply, LieEquiv.coe_toLinearEquiv, h,
    LieHom.rangeRestrict_apply, Matrix.adRangeEquivPi_apply_ad]

/-- The tangent action reconstructed from its normalized coordinates is the commutator
with the matrix obtained by filling the omitted last diagonal entry with zero. -/
@[simp]
theorem tangentEnd_tangentEquivPi_symm
    (c : {ij : Fin (r + 1) × Fin (r + 1) // ij ≠ (Fin.last r, Fin.last r)} → B)
    (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) B) :
    tangentEnd (r + 1) ((tangentEquivPi (R := R) r).symm c) Y =
      (of fun i j => if h : (i, j) = (Fin.last r, Fin.last r) then 0 else c ⟨(i, j), h⟩) * Y -
        Y * (of fun i j =>
          if h : (i, j) = (Fin.last r, Fin.last r) then 0 else c ⟨(i, j), h⟩) := by
  rw [← tangentLieEquivInnerDerivations_apply (R := R) (B := B) (r + 1)]
  simp only [tangentEquivPi, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    ← LieEquiv.coe_toLinearEquiv, LinearEquiv.apply_symm_apply,
    Matrix.adRangeEquivPi_symm_apply]

/-- The matrix-unit basis of the projective tangent Lie algebra, omitting `E_{rr}`. -/
def tangentBasis :
    Module.Basis {ij : Fin (r + 1) × Fin (r + 1) // ij ≠ (Fin.last r, Fin.last r)} B
      (Derivation R (coordinateHopfAlgebra (r + 1) R)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra (r + 1) R) B)) :=
  Module.Basis.ofEquivFun (tangentEquivPi r)

/-- The coefficients in the tangent basis are the normalized matrix coordinates. -/
@[simp]
theorem tangentBasis_repr_apply
    (d : Derivation R (coordinateHopfAlgebra (r + 1) R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra (r + 1) R) B))
    (ij : {ij : Fin (r + 1) × Fin (r + 1) // ij ≠ (Fin.last r, Fin.last r)}) :
    (tangentBasis r).repr d ij = tangentEquivPi r d ij :=
  Module.Basis.ofEquivFun_repr_apply _ _ _

/-- The tangent basis vector indexed by `(i,j)` acts by commutation with `Eᵢⱼ`. -/
@[simp]
theorem tangentEnd_tangentBasis
    (ij : {ij : Fin (r + 1) × Fin (r + 1) // ij ≠ (Fin.last r, Fin.last r)}) :
    tangentEnd (r + 1) (tangentBasis (R := R) (B := B) r ij) =
      LieAlgebra.ad B (Matrix (Fin (r + 1)) (Fin (r + 1)) B)
        (single ij.1.1 ij.1.2 1) := by
  rw [← tangentLieEquivInnerDerivations_apply (R := R) (B := B) (r + 1)]
  simp only [tangentBasis, Module.Basis.coe_ofEquivFun, tangentEquivPi,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, ← LieEquiv.coe_toLinearEquiv,
    LinearEquiv.apply_symm_apply, Matrix.adRangeEquivPi_symm_single,
    LieHom.rangeRestrict_apply]

variable (n : ℕ)

/-- The projective tangent module is free over every commutative coefficient algebra. -/
instance moduleFree_tangent :
    Module.Free B (Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B)) :=
  Module.Free.of_equiv (tangentLieEquivInnerDerivations (R := R) (B := B) n).toLinearEquiv.symm

/-- The projective tangent module is finite over every commutative coefficient algebra. -/
instance moduleFinite_tangent :
    Module.Finite B (Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B)) :=
  Module.Finite.equiv (tangentLieEquivInnerDerivations (R := R) (B := B) n).toLinearEquiv.symm

/-- The projective tangent module has rank `n² - 1`. In particular, this dimension
formula does not require the matrix size to be invertible in the coefficient ring. -/
@[simp]
theorem finrank_tangent [Nontrivial B] :
    Module.finrank B (Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B)) = n ^ 2 - 1 := by
  rw [(tangentLieEquivInnerDerivations (R := R) (B := B) n).toLinearEquiv.finrank_eq,
    Matrix.finrank_adRange, Fintype.card_fin]

end

end TauCeti.ProjectiveGeneralLinear
