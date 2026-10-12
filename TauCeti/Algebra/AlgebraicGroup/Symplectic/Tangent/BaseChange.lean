/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Tangent.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Smooth

/-!
# Base change of the symplectic tangent Lie algebra

Coefficient-valued tangent vectors to `Sp₂ₘ` over `R` identify with tangent vectors
of `Sp₂ₘ` over the coefficient ring `K`: both are symplectic matrices over `K`.
`tangentCoefficientLieEquiv` preserves those matrices and the Lie bracket. Its
compatibility with the canonical coordinate-algebra base-change isomorphism
certifies that this is the geometric comparison, not just an abstract isomorphism.
`cotangentDualBaseChangeEquiv` gives the resulting scalar extension of the
cotangent dual, used to compare normalized root vectors and pinnings.

All comparisons include characteristic two, nonflat base changes and rank zero.

## References

* `SpecialLinear.Tangent.BaseChange`: the corresponding tangent comparison for
  special-linear groups.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 24.6.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Symplectic

universe u v

noncomputable section

variable (R : Type u) (K : Type v) [CommRing R] [CommRing K] [Algebra R K]
variable (m : ℕ)

/-- Coefficient-valued symplectic tangent vectors identify with tangent vectors over
that coefficient ring, preserving their matrices and Lie bracket. -/
def tangentCoefficientLieEquiv :
    Derivation R (coordinateHopfAlgebra R m)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) K) ≃ₗ⁅K⁆
      Derivation K (coordinateHopfAlgebra K m)
        (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K m) K) :=
  (tangentLieEquivSp (R := R) (B := K) m).trans
    (tangentLieEquivSp (R := K) (B := K) m).symm

/-- The coefficient comparison leaves the symplectic tangent matrix unchanged. -/
@[simp↓]
theorem tangentMatrix_tangentCoefficientLieEquiv
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) K)) :
    tangentMatrix m (tangentCoefficientLieEquiv R K m d) = tangentMatrix m d := by
  -- `rw` aligns the quotient-indexed tangent modules, which `simp` does not match.
  rw [← tangentLieEquivSp_apply, tangentCoefficientLieEquiv, LieEquiv.trans_apply,
    LieEquiv.apply_symm_apply, tangentLieEquivSp_apply]

/-- The inverse coefficient comparison leaves the symplectic tangent matrix unchanged. -/
@[simp↓]
theorem tangentMatrix_tangentCoefficientLieEquiv_symm
    (d : Derivation K (coordinateHopfAlgebra K m)
      (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K m) K)) :
    tangentMatrix m ((tangentCoefficientLieEquiv R K m).symm d) = tangentMatrix m d := by
  exact (tangentMatrix_tangentCoefficientLieEquiv R K m
    ((tangentCoefficientLieEquiv R K m).symm d)).symm.trans
      (congrArg (tangentMatrix m) ((tangentCoefficientLieEquiv R K m).apply_symm_apply d))

/-- Scalar extension of the symplectic cotangent dual under the canonical
coordinate-algebra base-change identification. -/
def cotangentDualBaseChangeEquiv :
    K ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R m)) ≃ₗ[K]
      Module.Dual K (Bialgebra.CotangentSpace K (coordinateHopfAlgebra K m)) :=
  (Derivation.tangentScalarExtensionEquiv
    (R := R) (A := coordinateHopfAlgebra R m) (B := K)).trans
      ((tangentCoefficientLieEquiv R K m).toLinearEquiv.trans
        (Derivation.cotangentLinearEquiv (R := K)
          (A := coordinateHopfAlgebra K m) (B := K)).symm)

/-- Cotangent duality identifies the cotangent-dual comparison with the
coefficient comparison of tangent derivations. -/
@[simp↓]
theorem cotangentLinearEquiv_cotangentDualBaseChangeEquiv
    (x : K ⊗[R]
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R m))) :
    Derivation.cotangentLinearEquiv (R := K)
        (A := coordinateHopfAlgebra K m) (B := K) (cotangentDualBaseChangeEquiv R K m x) =
      tangentCoefficientLieEquiv R K m
        (Derivation.tangentScalarExtensionEquiv
          (R := R) (A := coordinateHopfAlgebra R m) (B := K) x) := by
  simp only [cotangentDualBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LieEquiv.coe_toLinearEquiv]

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
  (m : ℕ)

/-- Restriction along the coordinate base-change isomorphism recovers the inverse
coefficient comparison. This certifies its geometric meaning. -/
theorem tangentBaseChangeLieEquiv_symm_derivationComp
    (d : Derivation K (coordinateHopfAlgebra K m)
      (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K m) K)) :
    (tangentBaseChangeLieEquiv (R := R) (K := K)
      (H := coordinateHopfAlgebra R m)).symm
        (derivationComp (B := K) (coordinateHopfAlgebraBaseChangeIso R K m).hom.hom d) =
      (tangentCoefficientLieEquiv R K m).symm d := by
  apply (tangentLieEquivSp (R := R) (B := K) m).injective
  simp only [LieEquiv.coe_toLieHom]
  erw [tangentLieEquivSp_apply, tangentLieEquivSp_apply,
    tangentMatrix_tangentCoefficientLieEquiv_symm]
  apply Subtype.ext
  ext i j
  -- These computation rules need `rw` to align quotient-indexed scalar structures;
  -- `simp` does not match even the tangent-matrix rule on this presentation.
  rw [tangentMatrix_apply_coe, tangentMatrix_apply_coe, Matrix.submatrix_apply,
    Matrix.submatrix_apply, GeneralLinear.tangentMatrix_apply,
    GeneralLinear.tangentMatrix_apply, HopfIdeal.quotientLieHom_apply,
    HopfIdeal.quotientLieHom_apply, algEquivSelf_derivationComp_apply,
    tangentBaseChangeLieEquiv_symm_apply, AlgEquiv.apply_symm_apply,
    algEquivSelf_derivationComp_apply]
  -- Identify both quotient maps with the constant-form coordinate maps for `JFin`.
  simp only [← CommHopfAlgCat.hom_mkQuotient, ← ConstantForm.coordinateMap_def]
  -- Elaborated rewriting aligns the quotient-indexed scalar structures.
  erw [coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap R K m,
    GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, v}]
  simp only [MvPolynomial.map_X, one_smul, algEquivSelf_derivationComp_apply,
    BialgHom.coe_toAlgHom]

/-- The forward comparison intertwines extension of derivations with the
canonical coordinate base-change isomorphism. -/
theorem derivationComp_tangentCoefficientLieEquiv
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) K)) :
    derivationComp (B := K) (coordinateHopfAlgebraBaseChangeIso R K m).hom.hom
        (tangentCoefficientLieEquiv R K m d) =
      tangentBaseChangeLieEquiv (R := R) (K := K) (H := coordinateHopfAlgebra R m) d := by
  apply (tangentBaseChangeLieEquiv (R := R) (K := K)
    (H := coordinateHopfAlgebra R m)).symm.injective
  simp only [LieEquiv.coe_toLieHom]
  rw [tangentBaseChangeLieEquiv_symm_derivationComp, LieEquiv.symm_apply_apply,
    LieEquiv.symm_apply_apply]

end

end TauCeti.Symplectic
