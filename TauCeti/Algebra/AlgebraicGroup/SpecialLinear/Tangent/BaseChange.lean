/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Smooth

/-!
# Base change of the special-linear tangent Lie algebra

The coefficient-valued Lie algebra of `SLₙ` over `R` identifies with the Lie algebra
of `SLₙ` over an `R`-algebra `K`. Both are the trace-zero matrices over `K`.
`tangentCoefficientLieEquiv` implements this identification, and
`tangentBaseChangeLieEquiv_symm_derivationComp` proves that it agrees with the
canonical coordinate Hopf-algebra base-change isomorphism. Thus it can transport
root vectors using their matrix normalization without replacing geometric base change
by an unrelated abstract isomorphism. `cotangentDualBaseChangeEquiv` gives the
corresponding scalar-extension comparison of the cotangent dual. No flatness or
characteristic assumption is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21, Example 21.2.
* The construction uses `SpecialLinear.tangentLieEquivSl` and
  `TauCeti.tangentBaseChangeLieEquiv`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u v

noncomputable section

variable (R : Type u) (K : Type v) [CommRing R] [CommRing K] [Algebra R K]
variable (n : ℕ)

/-- Coefficient-valued tangent vectors to `SLₙ` identify with tangent vectors to
`SLₙ` over the coefficient ring, preserving their trace-zero matrices and Lie bracket. -/
def tangentCoefficientLieEquiv :
    Derivation R (coordinateHopfAlgebra R n)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) K) ≃ₗ⁅K⁆
      Derivation K (coordinateHopfAlgebra K n)
        (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K n) K) :=
  (tangentLieEquivSl (R := R) (B := K) n).trans
    (tangentLieEquivSl (R := K) (B := K) n).symm

/-- The tangent comparison leaves the trace-zero matrix unchanged. -/
@[simp]
theorem tangentMatrix_tangentCoefficientLieEquiv
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) K)) :
    tangentMatrix n (tangentCoefficientLieEquiv R K n d) = tangentMatrix n d := by
  rw [← tangentLieEquivSl_apply, tangentCoefficientLieEquiv, LieEquiv.trans_apply,
    LieEquiv.apply_symm_apply, tangentLieEquivSl_apply]

/-- The inverse tangent comparison also leaves the trace-zero matrix unchanged. -/
@[simp]
theorem tangentMatrix_tangentCoefficientLieEquiv_symm
    (d : Derivation K (coordinateHopfAlgebra K n)
      (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K n) K)) :
    tangentMatrix n ((tangentCoefficientLieEquiv R K n).symm d) = tangentMatrix n d := by
  exact (tangentMatrix_tangentCoefficientLieEquiv R K n
    ((tangentCoefficientLieEquiv R K n).symm d)).symm.trans
      (congrArg (tangentMatrix n) ((tangentCoefficientLieEquiv R K n).apply_symm_apply d))

/-- Scalar extension of the special-linear cotangent dual, transported along the
canonical coordinate-algebra base-change identification. -/
def cotangentDualBaseChangeEquiv :
    K ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R n)) ≃ₗ[K]
      Module.Dual K (Bialgebra.CotangentSpace K (coordinateHopfAlgebra K n)) :=
  (Derivation.tangentScalarExtensionEquiv
    (R := R) (A := coordinateHopfAlgebra R n) (B := K)).trans
      ((tangentCoefficientLieEquiv R K n).toLinearEquiv.trans
        (Derivation.cotangentLinearEquiv (R := K)
          (A := coordinateHopfAlgebra K n) (B := K)).symm)

/-- Cotangent duality turns the cotangent-dual base-change comparison into the coefficient
comparison of tangent derivations. -/
@[simp]
theorem cotangentLinearEquiv_cotangentDualBaseChangeEquiv
    (x : K ⊗[R]
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R n))) :
    Derivation.cotangentLinearEquiv (R := K)
        (A := coordinateHopfAlgebra K n) (B := K) (cotangentDualBaseChangeEquiv R K n x) =
      tangentCoefficientLieEquiv R K n
        (Derivation.tangentScalarExtensionEquiv
          (R := R) (A := coordinateHopfAlgebra R n) (B := K) x) := by
  simp only [cotangentDualBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LieEquiv.coe_toLinearEquiv]

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
  (n : ℕ)

/-- Restricting a tangent vector along the canonical coordinate base-change isomorphism
recovers the coefficient tangent comparison. This certifies its geometric meaning. -/
theorem tangentBaseChangeLieEquiv_symm_derivationComp
    (d : Derivation K (coordinateHopfAlgebra K n)
      (Bialgebra.CounitAlgebra K (coordinateHopfAlgebra K n) K)) :
    (tangentBaseChangeLieEquiv (R := R) (K := K)
      (H := coordinateHopfAlgebra R n)).symm
        (derivationComp (B := K) (coordinateHopfAlgebraBaseChangeIso R K n).hom.hom d) =
      (tangentCoefficientLieEquiv R K n).symm d := by
  apply (tangentLieEquivSl (R := R) (B := K) n).injective
  simp only [LieEquiv.coe_toLieHom]
  erw [tangentLieEquivSl_apply, tangentLieEquivSl_apply,
    tangentMatrix_tangentCoefficientLieEquiv_symm]
  apply Subtype.ext
  ext i j
  rw [tangentMatrix_apply, tangentMatrix_apply, tangentBaseChangeLieEquiv_symm_apply,
    AlgEquiv.apply_symm_apply, algEquivSelf_derivationComp_apply]
  -- The differential exposes the quotient-indexed coordinate algebra.
  erw [coordinateHopfAlgebraBaseChangeIso_hom_tmul_coordinateMap R K n,
    GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, v}]
  simp only [MvPolynomial.map_X, one_smul]

/-- The forward tangent comparison intertwines extension of derivations with the
canonical coordinate base-change isomorphism. -/
theorem derivationComp_tangentCoefficientLieEquiv
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) K)) :
    derivationComp (B := K) (coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
        (tangentCoefficientLieEquiv R K n d) =
      tangentBaseChangeLieEquiv (R := R) (K := K) (H := coordinateHopfAlgebra R n) d := by
  apply (tangentBaseChangeLieEquiv (R := R) (K := K)
    (H := coordinateHopfAlgebra R n)).symm.injective
  simp only [LieEquiv.coe_toLieHom]
  rw [tangentBaseChangeLieEquiv_symm_derivationComp, LieEquiv.symm_apply_apply,
    LieEquiv.symm_apply_apply]

end

end TauCeti.SpecialLinear
