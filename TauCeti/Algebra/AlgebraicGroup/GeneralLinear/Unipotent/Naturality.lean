/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Uniqueness
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Tangent

/-!
# Recognizing exponential curves after a representation

A polynomial one-parameter subgroup with unipotent value `g` at parameter one is necessarily
`t ↦ exp(t log g)`. This is equality of regular coordinate maps, hence holds on points over
every value algebra. Its velocity is therefore the finite logarithm of `g`.

In particular, after composing an intrinsic exponential curve with any affine-group
representation, its velocity is the logarithm of the represented point whenever that point
is unipotent. The target invariant vector field need not be assumed locally nilpotent.
This comparison is useful for identifying logarithms computed in different faithful matrix
realizations. It does not assert that every tangent vector of an arbitrary affine group
has a polynomial exponential, or that its every point is unipotent.

The argument combines uniqueness of polynomial one-parameter subgroups with the finite
matrix exp/log inverse identities and the coefficient formula for curve velocity.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
* J. S. Milne, *Algebraic Groups* (2017), §14.c.
-/

public section

open Polynomial WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [Algebra ℚ R] (n : ℕ)

/-- A polynomial one-parameter subgroup of `GLₙ` through a unipotent matrix `g` is the
finite exponential curve of `log g`. The conclusion identifies regular maps, not only points. -/
theorem eq_nilpotentOneParameterCoordinateMap_log
    (γ : coordinateHopfAlgebra R n →ₐ[R] R[X])
    (hγ : ∀ s t : R, toConv ((aeval (s + t)).comp γ) =
      toConv ((aeval s).comp γ) * toConv ((aeval t).comp γ))
    (g : Matrix.GeneralLinearGroup (Fin n) R)
    (hg : IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1))
    (h : toConv ((aeval (1 : R)).comp γ) = generalLinearToPoint n g) :
    γ = nilpotentOneParameterCoordinateMap n (IsNilpotent.isNilpotent_log hg) := by
  have : CharZero R := Algebra.charZero_of_charZero ℚ R
  apply γ.eq_of_aeval_one_comp_eq _ hγ
    (aeval_comp_nilpotentOneParameterCoordinateMap_add n _)
  apply toConv_injective
  rw [h, aeval_comp_nilpotentOneParameterCoordinateMap, toConv_ofConv]
  congr 1
  ext i j
  simp [IsNilpotent.exp_log hg]

/-- The velocity of a polynomial one-parameter subgroup of `GLₙ` is the logarithm of its
unipotent value at parameter one. -/
theorem tangentMatrix_curveVelocity_eq_log
    (γ : coordinateHopfAlgebra R n →ₐ[R] R[X])
    (hγ : ∀ s t : R, toConv ((aeval (s + t)).comp γ) =
      toConv ((aeval s).comp γ) * toConv ((aeval t).comp γ))
    (hzero : (aeval (0 : R)).comp γ = Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n))
    (g : Matrix.GeneralLinearGroup (Fin n) R)
    (hg : IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1))
    (h : toConv ((aeval (1 : R)).comp γ) = generalLinearToPoint n g) :
    tangentMatrix n (Bialgebra.curveVelocity γ hzero) =
      IsNilpotent.log (g : Matrix (Fin n) (Fin n) R) := by
  have heq := eq_nilpotentOneParameterCoordinateMap_log n γ hγ g hg h
  subst γ
  exact tangentMatrix_curveVelocity_nilpotentOneParameterCoordinateMap n _

variable {H : Type v} [CommRing H] [_root_.Bialgebra R H] [Algebra ℚ H]

/-- In any representation, the differential of an intrinsic exponential direction is the
finite logarithm of the represented exponential point, when that matrix is unipotent.
No nilpotence hypothesis on the target differential is required. -/
theorem tangentMatrix_derivationComp_eq_log
    (f : coordinateHopfAlgebra R n →ₐc[R] H)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (hd : ∀ x, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] x = 0)
    (g : Matrix.GeneralLinearGroup (Fin n) R)
    (hg : IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1))
    (h : BialgHom.mapDomain f (toConv (Bialgebra.expPoint d hd)) =
      generalLinearToPoint n g) :
    tangentMatrix n (derivationComp f d) = IsNilpotent.log (g : Matrix (Fin n) (Fin n) R) := by
  have hcurve : (Bialgebra.expPointPolynomial d hd).comp f.toAlgHom =
      nilpotentOneParameterCoordinateMap n (IsNilpotent.isNilpotent_log hg) := by
    apply eq_nilpotentOneParameterCoordinateMap_log n _ ?_ g hg ?_
    · intro s t
      simpa only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_assoc, map_mul] using
        congrArg (BialgHom.mapDomain f)
          (Bialgebra.aeval_comp_expPointPolynomial_add d hd s t)
    · simpa only [BialgHom.mapDomain_apply, ofConv_toConv, ← AlgHom.comp_assoc,
        Bialgebra.aeval_one_comp_expPointPolynomial] using h
  ext i j
  rw [tangentMatrix_apply, algEquivSelf_derivationComp_apply]
  have hc := congrArg (fun p : coordinateHopfAlgebra R n →ₐ[R] R[X] ↦
    (p (genericMatrix R n i j)).coeff 1) hcurve
  simpa only [AlgHom.comp_apply, Bialgebra.coeff_one_expPointPolynomial,
    genericMatrix_apply, nilpotentOneParameterCoordinateMap_apply_X,
    Matrix.coeff_one_exp_X_smul_C_mapMatrix (IsNilpotent.isNilpotent_log hg)] using hc

end TauCeti.GeneralLinear
