/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Tangent

/-!
# Recognizing exponential curves after a representation

This module proves `TauCeti.GeneralLinear.tangentMatrix_derivationComp_eq_log`: the
differential of a represented intrinsic exponential direction is the finite logarithm of
the represented point whenever that point is unipotent. The underlying polynomial subgroup
is identified by `TauCeti.GeneralLinear.eq_nilpotentOneParameterCoordinateMap_log`, and its
velocity is described by `TauCeti.GeneralLinear.tangentMatrix_curveVelocity_eq_log`.
The target invariant vector field need not be assumed locally nilpotent.
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
  have hzero : (aeval (0 : R)).comp ((Bialgebra.expPointPolynomial d hd).comp f.toAlgHom) =
      _root_.Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n) := by
    rw [← AlgHom.comp_assoc, Bialgebra.aeval_zero_comp_expPointPolynomial]
    exact f.counitAlgHom_comp
  rw [← Bialgebra.curveVelocity_expPointPolynomial_comp d hd f (hzero := hzero)]
  apply tangentMatrix_curveVelocity_eq_log n _ ?_ hzero g hg ?_
  · intro s t
    simpa only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_assoc, map_mul] using
      congrArg (BialgHom.mapDomain f)
        (Bialgebra.aeval_comp_expPointPolynomial_add d hd s t)
  · simpa only [BialgHom.mapDomain_apply, ofConv_toConv, ← AlgHom.comp_assoc,
      Bialgebra.aeval_one_comp_expPointPolynomial] using h

end TauCeti.GeneralLinear
