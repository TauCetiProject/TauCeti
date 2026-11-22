/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Gauge
public import TauCeti.RingTheory.Derivation.Matrix

/-!
# The gauge action of the general linear group on connection matrices

For `G = GLₙ` the tangent space at the identity is the matrix algebra
(`TauCeti.GeneralLinear.tangentMatrix`). This file computes the logarithmic derivative and the
gauge action of points of `GLₙ` (`Derivation.pointRightLogDeriv`, `Derivation.pointGauge`) in
these terms: along a derivation `D` of `B`, the logarithmic derivative of `g ∈ GLₙ(B)` is the
matrix `(Dg) g⁻¹`, and the gauge action on tangent matrices is the classical
`g M g⁻¹ - (Dg) g⁻¹` of `Derivation.matrixGauge`. So the gauge action defined intrinsically
from the Hopf algebra recovers the gauge action on connection matrices.

## Main results

* `TauCeti.GeneralLinear.tangentMatrix_pointRightLogDeriv`: `dlog g = (Dg) g⁻¹`.
* `TauCeti.GeneralLinear.tangentMatrix_pointGauge`: the gauge action of `GLₙ` is
  `g M g⁻¹ - (Dg) g⁻¹`.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (n : ℕ) (D : Derivation R B B)

/-- **The logarithmic derivative of a point of `GLₙ` is the matrix `(Dg) g⁻¹`.** -/
@[simp]
theorem tangentMatrix_pointRightLogDeriv
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] B)) :
    tangentMatrix n (D.pointRightLogDeriv g) = D.matrixRightLogDeriv (pointsMulEquiv n g) := by
  ext i j
  have hconv (f h : WithConv (coordinateHopfAlgebra R n →ₗ[R] B)) :
      (f * h).ofConv (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
        ∑ k : Fin n,
          f.ofConv (coordinateHopfAlgebraAlgEquiv R n
              (coordinateRingMap R n (MvPolynomial.X (i, k)))) *
            h.ofConv (coordinateHopfAlgebraAlgEquiv R n
              (coordinateRingMap R n (MvPolynomial.X (k, j)))) := by
    simp
  rw [tangentMatrix_apply, Derivation.algEquivSelf_pointRightLogDeriv_apply, hconv,
    Derivation.matrixRightLogDeriv_def, Matrix.mul_apply, ← map_inv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Derivation.coeFn_coe, Matrix.map_apply, pointsMulEquiv_apply, pointToGeneralLinear_apply]

/-- **The gauge action of `GLₙ` on tangent matrices is `g M g⁻¹ - (Dg) g⁻¹`.** -/
@[simp]
theorem tangentMatrix_pointGauge (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] B))
    (A : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    tangentMatrix n (D.pointGauge g A) =
      D.matrixGauge (pointsMulEquiv n g) (tangentMatrix n A) := by
  rw [Derivation.pointGauge_def, map_sub, tangentMatrix_adDerivation,
    tangentMatrix_pointRightLogDeriv, Derivation.matrixGauge_eq_conj_sub_matrixRightLogDeriv,
    counitPointsMulEquiv_eq_pointsMulEquiv,
    ← Bialgebra.CounitAlgebra.pointsMulEquiv_eq_mapValue, MulEquiv.apply_symm_apply]

end TauCeti.GeneralLinear
