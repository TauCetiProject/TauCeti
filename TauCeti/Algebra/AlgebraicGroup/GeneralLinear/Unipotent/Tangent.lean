/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.OneParameter
public import TauCeti.Algebra.AlgebraicGroup.Tangent.PolynomialCurve

/-!
# Logarithms of unipotent points lie in the Lie algebra

Let `H` be a closed subgroup of `GLₙ` over a rational domain `R`, cut out by a Hopf ideal of
the coordinate Hopf algebra. If `X` is a nilpotent matrix with `exp X ∈ H(R)`, then `X` lies in
the Lie algebra of `H`, viewed inside the matrix Lie algebra `𝔤𝔩ₙ(R)`. In particular, for a
unipotent point `g ∈ H(R)` the nilpotent matrix `log g` lies in `Lie H`.

The proof differentiates the polynomial one-parameter subgroup `t ↦ exp(tX)` at `t = 0`. That
curve lies in `H` scheme-theoretically by
`TauCeti.GeneralLinear.expSMulHom_ofAdd_X_mem_hopfIdealPointsSubgroup`, so its velocity lies in
the Lie algebra of `H`, and the velocity of `t ↦ exp(tX)` has matrix `X`. No smoothness,
connectedness or reducedness assumption on `H` is needed.

## Main declarations

* `TauCeti.GeneralLinear.tangentMatrix_curveVelocity_nilpotentOneParameterCoordinateMap`: the
  velocity of `t ↦ exp(tX)` at `t = 0` has matrix `X`.
* `TauCeti.GeneralLinear.mem_map_lieSubalgebra_of_nilpotentExpUnit_mem`: a nilpotent matrix
  whose exponential lies in a closed subgroup lies in its Lie algebra.
* `TauCeti.GeneralLinear.log_mem_map_lieSubalgebra`: the logarithm of a unipotent point of a
  closed subgroup lies in its Lie algebra.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §15.3.
* J. S. Milne, *Algebraic Groups* (2017), §14.c.
-/

public section

open WithConv
open scoped Polynomial

namespace TauCeti.GeneralLinear

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R] [Algebra ℚ R] (n : ℕ)
variable {X : Matrix (Fin n) (Fin n) R}

/-- The velocity at `t = 0` of the polynomial curve `t ↦ exp(tX)` has matrix `X`. -/
@[simp]
theorem tangentMatrix_curveVelocity_nilpotentOneParameterCoordinateMap (hX : IsNilpotent X) :
    tangentMatrix n (Bialgebra.curveVelocity (nilpotentOneParameterCoordinateMap n hX)
      (aeval_zero_comp_nilpotentOneParameterCoordinateMap n hX)) = X := by
  ext i j
  rw [tangentMatrix_apply, Bialgebra.algEquivSelf_curveVelocity_apply,
    nilpotentOneParameterCoordinateMap_apply_X, Matrix.coeff_one_exp_X_smul_C_mapMatrix hX]

variable [IsDomain R]

/-- **A nilpotent matrix whose exponential lies in a closed subgroup of `GLₙ` lies in its Lie
algebra.** The closed subgroup is cut out by the Hopf ideal `I`, and its Lie algebra is read
inside the matrix Lie algebra through `tangentLieEquivMatrix`. -/
theorem mem_map_lieSubalgebra_of_nilpotentExpUnit_mem
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (hX : IsNilpotent X)
    (hI : nilpotentExpUnit hX ∈ hopfIdealPointsSubgroup n I R) :
    X ∈ (I.lieSubalgebra (B := R)).map (tangentLieEquivMatrix (R := R) (B := R) n).toLieHom := by
  have hcurve := expSMulHom_ofAdd_X_mem_hopfIdealPointsSubgroup n I hX hI
  rw [mem_hopfIdealPointsSubgroup_iff, pointsMulEquiv_symm_apply,
    ← toConv_nilpotentOneParameterCoordinateMap n hX, ofConv_toConv] at hcurve
  refine (LieSubalgebra.mem_map _ _ _).mpr ⟨_, Bialgebra.curveVelocity_mem_lieSubalgebra _
    (aeval_zero_comp_nilpotentOneParameterCoordinateMap n hX) I hcurve, ?_⟩
  rw [LieEquiv.coe_toLieHom, tangentLieEquivMatrix_apply,
    tangentMatrix_curveVelocity_nilpotentOneParameterCoordinateMap]

/-- **The logarithm of a unipotent point of a closed subgroup of `GLₙ` lies in its Lie
algebra.** Here `g - 1` is nilpotent, so `log g` is the finite logarithm series; the closed
subgroup is cut out by the Hopf ideal `I`. -/
theorem log_mem_map_lieSubalgebra
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (hg : IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1))
    (hI : g ∈ hopfIdealPointsSubgroup n I R) :
    IsNilpotent.log (g : Matrix (Fin n) (Fin n) R) ∈
      (I.lieSubalgebra (B := R)).map (tangentLieEquivMatrix (R := R) (B := R) n).toLieHom :=
  mem_map_lieSubalgebra_of_nilpotentExpUnit_mem n I (IsNilpotent.isNilpotent_log hg)
    (by rwa [Units.nilpotentExpUnit_log g hg])

end TauCeti.GeneralLinear
