/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Congruence
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.IsotropicFlag.Antidiagonal.Congr

/-!
# The symplectic group of the antidiagonal form

Flag varieties, Schubert cells and many representation-theoretic sources write `Sp₂ₘ` as the group
preserving the antidiagonal alternating form `Q = TauCeti.JAntidiag m R`. The carrier of `Sp₂ₘ`
in Tau Ceti is instead the constant-form subgroup scheme of `TauCeti.JFin m R`. The explicit signed
permutation `P = TauCeti.antidiagCongr m R` satisfies `P Q Pᵀ = JFin m R`
(`TauCeti.antidiagCongr_mul_JAntidiag_mul_transpose`), so conjugation by `P` identifies the
subgroup scheme preserving `Q` with `Sp₂ₘ` (`TauCeti.ConstantForm.groupSchemeCongr`). This file
records the consequences:

* the subgroup scheme preserving `Q` is smooth
  (`TauCeti.Symplectic.instSmoothCoordinateHopfAlgebraJAntidiag`);
* it carries the standard pinning of `Sp₂ₘ` transported along `P`
  (`TauCeti.Symplectic.antidiagPinning`), whose torus and Borel subgroup are the pullbacks of the
  diagonal torus and of the isotropic-flag Borel subgroup of `Sp₂ₘ`
  (`TauCeti.Symplectic.constantFormPinning_torus`, `TauCeti.Symplectic.constantFormPinning_borel`,
  which apply to it directly since it is an abbreviation).

On points, the identification sends a matrix `M` preserving `JFin` to `P⁻¹ M P`
(`TauCeti.ConstantForm.pointsMulEquiv_mapPointsFunctor_coordinateHopfAlgebraCongr`). By
`TauCeti.antidiagCongr_inv_mul_diagonal_mul` and
`TauCeti.blockTriangular_antidiagCongr_inv_mul_mul_iff`, this conjugation turns the diagonal
torus `diag(t₁, …, t_m, t₁⁻¹, …, t_m⁻¹)` into `diag(t₁, …, t_m, t_m⁻¹, …, t₁⁻¹)` and the
isotropic-flag condition into upper triangularity.

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1, for transporting pinnings.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.Symplectic

universe u

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The subgroup scheme preserving the antidiagonal form is smooth, being isomorphic to `Sp₂ₘ`
by the signed permutation congruence `TauCeti.antidiagCongr`. -/
instance instSmoothCoordinateHopfAlgebraJAntidiag :
    Algebra.Smooth R (ConstantForm.coordinateHopfAlgebra R (m + m) (JAntidiag m R)) :=
  ConstantForm.smooth_of_congr (antidiagCongr m R) antidiagCongr_mul_JAntidiag_mul_transpose

/-- **The pinning of the antidiagonal model.** The standard pinning of `Sp₂ₘ` transported to the
subgroup scheme preserving the antidiagonal form along the signed permutation congruence
`TauCeti.antidiagCongr`. Its torus and Borel subgroup are computed by
`TauCeti.Symplectic.constantFormPinning_torus` and
`TauCeti.Symplectic.constantFormPinning_borel`. -/
noncomputable abbrev antidiagPinning [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)] :
    Pinning R (ConstantForm.coordinateHopfAlgebra R (m + m) (JAntidiag m R)) m :=
  constantFormPinning (antidiagCongr m R) antidiagCongr_mul_JAntidiag_mul_transpose

end TauCeti.Symplectic
