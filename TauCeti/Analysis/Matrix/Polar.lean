/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# The polar decomposition of an invertible matrix

Over `𝕜 = ℝ` or `ℂ`, every invertible matrix `A : GL n 𝕜` factors uniquely as `A = P U` with `P`
positive definite and `U` unitary (orthogonal when `𝕜 = ℝ`): `P = √(A Aᴴ)` is the square root of
the continuous functional calculus and `U = Units.polarUnitary A`. This file specializes the
polar decomposition of invertible elements of
`TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean` to matrices, where the
positive factor is positive definite, and computes the determinants of both factors:
`det P = ‖det A‖` and `det U = det A / ‖det A‖`.

In particular, for `A` of determinant one, as in `SL(n, ℂ)` or `SL(n, ℝ)`, both factors have
determinant one, and so does every real power `P ^ s` of the positive factor.

## Main results

* `Matrix.GeneralLinearGroup.posDef_sqrt_mul_star`: the positive factor `√(A Aᴴ)` is positive
  definite.
* `Matrix.GeneralLinearGroup.existsUnique_posDef_mul_unitary`: existence and uniqueness of the
  polar decomposition `A = P U` with `P` positive definite and `U` unitary.
* `Matrix.PosSemidef.det_rpow`: the determinant of a real power `X ^ s` of a positive
  semidefinite matrix is `(det X) ^ s`.
* `Matrix.GeneralLinearGroup.det_sqrt_mul_star`, `Matrix.GeneralLinearGroup.det_polarUnitary`: the
  determinants of the two factors.
* `Matrix.GeneralLinearGroup.det_rpow_sqrt_mul_star_of_det_eq_one`,
  `Matrix.GeneralLinearGroup.det_polarUnitary_of_det_eq_one`: for `det A = 1`, every real power of
  the positive factor, and the unitary factor, have determinant one.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The determinant of a real power `X ^ s` of a positive semidefinite matrix is the real power
`(det X) ^ s` of its determinant, which is a nonnegative real number. -/
theorem PosSemidef.det_rpow {X : Matrix n n 𝕜} (hX : X.PosSemidef) (s : ℝ) :
    (X ^ s).det = ((RCLike.re X.det ^ s : ℝ) : 𝕜) := by
  rw [CFC.rpow_eq_cfc_real hX.nonneg, hX.isHermitian.cfc_eq, hX.isHermitian.det_eq_prod_eigenvalues]
  simp only [IsHermitian.cfc, det_map, det_diagonal, Function.comp_apply, ← RCLike.ofReal_prod,
    RCLike.ofReal_re, Real.finsetProd_rpow _ _ (fun i _ ↦ hX.eigenvalues_nonneg i) s]

namespace GeneralLinearGroup

variable (A : GL n 𝕜)

/-- The positive factor `√(A Aᴴ)` of the polar decomposition of an invertible matrix is positive
definite. -/
theorem posDef_sqrt_mul_star : (CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))).PosDef :=
  isStrictlyPositive_iff_posDef.1 (Units.isStrictlyPositive_sqrt_mul_star A)

/-- **The polar decomposition of an invertible matrix.** Every `A : GL n 𝕜` is uniquely a product
`P U` of a positive definite matrix `P` and a unitary matrix `U`; over `ℝ`, `U` is orthogonal. -/
theorem existsUnique_posDef_mul_unitary :
    ∃! PU : Matrix n n 𝕜 × unitaryGroup n 𝕜, PU.1.PosDef ∧ PU.1 * PU.2 = A := by
  refine ⟨(CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)), Units.polarUnitary A),
    ⟨posDef_sqrt_mul_star A, Units.sqrt_mul_star_mul_polarUnitary A⟩, ?_⟩
  rintro ⟨P, U⟩ ⟨hP, h⟩
  exact Prod.ext (Units.sqrt_mul_star_eq_of_mul_eq A hP.posSemidef.nonneg h).symm
    (Units.polarUnitary_eq_of_mul_eq A hP.posSemidef.nonneg h).symm

/-- The determinant of the positive factor `√(A Aᴴ)` is `‖det A‖`. -/
theorem det_sqrt_mul_star :
    (CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))).det = ‖(A : Matrix n n 𝕜).det‖ := by
  have hAA : ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)).PosSemidef :=
    nonneg_iff_posSemidef.1 (mul_star_self_nonneg _)
  rw [CFC.sqrt_eq_rpow, hAA.det_rpow, det_mul, star_eq_conjTranspose, det_conjTranspose,
    RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _)]

/-- The determinant of the unitary factor of `A` is `det A / ‖det A‖`. -/
theorem det_polarUnitary :
    ((Units.polarUnitary A : unitaryGroup n 𝕜) : Matrix n n 𝕜).det =
      (A : Matrix n n 𝕜).det / ‖(A : Matrix n n 𝕜).det‖ := by
  have hdet : ((‖(A : Matrix n n 𝕜).det‖ : ℝ) : 𝕜) ≠ 0 := by
    simpa using (A.isUnit.map detMonoidHom).ne_zero
  rw [eq_div_iff hdet, mul_comm, ← det_sqrt_mul_star, ← det_mul,
    Units.sqrt_mul_star_mul_polarUnitary]

/-- For `det A = 1`, every real power of the positive factor `√(A Aᴴ)` has determinant one. -/
theorem det_rpow_sqrt_mul_star_of_det_eq_one (hA : (A : Matrix n n 𝕜).det = 1) (s : ℝ) :
    (CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)) ^ s).det = 1 := by
  rw [(posDef_sqrt_mul_star A).posSemidef.det_rpow, det_sqrt_mul_star, hA]
  simp

/-- For `det A = 1`, the unitary factor of `A` has determinant one. -/
theorem det_polarUnitary_of_det_eq_one (hA : (A : Matrix n n 𝕜).det = 1) :
    ((Units.polarUnitary A : unitaryGroup n 𝕜) : Matrix n n 𝕜).det = 1 := by
  rw [det_polarUnitary, hA]
  simp

end GeneralLinearGroup

end Matrix
