/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.Analysis.Matrix.Rpow
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
* `Matrix.det_sqrt_mul_star`, `Matrix.GeneralLinearGroup.det_polarUnitary`: the determinants of
  the two factors; the first holds for every square matrix.
* `Matrix.GeneralLinearGroup.exists_scalar_mul_mul_toGL_eq`: every invertible matrix is a scalar
  times a unitary matrix times a matrix of determinant one.
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

/-- The determinant of the positive factor `√(A Aᴴ)` of the polar decomposition is `‖det A‖`;
this holds for every square matrix `A`, invertible or not. -/
theorem det_sqrt_mul_star (A : Matrix n n 𝕜) : (CFC.sqrt (A * star A)).det = ‖A.det‖ := by
  have hAA : (A * star A).PosSemidef := nonneg_iff_posSemidef.1 (mul_star_self_nonneg _)
  rw [CFC.sqrt_eq_rpow, hAA.det_rpow, det_mul, star_eq_conjTranspose, det_conjTranspose,
    RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _)]

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

/-- **Every invertible matrix over `ℝ` or `ℂ` is a scalar times a unitary matrix times a matrix of
determinant one**: `A = c V g` with `c` a scalar matrix, `V` unitary and `g ∈ SL n 𝕜`. -/
theorem exists_scalar_mul_mul_toGL_eq :
    ∃ c : 𝕜ˣ, ∃ V ∈ unitarySubgroup (GL n 𝕜), ∃ g : SpecialLinearGroup n 𝕜,
      GeneralLinearGroup.scalar n c * V * SpecialLinearGroup.toGL g = A := by
  have hdet : (A : Matrix n n 𝕜).det ≠ 0 := det_ne_zero A
  set d := ‖(A : Matrix n n 𝕜).det‖ with hd_def
  have hd : 0 < d := norm_pos_iff.mpr hdet
  -- The positive real scalar `r` with `r ^ card n * ‖det A‖ = 1`.
  set r : ℝ := (d ^ (Fintype.card n : ℝ)⁻¹)⁻¹
  have hr : (r : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (inv_pos.mpr (Real.rpow_pos_of_pos hd _)).ne'
  have hrd : r ^ Fintype.card n * d = 1 := by
    rcases isEmpty_or_nonempty n with hn | hn
    · simp [hd_def]
    · simp [r, inv_pow, Real.rpow_inv_natCast_pow hd.le Fintype.card_ne_zero, hd.ne']
  set U : GL n 𝕜 := Unitary.toUnits (Units.polarUnitary A)
  set s : GL n 𝕜 := GeneralLinearGroup.scalar n (Units.mk0 (r : 𝕜) hr)
  have hdet' : ((s * (U⁻¹ * A) : GL n 𝕜) : Matrix n n 𝕜).det = 1 := by
    -- The unitary factor has determinant `det A / ‖det A‖`, so `U⁻¹ A` has determinant `‖det A‖`.
    have hU : ((U : GL n 𝕜) : Matrix n n 𝕜).det = (A : Matrix n n 𝕜).det / d :=
      det_polarUnitary A
    have hUA : ((U⁻¹ * A : GL n 𝕜) : Matrix n n 𝕜).det = d := by
      simp only [Units.val_mul, coe_units_inv, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', hU]
      field_simp
    have hs : (s : Matrix n n 𝕜).det = (r : 𝕜) ^ Fintype.card n := by
      simp [s]
    rw [Units.val_mul, det_mul, hUA, hs]
    exact_mod_cast hrd
  refine ⟨(Units.mk0 (r : 𝕜) hr)⁻¹, U, ?_, ⟨_, hdet'⟩, ?_⟩
  · rw [mem_unitarySubgroup_iff, Units.unitary_eq]
    exact (Units.polarUnitary A).2
  have htoGL : SpecialLinearGroup.toGL (⟨_, hdet'⟩ : SpecialLinearGroup n 𝕜) = s * (U⁻¹ * A) :=
    Units.ext (SpecialLinearGroup.coe_GL_coe_matrix _)
  -- The scalar `s` is central.
  have hs : Commute s U := GeneralLinearGroup.scalar_commute _ U
  rw [htoGL, map_inv, ← mul_assoc, hs.inv_mul_cancel, mul_inv_cancel_left]

end GeneralLinearGroup

end Matrix
