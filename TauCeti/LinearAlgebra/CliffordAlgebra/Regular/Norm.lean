/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Metric
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The scalar-part norm on real regular Clifford modules

For a negative definite real quadratic form, `CliffordAlgebra.regularNorm` is the
Euclidean norm associated to the intrinsic scalar-part metric. It is independent of a
frame, invariant under quadratic isometries and left Clifford-unitary multiplication,
and makes Clifford multiplication bounded. These facts allow the model norm and
multiplication to descend to metric Clifford bundles.

The vector multiplication formula is exact: multiplication by `ι v`, on either side,
scales this norm by `√(-Q v)`. General multiplication has a uniform bilinear bound;
we do not assert submultiplicativity with constant one. This Euclidean norm is not
an operator-algebra norm, and no global norm instance is installed.

The construction uses `CliffordAlgebra.regularInnerProductCore` and Mathlib's
finite-dimensional linear-to-continuous-linear equivalence.
-/

public section

noncomputable section

namespace CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (Q : QuadraticForm ℝ V)

/-- The intrinsic Euclidean norm of a real Clifford element for negative definite `Q`.
It is the square root of its scalar-part squared length. -/
def regularNorm (x : CliffordAlgebra Q) : ℝ :=
  Real.sqrt (regularBilinForm Q x x)

/-- The scalar-part norm is the square root of the intrinsic squared length. -/
theorem regularNorm_def (x : CliffordAlgebra Q) :
    regularNorm Q x = Real.sqrt (regularBilinForm Q x x) := (rfl)

/-- The scalar-part norm is nonnegative. -/
theorem regularNorm_nonneg (x : CliffordAlgebra Q) : 0 ≤ regularNorm Q x :=
  Real.sqrt_nonneg _

@[simp]
theorem regularNorm_zero : regularNorm Q 0 = 0 := by
  simp [regularNorm]

@[simp]
theorem regularNorm_one : regularNorm Q 1 = 1 := by
  simp [regularNorm]

@[simp]
theorem regularNorm_neg (x : CliffordAlgebra Q) : regularNorm Q (-x) = regularNorm Q x := by
  simp [regularNorm]

/-- Squaring the norm recovers the intrinsic metric for negative semidefinite forms. -/
theorem regularNorm_sq [FiniteDimensional ℝ V] (hQ : ∀ v, Q v ≤ 0) (x : CliffordAlgebra Q) :
    regularNorm Q x ^ 2 = regularBilinForm Q x x :=
  Real.sq_sqrt (regularBilinForm_self_nonneg Q hQ x)

/-- Clifford conjugation is an isometry of the scalar-part norm. -/
@[simp]
theorem regularNorm_star (x : CliffordAlgebra Q) : regularNorm Q (star x) = regularNorm Q x := by
  simp only [regularNorm, regularBilinForm_apply, star_star]
  rw [scalarTrace_mul_comm]

/-- The grade involution preserves the scalar-part norm. -/
@[simp]
theorem regularNorm_involute (x : CliffordAlgebra Q) :
    regularNorm Q (involute x) = regularNorm Q x := by
  simp only [regularNorm, regularBilinForm_involute]

/-- Reversal preserves the scalar-part norm. -/
@[simp]
theorem regularNorm_reverse (x : CliffordAlgebra Q) :
    regularNorm Q (reverse x) = regularNorm Q x := by
  rw [← regularNorm_star Q (reverse x), star_def, reverse_involute, reverse_reverse,
    regularNorm_involute]

/-- Left Clifford-unitary multiplication is isometric, including in rank zero. -/
theorem regularNorm_unitary_mul {a : CliffordAlgebra Q} (ha : star a * a = 1)
    (x : CliffordAlgebra Q) : regularNorm Q (a * x) = regularNorm Q x := by
  simp only [regularNorm, regularBilinForm_unitary_mul Q ha]

/-- The left regular Spin action preserves the scalar-part norm. -/
@[simp]
theorem regularNorm_spin_mul (g : spinGroup Q) (x : CliffordAlgebra Q) :
    regularNorm Q ((g : CliffordAlgebra Q) * x) = regularNorm Q x :=
  regularNorm_unitary_mul Q (spinGroup.coe_star_mul_self g) x

/-- Quadratic isometries preserve the model norm used in Clifford bundles. -/
@[simp]
theorem regularNorm_map {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q' : QuadraticForm ℝ W} (f : Q →qᵢ Q')
    (x : CliffordAlgebra Q) : regularNorm Q' (map f x) = regularNorm Q x := by
  simp only [regularNorm, regularBilinForm_map]

/-- Quadratic isometry equivalences preserve the scalar-part norm. -/
theorem regularNorm_equivOfIsometry {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q' : QuadraticForm ℝ W} (f : Q.IsometryEquiv Q') (x : CliffordAlgebra Q) :
    regularNorm Q' (equivOfIsometry f x) = regularNorm Q x :=
  regularNorm_map Q f.toIsometry x

/-- Left vector multiplication has its exact Euclidean norm scaling factor. -/
theorem regularNorm_ι_mul (v : V) (hv : Q v ≤ 0) (x : CliffordAlgebra Q) :
    regularNorm Q (ι Q v * x) = Real.sqrt (-Q v) * regularNorm Q x := by
  simp only [regularNorm, regularBilinForm_ι_mul_self]
  exact Real.sqrt_mul (neg_nonneg.mpr hv) _

/-- Right vector multiplication has the same scaling factor as left multiplication. -/
theorem regularNorm_mul_ι (v : V) (hv : Q v ≤ 0) (x : CliffordAlgebra Q) :
    regularNorm Q (x * ι Q v) = Real.sqrt (-Q v) * regularNorm Q x := by
  rw [← regularNorm_star Q (x * ι Q v), star_mul, star_ι, neg_mul,
    regularNorm_neg, regularNorm_ι_mul Q v hv, regularNorm_star]

/-- The norm of a vector is the square root of the negative quadratic form. -/
@[simp]
theorem regularNorm_ι (v : V) (hv : Q v ≤ 0) :
    regularNorm Q (ι Q v) = Real.sqrt (-Q v) := by
  simpa using regularNorm_ι_mul Q v hv 1

/-- Real scalar multiplication has the usual absolute-value norm formula. -/
@[simp]
theorem regularNorm_smul (r : ℝ) (x : CliffordAlgebra Q) :
    regularNorm Q (r • x) = |r| * regularNorm Q x := by
  simp only [regularNorm, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

section Definite

variable [FiniteDimensional ℝ V] (hQ : (-Q).PosDef)

include hQ

/-- The scalar-part norm vanishes exactly at zero for a negative definite form. -/
@[simp]
theorem regularNorm_eq_zero_iff (x : CliffordAlgebra Q) : regularNorm Q x = 0 ↔ x = 0 := by
  rw [regularNorm, Real.sqrt_eq_zero (regularBilinForm_self_nonneg Q
    (fun v ↦ neg_nonneg.mp (hQ.nonneg v)) x), regularBilinForm_self_eq_zero_iff Q hQ]

/-- The scalar-part norm agrees with the norm induced by the regular inner product core. -/
theorem regularNorm_eq_norm_core (x : CliffordAlgebra Q) :
    letI := InnerProductSpace.Core.toNormedAddCommGroup
      (cd := regularInnerProductCore Q hQ)
    regularNorm Q x = ‖x‖ := by
  simpa only [regularNorm_def, RCLike.re_to_real, InnerProductSpace.Core.toPreInner',
    regularInnerProductCore_inner] using
    (InnerProductSpace.Core.norm_eq_sqrt_re_inner
      (c := (regularInnerProductCore Q hQ).toCore) x).symm

/-- The intrinsic scalar-part norm satisfies the triangle inequality. -/
theorem regularNorm_add_le (x y : CliffordAlgebra Q) :
    regularNorm Q (x + y) ≤ regularNorm Q x + regularNorm Q y := by
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (cd := regularInnerProductCore Q hQ)
  simp only [regularNorm_eq_norm_core Q hQ]
  exact norm_add_le x y

/-- Clifford multiplication is uniformly bounded for the intrinsic Euclidean norm.
The constant depends only on the quadratic space, not on a frame or the two elements.
This includes the zero-dimensional quadratic space. -/
theorem exists_regularNorm_mul_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : CliffordAlgebra Q,
      regularNorm Q (x * y) ≤ C * regularNorm Q x * regularNorm Q y := by
  -- These instances use the scalar-part metric, not any ambient algebra norm.
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (cd := regularInnerProductCore Q hQ)
  let : InnerProductSpace ℝ (CliffordAlgebra Q) :=
    InnerProductSpace.ofCore (regularInnerProductCore Q hQ).toCore
  let m : CliffordAlgebra Q →ₗ[ℝ] CliffordAlgebra Q →L[ℝ] CliffordAlgebra Q :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (LinearMap.mul ℝ (CliffordAlgebra Q))
  let f := m.toContinuousLinearMap
  refine ⟨max ‖f‖ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x y ↦ ?_⟩
  simp only [regularNorm_eq_norm_core Q hQ]
  exact (f.le_opNorm₂ x y).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)) (norm_nonneg y))

end Definite

end CliffordAlgebra
