/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization

/-!
# Ratios of Gram determinants

`LinearMap.BilinForm.detRatio` is the ratio of the Gram determinants of two real bilinear
forms. A change of basis multiplies both determinants by the same nonzero square, so the ratio
is basis independent. For positive-definite symmetric forms it is positive; for a nondegenerate
form its self ratio is one.
-/

public section

noncomputable section

open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Gram determinant of a symmetric positive-definite bilinear form is positive in every
basis. -/
theorem Module.Basis.det_toMatrix_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V)
    {B : BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    0 < (BilinForm.toMatrix b B).det :=
  ((BilinForm.posDef_toQuadraticMap_iff_matrix b B ⟨hsymm⟩).1 hpos).det_pos

variable [Module.Finite ℝ V]

/-- The ratio `det B' / det B` of the Gram determinants of two bilinear forms on a
finite-dimensional real vector space, computed in the basis `Module.finBasis ℝ V`. It does not
depend on the basis: see `Module.Basis.bilinFormDetRatio_eq`. -/
def LinearMap.BilinForm.detRatio (B B' : BilinForm ℝ V) : ℝ :=
  (BilinForm.toMatrix (Module.finBasis ℝ V) B').det /
    (BilinForm.toMatrix (Module.finBasis ℝ V) B).det

/-- **Basis independence of the Gram determinant ratio.** In any basis `b`, the determinant
ratio is the ratio of the Gram determinants of `B'` and `B`. -/
theorem Module.Basis.bilinFormDetRatio_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V)
    (B B' : BilinForm ℝ V) :
    BilinForm.detRatio B B' =
      (BilinForm.toMatrix b B').det / (BilinForm.toMatrix b B).det := by
  set b₀ := (Module.finBasis ℝ V).reindex ((Module.finBasis ℝ V).indexEquiv b)
  have hP : (b₀.toMatrix b).det ≠ 0 := by
    rw [← Module.Basis.det_apply]
    exact (b₀.isUnit_det b).ne_zero
  rw [BilinForm.detRatio,
    ← BilinForm.det_toMatrix_reindex _ ((Module.finBasis ℝ V).indexEquiv b) B,
    ← BilinForm.det_toMatrix_reindex _ ((Module.finBasis ℝ V).indexEquiv b) B',
    BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ b, BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ b,
    mul_div_mul_left _ _ (pow_ne_zero 2 hP)]

/-- In a basis in which `B` has the identity Gram matrix, `BilinForm.detRatio B B'` is the Gram
determinant of `B'`. -/
theorem Module.Basis.bilinFormDetRatio_eq_det_of_toMatrix_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) {B : BilinForm ℝ V} (hB : BilinForm.toMatrix b B = 1)
    (B' : BilinForm ℝ V) :
    BilinForm.detRatio B B' = (BilinForm.toMatrix b B').det := by
  rw [b.bilinFormDetRatio_eq, hB, Matrix.det_one, div_one]

/-- The Gram determinant ratio of two symmetric positive-definite bilinear forms is positive. -/
theorem LinearMap.BilinForm.detRatio_pos {B B' : BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) (hsymm' : ∀ v w, B' v w = B' w v)
    (hpos' : ∀ v, v ≠ 0 → 0 < B' v v) :
    0 < BilinForm.detRatio B B' :=
  div_pos (Module.Basis.det_toMatrix_pos _ hsymm' hpos')
    (Module.Basis.det_toMatrix_pos _ hsymm hpos)

/-- The Gram determinant ratio of a nondegenerate bilinear form with itself is one. -/
theorem LinearMap.BilinForm.detRatio_self {B : BilinForm ℝ V} (hB : B.Nondegenerate) :
    B.detRatio B = 1 :=
  div_self ((BilinForm.nondegenerate_iff_det_ne_zero (Module.finBasis ℝ V)).1 hB)
