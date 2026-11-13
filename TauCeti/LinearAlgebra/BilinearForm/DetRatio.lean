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

`LinearMap.BilinForm.detRatio` is the ratio of the Gram determinants of two bilinear
forms. A change of basis multiplies both determinants by the same nonzero square, so the ratio
is basis independent. For positive-definite symmetric forms it is positive; for a nondegenerate
form its self ratio is one.
-/

public section

noncomputable section

open LinearMap (BilinForm)

variable {R V : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- The Gram determinant of a symmetric positive-definite bilinear form is positive in every
basis. -/
theorem Module.Basis.det_toMatrix_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R V)
    {B : BilinForm R V} (hsymm : ∀ v w, B v w = B w v) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    0 < (BilinForm.toMatrix b B).det := by
  let : StarRing R := starRingOfComm
  have : TrivialStar R := ⟨fun _ ↦ rfl⟩
  exact ((BilinForm.posDef_toQuadraticMap_iff_matrix b B ⟨hsymm⟩).1 hpos).det_pos

variable {K : Type*} [Field K] [Module K V] [Module.Finite K V]

/-- The ratio `det B' / det B` of the Gram determinants of two bilinear forms on a
finite-dimensional vector space, computed in the basis `Module.finBasis K V`. It does not
depend on the basis: see `Module.Basis.bilinFormDetRatio_eq`. -/
def LinearMap.BilinForm.detRatio (B B' : BilinForm K V) : K :=
  (BilinForm.toMatrix (Module.finBasis K V) B').det /
    (BilinForm.toMatrix (Module.finBasis K V) B).det

/-- **Basis independence of the Gram determinant ratio.** In any basis `b`, the determinant
ratio is the ratio of the Gram determinants of `B'` and `B`. -/
theorem Module.Basis.bilinFormDetRatio_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V)
    (B B' : BilinForm K V) :
    BilinForm.detRatio B B' =
      (BilinForm.toMatrix b B').det / (BilinForm.toMatrix b B).det := by
  set b₀ := (Module.finBasis K V).reindex ((Module.finBasis K V).indexEquiv b)
  have hP : (b₀.toMatrix b).det ≠ 0 := by
    rw [← Module.Basis.det_apply]
    exact (b₀.isUnit_det b).ne_zero
  rw [BilinForm.detRatio,
    ← BilinForm.det_toMatrix_reindex _ ((Module.finBasis K V).indexEquiv b) B,
    ← BilinForm.det_toMatrix_reindex _ ((Module.finBasis K V).indexEquiv b) B',
    BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ b, BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ b,
    mul_div_mul_left _ _ (pow_ne_zero 2 hP)]

/-- In a basis in which `B` has the identity Gram matrix, `BilinForm.detRatio B B'` is the Gram
determinant of `B'`. -/
theorem Module.Basis.bilinFormDetRatio_eq_det_of_toMatrix_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) {B : BilinForm K V} (hB : BilinForm.toMatrix b B = 1)
    (B' : BilinForm K V) :
    BilinForm.detRatio B B' = (BilinForm.toMatrix b B').det := by
  rw [b.bilinFormDetRatio_eq, hB, Matrix.det_one, div_one]

/-- The Gram determinant ratio of two symmetric positive-definite bilinear forms is positive. -/
theorem LinearMap.BilinForm.detRatio_pos [LinearOrder K] [IsStrictOrderedRing K]
    (B B' : BilinForm K V) (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) (hsymm' : ∀ v w, B' v w = B' w v)
    (hpos' : ∀ v, v ≠ 0 → 0 < B' v v) :
    0 < BilinForm.detRatio B B' :=
  div_pos (Module.Basis.det_toMatrix_pos _ hsymm' hpos')
    (Module.Basis.det_toMatrix_pos _ hsymm hpos)

/-- The Gram determinant ratio of a nondegenerate bilinear form with itself is one. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_self (B : BilinForm K V) (hB : B.Nondegenerate) :
    B.detRatio B = 1 :=
  div_self ((BilinForm.nondegenerate_iff_det_ne_zero (Module.finBasis K V)).1 hB)

/-- Reversing the forms inverts the determinant ratio. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_inv (B B' : BilinForm K V) :
    (B.detRatio B')⁻¹ = B'.detRatio B := by
  simp only [detRatio, inv_div]

/-- Ratios multiply when the intermediate form is nondegenerate. -/
theorem LinearMap.BilinForm.detRatio_mul_detRatio (B B' B'' : BilinForm K V)
    (hB' : B'.Nondegenerate) : B.detRatio B' * B'.detRatio B'' = B.detRatio B'' := by
  rw [detRatio, detRatio, detRatio, mul_comm,
    div_mul_div_cancel₀ ((nondegenerate_iff_det_ne_zero (Module.finBasis K V)).1 hB')]

/-- Scaling the numerator scales its Gram determinant by the dimension power. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_smul_right (B B' : BilinForm K V) (c : K) :
    B.detRatio (c • B') = c ^ Module.finrank K V * B.detRatio B' := by
  simp only [detRatio, map_smul, Matrix.det_smul, Fintype.card_fin, mul_div_assoc]

/-- Scaling the denominator divides the ratio by the dimension power. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_smul_left (B B' : BilinForm K V) (c : K) :
    (c • B).detRatio B' = B.detRatio B' / c ^ Module.finrank K V := by
  simp only [detRatio, map_smul, Matrix.det_smul, Fintype.card_fin, div_mul_eq_div_div]
  rw [div_right_comm]

/-- A linear equivalence transports both forms without changing their determinant ratio. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_congr (B B' : BilinForm K V) {W : Type*}
    [AddCommGroup W] [Module K W] [Module.Finite K W] (e : V ≃ₗ[K] W) :
    (BilinForm.congr e B).detRatio (BilinForm.congr e B') = B.detRatio B' := by
  rw [((Module.finBasis K V).map e).bilinFormDetRatio_eq,
    (Module.finBasis K V).bilinFormDetRatio_eq]
  congr 2 <;> ext i j <;> simp [BilinForm.toMatrix_apply, BilinForm.congr_apply]
