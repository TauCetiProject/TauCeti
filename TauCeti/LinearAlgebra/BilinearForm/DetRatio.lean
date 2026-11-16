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

`LinearMap.BilinForm.detRatio B B'` is the Gram determinant ratio `det B' / det B`,
comparing a bilinear form `B'` against a reference form `B`. A change of basis multiplies both
determinants by the same nonzero square, so the ratio
is basis independent. For forms positive on nonzero diagonal inputs it is positive; for a
nondegenerate form its self ratio is one. This provides a basis- and orientation-free comparison
of bilinear forms; its square root gives
`Bundle.RiemannianMetric.relativeVolumeDensity` for Riemannian metrics.
-/

public section

noncomputable section

open LinearMap (BilinForm)
open Matrix
open scoped Matrix

variable {R V : Type*} [CommRing R] [PartialOrder R]
  [Nontrivial R] [IsOrderedRing R] [PosMulReflectLT R]
  [AddCommGroup V] [Module R V]

/-- The Gram determinant of a bilinear form positive on nonzero diagonal inputs is positive in
every basis. Symmetry is not required. -/
theorem Module.Basis.det_bilinFormToMatrix_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R V) {B : BilinForm R V} (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    0 < (BilinForm.toMatrix b B).det := by
  -- Adapt the adjugate induction of Matrix.PosDef.det_pos, which does not use symmetry.
  suffices hdet : ∀ k (N : Matrix (Fin k) (Fin k) R),
      (∀ v, v ≠ 0 → 0 < v ⬝ᵥ N *ᵥ v) → 0 < N.det by
    let e := (Fintype.equivFin ι).symm
    rw [← det_submatrix_equiv_self e (BilinForm.toMatrix b B)]
    apply hdet
    intro v hv
    rw [submatrix_mulVec_equiv, dotProduct_comp_equiv_symm,
      BilinForm.dotProduct_toMatrix_mulVec]
    apply hpos
    intro hz
    apply hv
    funext i
    have h := congrArg b.equivFun hz
    rw [b.equivFun.apply_symm_apply, map_zero] at h
    simpa [e] using congrFun h (e i)
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro N hN
    set M := N.submatrix Fin.succ Fin.succ with M_def
    set v := N.adjugate.col 0 with v_def
    have hM : ∀ w, w ≠ 0 → 0 < w ⬝ᵥ M *ᵥ w := by
      intro w hw
      have hw' : vecCons 0 w ≠ 0 := by
        intro h
        apply hw
        funext i
        exact congrFun h i.succ
      simpa [dotProduct, mulVec, Fin.sum_univ_succ, M_def] using hN _ hw'
    have hvM : v 0 = M.det := by simp [M_def, v_def, adjugate_fin_succ_eq_det_submatrix]
    replace ih : 0 < M.det := ih _ hM
    suffices 0 < M.det * N.det from lt_of_mul_lt_mul_left (by simpa using this) ih.le
    have hNv : N *ᵥ v = fun i ↦ if i = 0 then N.det else 0 := by
      ext
      simp [v_def, ← col_mul_eq_mulVec_col, mul_adjugate, Matrix.one_apply]
    have hv₀ : v ≠ 0 := fun contra ↦ ih.ne' <| by simp [← hvM, contra]
    simpa [hNv, dotProduct, hvM] using hN v hv₀

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
theorem Module.Basis.bilinFormDetRatio_eq_det_bilinFormToMatrix_of_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) {B : BilinForm K V} (hB : BilinForm.toMatrix b B = 1)
    (B' : BilinForm K V) :
    BilinForm.detRatio B B' = (BilinForm.toMatrix b B').det := by
  rw [b.bilinFormDetRatio_eq, hB, Matrix.det_one, div_one]

/-- The Gram determinant ratio of two forms positive on nonzero diagonal inputs is positive. -/
theorem LinearMap.BilinForm.detRatio_pos [PartialOrder K] [IsOrderedRing K] [PosMulReflectLT K]
    (B B' : BilinForm K V) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (hpos' : ∀ v, v ≠ 0 → 0 < B' v v) :
    0 < BilinForm.detRatio B B' :=
  div_pos (Module.Basis.det_bilinFormToMatrix_pos _ hpos')
    (Module.Basis.det_bilinFormToMatrix_pos _ hpos)

/-- The Gram determinant ratio of a nondegenerate bilinear form with itself is one. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_self (B : BilinForm K V) (hB : B.Nondegenerate) :
    B.detRatio B = 1 :=
  div_self ((BilinForm.nondegenerate_iff_det_ne_zero (Module.finBasis K V)).1 hB)

/-- The determinant ratio is nonzero exactly when both forms are nondegenerate. -/
theorem LinearMap.BilinForm.detRatio_ne_zero_iff (B B' : BilinForm K V) :
    B.detRatio B' ≠ 0 ↔ B.Nondegenerate ∧ B'.Nondegenerate := by
  simp only [detRatio, ne_eq, div_eq_zero_iff, not_or,
    ← nondegenerate_iff_det_ne_zero (Module.finBasis K V)]
  exact and_comm

/-- The determinant ratio vanishes exactly when at least one form is degenerate. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_eq_zero_iff (B B' : BilinForm K V) :
    B.detRatio B' = 0 ↔ ¬ B.Nondegenerate ∨ ¬ B'.Nondegenerate := by
  simpa only [not_and_or, not_not] using (not_congr (detRatio_ne_zero_iff B B'))

/-- Reversing the forms inverts the determinant ratio. -/
theorem LinearMap.BilinForm.inv_detRatio (B B' : BilinForm K V) :
    (B.detRatio B')⁻¹ = B'.detRatio B := by
  simp only [detRatio, inv_div]

/-- Ratios multiply when the intermediate form is nondegenerate. -/
@[simp]
theorem LinearMap.BilinForm.detRatio_mul_detRatio (B B' B'' : BilinForm K V)
    (hB' : B'.Nondegenerate) : B.detRatio B' * B'.detRatio B'' = B.detRatio B'' := by
  rw [detRatio, detRatio, detRatio, mul_comm,
    div_mul_div_cancel₀ ((nondegenerate_iff_det_ne_zero (Module.finBasis K V)).1 hB')]

/-- Scaling the numerator form multiplies the determinant ratio by the dimension power. -/
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
