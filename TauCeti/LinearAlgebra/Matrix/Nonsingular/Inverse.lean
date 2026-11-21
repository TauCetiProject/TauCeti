/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Matrix inverse identities and entrywise bounds

Applying a ring homomorphism `f : R →+* S` entrywise commutes with taking the inverse of a square
matrix, provided `f` is a local homomorphism (`Matrix.map_nonsing_inv`). The inverse
`A⁻¹ = Ring.inverse (det A) • adjugate A` is built from the determinant and the adjugate, which
commute with every ring homomorphism (`RingHom.map_det`, `RingHom.map_adjugate`), and a local
homomorphism commutes with `Ring.inverse` (`map_ringInverse`).

Locality is needed: `ℤ →+* ℚ` is not local, and the `1 × 1` matrix `2` over `ℤ` has inverse `0`,
while its image in `ℚ` has inverse `1 / 2`. Every ring homomorphism from a field to a nontrivial
ring is local, so the statement applies, for instance, to the casts `ℚ → ℝ` and `ℝ → ℂ`: an
inverse computed over `ℚ` is the inverse over `ℝ`.

`Matrix.inv_submatrix_mul_row_eq_single` normalizes the rows of a matrix whose columns off a pivot
set vanish to coordinate vectors, by the inverse of its pivot submatrix.

Two matrices `L` and `M` with the same Gram matrix `L * Lᵀ = M * Mᵀ`, where `det L` is a unit,
differ by the orthogonal matrix `L⁻¹ * M` (`Matrix.inv_mul_mul_transpose_inv_mul_eq_one`).

Scaling a square matrix by a semifield scalar scales its nonsingular inverse by the inverse scalar
(`Matrix.nonsing_inv_smul`), including at zero and for singular matrices. Given a ring homomorphism
`f : R →+* A`, a matrix `w` with right inverse `w_inv`, and an invariance relation
`v * M.map f * w = M.map f`, the mapped inverse satisfies `w * M⁻¹.map f * v = M⁻¹.map f`
(`Matrix.mul_map_nonsing_inv_mul`).

`LinearMap.toMatrix_ringInverse` identifies the matrix of an endomorphism's ring inverse.

For invertible matrices `A`, `B` over a linearly ordered field, inverse entries bounded by `L`
and entrywise difference bounded by `d` give `|A⁻¹ i j - B⁻¹ i j| ≤ (card ι)² L² d`
(`Matrix.abs_inv_sub_inv_apply_le`). This estimate supplies the inverse-entry Hölder modulus.
It is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

namespace Matrix

variable {n R S F : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
  [FunLike F R S] [RingHomClass F R S]

/-- A local ring homomorphism applied entrywise commutes with the inverse of a square matrix. -/
@[simp]
theorem map_nonsing_inv (f : F) [IsLocalHom f] (A : Matrix n n R) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : f A.det = (A.map f).det := RingHom.map_det (f : R →+* S) A
  have hadj : A.adjugate.map f = (A.map f).adjugate := RingHom.map_adjugate (f : R →+* S) A
  rw [inv_def, inv_def, ← hdet, ← hadj, ← map_ringInverse f]
  ext i j
  simp

/-- Scaling a square matrix by a scalar in a semifield scales its nonsingular inverse by the
inverse scalar (including when the scalar is zero or the matrix is singular). -/
theorem nonsing_inv_smul {n R α : Type*} [Fintype n] [DecidableEq n]
    [Semifield R] [CommRing α] [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]
    (r : R) (A : Matrix n n α) :
    (r • A)⁻¹ = r⁻¹ • A⁻¹ := by
  by_cases hr : r = 0
  · simp [hr]
  · by_cases hdet : IsUnit A.det
    · refine inv_eq_left_inv ?_
      rw [smul_mul_smul_comm, inv_mul_cancel₀ hr, one_smul, nonsing_inv_mul A hdet]
    · have hrdet : ¬IsUnit (r • A).det := fun hu ↦ hdet <|
        isUnit_det_of_left_inverse (B := r • (r • A)⁻¹) (by
          rw [smul_mul, ← Matrix.mul_smul, nonsing_inv_mul (r • A) hu])
      rw [nonsing_inv_apply_not_isUnit _ hrdet, nonsing_inv_apply_not_isUnit _ hdet, smul_zero]

/-- Invert an invariance equation `v * M.map f * w = M.map f` across a ring homomorphism `f` when
`w` has a right inverse `w_inv` (handling singular `M` via `M⁻¹ = 0`). -/
theorem mul_map_nonsing_inv_mul {n R A F : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [Semiring A] [FunLike F R A] [RingHomClass F R A] (f : F)
    {w w_inv v : Matrix n n A} (hw : w * w_inv = 1) {M : Matrix n n R}
    (hinv : v * M.map f * w = M.map f) :
    w * M⁻¹.map f * v = M⁻¹.map f := by
  by_cases hdet : IsUnit M.det
  · set MA := M.map f
    set MiA := M⁻¹.map f
    have hMMi : MA * MiA = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv M hdet, Matrix.map_one _ (map_zero f) (map_one f)]
    have hMiM : MiA * MA = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul M hdet, Matrix.map_one _ (map_zero f) (map_one f)]
    have hvM : v * MA = MA * w_inv := by
      calc
        v * MA = v * MA * (w * w_inv) := by rw [hw, Matrix.mul_one]
        _ = (v * MA * w) * w_inv := by simp only [Matrix.mul_assoc]
        _ = MA * w_inv := by rw [hinv]
    have hMiv : MiA * v = w_inv * MiA := by
      calc
        MiA * v = MiA * (v * (MA * MiA)) := by rw [hMMi, Matrix.mul_one]
        _ = (MiA * MA) * w_inv * MiA := by
          rw [← Matrix.mul_assoc v MA MiA, hvM]; simp only [Matrix.mul_assoc]
        _ = w_inv * MiA := by rw [hMiM, Matrix.one_mul]
    calc
      w * MiA * v = w * (MiA * v) := by rw [Matrix.mul_assoc]
      _ = (w * w_inv) * MiA := by rw [hMiv, Matrix.mul_assoc]
      _ = MiA := by rw [hw, Matrix.one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hdet, Matrix.map_zero _ (map_zero f),
      Matrix.mul_zero, Matrix.zero_mul]

/-- If the column change `Q` kills `x` off the pivot columns `e`, then normalizing by the inverse of
the pivot matrix turns the rows of `x * Q` into coordinate vectors. -/
theorem inv_submatrix_mul_row_eq_single {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    {p : ℕ} {x : Matrix (Fin p) ι K} {e : Fin p ↪ ι} {Q : Matrix ι ι K}
    (he : IsUnit (x.submatrix id e).det)
    (hred : ∀ i j, (x * Q) i j = if j ∈ Set.range e then x i j else 0) :
    ((x.submatrix id e)⁻¹ * (x * Q)).row = fun i ↦ Pi.single (e i) 1 := by
  set P := x.submatrix id e
  ext i j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨b, rfl⟩ := hj
    have h := congrArg (fun M : Matrix (Fin p) (Fin p) K ↦ M i b)
      (Matrix.nonsing_inv_mul P he)
    simpa [P, Matrix.mul_apply, hred, Pi.single_apply,
      e.injective.eq_iff, Matrix.one_apply, eq_comm] using h
  · have hz : ∀ b, e b ≠ j := fun b h ↦ hj ⟨b, h⟩
    simp [Matrix.mul_apply, hred, hj, hz, Ne.symm]

/-- If `L` has unit determinant and `L * Lᵀ = M * Mᵀ`, then `L⁻¹ * M` is orthogonal:
`(L⁻¹ * M) * (L⁻¹ * M)ᵀ = 1`. -/
theorem inv_mul_mul_transpose_inv_mul_eq_one {L M : Matrix n n R} (hLdet : IsUnit L.det)
    (hgram : L * Lᵀ = M * Mᵀ) : (L⁻¹ * M) * (L⁻¹ * M)ᵀ = 1 := by
  have hLinvt_right : Lᵀ * L⁻¹ᵀ = 1 := by
    rw [← transpose_mul, nonsing_inv_mul L hLdet, transpose_one]
  rw [transpose_mul]
  calc
    (L⁻¹ * M) * (Mᵀ * L⁻¹ᵀ) = L⁻¹ * (M * Mᵀ) * L⁻¹ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = L⁻¹ * (L * Lᵀ) * L⁻¹ᵀ := by rw [← hgram]
    _ = (L⁻¹ * L) * (Lᵀ * L⁻¹ᵀ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul L hLdet, hLinvt_right, Matrix.one_mul]

end Matrix

namespace LinearMap

variable {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommMonoid M] [Module R M]

/-- The matrix of the ring inverse of an endomorphism is the inverse of its matrix. -/
theorem toMatrix_ringInverse (b : Module.Basis ι R M) (A : M →ₗ[R] M) :
    toMatrix b b (Ring.inverse A) = (toMatrix b b A)⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  simpa only [toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply] using
    map_ringInverse (toMatrixAlgEquiv b) A

end LinearMap

section InverseBound

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/--
**Entrywise modulus of the inverse.** For invertible `A`, `B` over a linearly ordered field
whose inverse entries are bounded by `L` and whose entrywise difference is bounded by `d`,
`|A⁻¹ᵢⱼ − B⁻¹ᵢⱼ| ≤ n² L² d` with `n = card ι`. -/
theorem Matrix.abs_inv_sub_inv_apply_le {A B : Matrix ι ι R} {L d : R}
    (hA : IsUnit A) (hB : IsUnit B)
    (ha : ∀ i j, |A⁻¹ i j| ≤ L) (hb : ∀ i j, |B⁻¹ i j| ≤ L)
    (hab : ∀ i j, |A i j - B i j| ≤ d) (i j : ι) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (Fintype.card ι : R) ^ 2 * L ^ 2 * d := by
  classical
  have hL : 0 ≤ L := (abs_nonneg _).trans (ha i i)
  have hd : 0 ≤ d := (abs_nonneg _).trans (hab i i)
  have hi : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := Matrix.inv_sub_inv ⟨fun _ => hB, fun _ => hA⟩
  calc
    |A⁻¹ i j - B⁻¹ i j| = |∑ k : ι, ∑ l : ι, A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      rw [← Matrix.sub_apply, hi]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
    _ ≤ ∑ k : ι, ∑ l : ι, |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      exact
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k : ι, ∑ _l : ι, L * d * L := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_mul, abs_sub_comm (B l k) (A l k)]
      exact
        mul_le_mul (mul_le_mul (ha i l) (hab l k) (abs_nonneg _) hL) (hb k j) (abs_nonneg _)
          (mul_nonneg hL hd)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end InverseBound
