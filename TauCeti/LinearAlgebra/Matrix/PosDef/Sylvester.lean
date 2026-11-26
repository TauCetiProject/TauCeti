/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# Sylvester's criterion for positive-definite matrices

A square matrix `B : Matrix (Fin n) (Fin n) K` over a star-ordered field `K` (such as `ℝ`, `ℂ`
with `ComplexOrder`, any `RCLike` field, or `ℚ`) is positive definite if and only if it is
Hermitian and all of its leading principal minors are positive
(`Matrix.posDef_iff_isHermitian_and_det_submatrix_castLE_pos`). Over any linearly ordered field
with trivial star, the same Schur-complement induction gives the symmetric form
(`Matrix.posDef_iff_isSymm_and_det_submatrix_castLE_pos`). In rank zero both sides hold
unconditionally.

For the application to semialgebraicity of the positive-definite cone in entry coordinates, see
`TauCeti/Geometry/RealAlgebraic/Semialgebraic/PosDef.lean`.

## Main results

* `Matrix.posDef_iff_isHermitian_and_det_submatrix_castLE_pos`: Sylvester's criterion for Hermitian
  matrices over a star-ordered field (including `ℝ` and `ℂ`).
* `Matrix.posDef_iff_isSymm_and_det_submatrix_castLE_pos`: Sylvester's criterion over a linearly
  ordered field with trivial star.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.2.5 (Sylvester's criterion).
-/

public section

open scoped Matrix

namespace Matrix

private theorem posDef_iff_isHermitian_and_det_submatrix_castLE_pos_of_forall_star_mul_self_pos
    {K : Type*} [Field K] [PartialOrder K] [IsOrderedRing K] [PosMulReflectLT K] [StarRing K]
    (hsq : ∀ t : K, t ≠ 0 → 0 < star t * t) {n : ℕ} {B : Matrix (Fin n) (Fin n) K} :
    B.PosDef ↔ B.IsHermitian ∧ ∀ k : Fin n,
      0 < (B.submatrix (Fin.castLE (Nat.succ_le_of_lt k.isLt))
        (Fin.castLE (Nat.succ_le_of_lt k.isLt))).det := by
  refine ⟨fun hB ↦ ⟨hB.isHermitian, fun k ↦
    (hB.submatrix (Fin.castLE_injective _)).det_pos⟩, ?_⟩
  induction n with
  | zero => intro _; exact PosDef.of_isEmpty B
  | succ n ih =>
    rintro ⟨hHerm, hMinors⟩
    set A : Matrix (Fin n) (Fin n) K := B.submatrix Fin.castSucc Fin.castSucc
    have hA : A.PosDef := ih ⟨hHerm.submatrix Fin.castSucc, fun i ↦ hMinors i.castSucc⟩
    have hdetB : 0 < B.det := by simpa using hMinors (Fin.last n)
    let : Invertible A := invertibleOfIsUnitDet A hA.det_pos.ne'.isUnit
    let g : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv.symm).trans finSumFinEquiv
    have hg_inl (i : Fin n) : g (Sum.inl i) = i.castSucc := by ext; simp [g]
    have hg_inr : g (Sum.inr ()) = Fin.last n := by ext; simp [g, finOneEquiv]
    let bCol : Matrix (Fin n) Unit K := of fun i _ ↦ B i.castSucc (Fin.last n)
    let bCorner : Matrix Unit Unit K := of fun _ _ ↦ B (Fin.last n) (Fin.last n)
    have hblk : B.submatrix g g = fromBlocks A bCol bColᴴ bCorner := by
      ext (i | ⟨⟩) (j | ⟨⟩)
      · simp [A, hg_inl]
      · simp [bCol, hg_inl, hg_inr]
      · simp [bCol, hg_inl, hg_inr, ← hHerm.apply (Fin.last n) j.castSucc]
      · simp [bCorner, hg_inr]
    set S : Matrix Unit Unit K := bCorner - bColᴴ * A⁻¹ * bCol
    have hdet_eq : B.det = A.det * S () () := by
      rw [← det_submatrix_equiv_self g B, hblk, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
        det_unique S]
    have hs_pos : 0 < S () () :=
      lt_of_mul_lt_mul_left (by simpa [hdet_eq] using hdetB) hA.det_pos.le
    have hblk_posDef : (fromBlocks A bCol bColᴴ bCorner).PosDef := by
      refine PosDef.of_dotProduct_mulVec_pos (hblk ▸ hHerm.submatrix g) fun x hx ↦ ?_
      rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x,
        schur_complement_eq₁₁ bCol bCorner (x ∘ Sum.inl) (x ∘ Sum.inr) hA.1,
        ← dotProduct_mulVec, ← dotProduct_mulVec (star (x ∘ Sum.inr))]
      set u : Fin n → K := x ∘ Sum.inl + (A⁻¹ * bCol) *ᵥ (x ∘ Sum.inr)
      have hu_nonneg : 0 ≤ star u ⬝ᵥ (A *ᵥ u) := hA.posSemidef.dotProduct_mulVec_nonneg u
      have hS_quad : star (x ∘ Sum.inr) ⬝ᵥ (S *ᵥ (x ∘ Sum.inr)) =
          S () () * (star (x (Sum.inr ())) * x (Sum.inr ())) := by
        simp only [Pi.star_def, dotProduct, mulVec, Fintype.univ_punit, Finset.sum_singleton,
          Function.comp_apply]
        ring
      rw [hS_quad]
      by_cases ht : x (Sum.inr ()) = 0
      · have hy0 : x ∘ Sum.inr = 0 := funext fun ⟨⟩ ↦ ht
        have hu_ne : u ≠ 0 := by
          simpa [u, hy0] using fun hxl0 : x ∘ Sum.inl = 0 ↦
            hx (funext fun | Sum.inl i => congrFun hxl0 i | Sum.inr () => ht)
        simpa [ht] using hA.dotProduct_mulVec_pos hu_ne
      · have hprod_pos : 0 < S () () * (star (x (Sum.inr ())) * x (Sum.inr ())) :=
          (mul_nonneg hs_pos.le (hsq _ ht).le).lt_of_ne' (mul_ne_zero hs_pos.ne' (hsq _ ht).ne')
        exact add_pos_of_nonneg_of_pos hu_nonneg hprod_pos
    exact (by rw [← hblk, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] :
      (fromBlocks A bCol bColᴴ bCorner).submatrix g.symm g.symm = B) ▸
        hblk_posDef.submatrix g.symm.injective

/-- **Sylvester's criterion.** Over a star-ordered field `K` (such as `ℝ`, `ℂ` with
`ComplexOrder`, any `RCLike` field, or `ℚ`), a matrix `B : Matrix (Fin n) (Fin n) K` is positive
definite if and only if it is Hermitian and every leading principal minor is positive. -/
theorem posDef_iff_isHermitian_and_det_submatrix_castLE_pos {K : Type*} [Field K] [PartialOrder K]
    [PosMulReflectLT K] [StarRing K] [StarOrderedRing K] {n : ℕ} {B : Matrix (Fin n) (Fin n) K} :
    B.PosDef ↔ B.IsHermitian ∧ ∀ k : Fin n,
      0 < (B.submatrix (Fin.castLE (Nat.succ_le_of_lt k.isLt))
        (Fin.castLE (Nat.succ_le_of_lt k.isLt))).det :=
  posDef_iff_isHermitian_and_det_submatrix_castLE_pos_of_forall_star_mul_self_pos fun _ ht ↦
    star_mul_self_pos (isUnit_iff_ne_zero.mpr ht).isRegular

/-- **Sylvester's criterion over a linearly ordered field with trivial star.** A matrix
`B : Matrix (Fin n) (Fin n) K` is positive definite if and only if it is symmetric and every
leading principal minor is positive. -/
theorem posDef_iff_isSymm_and_det_submatrix_castLE_pos {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [StarRing K] [TrivialStar K] {n : ℕ} {B : Matrix (Fin n) (Fin n) K} :
    B.PosDef ↔ B.IsSymm ∧ ∀ k : Fin n,
      0 < (B.submatrix (Fin.castLE (Nat.succ_le_of_lt k.isLt))
        (Fin.castLE (Nat.succ_le_of_lt k.isLt))).det := by
  rw [← isHermitian_iff_isSymm]
  exact posDef_iff_isHermitian_and_det_submatrix_castLE_pos_of_forall_star_mul_self_pos
    fun _ ht ↦ by simpa using mul_self_pos.mpr ht

end Matrix
