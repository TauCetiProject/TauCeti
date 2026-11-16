/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# Sylvester's criterion and semialgebraicity of positive-definite matrices

Over a linearly ordered field `K` with trivial star, a square matrix `B : Matrix (Fin n) (Fin n) K`
is positive definite if and only if it is symmetric and all of its leading principal minors are
positive (`Matrix.posDef_iff_isSymm_and_det_submatrix_castLE_pos`). In rank zero both sides hold
unconditionally.

Consequently, in matrix-entry coordinates `Fin n × Fin n → K`, the positive-definite cone is a
quantifier-free semialgebraic set (`TauCeti.isSemialgebraic_setOf_posDef`).

## Main results

* `Matrix.posDef_iff_isSymm_and_det_submatrix_castLE_pos`: Sylvester's criterion for
  `Matrix (Fin n) (Fin n) K`.
* `TauCeti.isSemialgebraic_setOf_posDef`: the positive-definite matrices form a semialgebraic set
  in entry coordinates.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.2.5 (Sylvester's criterion).
-/

public section

open scoped Matrix

namespace Matrix

/-- **Sylvester's criterion.** Over a linearly ordered field `K` with trivial star, a matrix
`B : Matrix (Fin n) (Fin n) K` is positive definite if and only if it is symmetric and every
leading principal minor is positive. -/
theorem posDef_iff_isSymm_and_det_submatrix_castLE_pos {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [StarRing K] [TrivialStar K] {n : ℕ} {B : Matrix (Fin n) (Fin n) K} :
    B.PosDef ↔ B.IsSymm ∧ ∀ k : Fin n,
      0 < (B.submatrix (Fin.castLE (Nat.succ_le_of_lt k.isLt))
        (Fin.castLE (Nat.succ_le_of_lt k.isLt))).det := by
  refine ⟨fun hB ↦ ⟨hB.isHermitian.isSymm, fun k ↦
    (hB.submatrix (Fin.castLE_injective _)).det_pos⟩, ?_⟩
  induction n with
  | zero => intro _; exact PosDef.of_isEmpty B
  | succ n ih =>
    rintro ⟨hSymm, hMinors⟩
    set A : Matrix (Fin n) (Fin n) K := B.submatrix Fin.castSucc Fin.castSucc
    have hA : A.PosDef := ih ⟨hSymm.submatrix Fin.castSucc, fun i ↦ hMinors i.castSucc⟩
    have hdetB : 0 < B.det := by simpa using hMinors (Fin.last n)
    let : Invertible A := invertibleOfIsUnitDet A hA.det_pos.ne'.isUnit
    let g : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      { toFun := Sum.elim Fin.castSucc (fun _ ↦ Fin.last n)
        invFun := Fin.lastCases (Sum.inr ()) Sum.inl
        left_inv := fun x ↦ by cases x <;> simp
        right_inv := fun i ↦ Fin.lastCases (by simp) (by simp) i }
    let bCol : Matrix (Fin n) Unit K := of fun i _ ↦ B i.castSucc (Fin.last n)
    let bCorner : Matrix Unit Unit K := of fun _ _ ↦ B (Fin.last n) (Fin.last n)
    have hblk : B.submatrix g g = fromBlocks A bCol bColᴴ bCorner := by
      ext (i | _) (j | _) <;> simp [A, g, bCol, bCorner, hSymm.apply _ (Fin.last n)]
    set S : Matrix Unit Unit K := bCorner - bColᴴ * A⁻¹ * bCol
    have hdet_eq : B.det = A.det * S () () := by
      rw [← det_submatrix_equiv_self g B, hblk, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
        det_unique S]
    have hs_pos : 0 < S () () := pos_of_mul_pos_right (hdet_eq ▸ hdetB) hA.det_pos.le
    have hblk_posDef : (fromBlocks A bCol bColᴴ bCorner).PosDef := by
      refine PosDef.of_dotProduct_mulVec_pos
        (hblk ▸ isHermitian_iff_isSymm.mpr (hSymm.submatrix g)) fun x hx ↦ ?_
      rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x,
        schur_complement_eq₁₁ bCol bCorner (x ∘ Sum.inl) (x ∘ Sum.inr) hA.1,
        ← dotProduct_mulVec, ← dotProduct_mulVec (star (x ∘ Sum.inr))]
      set u : Fin n → K := x ∘ Sum.inl + (A⁻¹ * bCol) *ᵥ (x ∘ Sum.inr)
      have hu_nonneg : 0 ≤ star u ⬝ᵥ (A *ᵥ u) := by
        simpa using hA.posSemidef.dotProduct_mulVec_nonneg u
      have hS_quad : star (x ∘ Sum.inr) ⬝ᵥ (S *ᵥ (x ∘ Sum.inr)) =
          S () () * (x (Sum.inr ())) ^ 2 := by
        simp only [star_trivial, dotProduct, mulVec, Fintype.univ_punit, Finset.sum_singleton,
          Function.comp_apply]
        ring
      rw [hS_quad]
      by_cases ht : x (Sum.inr ()) = 0
      · have hy0 : x ∘ Sum.inr = 0 := funext fun ⟨⟩ ↦ ht
        have hu_ne : u ≠ 0 := by
          simpa [u, hy0] using fun hxl0 : x ∘ Sum.inl = 0 ↦
            hx (funext fun | Sum.inl i => congrFun hxl0 i | Sum.inr () => ht)
        simpa [ht] using hA.dotProduct_mulVec_pos hu_ne
      · linarith [mul_pos hs_pos (sq_pos_of_ne_zero ht)]
    have hB_eq : (fromBlocks A bCol bColᴴ bCorner).submatrix g.symm g.symm = B := by
      rw [← hblk, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
    exact hB_eq ▸ hblk_posDef.submatrix g.symm.injective

end Matrix

namespace TauCeti

/-- In matrix-entry coordinates `Fin n × Fin n → K`, the set of positive-definite `n × n` matrices
over a linearly ordered field with trivial star is semialgebraic. -/
theorem isSemialgebraic_setOf_posDef {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [StarRing K] [TrivialStar K] (n : ℕ) :
    IsSemialgebraic {s : Fin n × Fin n → K | (Matrix.of (Function.curry s)).PosDef} := by
  have hdet {m : ℕ} (f : Fin m → Fin n) (s : Fin n × Fin n → K) :
      ((Matrix.of (Function.curry s)).submatrix f f).det =
        MvPolynomial.eval s (((Matrix.mvPolynomialX (Fin n) (Fin n) K).submatrix f f).det) := by
    rw [RingHom.map_det]
    congr 1; ext a b; simp [Matrix.mvPolynomialX_apply, Function.curry]
  have heq : {s : Fin n × Fin n → K | (Matrix.of (Function.curry s)).PosDef} =
      (⋂ p : Fin n × Fin n,
        {s | MvPolynomial.eval s (MvPolynomial.X p) =
          MvPolynomial.eval s (MvPolynomial.X p.swap)}) ∩
      (⋂ k : Fin n, {s | 0 < MvPolynomial.eval s
        (((Matrix.mvPolynomialX (Fin n) (Fin n) K).submatrix
          (Fin.castLE (Nat.succ_le_of_lt k.isLt))
          (Fin.castLE (Nat.succ_le_of_lt k.isLt))).det)}) := by
    ext s
    simp only [Matrix.posDef_iff_isSymm_and_det_submatrix_castLE_pos, Matrix.IsSymm.ext_iff,
      Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Prod.forall, MvPolynomial.eval_X,
      Prod.swap_prod_mk, Matrix.of_apply, Function.curry_apply, ← hdet]
    exact and_congr ⟨fun h i j ↦ (h i j).symm, fun h i j ↦ (h i j).symm⟩ Iff.rfl
  rw [heq]
  exact (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _).inter
    (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_pos _)

end TauCeti
