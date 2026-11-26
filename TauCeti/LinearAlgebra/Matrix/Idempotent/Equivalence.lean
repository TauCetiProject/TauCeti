/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import TauCeti.Algebra.Module.StableEquivalent
public import TauCeti.LinearAlgebra.Matrix.Idempotent.RightRange

import TauCeti.Data.Matrix.Block

/-!
# Further calculus of equivalence of idempotent matrices

Building on `Matrix.IdempotentEquivalent` in `TauCeti.LinearAlgebra.Matrix.Idempotent.Basic`, this
file develops size invariance of identity matrices and separation of `Eᵢᵢ` from `1` under
`InvariantBasisNumber`, the explicit isomorphism `Matrix.linearEquivRangeMulVecBilinOfMulEq` and
invariance of column-range `finrank`, and the comparison of `IdempotentEquivalent` and
`StableEquivalent` with unit conjugacy of `e ⊕ 0` and `0 ⊕ f`
(`Matrix.idempotentEquivalent_iff_exists_units_conj_fromBlocks_zero`,
`Matrix.stableEquivalent_range_mulVecBilin_iff`,
`Matrix.stableEquivalent_range_mulVecBilin_iff_exists_units_conj`).

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter I, §2, and Chapter II, §§1–2.
* B. Blackadar, *K-Theory for Operator Algebras*, §§4.2–4.6.
-/

public section

open LinearMap MulOpposite

namespace Matrix

section Semiring

variable {l m m' n n' R : Type*} [Semiring R]

/-- Over a semiring with invariant basis number, `1ₘ ∼ 1ₙ ↔ |m| = |n|`. -/
@[simp]
theorem idempotentEquivalent_one_iff [InvariantBasisNumber R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    IdempotentEquivalent (1 : Matrix m m R) (1 : Matrix n n R) ↔
      Fintype.card m = Fintype.card n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, y, hxy, hyx, _⟩ := idempotentEquivalent_iff.mp h
    exact Matrix.square_of_invertible x y hxy hyx
  · obtain ⟨σ⟩ := Fintype.card_eq.mp h
    simpa using (idempotentEquivalent_submatrix (IsIdempotentElem.one (M := Matrix n n R)) σ).symm

/-- Over a semiring with invariant basis number and `|m| > 1`, `Eᵢᵢ` is not equivalent to `1ₘ`. -/
theorem not_idempotentEquivalent_single_one_one [InvariantBasisNumber R] [Fintype m]
    [DecidableEq m] [Nontrivial m] (i : m) :
    ¬ IdempotentEquivalent (single i i (1 : R)) (1 : Matrix m m R) := fun h ↦
  (ne_of_lt Fintype.one_lt_card) (by
    simpa using idempotentEquivalent_one_iff.mp
      ((idempotentEquivalent_single_one_one i).symm.trans h))

/-- **Mutually inverse module maps from equivalence witnesses.** When `x * y = e` and `y * x = f`
for idempotent `e` and `f`, left multiplication by `x` and `y` induces `f Rⁿ ≃ₗ[Rᵐᵒᵖ] e Rᵐ`. -/
def linearEquivRangeMulVecBilinOfMulEq [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    range (f.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ) :=
  (rangeVecMulLinearTransposeMapOpEquiv f).symm.trans <|
    (linearEquivRangeVecMulLinearOfMulEq
      (by rw [← transpose_mul_map_op, hyx]) (by rw [← transpose_mul_map_op, hxy])
      hf.matrix_transpose_map_op he.matrix_transpose_map_op).trans
      (rangeVecMulLinearTransposeMapOpEquiv e)

@[simp]
theorem coe_linearEquivRangeMulVecBilinOfMulEq_apply [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (v : range (f.mulVecBilin R Rᵐᵒᵖ)) :
    (linearEquivRangeMulVecBilinOfMulEq hxy hyx he hf v : m → R) = x *ᵥ v := by
  ext i; simp [linearEquivRangeMulVecBilinOfMulEq, ← op_comp_mulVec]

@[simp]
theorem coe_linearEquivRangeMulVecBilinOfMulEq_symm_apply [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (w : range (e.mulVecBilin R Rᵐᵒᵖ)) :
    ((linearEquivRangeMulVecBilinOfMulEq hxy hyx he hf).symm w : n → R) = y *ᵥ w := by
  ext i; simp [linearEquivRangeMulVecBilinOfMulEq, ← op_comp_mulVec]

/-- Equivalent idempotent matrices have equal right `R`-rank on their column ranges. -/
theorem IdempotentEquivalent.finrank_range_mulVecBilin_eq [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (h : IdempotentEquivalent e f) :
    Module.finrank Rᵐᵒᵖ (range (e.mulVecBilin R Rᵐᵒᵖ)) =
      Module.finrank Rᵐᵒᵖ (range (f.mulVecBilin R Rᵐᵒᵖ)) :=
  ((nonempty_linearEquiv_range_mulVecBilin_iff h.isIdempotentElem_left
    h.isIdempotentElem_right).mpr h).some.finrank_eq

/-- **Stable equivalence of column ranges in matrix form.** Column ranges of idempotents `e` and
`f` are stably equivalent right `R`-modules iff `e ⊕ 1ₖ` and `f ⊕ 1ₖ` are equivalent for some
`k`. -/
theorem stableEquivalent_range_mulVecBilin_iff [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    TauCeti.StableEquivalent Rᵐᵒᵖ
        (range (e.mulVecBilin R Rᵐᵒᵖ)) (range (f.mulVecBilin R Rᵐᵒᵖ)) ↔
      ∃ k : ℕ, IdempotentEquivalent (fromBlocks e 0 0 (1 : Matrix (Fin k) (Fin k) R))
        (fromBlocks f 0 0 (1 : Matrix (Fin k) (Fin k) R)) := by
  rw [TauCeti.stableEquivalent_iff]
  refine exists_congr fun k ↦ ?_
  rw [← nonempty_linearEquiv_range_mulVecBilin_iff
    (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.one)
    (hf.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.one)]
  let eqL := (rangeMulVecBilinFromBlocksEquiv e (1 : Matrix (Fin k) (Fin k) R)).trans
    ((LinearEquiv.refl Rᵐᵒᵖ _).prodCongr (rangeMulVecBilinOneEquiv (Fin k) R))
  let eqR := (rangeMulVecBilinFromBlocksEquiv f (1 : Matrix (Fin k) (Fin k) R)).trans
    ((LinearEquiv.refl Rᵐᵒᵖ _).prodCongr (rangeMulVecBilinOneEquiv (Fin k) R))
  exact ⟨fun ⟨ψ⟩ ↦ ⟨eqL.trans (ψ.trans eqR.symm)⟩, fun ⟨ψ⟩ ↦ ⟨eqL.symm.trans (ψ.trans eqR)⟩⟩

end Semiring

section Ring

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring R]

/-- **Equivalent idempotents become unit-conjugate after zero-block stabilization.** -/
theorem IdempotentEquivalent.exists_units_conj_fromBlocks_zero
    {e : Matrix m m R} {f : Matrix n n R} (h : IdempotentEquivalent e f) :
    ∃ u : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ,
      u.val * Matrix.fromBlocks e 0 0 0 * u⁻¹.val = Matrix.fromBlocks 0 0 0 f := by
  obtain ⟨x, y, hxy, hyx, hex, -, -, hye⟩ := idempotentEquivalent_iff.mp h
  have hinv := fromBlocks_one_sub_mul_self_of_mul_eq hxy hyx hex hye
  refine ⟨⟨Matrix.fromBlocks (1 - e) x y (1 - f), Matrix.fromBlocks (1 - e) x y (1 - f),
    hinv, hinv⟩, fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq hxy hyx hye⟩

/-- **Equivalence of an idempotent with another matrix is stabilized similarity.** -/
theorem idempotentEquivalent_iff_exists_units_conj_fromBlocks_zero
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) :
    IdempotentEquivalent e f ↔ ∃ u : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ,
      u.val * fromBlocks e 0 0 0 * u⁻¹.val = fromBlocks 0 0 0 f := by
  refine ⟨IdempotentEquivalent.exists_units_conj_fromBlocks_zero, fun ⟨u, hu⟩ ↦ ?_⟩
  have hconj : IdempotentEquivalent (fromBlocks (0 : Matrix m m R) 0 0 f)
      (fromBlocks e 0 0 (0 : Matrix n n R)) := by
    rw [← hu]
    exact (idempotentEquivalent_conj (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.zero) u).symm
  have hf : IsIdempotentElem f := by
    rw [IsIdempotentElem]
    simpa [fromBlocks_multiply] using congrArg toBlocks₂₂ hconj.isIdempotentElem_left.eq
  exact (he.idempotentEquivalent_fromBlocks_zero_right n).symm.trans
    (hconj.symm.trans (hf.idempotentEquivalent_fromBlocks_zero_left m))

/-- **Stable equivalence of column ranges is stabilized similarity.** For idempotent matrices `e`
and `f`, their column ranges are stably equivalent right `R`-modules if and only if after adding a
common identity block `1ₖ` and complementary zero blocks, the resulting block matrices are
conjugate by an invertible matrix. -/
theorem stableEquivalent_range_mulVecBilin_iff_exists_units_conj
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    TauCeti.StableEquivalent Rᵐᵒᵖ
        (range (e.mulVecBilin R Rᵐᵒᵖ)) (range (f.mulVecBilin R Rᵐᵒᵖ)) ↔
      ∃ (k : ℕ) (u : (Matrix ((m ⊕ Fin k) ⊕ (n ⊕ Fin k)) ((m ⊕ Fin k) ⊕ (n ⊕ Fin k)) R)ˣ),
        u.val * fromBlocks (fromBlocks e 0 0 (1 : Matrix (Fin k) (Fin k) R)) 0 0 0 * u⁻¹.val =
          fromBlocks 0 0 0 (fromBlocks f 0 0 (1 : Matrix (Fin k) (Fin k) R)) := by
  rw [stableEquivalent_range_mulVecBilin_iff he hf]
  exact exists_congr fun k ↦ idempotentEquivalent_iff_exists_units_conj_fromBlocks_zero
    (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.one)

end Ring

end Matrix
