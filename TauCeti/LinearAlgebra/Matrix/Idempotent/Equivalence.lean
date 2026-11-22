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

Building on `Matrix.IdempotentEquivalent` in `TauCeti.LinearAlgebra.Matrix.Idempotent`, this
file develops the additional algebraic properties needed for `IdempotentMonoid` and stabilized
similarity:

* symmetry in iff form (`idempotentEquivalent_comm`), `reindex`, self-equivalence iff idempotence,
  and characterization of equivalence with zero matrices and padding by zero blocks;
* over any semiring with invariant basis number, characterization of equivalence between identity
  matrices (`1ₘ ∼ 1ₙ ↔ |m| = |n|`) and separation of rank-one matrix units `Eᵢᵢ` from `0` and
  `1ₘ` (`|m| > 1`);
* the explicit right-module isomorphism `Matrix.linearEquivRangeMulVecBilinOfMulEq` induced by
  witnesses `x * y = e`, `y * x = f`, and invariance of column-range `finrank`;
* comparison of stable equivalence of column ranges with `IdempotentEquivalent` after adding `1ₖ`
  and with unit conjugacy after also adding zero blocks (`e ⊕ 0` and `0 ⊕ f` are conjugate by the
  involution `!![1 - e, x; y, 1 - f]`).

## Main definitions

* `Matrix.linearEquivRangeMulVecBilinOfMulEq`: the explicit `Rᵐᵒᵖ`-linear isomorphism between
  column ranges induced by witnesses `x * y = e` and `y * x = f` for idempotent `e` and `f`.

## Main results

* `Matrix.idempotentEquivalent_one_iff`, `Matrix.not_idempotentEquivalent_single_one_zero`, and
  `Matrix.not_idempotentEquivalent_single_one_one`: size invariance of identity matrices and
  separation of rank-one matrix units `Eᵢᵢ` from `0` and `1` under invariant basis number.
* `Matrix.IdempotentEquivalent.finrank_range_mulVecBilin_eq`: equivalence preserves column-range
  `finrank`.
* `Matrix.idempotentEquivalent_iff_exists_units_conj_fromBlocks_zero`: equivalence of an idempotent
  `e` with `f` is unit conjugacy of `e ⊕ 0` and `0 ⊕ f`.
* `Matrix.stableEquivalent_range_mulVecBilin_iff` and
  `Matrix.stableEquivalent_range_mulVecBilin_iff_exists_units_conj`: stable equivalence of column
  ranges matches equivalence after adding `1ₖ`, and unit conjugacy after also adding zero blocks.

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

theorem idempotentEquivalent_comm [Fintype m] [Fintype n] {e : Matrix m m R} {f : Matrix n n R} :
    IdempotentEquivalent e f ↔ IdempotentEquivalent f e :=
  ⟨IdempotentEquivalent.symm, IdempotentEquivalent.symm⟩

/-- Simultaneous row-and-column reindexing preserves equivalence of idempotents. -/
theorem IdempotentEquivalent.reindex [Fintype m] [Fintype m'] [Fintype n] [Fintype n']
    {e : Matrix m m R} {f : Matrix n n R} (h : IdempotentEquivalent e f) (σ : m ≃ m')
    (τ : n ≃ n') : IdempotentEquivalent (e.reindex σ σ) (f.reindex τ τ) :=
  (idempotentEquivalent_submatrix h.isIdempotentElem_left σ.symm).symm.trans
    (h.trans (idempotentEquivalent_submatrix h.isIdempotentElem_right τ.symm))

/-- Reindexing an idempotent matrix along an index bijection yields an equivalent idempotent. -/
theorem _root_.IsIdempotentElem.idempotentEquivalent_reindex [Fintype m] [Fintype m']
    {e : Matrix m m R} (he : IsIdempotentElem e) (σ : m ≃ m') :
    IdempotentEquivalent (e.reindex σ σ) e :=
  (idempotentEquivalent_submatrix he σ.symm).symm

/-- Zero matrices of any two finite sizes are equivalent idempotents. -/
theorem idempotentEquivalent_zero_zero (m n : Type*) [Fintype m] [Fintype n] :
    IdempotentEquivalent (0 : Matrix m m R) (0 : Matrix n n R) :=
  idempotentEquivalent_iff.mpr ⟨0, 0, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Only the zero matrix is equivalent to a zero matrix. -/
@[simp]
theorem idempotentEquivalent_zero_iff [Fintype m] [Fintype n] {e : Matrix m m R} :
    IdempotentEquivalent e (0 : Matrix n n R) ↔ e = 0 := by
  refine ⟨?_, fun h ↦ h ▸ idempotentEquivalent_zero_zero m n⟩
  rw [idempotentEquivalent_iff]
  rintro ⟨x, y, rfl, -, -, hxf, -, -⟩
  rw [← hxf, Matrix.mul_zero, Matrix.zero_mul]

/-- A zero matrix is equivalent only to the zero matrix. -/
@[simp]
theorem zero_idempotentEquivalent_iff [Fintype m] [Fintype n] {f : Matrix n n R} :
    IdempotentEquivalent (0 : Matrix m m R) f ↔ f = 0 := by
  rw [idempotentEquivalent_comm, idempotentEquivalent_zero_iff]

/-- Padding an idempotent matrix by a lower-right zero block preserves its equivalence class. -/
theorem _root_.IsIdempotentElem.idempotentEquivalent_fromBlocks_zero_right (n : Type*)
    [Fintype m] [Fintype n] {e : Matrix m m R} (he : IsIdempotentElem e) :
    IdempotentEquivalent (fromBlocks e 0 0 (0 : Matrix n n R)) e := by
  let x : Matrix (m ⊕ n) m R := of fun i j ↦ match i with | Sum.inl i => e i j | Sum.inr _ => 0
  let y : Matrix m (m ⊕ n) R := of fun i j ↦ match j with | Sum.inl j => e i j | Sum.inr _ => 0
  have he' (i j : m) : ∑ k, e i k * e k j = e i j := congrFun (congrFun he.eq i) j
  refine idempotentEquivalent_iff.mpr ⟨x, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext (i | i) (j | j) <;> simp [x, y, Matrix.mul_apply, he']
  · ext i j; simp [x, y, Matrix.mul_apply, Fintype.sum_sum_type, he']
  · ext (i | i) j <;> simp [x, Matrix.mul_apply, Fintype.sum_sum_type, he']
  · ext (i | i) j <;> simp [x, Matrix.mul_apply, he']
  · ext i (j | j) <;> simp [y, Matrix.mul_apply, he']
  · ext i (j | j) <;> simp [y, Matrix.mul_apply, Fintype.sum_sum_type, he']

/-- Padding an idempotent matrix by an upper-left zero block preserves its equivalence class. -/
theorem _root_.IsIdempotentElem.idempotentEquivalent_fromBlocks_zero_left (m : Type*)
    [Fintype m] [Fintype n] {e : Matrix n n R} (he : IsIdempotentElem e) :
    IdempotentEquivalent (fromBlocks (0 : Matrix m m R) 0 0 e) e := by
  have hEq : fromBlocks (0 : Matrix m m R) 0 0 e =
      (fromBlocks e 0 0 (0 : Matrix m m R)).reindex (Equiv.sumComm n m) (Equiv.sumComm n m) := by
    ext (_ | _) (_ | _) <;> rfl
  rw [hEq]
  exact (he.idempotentEquivalent_fromBlocks_zero_right m).reindex
    (Equiv.sumComm n m) (Equiv.refl n)

/-- A square matrix is equivalent to itself if and only if it is idempotent. -/
@[simp]
theorem idempotentEquivalent_self_iff [Fintype m] {e : Matrix m m R} :
    IdempotentEquivalent e e ↔ IsIdempotentElem e :=
  ⟨IdempotentEquivalent.isIdempotentElem_left, IdempotentEquivalent.refl⟩

/-- Any two diagonal matrix units `Eᵢᵢ ∈ Matrix m m R` and `Eⱼⱼ ∈ Matrix n n R` are equivalent
idempotents, witnessed by `Eᵢⱼ` and `Eⱼᵢ`. -/
theorem idempotentEquivalent_single_one [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) : IdempotentEquivalent (single i i (1 : R)) (single j j (1 : R)) :=
  idempotentEquivalent_iff.mpr
    ⟨single i j 1, single j i 1, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Any diagonal matrix unit `Eᵢᵢ` is equivalent to the `1 × 1` identity matrix. -/
theorem idempotentEquivalent_single_one_one [Fintype m] [DecidableEq m] (i : m) :
    IdempotentEquivalent (single i i (1 : R)) (1 : Matrix (Fin 1) (Fin 1) R) := by
  have h1 : single (0 : Fin 1) 0 (1 : R) = (1 : Matrix (Fin 1) (Fin 1) R) := by
    ext a b
    fin_cases a
    fin_cases b
    rfl
  exact h1 ▸ idempotentEquivalent_single_one i (0 : Fin 1)

/-- Over a nontrivial semiring, a diagonal matrix unit `Eᵢᵢ` is not equivalent to a zero
matrix. -/
theorem not_idempotentEquivalent_single_one_zero [Nontrivial R] [Fintype m] [Fintype n]
    [DecidableEq m] (i : m) :
    ¬ IdempotentEquivalent (single i i (1 : R)) (0 : Matrix n n R) := by
  rw [idempotentEquivalent_zero_iff]
  intro h
  have hii := congrFun (congrFun h i) i
  simp at hii

/-- Over a semiring with invariant basis number, two identity matrices are equivalent idempotents
if and only if they have the same size. -/
@[simp]
theorem idempotentEquivalent_one_iff [InvariantBasisNumber R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    IdempotentEquivalent (1 : Matrix m m R) (1 : Matrix n n R) ↔
      Fintype.card m = Fintype.card n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, y, hxy, hyx, _⟩ := idempotentEquivalent_iff.mp h
    exact Matrix.square_of_invertible x y hxy hyx
  · obtain ⟨σ⟩ := Fintype.card_eq.mp h.symm
    simpa using (IsIdempotentElem.one (M := Matrix n n R)).idempotentEquivalent_reindex σ

/-- Over a semiring with invariant basis number and any finite index type `m` with at least two
elements, a diagonal matrix unit `Eᵢᵢ` is not equivalent to `1 : Matrix m m R`. -/
theorem not_idempotentEquivalent_single_one_one [InvariantBasisNumber R] [Fintype m]
    [DecidableEq m] [Nontrivial m] (i : m) :
    ¬ IdempotentEquivalent (single i i (1 : R)) (1 : Matrix m m R) := by
  intro h
  have h1 := (idempotentEquivalent_single_one_one i).symm.trans h
  exact (ne_of_lt Fintype.one_lt_card) (idempotentEquivalent_one_iff.mp h1)

/-- **Mutually inverse module maps from equivalence witnesses.** When `e` and `f` are idempotent
and `x * y = e`, `y * x = f`, left multiplication by `x` and `y` restrict to mutually inverse
`Rᵐᵒᵖ`-linear maps between `f Rⁿ` and `e Rᵐ`. -/
def linearEquivRangeMulVecBilinOfMulEq [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    range (f.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ) where
  toFun v := ⟨x *ᵥ v, he.mem_range_mulVecBilin_iff.mpr <| by
    rw [mulVec_mulVec, ← hxy, Matrix.mul_assoc, hyx, ← mulVec_mulVec,
      hf.mem_range_mulVecBilin_iff.mp v.property]⟩
  invFun w := ⟨y *ᵥ w, hf.mem_range_mulVecBilin_iff.mpr <| by
    rw [mulVec_mulVec, ← hyx, Matrix.mul_assoc, hxy, ← mulVec_mulVec,
      he.mem_range_mulVecBilin_iff.mp w.property]⟩
  map_add' u v := Subtype.ext (mulVec_add x u v)
  map_smul' r v := Subtype.ext (mulVec_smul x r v)
  left_inv v := Subtype.ext <| by
    simp [mulVec_mulVec, hyx, hf.mem_range_mulVecBilin_iff.mp v.property]
  right_inv w := Subtype.ext <| by
    simp [mulVec_mulVec, hxy, he.mem_range_mulVecBilin_iff.mp w.property]

@[simp]
theorem coe_linearEquivRangeMulVecBilinOfMulEq_apply [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (v : range (f.mulVecBilin R Rᵐᵒᵖ)) :
    (linearEquivRangeMulVecBilinOfMulEq hxy hyx he hf v : m → R) = x *ᵥ v :=
  (rfl)

@[simp]
theorem coe_linearEquivRangeMulVecBilinOfMulEq_symm_apply [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (w : range (e.mulVecBilin R Rᵐᵒᵖ)) :
    ((linearEquivRangeMulVecBilinOfMulEq hxy hyx he hf).symm w : n → R) = y *ᵥ w :=
  (rfl)

/-- Equivalent idempotent matrices have equal right `R`-rank on their column ranges. -/
theorem IdempotentEquivalent.finrank_range_mulVecBilin_eq [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (h : IdempotentEquivalent e f) :
    Module.finrank Rᵐᵒᵖ (range (e.mulVecBilin R Rᵐᵒᵖ)) =
      Module.finrank Rᵐᵒᵖ (range (f.mulVecBilin R Rᵐᵒᵖ)) := by
  obtain ⟨ψ⟩ := (nonempty_linearEquiv_range_mulVecBilin_iff
    h.isIdempotentElem_left h.isIdempotentElem_right).mpr h
  exact ψ.finrank_eq

/-- **Stable equivalence of column ranges in matrix form.** For idempotent matrices `e` and `f`,
their column ranges are stably equivalent right `R`-modules if and only if `e ⊕ 1ₖ` and `f ⊕ 1ₖ`
are equivalent idempotents for some `k : ℕ`. -/
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
  let eqLeft := (rangeMulVecBilinFromBlocksEquiv e (1 : Matrix (Fin k) (Fin k) R)).trans
    ((LinearEquiv.refl Rᵐᵒᵖ _).prodCongr (rangeMulVecBilinOneEquiv (Fin k) R))
  let eqRight := (rangeMulVecBilinFromBlocksEquiv f (1 : Matrix (Fin k) (Fin k) R)).trans
    ((LinearEquiv.refl Rᵐᵒᵖ _).prodCongr (rangeMulVecBilinOneEquiv (Fin k) R))
  exact ⟨fun ⟨ψ⟩ ↦ ⟨eqLeft.trans (ψ.trans eqRight.symm)⟩,
    fun ⟨ψ⟩ ↦ ⟨eqLeft.symm.trans (ψ.trans eqRight)⟩⟩

end Semiring

section Ring

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring R]

/-- **Equivalent idempotents become unit-conjugate after zero-block stabilization.** If `e` and
`f` are equivalent idempotents, the involution `!![1 - e, x; y, 1 - f]` conjugates `e ⊕ 0` to
`0 ⊕ f`. -/
theorem IdempotentEquivalent.exists_units_conj_fromBlocks_zero
    {e : Matrix m m R} {f : Matrix n n R} (h : IdempotentEquivalent e f) :
    ∃ u : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ,
      u.val * Matrix.fromBlocks e 0 0 0 * u⁻¹.val = Matrix.fromBlocks 0 0 0 f := by
  obtain ⟨x, y, hxy, hyx, hex, -, -, hye⟩ := idempotentEquivalent_iff.mp h
  have hinv := fromBlocks_one_sub_mul_self_of_mul_eq hxy hyx hex hye
  refine ⟨⟨Matrix.fromBlocks (1 - e) x y (1 - f), Matrix.fromBlocks (1 - e) x y (1 - f),
    hinv, hinv⟩, ?_⟩
  exact fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq hxy hyx hye

/-- **Equivalence of an idempotent with another matrix is stabilized similarity.** For an
idempotent matrix `e`, `e` is equivalent to `f` if and only if `e ⊕ 0` and `0 ⊕ f` are conjugate
by an invertible block matrix. -/
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
    have h0f := hconj.isIdempotentElem_left.eq
    rw [fromBlocks_multiply] at h0f
    rw [IsIdempotentElem]
    simpa using congrArg toBlocks₂₂ h0f
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
