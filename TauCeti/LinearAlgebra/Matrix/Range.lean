/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Basic

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import TauCeti.Data.Matrix.Mul

/-!
# Factoring matrices through a column range

A matrix `L'` factors as `L * G` whenever each of its columns belongs to the range of
matrix-vector multiplication by `L`. The column index type of `L'` need not be finite. Over an
`S`-algebra, if the columns of `L'` lie in the `S`-span of those of `L`, the factor `G` can be taken
over `S`. Over a field, a matrix with independent columns has a left inverse. We also
give a criterion, splitting off the top row, for the column range of a matrix to be a given
submodule.

Over an arbitrary semiring `R` (not necessarily commutative), this file also collects the basic
properties of row ranges `LinearMap.range M.vecMulLinear` and right-module column ranges
`LinearMap.range (M.mulVecBilin R Rᵐᵒᵖ)` (over `Rᵐᵒᵖ`): functoriality under entrywise ring
homomorphisms, block-diagonal decompositions, the equivalence between row ranges over `Rᵐᵒᵖ` and
column ranges over `R`, finiteness, `Matrix.submatrix`, the identity matrix
`1 : Matrix m m R`, and column-range `finrank` formulas under `StrongRankCondition Rᵐᵒᵖ`.

Over a field, a vector `v` lies in the column range of `A` exactly when it is orthogonal, for the
dot product, to every `z` with `z ᵥ* A = 0` (the Fredholm alternative): a linear functional
vanishing on the range is a dot product with such a `z`.

## Main definitions

* `Matrix.rangeVecMulLinearMap`, `Matrix.rangeVecMulLinearEquiv`, and
  `Matrix.rangeMulVecBilinMap`: semilinear maps and equivalences on row and column ranges induced
  by applying a ring homomorphism or ring equivalence coordinatewise.
* `Matrix.rangeVecMulLinearFromBlocksEquiv` and `Matrix.rangeMulVecBilinFromBlocksEquiv`: product
  decompositions for the row and column ranges of `Matrix.fromBlocks e 0 0 f`.
* `Matrix.rangeVecMulLinearTransposeMapOpEquiv`: `Rᵐᵒᵖ`-linear isomorphism identifying the row
  range of `eᵀ.map MulOpposite.op` with the column range of `e`.
* `Matrix.rangeMulVecBilinSubmatrixEquiv`: `Rᵐᵒᵖ`-linear isomorphism of column ranges when both
  rows and columns are reindexed along equivalences via `Matrix.submatrix`.
* `Matrix.rangeMulVecBilinOneEquiv` and `Matrix.rangeMulVecBilinSingleOneEquiv`: the column ranges
  of `1 : Matrix m m R` and of a diagonal matrix unit `Eᵢᵢ` are `m → Rᵐᵒᵖ` and `Rᵐᵒᵖ`.
* `Matrix.rangeMulVecBilinOfUniqueEquivSpan`: the column range of the `1 × 1` matrix
  `Matrix.uniqueRingEquiv.symm a` with entry `a` is the principal right ideal `aR`.

## Main result

* `Matrix.col_mem_range_mulVecLin`: every column of `L` lies in the range of `L.mulVecLin`.
* `Matrix.range_mulVecLin_transpose_of_cons_cons`: the column range of the matrix with columns
  `u` and `v` is the span of `u` and `v`.
* `Matrix.row_mem_range_vecMulLinear`: every row of `e` lies in the range of `e.vecMulLinear`.
* `Matrix.col_mem_range_mulVecBilin`: every column of `M` lies in the range of
  `M.mulVecBilin R Rᵐᵒᵖ`.
* `Matrix.mem_range_vecMulLinear_fromBlocks_iff` and `Matrix.mem_range_mulVecBilin_fromBlocks_iff`:
  membership in the row and column ranges of a block-diagonal matrix.
* `Matrix.mem_range_mulVecBilin_iff_op_comp`: membership in the column range of `M` in terms of
  the row range of `Mᵀ.map op`.
* `Matrix.finite_range_mulVecBilin`: the column range of a matrix with finitely many columns is a
  finitely generated right `R`-module.
* `Matrix.finrank_range_mulVecBilin_one` and `Matrix.finrank_range_mulVecBilin_single_one`:
  column-range `finrank` of `1` and of diagonal matrix units `Eᵢᵢ` under
  `StrongRankCondition Rᵐᵒᵖ`.
* `Matrix.exists_mul_eq_of_range_le`: construct the right factor from column preimages.
* `Matrix.exists_mul_map_eq_of_span_le`: if the columns of `C` lie in the `S`-span of those of
  `B`, then `C = B U` with `U` over `S`.
* `Matrix.exists_mul_eq_one_of_linearIndependent_col`,
  `Matrix.exists_mul_map_mul_eq_one_of_linearIndependent_col`: over a field, a matrix with
  independent columns has a left inverse, and so does its product with an invertible matrix over
  an algebra.
* `Matrix.mul_left_cancel_of_mulVec_injective`: cancel an injective left factor even for
  matrices with an empty output-column index type.
* `Matrix.range_mulVecLin_eq_of_succ`: a matrix with columns in a submodule `L` of `R^(n+1)` has
  column range `L` if it reaches every vector of `L` below the top row and every vector of `L`
  supported on the top row.
* `Matrix.mem_range_mulVecLin_iff_forall_vecMul_eq_zero`: over a field, `v` is in the column range
  of `A` if and only if `z ⬝ᵥ v = 0` whenever `z ᵥ* A = 0`.
-/

public section

namespace Matrix

section LeftCancellation

variable {R m ι κ : Type*} [NonUnitalSemiring R] [Fintype ι]

/-- If matrix-vector multiplication by `L` is injective, multiplication by `L`
cancels on the left, even when the right-hand matrices have no columns. -/
theorem mul_left_cancel_of_mulVec_injective
    {L : Matrix m ι R} (hL : Function.Injective L.mulVec)
    {X Y : Matrix ι κ R} (hXY : L * X = L * Y) : X = Y := by
  classical
  rcases isEmpty_or_nonempty κ with hEmpty | hNonempty
  · ext i j
    exact (hEmpty.false j).elim
  · let : Inhabited κ := ⟨Classical.choice hNonempty⟩
    exact (mul_right_injective_iff_mulVec_injective.mpr hL) hXY

end LeftCancellation

variable {R m ι κ : Type*} [CommSemiring R] [Fintype ι]

/-- Every column of `L` lies in the range of matrix-vector multiplication by `L`. -/
theorem col_mem_range_mulVecLin (L : Matrix m ι R) (j : ι) :
    L.col j ∈ LinearMap.range L.mulVecLin := by
  classical
  exact ⟨Pi.single j 1, by rw [mulVecLin_apply, mulVec_single_one]⟩

/-- The column range of the matrix with the two columns `u` and `v` is the span of `u` and `v`. -/
theorem range_mulVecLin_transpose_of_cons_cons (u v : m → R) :
    LinearMap.range (of ![u, v])ᵀ.mulVecLin = Submodule.span R {u, v} := by
  rw [range_mulVecLin, col_transpose, ← range_cons_cons_empty u v ![]]
  rfl

/-- If every column of `L'` lies in the range of `L`, then `L' = L * G` for some `G`.
The index type of the columns of `L'` need not be finite. -/
theorem exists_mul_eq_of_range_le {L : Matrix m ι R} {L' : Matrix m κ R}
    (h : ∀ j : κ, L'.col j ∈ LinearMap.range L.mulVecLin) :
    ∃ G : Matrix ι κ R, L * G = L' := by
  classical
  have hpre (j : κ) : ∃ v : ι → R, L.mulVec v = L'.col j := h j
  choose v hv using hpre
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hv j) i

/-- Let `A` be an `S`-algebra. If the columns of `C` lie in the `S`-span of the columns of `B`,
then `C = B U` for a matrix `U` with entries in `S`. Adapted from
`New.Filling.exists_isIntMatrix_mul_eq` in `src/New/Spanning/RemainingTerms/Discriminants.lean`
of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). -/
theorem exists_mul_map_eq_of_span_le {S A : Type*} [CommSemiring S] [CommSemiring A]
    [Algebra S A] {B : Matrix m ι A} {C : Matrix m κ A}
    (h : Submodule.span S (Set.range C.col) ≤ Submodule.span S (Set.range B.col)) :
    ∃ U : Matrix ι κ S, B * U.map (algebraMap S A) = C := by
  choose c hc using fun j ↦
    Submodule.mem_span_range_iff_exists_fun S |>.1 (h (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Matrix.of fun i j ↦ c j i, Matrix.ext fun k j ↦ ?_⟩
  have := congrFun (hc j) k
  simp only [Finset.sum_apply, Pi.smul_apply, col_apply] at this
  simp only [Algebra.smul_def] at this
  simp only [Matrix.mul_apply, map_apply, of_apply, ← this, mul_comm]

section Field

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

/-- **The Fredholm alternative for matrices.** Over a field, `v` lies in the column range of `A`
if and only if it is orthogonal, for the dot product, to every `z` with `z ᵥ* A = 0`. -/
theorem mem_range_mulVecLin_iff_forall_vecMul_eq_zero (A : Matrix m n K) (v : m → K) :
    v ∈ LinearMap.range A.mulVecLin ↔ ∀ z, z ᵥ* A = 0 → z ⬝ᵥ v = 0 := by
  classical
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨y, rfl⟩ z hz
    rw [mulVecLin_apply, dotProduct_mulVec, hz, zero_dotProduct]
  · refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ v).mp fun φ hφ => ?_
    -- Every linear functional on `m → K` is the dot product with some `z`.
    obtain ⟨z, rfl⟩ := (dotProductEquiv K m).surjective φ
    refine h z (funext fun j => ?_)
    have := (Submodule.mem_dualAnnihilator _).mp hφ _ (LinearMap.mem_range_self _ (Pi.single j 1))
    rwa [dotProductEquiv_apply_apply, mulVecLin_apply, dotProduct_mulVec,
      dotProduct_single_one] at this

omit [Fintype n] in
/-- A matrix over a field with linearly independent columns has a left inverse. -/
theorem exists_mul_eq_one_of_linearIndependent_col [Finite n] [DecidableEq n] {x : Matrix m n K}
    (hx : LinearIndependent K x.col) : ∃ l : Matrix n m K, l * x = 1 := by
  classical
  cases nonempty_fintype n
  obtain ⟨g, hg⟩ := x.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hx))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' x, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
    LinearMap.toMatrix'_id]

/-- Let `A` be a `K`-algebra. If `x` is a matrix over the field `K` with linearly independent
columns and `a` is an invertible matrix over `A`, then `x a`, read over `A`, has a left inverse.
Adapted from `New.Filling.hasLeftInv_finAdeleMatrix_mul` in
`src/New/Spanning/RemainingTerms/Discriminants.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). -/
theorem exists_mul_map_mul_eq_one_of_linearIndependent_col {A : Type*} [CommRing A]
    [Algebra K A] [DecidableEq n] {x : Matrix m n K} (hx : LinearIndependent K x.col)
    (a : GL n A) : ∃ l : Matrix n m A, l * (x.map (algebraMap K A) * (a : Matrix n n A)) = 1 := by
  obtain ⟨l, hl⟩ := exists_mul_eq_one_of_linearIndependent_col hx
  refine ⟨((a⁻¹ : GL n A) : Matrix n n A) * l.map (algebraMap K A), ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (l.map _), ← Matrix.map_mul, hl,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  exact a.inv_mul

end Field

section Succ

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- A matrix `H` with columns in a submodule `L` of `R^(n+1)` has column range `L` if every vector
of `L` agrees with a vector of the column range below the top row, and every vector of `L`
supported on the top row lies in the column range. -/
theorem range_mulVecLin_eq_of_succ {n : ℕ} {L : Submodule R (Fin (n + 1) → R)}
    {H : Matrix (Fin (n + 1)) ι R} (hcol : ∀ j, H.col j ∈ L)
    (htail : ∀ x ∈ L, ∃ c, ∀ i : Fin n, (H *ᵥ c) i.succ = x i.succ)
    (hsingle : ∀ a, Pi.single 0 a ∈ L → Pi.single 0 a ∈ LinearMap.range H.mulVecLin) :
    LinearMap.range H.mulVecLin = L := by
  have hle : LinearMap.range H.mulVecLin ≤ L := by
    rw [range_mulVecLin, Submodule.span_le, Set.range_subset_iff]
    exact hcol
  refine le_antisymm hle fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := htail x hx
  -- The difference of `x` and `H *ᵥ c` is supported on the top row.
  have hy : x - H *ᵥ c = Pi.single 0 ((x - H *ᵥ c) 0) := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [hc i]
  have hmem := hsingle _ (hy ▸ sub_mem hx (hle ⟨c, rfl⟩))
  rw [← hy] at hmem
  simpa using add_mem hmem (LinearMap.mem_range_self H.mulVecLin c)

end Succ

section RowRange

open LinearMap

variable {A : Type*} [Semiring A] {ι κ ι' κ' : Type*} [Fintype ι]

/-- Each row of a matrix lies in the range of right multiplication by it: it is the image of the
corresponding standard basis vector. -/
theorem row_mem_range_vecMulLinear (e : Matrix ι κ A) (i : ι) :
    e i ∈ range e.vecMulLinear := by
  classical
  exact ⟨Pi.single i 1, Matrix.single_one_vecMul i e⟩

/-- The `f`-semilinear map between the ranges of right multiplication of row vectors by a matrix
`e` and by its entrywise image `e.map f` under a ring homomorphism `f`, applying `f` to every
coordinate. For an idempotent `e` this is the map `Aⁿ e → Bⁿ f(e)`. -/
def rangeVecMulLinearMap {B : Type*} [Semiring B] (e : Matrix ι ι' A) (f : A →+* B) :
    range e.vecMulLinear →ₛₗ[f] range (e.map f).vecMulLinear where
  toFun v := ⟨f ∘ v, by
    obtain ⟨u, hu⟩ := v.property
    exact ⟨f ∘ u, funext fun i ↦ by simp [← hu, RingHom.map_vecMul]⟩⟩
  map_add' _ _ := Subtype.ext <| funext fun _ ↦ by simp
  map_smul' _ _ := Subtype.ext <| funext fun _ ↦ by simp

@[simp]
theorem coe_rangeVecMulLinearMap_apply {B : Type*} [Semiring B] (e : Matrix ι ι' A) (f : A →+* B)
    (v : range e.vecMulLinear) : (e.rangeVecMulLinearMap f v : ι' → B) = f ∘ v :=
  (rfl)

/-- A ring equivalence `σ : A ≃+* B` induces a `σ`-semilinear isomorphism between the row ranges
of a rectangular matrix `e` and of `e.map σ`, using `rangeVecMulLinearMap` in both directions. -/
def rangeVecMulLinearEquiv {B : Type*} [Semiring B] (e : Matrix ι ι' A) (σ : A ≃+* B) :
    haveI := RingHomInvPair.of_ringEquiv σ
    haveI := RingHomInvPair.of_ringEquiv_symm σ
    range e.vecMulLinear ≃ₛₗ[(σ : A →+* B)] range (e.map σ).vecMulLinear :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f := e.rangeVecMulLinearMap (σ : A →+* B)
  let g := (e.map σ).rangeVecMulLinearMap (σ.symm : B →+* A)
  { toFun := fun v ↦ ⟨(f v : ι' → B), (f v).property⟩
    invFun := fun w ↦ ⟨(g w : ι' → A), by
      simpa [Matrix.map_map, Function.comp_def] using (g w).property⟩
    map_add' := fun _ _ ↦ Subtype.ext <| funext fun _ ↦ map_add σ _ _
    map_smul' := fun _ _ ↦ Subtype.ext <| funext fun _ ↦ map_mul σ _ _
    left_inv := fun _ ↦ Subtype.ext <| funext fun _ ↦ σ.symm_apply_apply _
    right_inv := fun _ ↦ Subtype.ext <| funext fun _ ↦ σ.apply_symm_apply _ }

@[simp]
theorem coe_rangeVecMulLinearEquiv_apply {B : Type*} [Semiring B] (e : Matrix ι ι' A)
    (σ : A ≃+* B) (v : range e.vecMulLinear) :
    (e.rangeVecMulLinearEquiv σ v : ι' → B) = σ ∘ v := (rfl)

@[simp]
theorem coe_rangeVecMulLinearEquiv_symm_apply {B : Type*} [Semiring B] (e : Matrix ι ι' A)
    (σ : A ≃+* B) (w : range (e.map σ).vecMulLinear) :
    ((e.rangeVecMulLinearEquiv σ).symm w : ι' → A) = σ.symm ∘ w := (rfl)

section FromBlocks

variable [Fintype κ]

/-- A row vector lies in the range of right multiplication by the block-diagonal matrix
`Matrix.fromBlocks e 0 0 f` exactly when its two parts lie in the ranges of `e` and of `f`. -/
theorem mem_range_vecMulLinear_fromBlocks_iff {e : Matrix ι ι' A} {f : Matrix κ κ' A}
    {v : ι' ⊕ κ' → A} :
    v ∈ range (fromBlocks e 0 0 f).vecMulLinear ↔
      v ∘ Sum.inl ∈ range e.vecMulLinear ∧ v ∘ Sum.inr ∈ range f.vecMulLinear := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨u ∘ Sum.inl, ?_⟩, ⟨u ∘ Sum.inr, ?_⟩⟩ <;>
      rw [vecMulLinear_apply, vecMulLinear_apply, ← Sum.elim_comp_inl_inr u,
        vecMul_fromBlocks] <;> simp
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨Sum.elim a b, ?_⟩
    rw [← Sum.elim_comp_inl_inr v, ← ha, ← hb]; simp [vecMul_fromBlocks]

/-- **Block sums of matrices.** The range of right multiplication by the block-diagonal matrix
`Matrix.fromBlocks e 0 0 f` is the product of the ranges of `e` and of `f`. -/
def rangeVecMulLinearFromBlocksEquiv (e : Matrix ι ι' A) (f : Matrix κ κ' A) :
    range (fromBlocks e 0 0 f).vecMulLinear ≃ₗ[A]
      range e.vecMulLinear × range f.vecMulLinear where
  toFun v := (⟨(v : ι' ⊕ κ' → A) ∘ Sum.inl, (mem_range_vecMulLinear_fromBlocks_iff.1 v.property).1⟩,
    ⟨(v : ι' ⊕ κ' → A) ∘ Sum.inr, (mem_range_vecMulLinear_fromBlocks_iff.1 v.property).2⟩)
  invFun p := ⟨Sum.elim p.1 p.2, mem_range_vecMulLinear_fromBlocks_iff.2 ⟨p.1.property,
      p.2.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (Sum.elim_comp_inl_inr _)
  right_inv _ := rfl

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_apply_fst (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (v : range (fromBlocks e 0 0 f).vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f v).1 : ι' → A) = (v : ι' ⊕ κ' → A) ∘ Sum.inl := (rfl)

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_apply_snd (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (v : range (fromBlocks e 0 0 f).vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f v).2 : κ' → A) = (v : ι' ⊕ κ' → A) ∘ Sum.inr := (rfl)

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_symm_apply (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (p : range e.vecMulLinear × range f.vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f).symm p : ι' ⊕ κ' → A) =
      Sum.elim (p.1 : ι' → A) (p.2 : κ' → A) := (rfl)

end FromBlocks

end RowRange

section ColumnRange

open LinearMap MulOpposite

variable {R : Type*} [Semiring R] {ι ι' κ κ' : Type*}

section Fintype

variable [Fintype ι]

/-- Each column of a matrix lies in the range of its right-module column action: it is the image
of the corresponding standard basis vector. -/
theorem col_mem_range_mulVecBilin (M : Matrix ι' ι R) (j : ι) :
    M.col j ∈ range (M.mulVecBilin R Rᵐᵒᵖ) := by
  classical
  exact ⟨Pi.single j 1, by rw [mulVecBilin_apply, mulVec_single_one]⟩

/-- **Columns as rows over the opposite ring.** For `e : Matrix ι' ι R`, the column range
`range (e.mulVecBilin R Rᵐᵒᵖ)` is `Rᵐᵒᵖ`-linearly isomorphic via coordinatewise `unop` to the
row range of `eᵀ.map op` over `Rᵐᵒᵖ`. -/
def rangeVecMulLinearTransposeMapOpEquiv (e : Matrix ι' ι R) :
    range (eᵀ.map MulOpposite.op).vecMulLinear ≃ₗ[Rᵐᵒᵖ] range (mulVecBilin R Rᵐᵒᵖ e) :=
  let L' : (ι' → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (ι' → R) :=
    .piCongrRight fun _ ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  let L : (ι → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (ι → R) :=
    .piCongrRight fun _ ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  have hL : L'.toLinearMap ∘ₗ (eᵀ.map MulOpposite.op).vecMulLinear =
      mulVecBilin R Rᵐᵒᵖ e ∘ₗ L.toLinearMap := by
    ext v i; simp [L, L', vecMul, mulVec, dotProduct]
  (L'.submoduleMap _).trans <| .ofEq _ _ <| by
    rw [← range_comp, hL, range_comp_of_range_eq_top _ L.range]

@[simp]
theorem coe_rangeVecMulLinearTransposeMapOpEquiv_apply (e : Matrix ι' ι R)
    (v : range (eᵀ.map MulOpposite.op).vecMulLinear) :
    (rangeVecMulLinearTransposeMapOpEquiv e v : ι' → R) = MulOpposite.unop ∘ v := (rfl)

@[simp]
theorem coe_rangeVecMulLinearTransposeMapOpEquiv_symm_apply (M : Matrix ι' ι R)
    (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeVecMulLinearTransposeMapOpEquiv M).symm v : ι' → Rᵐᵒᵖ) = op ∘ v := by
  conv_rhs =>
    rw [← (rangeVecMulLinearTransposeMapOpEquiv M).apply_symm_apply v,
      coe_rangeVecMulLinearTransposeMapOpEquiv_apply]
  ext i; simp

/-- A column vector `v` lies in the column range of `M` iff `op ∘ v` lies in the row range of
`Mᵀ.map op`. -/
theorem mem_range_mulVecBilin_iff_op_comp {M : Matrix ι' ι R} {v : ι' → R} :
    v ∈ range (M.mulVecBilin R Rᵐᵒᵖ) ↔ op ∘ v ∈ range (M.transpose.map op).vecMulLinear := by
  refine ⟨fun hv ↦ ?_, fun hw ↦ ?_⟩
  · simpa only [coe_rangeVecMulLinearTransposeMapOpEquiv_symm_apply] using
      ((rangeVecMulLinearTransposeMapOpEquiv M).symm ⟨v, hv⟩).property
  · convert (rangeVecMulLinearTransposeMapOpEquiv M ⟨op ∘ v, hw⟩).property using 1
    ext i; simp

/-- The column range of any matrix with finitely many columns is finitely generated over `Rᵐᵒᵖ`. -/
instance finite_range_mulVecBilin (M : Matrix ι' ι R) :
    Module.Finite Rᵐᵒᵖ (range (M.mulVecBilin R Rᵐᵒᵖ)) :=
  Module.Finite.equiv (rangeVecMulLinearTransposeMapOpEquiv M)

/-- Applying `f : R →+* S` entrywise gives a `RingHom.op f`-semilinear map between the column
ranges of `M` and `M.map f`. -/
def rangeMulVecBilinMap {S : Type*} [Semiring S] (M : Matrix ι' ι R) (f : R →+* S) :
    range (M.mulVecBilin R Rᵐᵒᵖ) →ₛₗ[RingHom.op f] range ((M.map f).mulVecBilin S Sᵐᵒᵖ) :=
  ((rangeVecMulLinearTransposeMapOpEquiv (M.map f)).toLinearMap.comp
    ((LinearEquiv.ofEq _ _ (congrArg (fun N ↦ range N.vecMulLinear)
      (transpose_map_op_map_ringHom_op M f))).toLinearMap.comp
      ((M.transpose.map op).rangeVecMulLinearMap (RingHom.op f)))).comp
    (rangeVecMulLinearTransposeMapOpEquiv M).symm.toLinearMap

@[simp]
theorem coe_rangeMulVecBilinMap_apply {S : Type*} [Semiring S] (M : Matrix ι' ι R) (f : R →+* S)
    (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinMap f v : ι' → S) = f ∘ v := by ext i; simp [rangeMulVecBilinMap]

/-- Reindexing rows and columns via `Matrix.submatrix` induces an `Rᵐᵒᵖ`-linear isomorphism
between column ranges, acting by precomposition with `σ`. -/
def rangeMulVecBilinSubmatrixEquiv {ι₂ ι₂' : Type*} [Fintype ι₂] (M : Matrix ι' ι R)
    (σ : ι₂' ≃ ι') (τ : ι₂ ≃ ι) :
    range (M.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range ((M.submatrix σ τ).mulVecBilin R Rᵐᵒᵖ) where
  toFun v := ⟨(v : ι' → R) ∘ σ, by
    obtain ⟨u, hu⟩ := v.property
    exact ⟨u ∘ τ, by simp [mulVecBilin_apply, submatrix_mulVec_equiv, Function.comp_assoc, ← hu]⟩⟩
  invFun w := ⟨(w : ι₂' → R) ∘ σ.symm, by
    obtain ⟨u, hu⟩ := w.property
    refine ⟨u ∘ τ.symm, ?_⟩
    have hM : (M.submatrix σ τ).submatrix σ.symm τ.symm = M := by simp
    calc
      mulVecBilin R Rᵐᵒᵖ M (u ∘ τ.symm)
        = (M.submatrix σ τ).submatrix σ.symm τ.symm *ᵥ (u ∘ τ.symm) := by
            rw [mulVecBilin_apply, hM]
      _ = (M.submatrix σ τ *ᵥ u) ∘ σ.symm := by
            simp [submatrix_mulVec_equiv, Function.comp_assoc]
      _ = (w : ι₂' → R) ∘ σ.symm := by
            simpa [mulVecBilin_apply] using congrArg (· ∘ σ.symm) hu⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := Subtype.ext <| funext fun i ↦ by simp
  right_inv w := Subtype.ext <| funext fun i₂ ↦ by simp

@[simp]
theorem coe_rangeMulVecBilinSubmatrixEquiv_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι₂' ≃ ι') (τ : ι₂ ≃ ι) (v : range (M.mulVecBilin R Rᵐᵒᵖ)) :
    (M.rangeMulVecBilinSubmatrixEquiv σ τ v : ι₂' → R) = (v : ι' → R) ∘ σ := (rfl)

@[simp]
theorem coe_rangeMulVecBilinSubmatrixEquiv_symm_apply {ι₂ ι₂' : Type*} [Fintype ι₂]
    (M : Matrix ι' ι R) (σ : ι₂' ≃ ι') (τ : ι₂ ≃ ι)
    (w : range ((M.submatrix σ τ).mulVecBilin R Rᵐᵒᵖ)) :
    ((M.rangeMulVecBilinSubmatrixEquiv σ τ).symm w : ι' → R) = (w : ι₂' → R) ∘ σ.symm := (rfl)

end Fintype

section FromBlocks

variable [Fintype ι] [Fintype κ]

/-- A column vector lies in the column range of `Matrix.fromBlocks e 0 0 f` iff its two halves
lie in the column ranges of `e` and `f`. -/
theorem mem_range_mulVecBilin_fromBlocks_iff {e : Matrix ι' ι R} {f : Matrix κ' κ R}
    {v : ι' ⊕ κ' → R} :
    v ∈ range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ) ↔
      v ∘ Sum.inl ∈ range (e.mulVecBilin R Rᵐᵒᵖ) ∧
        v ∘ Sum.inr ∈ range (f.mulVecBilin R Rᵐᵒᵖ) := by
  rw [mem_range_mulVecBilin_iff_op_comp]
  simp only [fromBlocks_transpose, transpose_zero, fromBlocks_map, Matrix.map_zero _ op_zero]
  rw [mem_range_vecMulLinear_fromBlocks_iff, mem_range_mulVecBilin_iff_op_comp,
    mem_range_mulVecBilin_iff_op_comp]
  rfl

/-- **Block sums on column ranges.** The column range of `Matrix.fromBlocks e 0 0 f` is the
product of the column ranges of `e` and `f`. -/
def rangeMulVecBilinFromBlocksEquiv (e : Matrix ι' ι R) (f : Matrix κ' κ R) :
    range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ]
      range (e.mulVecBilin R Rᵐᵒᵖ) × range (f.mulVecBilin R Rᵐᵒᵖ) :=
  (rangeVecMulLinearTransposeMapOpEquiv (fromBlocks e 0 0 f)).symm.trans <|
    (LinearEquiv.ofEq _ _ (congrArg (fun N : Matrix (ι ⊕ κ) (ι' ⊕ κ') Rᵐᵒᵖ ↦ range N.vecMulLinear)
      (by simp [fromBlocks_transpose, fromBlocks_map]))).trans <|
      (rangeVecMulLinearFromBlocksEquiv (e.transpose.map op) (f.transpose.map op)).trans <|
        (rangeVecMulLinearTransposeMapOpEquiv e).prodCongr
          (rangeVecMulLinearTransposeMapOpEquiv f)

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_apply_fst (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (v : range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f v).1 : ι' → R) = (v : ι' ⊕ κ' → R) ∘ Sum.inl := by
  ext i; simp [rangeMulVecBilinFromBlocksEquiv]

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_apply_snd (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (v : range ((fromBlocks e 0 0 f).mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f v).2 : κ' → R) = (v : ι' ⊕ κ' → R) ∘ Sum.inr := by
  ext i; simp [rangeMulVecBilinFromBlocksEquiv]

@[simp]
theorem coe_rangeMulVecBilinFromBlocksEquiv_symm_apply (e : Matrix ι' ι R) (f : Matrix κ' κ R)
    (p : range (e.mulVecBilin R Rᵐᵒᵖ) × range (f.mulVecBilin R Rᵐᵒᵖ)) :
    ((rangeMulVecBilinFromBlocksEquiv e f).symm p : ι' ⊕ κ' → R) =
      Sum.elim (p.1 : ι' → R) (p.2 : κ' → R) := by
  ext (i | i) <;> simp [rangeMulVecBilinFromBlocksEquiv]

end FromBlocks

end ColumnRange

/-- The column range of `1 : Matrix m m R` is `Rᵐᵒᵖ`-linearly isomorphic to `m → Rᵐᵒᵖ`. -/
def rangeMulVecBilinOneEquiv (m R : Type*) [Semiring R] [Fintype m] [DecidableEq m] :
    LinearMap.range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (m → Rᵐᵒᵖ) where
  toFun v := MulOpposite.op ∘ v
  invFun v := ⟨MulOpposite.unop ∘ v, ⟨MulOpposite.unop ∘ v, by simp⟩⟩
  map_add' _ _ := rfl
  map_smul' r v := funext fun i ↦ MulOpposite.op_smul r ((v : m → R) i)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem rangeMulVecBilinOneEquiv_apply {m R : Type*} [Semiring R] [Fintype m] [DecidableEq m]
    (v : LinearMap.range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) :
    rangeMulVecBilinOneEquiv m R v = MulOpposite.op ∘ (v : m → R) := (rfl)

@[simp]
theorem coe_rangeMulVecBilinOneEquiv_symm_apply {m R : Type*} [Semiring R] [Fintype m]
    [DecidableEq m] (v : m → Rᵐᵒᵖ) :
    ((rangeMulVecBilinOneEquiv m R).symm v : m → R) = MulOpposite.unop ∘ v := (rfl)

/-- When `Rᵐᵒᵖ` has the strong rank condition, `range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)`
has right `R`-rank `Fintype.card m`. -/
@[simp]
theorem finrank_range_mulVecBilin_one (R : Type*) [Semiring R] [StrongRankCondition Rᵐᵒᵖ]
    (m : Type*) [Fintype m] [DecidableEq m] :
    Module.finrank Rᵐᵒᵖ (LinearMap.range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) =
      Fintype.card m :=
  (rangeMulVecBilinOneEquiv m R).finrank_eq.trans (Module.finrank_fintype_fun_eq_card Rᵐᵒᵖ)

/-- The column range of a diagonal matrix unit `Eᵢᵢ` is `Rᵐᵒᵖ`-linearly isomorphic to `Rᵐᵒᵖ`,
via coordinate evaluation at `i` and `Pi.single i`. -/
def rangeMulVecBilinSingleOneEquiv (R : Type*) [Semiring R] {m : Type*} [Fintype m]
    [DecidableEq m] (i : m) :
    LinearMap.range ((single i i (1 : R)).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun w := MulOpposite.op ((w : m → R) i)
  invFun r := ⟨Pi.single i (MulOpposite.unop r), ⟨Pi.single i (MulOpposite.unop r), by
    rw [mulVecBilin_apply, Matrix.single_mulVec]
    ext j
    simp [Function.update_apply, Pi.single_apply]⟩⟩
  map_add' _ _ := MulOpposite.op_add _ _
  map_smul' r w := by simp
  left_inv w := Subtype.ext <| by
    obtain ⟨v, hv⟩ := w.property
    simp_rw [← hv, mulVecBilin_apply, Matrix.single_mulVec]
    ext j
    simp [Function.update_apply, Pi.single_apply]
  right_inv _ := by simp

@[simp]
theorem rangeMulVecBilinSingleOneEquiv_apply (R : Type*) [Semiring R] {m : Type*} [Fintype m]
    [DecidableEq m] (i : m) (w : LinearMap.range ((single i i (1 : R)).mulVecBilin R Rᵐᵒᵖ)) :
    rangeMulVecBilinSingleOneEquiv R i w = MulOpposite.op ((w : m → R) i) := (rfl)

@[simp]
theorem coe_rangeMulVecBilinSingleOneEquiv_symm_apply (R : Type*) [Semiring R] {m : Type*}
    [Fintype m] [DecidableEq m] (i : m) (r : Rᵐᵒᵖ) :
    ((rangeMulVecBilinSingleOneEquiv R i).symm r : m → R) =
      Pi.single i (MulOpposite.unop r) := (rfl)

/-- When `Rᵐᵒᵖ` has the strong rank condition, the column range of `Eᵢᵢ` has right `R`-rank `1`.
-/
@[simp]
theorem finrank_range_mulVecBilin_single_one (R : Type*) [Semiring R] [StrongRankCondition Rᵐᵒᵖ]
    {m : Type*} [Fintype m] [DecidableEq m] (i : m) :
    Module.finrank Rᵐᵒᵖ (LinearMap.range ((single i i (1 : R)).mulVecBilin R Rᵐᵒᵖ)) = 1 :=
  (rangeMulVecBilinSingleOneEquiv R i).finrank_eq.trans (Module.finrank_self Rᵐᵒᵖ)

/-- The column range of the `1 × 1` matrix `Matrix.uniqueRingEquiv.symm a` with entry `a` is the
principal right ideal `aR`, a submodule of `Rᵐᵒᵖ`: a column is sent to the opposite of its unique
entry. -/
def rangeMulVecBilinOfUniqueEquivSpan (R : Type*) [Semiring R] (m : Type*) [Unique m] (a : R) :
    LinearMap.range ((uniqueRingEquiv.symm a : Matrix m m R).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ]
      Submodule.span Rᵐᵒᵖ {MulOpposite.op a} where
  toFun w := ⟨MulOpposite.op ((w : m → R) default), by
    obtain ⟨v, hv⟩ := w.property
    rw [← hv, Submodule.mem_span_singleton]
    exact ⟨MulOpposite.op (v default), by simp [mulVec, dotProduct]⟩⟩
  invFun x := ⟨fun _ ↦ MulOpposite.unop (x : Rᵐᵒᵖ), by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 x.property
    exact ⟨fun _ ↦ MulOpposite.unop r, funext fun _ ↦ by simp [mulVec, dotProduct, ← hr]⟩⟩
  map_add' _ _ := Subtype.ext (MulOpposite.op_add _ _)
  map_smul' r w := Subtype.ext (by simp)
  left_inv w := Subtype.ext (funext fun i ↦ by simp [Unique.eq_default i])
  right_inv _ := Subtype.ext (by simp)

@[simp]
theorem coe_rangeMulVecBilinOfUniqueEquivSpan_apply (R : Type*) [Semiring R] (m : Type*)
    [Unique m] (a : R)
    (w : LinearMap.range ((uniqueRingEquiv.symm a : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) :
    (rangeMulVecBilinOfUniqueEquivSpan R m a w : Rᵐᵒᵖ) = MulOpposite.op ((w : m → R) default) :=
  (rfl)

@[simp]
theorem coe_rangeMulVecBilinOfUniqueEquivSpan_symm_apply (R : Type*) [Semiring R] (m : Type*)
    [Unique m] (a : R) (x : Submodule.span Rᵐᵒᵖ {MulOpposite.op a}) :
    ((rangeMulVecBilinOfUniqueEquivSpan R m a).symm x : m → R) =
      fun _ ↦ MulOpposite.unop (x : Rᵐᵒᵖ) :=
  (rfl)

end Matrix
