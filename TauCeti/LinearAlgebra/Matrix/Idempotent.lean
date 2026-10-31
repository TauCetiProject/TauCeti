/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Finitely generated projective modules from idempotent matrices

Let `A` be a semiring, not necessarily commutative. An idempotent matrix `e : Matrix ι ι A` acts on
row vectors `ι → A` on the right, and this action is linear for the left `A`-module structure.
Its range, the row vectors fixed by `e`, is a direct summand of `ι → A`, hence a finitely
generated projective left `A`-module. This file proves the two facts that make idempotent
matrices a presentation of finitely generated projective modules, the stable-idempotent
description of algebraic `K₀`:

* every finitely generated projective module is isomorphic to such a range;
* two such ranges are isomorphic exactly when the idempotents are *algebraically equivalent*,
  `e = x * y` and `f = y * x` for rectangular matrices `x` and `y`.

The range for the block-diagonal matrix `Matrix.fromBlocks e 0 0 f` is the product of the ranges,
so direct sums of modules correspond to block sums of idempotents.

## Main results

* `IsIdempotentElem.mem_range_vecMulLinear_iff`: the range of an idempotent matrix consists of its
  fixed row vectors.
* `IsIdempotentElem.linearMap_apply_eq_vecMul`: a linear map out of this range is right
  multiplication by the matrix of its values on the rows.
* `Matrix.nonempty_linearEquiv_range_vecMulLinear_iff`: the ranges of two idempotent matrices are
  isomorphic if and only if the matrices are algebraically equivalent.
* `Module.Finite.exists_linearEquiv_range_vecMulLinear`: a finitely generated projective module is
  isomorphic to the range of an idempotent matrix.
* `Matrix.mem_range_vecMulLinear_fromBlocks_iff`: a row vector lies in the range of a
  block-diagonal matrix exactly when its two parts lie in the ranges of the blocks.
* `Matrix.rangeVecMulLinearFromBlocksEquiv`: the range of a block-diagonal matrix is the product of
  the ranges of its blocks.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. Weibel, *The K-book*, Chapter II, §2.
-/

public section

open LinearMap Matrix

section Idempotent

variable {A : Type*} [Semiring A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Right multiplication of row vectors by an idempotent matrix is an idempotent endomorphism. -/
theorem IsIdempotentElem.vecMulLinear {e : Matrix ι ι A} (he : IsIdempotentElem e) :
    IsIdempotentElem e.vecMulLinear := by
  ext v : 1
  simp [Module.End.mul_apply, Matrix.vecMul_vecMul, he.eq]

/-- The range of right multiplication by an idempotent matrix `e` consists of the row vectors
fixed by `e`. -/
theorem IsIdempotentElem.mem_range_vecMulLinear_iff {e : Matrix ι ι A} (he : IsIdempotentElem e)
    {v : ι → A} : v ∈ range e.vecMulLinear ↔ v ᵥ* e = v :=
  he.vecMulLinear.mem_range_iff

/-- Each row of an idempotent matrix lies in its range. -/
theorem IsIdempotentElem.row_mem_range_vecMulLinear {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (i : ι) : e i ∈ range e.vecMulLinear := by
  rw [he.mem_range_vecMulLinear_iff, ← Matrix.mul_apply_eq_vecMul, he.eq]

omit [Fintype ι] in
/-- A linear map from the range of an idempotent matrix `f` to row vectors is right multiplication
by the matrix of its values on the rows of `f`. -/
theorem IsIdempotentElem.linearMap_apply_eq_vecMul {f : Matrix κ κ A} (hf : IsIdempotentElem f)
    (g : range f.vecMulLinear →ₗ[A] (ι → A)) {w : κ → A} (hw : w ∈ range f.vecMulLinear) :
    g ⟨w, hw⟩ = w ᵥ* .of fun j ↦ g ⟨f j, hf.row_mem_range_vecMulLinear j⟩ := by
  have hsum : (⟨w, hw⟩ : range f.vecMulLinear) =
      ∑ j, w j • ⟨f j, hf.row_mem_range_vecMulLinear j⟩ := by
    ext1
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, ← vecMul_eq_sum]
    exact ((hf.mem_range_vecMulLinear_iff).1 hw).symm
  rw [hsum, map_sum]
  simp only [map_smul]
  ext k
  simp [vecMul_eq_sum]

namespace Matrix

/-- The matrix whose rows are the images of the rows of an idempotent matrix `e` under an
isomorphism of ranges. -/
private def rowImage {e : Matrix ι ι A} {f : Matrix κ κ A} (he : IsIdempotentElem e)
    (ψ : range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear) : Matrix ι κ A :=
  .of fun i ↦ ψ ⟨e i, he.row_mem_range_vecMulLinear i⟩

private theorem rowImage_mul_rowImage_symm {e : Matrix ι ι A} {f : Matrix κ κ A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (ψ : range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear) :
    rowImage he ψ * rowImage hf ψ.symm = e := by
  ext i j
  rw [mul_apply_eq_vecMul]
  have h := hf.linearMap_apply_eq_vecMul ((range e.vecMulLinear).subtype ∘ₗ ψ.symm.toLinearMap)
    (ψ ⟨e i, he.row_mem_range_vecMulLinear i⟩).2
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, Subtype.coe_eta,
    LinearEquiv.symm_apply_apply] at h
  exact congrFun h.symm j

/-- **Algebraic equivalence of idempotent matrices.** The ranges of right multiplication by two
idempotent matrices `e` and `f` are isomorphic left `A`-modules if and only if `e = x * y` and
`f = y * x` for some rectangular matrices `x` and `y`. -/
theorem nonempty_linearEquiv_range_vecMulLinear_iff {e : Matrix ι ι A} {f : Matrix κ κ A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    Nonempty (range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear) ↔
      ∃ (x : Matrix ι κ A) (y : Matrix κ ι A), x * y = e ∧ y * x = f := by
  constructor
  · rintro ⟨ψ⟩
    refine ⟨rowImage he ψ, rowImage hf ψ.symm, rowImage_mul_rowImage_symm he hf ψ, ?_⟩
    simpa using rowImage_mul_rowImage_symm hf he ψ.symm
  · rintro ⟨x, y, hxy, hyx⟩
    -- Right multiplication by `x` and by `y` restrict to mutually inverse maps of the ranges.
    have hx : ∀ v ∈ range e.vecMulLinear, v ᵥ* x ∈ range f.vecMulLinear := fun v hv ↦ by
      rw [hf.mem_range_vecMulLinear_iff, vecMul_vecMul, ← hyx, ← Matrix.mul_assoc, hxy,
        ← vecMul_vecMul, (he.mem_range_vecMulLinear_iff).1 hv]
    have hy : ∀ w ∈ range f.vecMulLinear, w ᵥ* y ∈ range e.vecMulLinear := fun w hw ↦ by
      rw [he.mem_range_vecMulLinear_iff, vecMul_vecMul, ← hxy, ← Matrix.mul_assoc, hyx,
        ← vecMul_vecMul, (hf.mem_range_vecMulLinear_iff).1 hw]
    exact ⟨{
      toFun v := ⟨v ᵥ* x, hx v v.2⟩
      invFun w := ⟨w ᵥ* y, hy w w.2⟩
      map_add' v v' := Subtype.ext (add_vecMul _ _ _)
      map_smul' a v := Subtype.ext (smul_vecMul _ _ _)
      left_inv v := Subtype.ext <| by
        simp [vecMul_vecMul, hxy, (he.mem_range_vecMulLinear_iff).1 v.2]
      right_inv w := Subtype.ext <| by
        simp [vecMul_vecMul, hyx, (hf.mem_range_vecMulLinear_iff).1 w.2] }⟩

variable {ι' κ' : Type*}

/-- A row vector lies in the range of right multiplication by the block-diagonal matrix
`Matrix.fromBlocks e 0 0 f` exactly when its two parts lie in the ranges of `e` and of `f`. -/
theorem mem_range_vecMulLinear_fromBlocks_iff {e : Matrix ι ι' A} {f : Matrix κ κ' A}
    {v : ι' ⊕ κ' → A} :
    v ∈ range (fromBlocks e 0 0 f).vecMulLinear ↔
      v ∘ Sum.inl ∈ range e.vecMulLinear ∧ v ∘ Sum.inr ∈ range f.vecMulLinear := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨u ∘ Sum.inl, ?_⟩, ⟨u ∘ Sum.inr, ?_⟩⟩ <;>
      rw [vecMulLinear_apply, vecMulLinear_apply, ← Sum.elim_comp_inl_inr u, vecMul_fromBlocks] <;>
      simp
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨Sum.elim a b, ?_⟩
    rw [← Sum.elim_comp_inl_inr v, ← ha, ← hb]
    simp [vecMul_fromBlocks]

/-- **Block sums of matrices.** The range of right multiplication by the block-diagonal matrix
`Matrix.fromBlocks e 0 0 f` is the product of the ranges of `e` and of `f`. -/
def rangeVecMulLinearFromBlocksEquiv (e : Matrix ι ι' A) (f : Matrix κ κ' A) :
    range (fromBlocks e 0 0 f).vecMulLinear ≃ₗ[A]
      range e.vecMulLinear × range f.vecMulLinear where
  toFun v := (⟨(v : ι' ⊕ κ' → A) ∘ Sum.inl, (mem_range_vecMulLinear_fromBlocks_iff.1 v.2).1⟩,
    ⟨(v : ι' ⊕ κ' → A) ∘ Sum.inr, (mem_range_vecMulLinear_fromBlocks_iff.1 v.2).2⟩)
  invFun p := ⟨Sum.elim p.1 p.2, mem_range_vecMulLinear_fromBlocks_iff.2 ⟨p.1.2, p.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (Sum.elim_comp_inl_inr _)
  right_inv _ := rfl

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_apply_fst (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (v : range (fromBlocks e 0 0 f).vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f v).1 : ι' → A) = (v : ι' ⊕ κ' → A) ∘ Sum.inl :=
  (rfl)

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_apply_snd (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (v : range (fromBlocks e 0 0 f).vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f v).2 : κ' → A) = (v : ι' ⊕ κ' → A) ∘ Sum.inr :=
  (rfl)

@[simp]
theorem coe_rangeVecMulLinearFromBlocksEquiv_symm_apply (e : Matrix ι ι' A) (f : Matrix κ κ' A)
    (p : range e.vecMulLinear × range f.vecMulLinear) :
    ((rangeVecMulLinearFromBlocksEquiv e f).symm p : ι' ⊕ κ' → A) =
      Sum.elim (p.1 : ι' → A) (p.2 : κ' → A) :=
  (rfl)

end Matrix

end Idempotent

namespace Module.Finite

variable (A P : Type*) [Semiring A] [AddCommMonoid P] [Module A P] [Module.Finite A P]
  [Module.Projective A P]

/-- **Finitely generated projective modules come from idempotent matrices.** A finitely generated
projective left `A`-module is isomorphic to the range of right multiplication by an idempotent
square matrix over `A`. -/
theorem exists_linearEquiv_range_vecMulLinear :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e ∧
      Nonempty (P ≃ₗ[A] LinearMap.range e.vecMulLinear) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := exists_comp_eq_id_of_projective A P
  -- `e` is the matrix of the idempotent endomorphism `g ∘ f` of the row vectors.
  refine ⟨n, (g ∘ₗ f).toMatrixRight', isIdempotentElem_toMatrixRight'_comp hfg, ?_⟩
  have he : (g ∘ₗ f).toMatrixRight'.vecMulLinear = g ∘ₗ f :=
    LinearMap.ext (vecMul_toMatrixRight' _)
  rw [he, range_comp_of_range_eq_top g (range_eq_top.2 hf)]
  exact ⟨LinearEquiv.ofInjective g hg⟩

end Module.Finite
