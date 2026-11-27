/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Block
public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Adjunction
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Frobenius reciprocity for the Hall algebra

Let `k` be a finite field and `b : n → ι` a ranking of a finite index set by a linear order. The
invertible matrices that are block upper triangular for `b` form the parabolic subgroup
`P_b = TauCeti.blockTriangularGroup k b` of `GL n k`, with diagonal blocks `g_a ∈ GL_{n_a}(k)`,
`n_a = #{i | b i = a}`. For class functions `A_a` on all square matrices (elements of
`TauCeti.HallAlgebra k`) and a class function `Y` on `GL n k`,

`⟨(∏_a A_a|_{n_a})|_{GL n k}, Y⟩_{GL n k} = ⟨g ↦ ∏_a A_a(g_a), Y|_{P_b}⟩_{P_b}`,

the product on the left taken with the induction product `∗`. So on `GL n k` the product `∗` of
the Hall algebra is Harish-Chandra (parabolic) induction from the Levi factor `∏_a GL_{n_a}(k)`.

## Main results

* `TauCeti.HallAlgebra.expect_toClassFunction_eq_rankInner`: the inner product `⟨A, A′⟩_{#n}` is
  the mean over `GL n k` for any finite index type `n`.
* `TauCeti.HallAlgebra.exists_toClassFunction_eq`: every class function on `GL n k` is the
  restriction of an element of the Hall algebra.
* `TauCeti.HallAlgebra.blockAverage_toLin'`: the block average at the classes of two square
  matrices is the mean over the upper right blocks of the block upper triangular matrices.
* `TauCeti.HallAlgebra.expect_toClassFunction_prod_rankPart` (Frobenius reciprocity): the
  identity above. The proof removes the largest level `m` and uses the adjunction
  `TauCeti.HallAlgebra.rankInner_mul_eq_rankInner_mulAdjoint`: an element of `P_b`, with the
  indices of level `m` put last, is a block matrix with zero lower left block, so `P_b` is
  parametrised by `P_{b′}` (`b′` the ranking of the other indices), `GL_{n_m}(k)` and the upper
  right block, and the mean over `P_b` is the mean over these three that computes the adjoint.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.
* A. V. Zelevinsky, *Representations of finite classical groups: a Hopf algebra approach*,
  Lecture Notes in Math. 869 (1981).
* Adapted from `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.exists_eq_evalGL` and `New.classInner_evalGL_prod`, with the
  parabolic subgroup `New.parabolic` and its blocks `New.blockHom` replaced by
  `TauCeti.blockTriangularGroup` and `TauCeti.BlockTriangularGroup.diagBlock`.
-/

public section

open Module Matrix TauCeti.SimilarityClass ComplexConjugate
open scoped BigOperators

namespace TauCeti

namespace HallAlgebra

/-! ### Class functions on `GL n k` -/

section GeneralLinear

variable {k : Type*} [Field k] (n : Type*) [Fintype n] [DecidableEq n]

/-- Every class function on `GL n k` is `g ↦ X(g)` for an element `X` of the Hall algebra. -/
theorem exists_toClassFunction_eq (Y : ClassFunction ℂ (GL n k)) :
    ∃ X : HallAlgebra k, X.toClassFunction n = Y := by
  classical
  refine ⟨fun c ↦ if h : ∃ g : GL n k, ofEnd (toLin' (g : Matrix n n k)) = c then
    Y.val h.choose else 0, Subtype.ext (funext fun g ↦ ?_)⟩
  have h : ∃ g' : GL n k, ofEnd (toLin' (g' : Matrix n n k)) = ofEnd (toLin' (g : Matrix n n k)) :=
    ⟨g, rfl⟩
  simp only [toClassFunction_apply, h, ↓reduceDIte]
  exact ClassFunction.eq_of_isConj Y (isConj_of_ofEnd_toLin'_eq h.choose_spec)

variable [Fintype k] [DecidableEq k]

/-- The inner product `⟨A, A′⟩_{#n}` is the mean over `g ∈ GL n k` of `conj (A g) · A′ g`. -/
theorem expect_toClassFunction_eq_rankInner (F H : HallAlgebra k) :
    𝔼 g : GL n k, conj ((F.toClassFunction n).val g) * (H.toClassFunction n).val g =
      rankInner (Fintype.card n) F H := by
  have : Finite (Module.End k (n → k)) := Module.finite_of_finite k
  have := Fintype.ofFinite (Module.End k (n → k))ˣ
  rw [← Module.finrank_fintype_fun_eq_card (R := k), rankInner_finrank_eq_expect]
  refine Fintype.expect_equiv Matrix.GeneralLinearGroup.toLin.toEquiv _ _ fun g ↦ ?_
  simp [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply']

end GeneralLinear

/-! ### Block averages of matrices -/

section Blocks

variable {k : Type*} [Field k] [Fintype k]
  {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]

/-- The block average at the classes of two square matrices `A` and `C` is the mean, over the
matrices `M`, of the value at the block upper triangular matrix with blocks `A`, `M` and `C`. -/
theorem blockAverage_toLin' (F : HallAlgebra k) (A : Matrix n₁ n₁ k) (C : Matrix n₂ n₂ k) :
    blockAverage F (ofEnd (toLin' A)) (ofEnd (toLin' C)) =
      𝔼 M : Matrix n₁ n₂ k, F (ofEnd (toLin' (fromBlocks A M 0 C))) := by
  have : Finite ((n₂ → k) →ₗ[k] n₁ → k) := Module.finite_of_finite k
  have := Fintype.ofFinite ((n₂ → k) →ₗ[k] n₁ → k)
  rw [blockAverage_ofEnd]
  exact (Fintype.expect_equiv Matrix.toLin'.toEquiv _ _ fun M ↦ by
    simp [ofEnd_toLin'_fromBlocks]).symm

variable [DecidableEq k]

/-- `∂_{#n₂,f} X` at the class of `A` is the mean over `c ∈ GL n₂ k` and the matrices `M` of
`conj (f c)` times `X` at the block upper triangular matrix with blocks `A`, `M` and `c`. -/
theorem mulAdjoint_toLin' (f X : HallAlgebra k) (A : Matrix n₁ n₁ k) :
    mulAdjoint (Fintype.card n₂) f X (ofEnd (toLin' A)) =
      𝔼 c : GL n₂ k, 𝔼 M : Matrix n₁ n₂ k, conj ((f.toClassFunction n₂).val c) *
        X (ofEnd (toLin' (fromBlocks A M 0 (c : Matrix n₂ n₂ k)))) := by
  rw [mulAdjoint_apply, ← expect_toClassFunction_eq_rankInner]
  refine Finset.expect_congr rfl fun c _ ↦ ?_
  rw [toClassFunction_apply (blockAverage X _), blockAverage_toLin', Finset.mul_expect]

end Blocks

/-! ### A parabolic subgroup from its blocks -/

section Assemble

variable {k : Type*} [Field k] {ι : Type*} [LinearOrder ι] {n : Type*} (b : n → ι) (m : ι)

/-- The indices of level other than `m`, followed by those of level `m`. -/
private def splitEquiv : {i // ¬b i = m} ⊕ {i // b i = m} ≃ n :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl fun i ↦ b i = m)

/-- The ranking of the indices of level other than `m`. -/
private abbrev restLevel : {i // ¬b i = m} → ι := fun i ↦ b i

variable {b m}

private theorem splitEquiv_symm_apply_of_ne {i : n} (hi : ¬b i = m) :
    (splitEquiv b m).symm i = .inl ⟨i, hi⟩ := by
  simp [splitEquiv, hi]

private theorem splitEquiv_symm_apply_of_eq {i : n} (hi : b i = m) :
    (splitEquiv b m).symm i = .inr ⟨i, hi⟩ := by
  simp [splitEquiv, hi]

variable (b m) [Fintype n] [DecidableEq n]

/-- The invertible matrix with diagonal blocks `h` (levels other than `m`) and `c` (level `m`) and
upper right block `M`, its indices reordered by `splitEquiv`. -/
private noncomputable def assembleGL
    (t : GL {i // ¬b i = m} k × GL {i // b i = m} k × Matrix {i // ¬b i = m} {i // b i = m} k) :
    GL n k :=
  Units.map (reindexAlgEquiv k k (splitEquiv b m)).toMonoidHom
    ((isUnit_fromBlocks_zero₂₁ (B := t.2.2)).2 ⟨t.1.isUnit, t.2.1.isUnit⟩).unit

private theorem coe_assembleGL
    (t : GL {i // ¬b i = m} k × GL {i // b i = m} k × Matrix {i // ¬b i = m} {i // b i = m} k) :
    ((assembleGL b m t : GL n k) : Matrix n n k) =
      (fromBlocks (t.1 : Matrix _ _ k) t.2.2 0 (t.2.1 : Matrix _ _ k)).submatrix
        (splitEquiv b m).symm (splitEquiv b m).symm := by
  simp [assembleGL]

variable {b m}

private theorem assembleGL_mem (hm : ∀ i, b i ≤ m)
    (t : blockTriangularGroup k (restLevel b m) × GL {i // b i = m} k ×
      Matrix {i // ¬b i = m} {i // b i = m} k) :
    assembleGL b m (t.1, t.2) ∈ blockTriangularGroup k b := by
  rw [mem_blockTriangularGroup_iff, coe_assembleGL]
  intro i j hij
  have h_tri := mem_blockTriangularGroup_iff.1 t.1.property
  by_cases hi : b i = m <;> by_cases hj : b j = m
  · exact absurd hij (by rw [hi, hj]; exact lt_irrefl m)
  · simp [splitEquiv_symm_apply_of_eq hi, splitEquiv_symm_apply_of_ne hj]
  · exact absurd hij (by rw [hj]; exact not_lt.2 (hm i))
  · simp only [submatrix_apply, splitEquiv_symm_apply_of_ne hi, splitEquiv_symm_apply_of_ne hj,
      fromBlocks_apply₁₁]
    exact h_tri (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij

/-- An element of `P_b` from an element of `P_{b′}`, an element of `GL_{n_m}(k)` and an upper
right block. -/
private noncomputable def assemble (hm : ∀ i, b i ≤ m)
    (t : blockTriangularGroup k (restLevel b m) × GL {i // b i = m} k ×
      Matrix {i // ¬b i = m} {i // b i = m} k) :
    blockTriangularGroup k b :=
  ⟨assembleGL b m (t.1, t.2), assembleGL_mem hm t⟩

private theorem assemble_injective (hm : ∀ i, b i ≤ m) :
    Function.Injective (assemble (k := k) hm) := by
  rintro ⟨h, c, M⟩ ⟨h', c', M'⟩ h_eq
  have h_mat := congrArg (fun g : blockTriangularGroup k b ↦
    ((g : GL n k) : Matrix n n k).submatrix (splitEquiv b m) (splitEquiv b m)) h_eq
  simp only [assemble, coe_assembleGL, submatrix_submatrix, Equiv.symm_comp_self,
    submatrix_id_id, fromBlocks_inj] at h_mat
  obtain ⟨h₁, h₂, -, h₄⟩ := h_mat
  simp only [Prod.mk.injEq]
  exact ⟨Subtype.ext (Units.ext h₁), Units.ext h₄, h₂⟩

private theorem assemble_surjective (hm : ∀ i, b i ≤ m) :
    Function.Surjective (assemble (k := k) hm) := by
  intro g
  -- With the indices reordered, `g` has a zero lower left block.
  set N := ((g : GL n k) : Matrix n n k).submatrix (splitEquiv b m) (splitEquiv b m) with hN
  have h_tri := mem_blockTriangularGroup_iff.1 g.property
  have h₂₁ : N.toBlocks₂₁ = 0 := by
    ext i j
    exact h_tri (((hm _).lt_of_ne j.property).trans_eq i.property.symm)
  have h_blocks : fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ 0 N.toBlocks₂₂ = N := by
    rw [← h₂₁, fromBlocks_toBlocks]
  have h_unit : IsUnit N.toBlocks₁₁ ∧ IsUnit N.toBlocks₂₂ := by
    have h_det : IsUnit N := by
      rw [isUnit_iff_isUnit_det, hN, det_submatrix_equiv_self]
      exact (isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    rw [← h_blocks] at h_det
    exact isUnit_fromBlocks_zero₂₁.1 h_det
  have h_mem : h_unit.1.unit ∈ blockTriangularGroup k (restLevel b m) :=
    mem_blockTriangularGroup_iff.2 fun i j hij ↦ h_tri (i := i.val) (j := j.val) hij
  refine ⟨(⟨_, h_mem⟩, h_unit.2.unit, N.toBlocks₁₂), Subtype.ext (Units.ext ?_)⟩
  simp only [assemble, coe_assembleGL, IsUnit.unit_spec]
  rw [h_blocks, hN, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]

private theorem assemble_bijective (hm : ∀ i, b i ≤ m) :
    Function.Bijective (assemble (k := k) hm) :=
  ⟨assemble_injective hm, assemble_surjective hm⟩

private theorem ofEnd_assemble (hm : ∀ i, b i ≤ m)
    (t : blockTriangularGroup k (restLevel b m) × GL {i // b i = m} k ×
      Matrix {i // ¬b i = m} {i // b i = m} k) :
    ofEnd (toLin' (((assemble hm t : blockTriangularGroup k b) : GL n k) : Matrix n n k)) =
      ofEnd (toLin' (fromBlocks
        ((t.1 : GL {i // ¬b i = m} k) : Matrix {i // ¬b i = m} {i // ¬b i = m} k) t.2.2 0
        (t.2.1 : Matrix {i // b i = m} {i // b i = m} k))) :=
  by rw [assemble, coe_assembleGL]; exact ofEnd_toLin'_submatrix _ _

private theorem diagBlock_assemble_self (hm : ∀ i, b i ≤ m)
    (t : blockTriangularGroup k (restLevel b m) × GL {i // b i = m} k ×
      Matrix {i // ¬b i = m} {i // b i = m} k) :
    BlockTriangularGroup.diagBlock b m (assemble hm t) = t.2.1 := by
  ext i j
  simp [assemble, coe_assembleGL, toSquareBlock_def, splitEquiv_symm_apply_of_eq i.property,
    splitEquiv_symm_apply_of_eq j.property]

private theorem ofEnd_diagBlock_assemble (hm : ∀ i, b i ≤ m)
    (t : blockTriangularGroup k (restLevel b m) × GL {i // b i = m} k ×
      Matrix {i // ¬b i = m} {i // b i = m} k) {a : ι} (ha : a ≠ m) :
    ofEnd (toLin' (BlockTriangularGroup.diagBlock b a (assemble hm t) :
        Matrix {i // b i = a} {i // b i = a} k)) =
      ofEnd (toLin' (BlockTriangularGroup.diagBlock (restLevel b m) a t.1 :
        Matrix {i : {i // ¬b i = m} // restLevel b m i = a}
          {i : {i // ¬b i = m} // restLevel b m i = a} k)) := by
  -- The indices of level `a` are the same for `b` and for the ranking of the other levels.
  let σ : {i // b i = a} ≃ {i : {i // ¬b i = m} // restLevel b m i = a} :=
    (Equiv.subtypeSubtypeEquivSubtype fun h ↦ h ▸ ha).symm
  rw [← ofEnd_toLin'_submatrix σ]
  congr 2
  ext i j
  have hi : ¬b i = m := fun h ↦ ha (i.property.symm.trans h)
  have hj : ¬b j = m := fun h ↦ ha (j.property.symm.trans h)
  simp only [assemble, BlockTriangularGroup.coe_diagBlock, coe_assembleGL, toSquareBlock_def,
    submatrix_apply, of_apply, splitEquiv_symm_apply_of_ne hi, splitEquiv_symm_apply_of_ne hj,
    fromBlocks_apply₁₁, σ]
  -- What is left: `σ` keeps the underlying index.
  exact congrArg₂ _ (Subtype.ext (by simp)) (Subtype.ext (by simp))

end Assemble

/-! ### Frobenius reciprocity -/

section Frobenius

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {ι : Type*} [LinearOrder ι]

/-- A mean over a product is an iterated mean. -/
private theorem expect_prod_eq {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℂ) :
    𝔼 p, f p = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- Frobenius reciprocity with no levels: then `n` is empty. -/
private theorem rankInner_prod_rankPart_empty (F : ι → HallAlgebra k) {n : Type*} [Fintype n]
    [DecidableEq n] (b : n → ι) (hs : ∀ i, b i ∈ (∅ : Finset ι))
    [Fintype (blockTriangularGroup k b)] (X : HallAlgebra k) :
    rankInner (Fintype.card n) (∏ a ∈ ∅, (F a).rankPart (Fintype.card {i // b i = a})) X =
      𝔼 g : blockTriangularGroup k b, conj (∏ a ∈ ∅,
        ((F a).toClassFunction {i // b i = a}).val (BlockTriangularGroup.diagBlock b a g)) *
          (X.toClassFunction n).val g := by
  have : IsEmpty n := ⟨fun i ↦ by simpa using hs i⟩
  have ho : (ofEnd (0 : Module.End k (Fin 0 → k))).dim = 0 := by simp
  have h_class (g : GL n k) :
      ofEnd (toLin' (g : Matrix n n k)) = ofEnd (0 : Module.End k (Fin 0 → k)) :=
    eq_of_dim_eq_zero (by simp) ho
  rw [Fintype.card_eq_zero, rankInner_zero _ _ ho]
  simp [h_class]

/-- The step of Frobenius reciprocity: the largest level `m` is moved to the other side by the
adjunction, and `P_b` is assembled from `P_{b′}`, `GL_{n_m}(k)` and the upper right block. -/
private theorem rankInner_prod_rankPart_insert (F : ι → HallAlgebra k) {m : ι} {s : Finset ι}
    (hm : ∀ a ∈ s, a < m) {n : Type*} [Fintype n] [DecidableEq n] (b : n → ι)
    (hs : ∀ i, b i ∈ insert m s) [Fintype (blockTriangularGroup k b)] (X : HallAlgebra k)
    (ih : ∀ b' : {i // ¬b i = m} → ι, (∀ i, b' i ∈ s) →
      ∀ [Fintype (blockTriangularGroup k b')] (X : HallAlgebra k),
        rankInner (Fintype.card {i // ¬b i = m})
            (∏ a ∈ s, (F a).rankPart (Fintype.card {i // b' i = a})) X =
          𝔼 g : blockTriangularGroup k b', conj (∏ a ∈ s,
            ((F a).toClassFunction {i // b' i = a}).val (BlockTriangularGroup.diagBlock b' a g)) *
              (X.toClassFunction {i // ¬b i = m}).val g) :
    rankInner (Fintype.card n) (∏ a ∈ insert m s, (F a).rankPart (Fintype.card {i // b i = a})) X =
      𝔼 g : blockTriangularGroup k b, conj (∏ a ∈ insert m s,
        ((F a).toClassFunction {i // b i = a}).val (BlockTriangularGroup.diagBlock b a g)) *
          (X.toClassFunction n).val g := by
  have hm' : m ∉ s := fun h ↦ lt_irrefl m (hm m h)
  have hb (i : n) : b i ≤ m := (Finset.mem_insert.1 (hs i)).elim le_of_eq fun h ↦ (hm _ h).le
  have hs' (i : {i // ¬b i = m}) : restLevel b m i ∈ s :=
    (Finset.mem_insert.1 (hs i)).resolve_left i.property
  have := Fintype.ofFinite (blockTriangularGroup k (restLevel b m))
  -- The levels in `s` have the same sizes for `b` and for `b′`.
  have h_prod : ∏ a ∈ s, (F a).rankPart (Fintype.card {i // b i = a}) =
      ∏ a ∈ s, (F a).rankPart (Fintype.card {i : {i // ¬b i = m} // restLevel b m i = a}) :=
    Finset.prod_congr rfl fun a ha ↦ by
      rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtype fun h ↦ h ▸ (hm a ha).ne).symm]
  have h_dim : Fintype.card n = Fintype.card {i // b i = m} + Fintype.card {i // ¬b i = m} := by
    rw [← Fintype.card_congr (splitEquiv b m), Fintype.card_sum, add_comm]
  rw [Finset.prod_insert hm', h_prod, h_dim,
    rankInner_mul_eq_rankInner_mulAdjoint _ (fun c hc ↦ by simp [hc]), ih _ hs']
  refine Eq.trans ?_ (Fintype.expect_bijective (assemble hb) (assemble_bijective hb) _ _
    fun _ ↦ rfl)
  simp only [expect_prod_eq]
  refine Finset.expect_congr rfl fun h _ ↦ ?_
  rw [toClassFunction_apply, mulAdjoint_toLin', Finset.mul_expect]
  refine Finset.expect_congr rfl fun c _ ↦ ?_
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun M _ ↦ ?_
  have h_s : ∏ a ∈ s, ((F a).toClassFunction {i // b i = a}).val
        (BlockTriangularGroup.diagBlock b a (assemble hb (h, c, M))) =
      ∏ a ∈ s, ((F a).toClassFunction {i // restLevel b m i = a}).val
        (BlockTriangularGroup.diagBlock (restLevel b m) a h) :=
    Finset.prod_congr rfl fun a ha ↦ by
      simp only [toClassFunction_apply]
      rw [ofEnd_diagBlock_assemble hb _ (hm a ha).ne]
  rw [Finset.prod_insert hm', h_s, toClassFunction_apply X, ofEnd_assemble,
    diagBlock_assemble_self]
  simp only [toClassFunction_apply, rankPart_apply, dim_ofEnd,
    Module.finrank_fintype_fun_eq_card, ↓reduceIte, map_mul]
  ring

/-- Frobenius reciprocity for the restriction to `GL n k` of an element `X` of the Hall algebra. -/
private theorem rankInner_prod_rankPart (F : ι → HallAlgebra k) (s : Finset ι) {n : Type*}
    [Fintype n] [DecidableEq n] (b : n → ι) (hs : ∀ i, b i ∈ s)
    [Fintype (blockTriangularGroup k b)] (X : HallAlgebra k) :
    rankInner (Fintype.card n) (∏ a ∈ s, (F a).rankPart (Fintype.card {i // b i = a})) X =
      𝔼 g : blockTriangularGroup k b, conj (∏ a ∈ s,
        ((F a).toClassFunction {i // b i = a}).val (BlockTriangularGroup.diagBlock b a g)) *
          (X.toClassFunction n).val g := by
  induction s using Finset.induction_on_max generalizing n X with
  | empty => exact rankInner_prod_rankPart_empty F b hs X
  | insert m s hm ih =>
    exact rankInner_prod_rankPart_insert F hm b hs X fun b' hs' _ X ↦ ih b' hs' X

/-- **Frobenius reciprocity.** Let `b` rank the indices `n` by a linear order, with all levels in
`s`, and let `P_b = blockTriangularGroup k b` be the parabolic subgroup of `GL n k` of the block
upper triangular matrices, with diagonal blocks `g_a ∈ GL {i // b i = a} k`. For `A_a` in the Hall
algebra and a class function `Y` on `GL n k`, the inner product over `GL n k` of the restriction
of the induction product `∏_a A_a|_{n_a}` with `Y` is the inner product over `P_b` of
`g ↦ ∏_a A_a(g_a)` with the restriction of `Y`. So on `GL n k` the product of the Hall algebra is
parabolic induction. -/
theorem expect_toClassFunction_prod_rankPart {n : Type*} [Fintype n] [DecidableEq n]
    (b : n → ι) (F : ι → HallAlgebra k) {s : Finset ι} (hs : ∀ i, b i ∈ s)
    [Fintype (blockTriangularGroup k b)] (Y : ClassFunction ℂ (GL n k)) :
    𝔼 g : GL n k, conj (((∏ a ∈ s, (F a).rankPart (Fintype.card {i // b i = a})).toClassFunction
        n).val g) * Y.val g =
      𝔼 g : blockTriangularGroup k b, conj (∏ a ∈ s,
        ((F a).toClassFunction {i // b i = a}).val (BlockTriangularGroup.diagBlock b a g)) *
          Y.val g := by
  obtain ⟨X, rfl⟩ := exists_toClassFunction_eq n Y
  rw [expect_toClassFunction_eq_rankInner, rankInner_prod_rankPart F s b hs X]

end Frobenius

end HallAlgebra

end TauCeti
