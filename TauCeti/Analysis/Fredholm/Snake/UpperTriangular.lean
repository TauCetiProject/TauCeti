/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Fredholm.Snake.Basic
public import TauCeti.LinearAlgebra.Exact

/-!
# Upper-triangular block operators, parametrices, and composition snake diagrams

This file applies `TauCeti.Analysis.Fredholm.Snake.Basic` to upper-triangular `2 × 2` block
operators `[[T₀, B], [0, T₂]]` and derives two comparisons:

1. **Block-triangular parametrix comparison**: given compact parametrices `S₀` of `T₀` and `S₂`
   of `T₂`, `upperTriangularParametrix S₀ B S₂ = [[S₀, -S₀ ∘ B ∘ S₂], [0, S₂]]` certifies
   Fredholmness of `upperTriangular T₀ B T₂` via Atkinson's theorem, with index
   `-(T₀.index + T₂.index)`.
2. **Composition snake diagram**: specializing to `B = -id` gives
   `compSnakeMid T S : (x, y) ↦ (T x - y, S y)`, whose kernel and cokernel identify with
   `ker (S ∘L T)` and `G ⧸ range (S ∘L T)`, whose connecting map is `-LinearMap.kerToCoker T S`,
   and whose snake index formula recovers `(S ∘L T).index = T.index + S.index`.
-/

public section

open Module

namespace ContinuousLinearMap

/-! ### Upper-triangular block operators -/

section UpperTriangularAlgebra

variable {𝕜 E₀ E₂ F₀ F₂ : Type*} [Ring 𝕜]
  [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀] [ContinuousAdd F₀]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]

/-- The upper-triangular block operator `[[T₀, B], [0, T₂]] : (E₀ × E₂) →L[𝕜] (F₀ × F₂)` sending
`(x, y)` to `(T₀ x + B y, T₂ y)`. -/
def upperTriangular (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂) :
    (E₀ × E₂) →L[𝕜] (F₀ × F₂) :=
  (T₀.coprod B).prod (T₂.comp (snd 𝕜 E₀ E₂))

/-- Evaluating `upperTriangular T₀ B T₂` on `(x, y)` gives `(T₀ x + B y, T₂ y)`. -/
@[simp]
lemma upperTriangular_apply (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂)
    (x : E₀) (y : E₂) : upperTriangular T₀ B T₂ (x, y) = (T₀ x + B y, T₂ y) := (rfl)

/-- Left square of the upper-triangular snake diagram. -/
lemma inl_comp_eq_upperTriangular_comp_inl (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀)
    (T₂ : E₂ →L[𝕜] F₂) : (inl 𝕜 F₀ F₂).comp T₀ = (upperTriangular T₀ B T₂).comp (inl 𝕜 E₀ E₂) := by
  ext x <;> simp

/-- Right square of the upper-triangular snake diagram. -/
lemma snd_comp_upperTriangular (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂) :
    (snd 𝕜 F₀ F₂).comp (upperTriangular T₀ B T₂) = T₂.comp (snd 𝕜 E₀ E₂) := ext fun ⟨_, _⟩ ↦ rfl

/-- When the off-diagonal block vanishes, `upperTriangular T₀ 0 T₂` is `T₀.prodMap T₂`. -/
@[simp]
lemma upperTriangular_zero (T₀ : E₀ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂) :
    upperTriangular T₀ 0 T₂ = T₀.prodMap T₂ := by apply ext; rintro ⟨x, y⟩; simp

/-- The snake connecting map of `upperTriangular T₀ B T₂` is `y ↦ [B y]`. -/
theorem snakeConnectingL_upperTriangular (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂)
    (y : T₂.ker) :
    snakeConnectingL T₀ (upperTriangular T₀ B T₂) T₂ (inr 𝕜 E₀ E₂) (fst 𝕜 F₀ F₂) y =
      Submodule.Quotient.mk (B y) := by simp [snakeConnectingL_apply]

/-- Composing two upper-triangular block operators follows block-matrix multiplication. -/
theorem upperTriangular_comp_upperTriangular {G₀ G₂ : Type*}
    [AddCommGroup G₀] [Module 𝕜 G₀] [TopologicalSpace G₀] [ContinuousAdd G₀]
    [AddCommGroup G₂] [Module 𝕜 G₂] [TopologicalSpace G₂]
    (T₀' : F₀ →L[𝕜] G₀) (B' : F₂ →L[𝕜] G₀) (T₂' : F₂ →L[𝕜] G₂)
    (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂) :
    (upperTriangular T₀' B' T₂').comp (upperTriangular T₀ B T₂) =
      upperTriangular (T₀'.comp T₀) (T₀'.comp B + B'.comp T₂) (T₂'.comp T₂) := by
  apply ext; rintro ⟨x, y⟩; simp [map_add, add_assoc]

private lemma inl_inj (E₀ E₂ : Type*)
    [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
    [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂] : Function.Injective (inl 𝕜 E₀ E₂) :=
  fun _ _ h ↦ congrArg Prod.fst h

private lemma snd_surj (E₀ E₂ : Type*)
    [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
    [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂] : Function.Surjective (snd 𝕜 E₀ E₂) :=
  fun y ↦ ⟨(0, y), rfl⟩

private lemma exact_inl_snd (E₀ E₂ : Type*)
    [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
    [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂] :
    Function.Exact (inl 𝕜 E₀ E₂) (snd 𝕜 E₀ E₂) :=
  fun ⟨x, _⟩ ↦ ⟨fun hy ↦ ⟨x, Prod.ext rfl hy.symm⟩, fun ⟨_, ha⟩ ↦ (congrArg Prod.snd ha).symm⟩

end UpperTriangularAlgebra

section UpperTriangularIndex

variable {𝕜 E₀ E₂ F₀ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀] [ContinuousAdd F₀]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]

/-- The index of `upperTriangular T₀ B T₂` with Fredholm diagonal blocks is
`T₀.index + T₂.index`, independent of `B`. -/
theorem index_upperTriangular_of_diag {T₀ : E₀ →L[𝕜] F₀} {T₂ : E₂ →L[𝕜] F₂}
    (B : E₂ →L[𝕜] F₀) (hT₀ : T₀.IsFredholm) (hT₂ : T₂.IsFredholm) :
    (upperTriangular T₀ B T₂).index = T₀.index + T₂.index :=
  index_eq_add_of_exact_of_isFredholm_left_right (inl_inj E₀ E₂) (exact_inl_snd E₀ E₂)
    (snd_surj E₀ E₂) (inl_inj F₀ F₂) (exact_inl_snd F₀ F₂) (snd_surj F₀ F₂)
    (inl_comp_eq_upperTriangular_comp_inl T₀ B T₂) (snd_comp_upperTriangular T₀ B T₂) hT₀ hT₂

/-- The index of `upperTriangular T₀ B T₂` equals `T₀.index + T₂.index` when `upperTriangular`
and `T₂` are Fredholm. -/
theorem index_upperTriangular_of_right {T₀ : E₀ →L[𝕜] F₀} {B : E₂ →L[𝕜] F₀} {T₂ : E₂ →L[𝕜] F₂}
    (hM : (upperTriangular T₀ B T₂).IsFredholm) (hT₂ : T₂.IsFredholm) :
    (upperTriangular T₀ B T₂).index = T₀.index + T₂.index :=
  index_eq_add_of_exact_of_isFredholm_middle_right (inl_inj E₀ E₂) (exact_inl_snd E₀ E₂)
    (snd_surj E₀ E₂) (inl_inj F₀ F₂) (exact_inl_snd F₀ F₂) (snd_surj F₀ F₂)
    (inl_comp_eq_upperTriangular_comp_inl T₀ B T₂) (snd_comp_upperTriangular T₀ B T₂) hM hT₂

/-- The index of `upperTriangular T₀ B T₂` equals `T₀.index + T₂.index` when `T₀` and
`upperTriangular` are Fredholm. -/
theorem index_upperTriangular_of_left {T₀ : E₀ →L[𝕜] F₀} {B : E₂ →L[𝕜] F₀} {T₂ : E₂ →L[𝕜] F₂}
    (hT₀ : T₀.IsFredholm) (hM : (upperTriangular T₀ B T₂).IsFredholm) :
    (upperTriangular T₀ B T₂).index = T₀.index + T₂.index :=
  index_eq_add_of_exact_of_isFredholm_left_middle (inl_inj E₀ E₂) (exact_inl_snd E₀ E₂)
    (snd_surj E₀ E₂) (inl_inj F₀ F₂) (exact_inl_snd F₀ F₂) (snd_surj F₀ F₂)
    (inl_comp_eq_upperTriangular_comp_inl T₀ B T₂) (snd_comp_upperTriangular T₀ B T₂) hT₀ hM

end UpperTriangularIndex

section UpperTriangularBanach

variable {𝕜 E₀ E₂ F₀ F₂ : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- Between Banach spaces, `upperTriangular T₀ B T₂` with Fredholm diagonal blocks is Fredholm
for every continuous linear `B`. -/
theorem isFredholm_upperTriangular_of_diag
    [CompleteSpace E₀] [CompleteSpace E₂] [CompleteSpace F₀] [CompleteSpace F₂]
    {T₀ : E₀ →L[𝕜] F₀} {T₂ : E₂ →L[𝕜] F₂}
    (B : E₂ →L[𝕜] F₀) (hT₀ : T₀.IsFredholm) (hT₂ : T₂.IsFredholm) :
    (upperTriangular T₀ B T₂).IsFredholm :=
  isFredholm_middle_of_left_right (exact_inl_snd E₀ E₂) (snd_surj E₀ E₂) (inl_inj F₀ F₂)
    (exact_inl_snd F₀ F₂) (inl_comp_eq_upperTriangular_comp_inl T₀ B T₂)
    (snd_comp_upperTriangular T₀ B T₂) hT₀ hT₂

/-- If `upperTriangular T₀ B T₂` and `T₂` are Fredholm and `E₀`, `F₀` are Banach, so is `T₀`. -/
theorem isFredholm_left_of_upperTriangular [CompleteSpace E₀] [CompleteSpace F₀]
    {T₀ : E₀ →L[𝕜] F₀} {B : E₂ →L[𝕜] F₀} {T₂ : E₂ →L[𝕜] F₂}
    (hM : (upperTriangular T₀ B T₂).IsFredholm) (hT₂ : T₂.IsFredholm) : T₀.IsFredholm :=
  isFredholm_left_of_middle_right (inl_inj E₀ E₂) (exact_inl_snd E₀ E₂) (snd_surj E₀ E₂)
    (inl_inj F₀ F₂) (exact_inl_snd F₀ F₂) (inl_comp_eq_upperTriangular_comp_inl T₀ B T₂)
    (snd_comp_upperTriangular T₀ B T₂) hM hT₂

/-- If `T₀` and `upperTriangular T₀ B T₂` are Fredholm and `E₂`, `F₂` are Banach, so is `T₂`. -/
theorem isFredholm_right_of_upperTriangular [CompleteSpace E₂] [CompleteSpace F₂]
    {T₀ : E₀ →L[𝕜] F₀} {B : E₂ →L[𝕜] F₀} {T₂ : E₂ →L[𝕜] F₂}
    (hT₀ : T₀.IsFredholm) (hM : (upperTriangular T₀ B T₂).IsFredholm) : T₂.IsFredholm :=
  isFredholm_right_of_left_middle (exact_inl_snd E₀ E₂) (snd_surj E₀ E₂) (inl_inj F₀ F₂)
    (exact_inl_snd F₀ F₂) (snd_surj F₀ F₂) (inl_comp_eq_upperTriangular_comp_inl T₀ B T₂)
    (snd_comp_upperTriangular T₀ B T₂) hT₀ hM

end UpperTriangularBanach

/-! ### Explicit block-triangular parametrix and Atkinson comparison -/

section UpperTriangularParametrix

variable {𝕜 E₀ E₂ F₀ F₂ : Type*} [Ring 𝕜]
  [AddCommGroup E₀] [Module 𝕜 E₀] [TopologicalSpace E₀]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup F₀] [Module 𝕜 F₀] [TopologicalSpace F₀]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂]

/-- Explicit block-triangular parametrix `[[S₀, -S₀ ∘ B ∘ S₂], [0, S₂]]` of
`upperTriangular T₀ B T₂`. -/
def upperTriangularParametrix [IsTopologicalAddGroup E₀]
    (S₀ : F₀ →L[𝕜] E₀) (B : E₂ →L[𝕜] F₀) (S₂ : F₂ →L[𝕜] E₂) : (F₀ × F₂) →L[𝕜] (E₀ × E₂) :=
  upperTriangular S₀ (-(S₀.comp (B.comp S₂))) S₂

/-- Left remainder identity for `upperTriangularParametrix`. -/
theorem upperTriangularParametrix_comp_sub_one
    [IsTopologicalAddGroup E₀] [IsTopologicalAddGroup E₂] [ContinuousAdd F₀]
    (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂)
    (S₀ : F₀ →L[𝕜] E₀) (S₂ : F₂ →L[𝕜] E₂) :
    (upperTriangularParametrix S₀ B S₂).comp (upperTriangular T₀ B T₂) - 1 =
      upperTriangular (S₀.comp T₀ - 1) (S₀.comp (B.comp (1 - S₂.comp T₂)))
        (S₂.comp T₂ - 1) := by
  apply ext; rintro ⟨x, y⟩; ext
  · simp only [sub_apply, comp_apply, upperTriangularParametrix, upperTriangular_apply,
      neg_apply, map_add, map_sub, one_apply_eq_self, Prod.fst_sub]; abel
  · simp [upperTriangularParametrix]

/-- Right remainder identity for `upperTriangularParametrix`. -/
theorem comp_upperTriangularParametrix_sub_one
    [IsTopologicalAddGroup E₀] [IsTopologicalAddGroup F₀] [IsTopologicalAddGroup F₂]
    (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂)
    (S₀ : F₀ →L[𝕜] E₀) (S₂ : F₂ →L[𝕜] E₂) :
    (upperTriangular T₀ B T₂).comp (upperTriangularParametrix S₀ B S₂) - 1 =
      upperTriangular (T₀.comp S₀ - 1) ((1 - T₀.comp S₀).comp (B.comp S₂))
        (T₂.comp S₂ - 1) := by
  apply ext; rintro ⟨x, y⟩; ext
  · simp only [sub_apply, comp_apply, upperTriangularParametrix, upperTriangular_apply,
      neg_apply, map_add, map_neg, one_apply_eq_self, Prod.fst_sub]; abel
  · simp [upperTriangularParametrix]

/-- An upper-triangular block operator whose three blocks are compact is compact. -/
theorem isCompactOperator_upperTriangular [ContinuousAdd F₀] [ContinuousAdd F₂]
    {T₀ : E₀ →L[𝕜] F₀} {B : E₂ →L[𝕜] F₀} {T₂ : E₂ →L[𝕜] F₂}
    (hT₀ : IsCompactOperator T₀) (hB : IsCompactOperator B) (hT₂ : IsCompactOperator T₂) :
    IsCompactOperator (upperTriangular T₀ B T₂) := by
  have heq : upperTriangular T₀ B T₂ = (inl 𝕜 F₀ F₂).comp (T₀.comp (fst 𝕜 E₀ E₂)) +
      (inl 𝕜 F₀ F₂).comp (B.comp (snd 𝕜 E₀ E₂)) + (inr 𝕜 F₀ F₂).comp (T₂.comp (snd 𝕜 E₀ E₂)) := by
    apply ext; rintro ⟨x, y⟩; simp
  rw [heq, FunLike.coe_add, FunLike.coe_add]
  exact (((hT₀.comp_clm (fst 𝕜 E₀ E₂)).clm_comp (inl 𝕜 F₀ F₂)).add
      ((hB.comp_clm (snd 𝕜 E₀ E₂)).clm_comp (inl 𝕜 F₀ F₂))).add
    ((hT₂.comp_clm (snd 𝕜 E₀ E₂)).clm_comp (inr 𝕜 F₀ F₂))

/-- If `S₀ ∘ T₀ - 1` and `S₂ ∘ T₂ - 1` are compact, `upperTriangularParametrix S₀ B S₂` is a
left parametrix of `upperTriangular T₀ B T₂` modulo compact operators. -/
theorem isCompactOperator_upperTriangularParametrix_comp_sub_one
    [IsTopologicalAddGroup E₀] [IsTopologicalAddGroup E₂] [ContinuousAdd F₀]
    (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂)
    {S₀ : F₀ →L[𝕜] E₀} {S₂ : F₂ →L[𝕜] E₂}
    (h₀ : IsCompactOperator (S₀.comp T₀ - 1 : E₀ →L[𝕜] E₀))
    (h₂ : IsCompactOperator (S₂.comp T₂ - 1 : E₂ →L[𝕜] E₂)) :
    IsCompactOperator ((upperTriangularParametrix S₀ B S₂).comp (upperTriangular T₀ B T₂) - 1 :
      (E₀ × E₂) →L[𝕜] (E₀ × E₂)) := by
  rw [upperTriangularParametrix_comp_sub_one]
  have h₂' : IsCompactOperator (1 - S₂.comp T₂ : E₂ →L[𝕜] E₂) := by
    rw [show (1 - S₂.comp T₂ : E₂ →L[𝕜] E₂) = -(S₂.comp T₂ - 1) by abel, FunLike.coe_neg]
    exact h₂.neg
  exact isCompactOperator_upperTriangular h₀ ((h₂'.clm_comp B).clm_comp S₀) h₂

/-- If `T₀ ∘ S₀ - 1` and `T₂ ∘ S₂ - 1` are compact, `upperTriangularParametrix S₀ B S₂` is a
right parametrix of `upperTriangular T₀ B T₂` modulo compact operators. -/
theorem isCompactOperator_comp_upperTriangularParametrix_sub_one
    [IsTopologicalAddGroup E₀] [IsTopologicalAddGroup F₀] [IsTopologicalAddGroup F₂]
    (T₀ : E₀ →L[𝕜] F₀) (B : E₂ →L[𝕜] F₀) (T₂ : E₂ →L[𝕜] F₂)
    {S₀ : F₀ →L[𝕜] E₀} {S₂ : F₂ →L[𝕜] E₂}
    (h₀ : IsCompactOperator (T₀.comp S₀ - 1 : F₀ →L[𝕜] F₀))
    (h₂ : IsCompactOperator (T₂.comp S₂ - 1 : F₂ →L[𝕜] F₂)) :
    IsCompactOperator ((upperTriangular T₀ B T₂).comp (upperTriangularParametrix S₀ B S₂) - 1 :
      (F₀ × F₂) →L[𝕜] (F₀ × F₂)) := by
  rw [comp_upperTriangularParametrix_sub_one]
  have h₀' : IsCompactOperator (1 - T₀.comp S₀ : F₀ →L[𝕜] F₀) := by
    rw [show (1 - T₀.comp S₀ : F₀ →L[𝕜] F₀) = -(T₀.comp S₀ - 1) by abel, FunLike.coe_neg]
    exact h₀.neg
  exact isCompactOperator_upperTriangular h₀ (h₀'.comp_clm (B.comp S₂)) h₂

end UpperTriangularParametrix

section UpperTriangularAtkinson

variable {𝕜 E₀ E₂ F₀ F₂ : Type*}
  [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
  {T₀ : E₀ →L[𝕜] F₀} (B : E₂ →L[𝕜] F₀) {T₂ : E₂ →L[𝕜] F₂}
  {S₀ : F₀ →L[𝕜] E₀} {S₂ : F₂ →L[𝕜] E₂}
  (hL₀ : IsCompactOperator (S₀.comp T₀ - 1 : E₀ →L[𝕜] E₀))
  (hR₀ : IsCompactOperator (T₀.comp S₀ - 1 : F₀ →L[𝕜] F₀))
  (hL₂ : IsCompactOperator (S₂.comp T₂ - 1 : E₂ →L[𝕜] E₂))
  (hR₂ : IsCompactOperator (T₂.comp S₂ - 1 : F₂ →L[𝕜] F₂))

include hL₀ hR₀ hL₂ hR₂

/-- **Parametrix comparison with the snake theorem**: two-sided compact parametrices `S₀`, `S₂`
certify Fredholmness of `upperTriangular T₀ B T₂` via Atkinson's theorem. -/
theorem isFredholm_upperTriangular_of_parametrix : (upperTriangular T₀ B T₂).IsFredholm :=
  IsFredholm.of_isCompactOperator_comp_sub_one (S := upperTriangularParametrix S₀ B S₂)
    (isCompactOperator_upperTriangularParametrix_comp_sub_one T₀ B T₂ hL₀ hL₂)
    (isCompactOperator_comp_upperTriangularParametrix_sub_one T₀ B T₂ hR₀ hR₂)

/-- The explicit block-triangular parametrix `upperTriangularParametrix S₀ B S₂` has index
`-(T₀.index + T₂.index)`. -/
theorem index_upperTriangularParametrix :
    (upperTriangularParametrix S₀ B S₂).index = -(T₀.index + T₂.index) := by
  rw [← index_upperTriangular_of_diag B (.of_isCompactOperator_comp_sub_one hL₀ hR₀)
    (.of_isCompactOperator_comp_sub_one hL₂ hR₂)]
  exact index_eq_neg_of_isCompactOperator_comp_sub_one
    (isCompactOperator_upperTriangularParametrix_comp_sub_one T₀ B T₂ hL₀ hL₂)
    (isCompactOperator_comp_upperTriangularParametrix_sub_one T₀ B T₂ hR₀ hR₂)

end UpperTriangularAtkinson

/-! ### Comparison with composition: the composition snake diagram -/

section CompSnake

section CompRing

variable {𝕜 E F G : Type*} [Ring 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  (T : E →L[𝕜] F) (S : F →L[𝕜] G)

/-- Middle operator `(x, y) ↦ (T x - y, S y)` of the composition snake diagram covering `T` and
`S`, realized as `upperTriangular T (-id 𝕜 F) S`. -/
def compSnakeMid : (E × F) →L[𝕜] (F × G) :=
  upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S

/-- Evaluating `compSnakeMid T S` on `(x, y)` yields `(T x - y, S y)`. -/
@[simp]
lemma compSnakeMid_apply (x : E) (y : F) :
    compSnakeMid T S (x, y) = (T x - y, S y) := by simp [compSnakeMid, sub_eq_add_neg]

/-- Left square of the composition snake diagram. -/
lemma inl_comp_eq_compSnakeMid_comp_inl :
    (inl 𝕜 F G).comp T = (compSnakeMid T S).comp (inl 𝕜 E F) :=
  inl_comp_eq_upperTriangular_comp_inl T (-ContinuousLinearMap.id 𝕜 F) S

/-- Right square of the composition snake diagram. -/
lemma snd_comp_compSnakeMid :
    (snd 𝕜 F G).comp (compSnakeMid T S) = S.comp (snd 𝕜 E F) :=
  snd_comp_upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S

/-- The snake connecting map of the composition diagram is `-LinearMap.kerToCoker T S`. -/
theorem snakeConnectingL_compSnakeMid (y : S.ker) :
    snakeConnectingL T (compSnakeMid T S) S (inr 𝕜 E F) (fst 𝕜 F G) y =
      -(T : E →ₗ[𝕜] F).kerToCoker (S : F →ₗ[𝕜] G) y := by
  simp [compSnakeMid, LinearMap.kerToCoker_apply]

/-- The kernel of `compSnakeMid T S` is continuously linearly equivalent to `ker (S ∘L T)`, via
`(x, T x) ↔ x`. -/
def kerCompSnakeMidEquiv : (compSnakeMid T S).ker ≃L[𝕜] (S.comp T).ker :=
  ContinuousLinearEquiv.equivOfInverse
    (((fst 𝕜 E F).domRestrict (compSnakeMid T S).ker).codRestrict (S.comp T).ker fun ⟨⟨x, y⟩, hz⟩ ↦
      by
        rw [LinearMap.mem_ker, coe_coe, compSnakeMid_apply, Prod.mk_eq_zero] at hz
        rw [LinearMap.mem_ker]; change S (T x) = 0; rw [sub_eq_zero.mp hz.1, hz.2])
    (((ContinuousLinearMap.id 𝕜 E).prod T |>.domRestrict (S.comp T).ker).codRestrict
      (compSnakeMid T S).ker fun x ↦ LinearMap.mem_ker.mpr <| by
        change compSnakeMid T S (x.1, T x.1) = 0
        rw [compSnakeMid_apply, sub_self]; exact Prod.ext rfl (LinearMap.mem_ker.mp x.2))
    (fun ⟨⟨x, y⟩, hz⟩ ↦ by
      rw [LinearMap.mem_ker, coe_coe, compSnakeMid_apply, Prod.mk_eq_zero] at hz
      exact Subtype.ext (Prod.ext rfl (sub_eq_zero.mp hz.1)))
    (fun _ ↦ rfl)

/-- `kerCompSnakeMidEquiv` projects onto the first coordinate. -/
lemma coe_kerCompSnakeMidEquiv_apply (z : (compSnakeMid T S).ker) :
    (kerCompSnakeMidEquiv T S z : E) = z.1.1 := (rfl)

/-- The inverse of `kerCompSnakeMidEquiv` sends `x` to `(x, T x)`. -/
lemma coe_kerCompSnakeMidEquiv_symm_apply (x : (S.comp T).ker) :
    ((kerCompSnakeMidEquiv T S).symm x : E × F) = (x.1, T x.1) := (rfl)

/-- Under `kerCompSnakeMidEquiv`, `ker (compSnakeMid T S) → ker S` is `LinearMap.kerCompToKer`. -/
theorem snakeKerMapL_snd_comp_kerCompSnakeMidEquiv_symm (x : (S.comp T).ker) :
    snakeKerMapL (snd 𝕜 E F) (snd_comp_compSnakeMid T S) ((kerCompSnakeMidEquiv T S).symm x) =
      (T : E →ₗ[𝕜] F).kerCompToKer (S : F →ₗ[𝕜] G) x := by
  apply Subtype.ext; rw [coe_snakeKerMapL_apply]
  exact (LinearMap.coe_kerCompToKer_apply (T : E →ₗ[𝕜] F) (S : F →ₗ[𝕜] G) x).symm

/-- The cokernel of `compSnakeMid T S` is linearly equivalent to `G ⧸ range (S ∘L T)`, via
`[(y, z)] ↦ [S y + z]` with inverse `[z] ↦ [(0, z)]`. -/
def cokerCompSnakeMidEquiv :
    ((F × G) ⧸ (compSnakeMid T S).range) ≃ₗ[𝕜] (G ⧸ (S.comp T).range) :=
  LinearEquiv.ofLinearMap
    ((compSnakeMid T S).range.liftQ
      ((S.comp T).range.mkQ.comp ((S : F →ₗ[𝕜] G).comp (LinearMap.fst 𝕜 F G) +
        LinearMap.snd 𝕜 F G)) <| by
      rintro _ ⟨⟨x, y⟩, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.add_apply, coe_coe,
        compSnakeMid_apply, LinearMap.fst_apply, LinearMap.snd_apply, map_sub, sub_add_cancel]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩)
    ((S.comp T).range.liftQ ((compSnakeMid T S).range.mkQ.comp (LinearMap.inr 𝕜 F G)) <| by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.inr_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(x, T x), by simp⟩)
    (by
      apply Submodule.linearMap_qext; ext z
      change Submodule.Quotient.mk (S 0 + z) = Submodule.Quotient.mk z; simp)
    (by
      apply Submodule.linearMap_qext; apply LinearMap.ext; rintro ⟨y, z⟩
      exact (Submodule.Quotient.eq _).mpr ⟨(0, y), by simp⟩)

/-- Evaluating `cokerCompSnakeMidEquiv` on `[(y, z)]` yields `[S y + z]`. -/
lemma cokerCompSnakeMidEquiv_mk (y : F) (z : G) :
    cokerCompSnakeMidEquiv T S (Submodule.Quotient.mk (y, z)) =
      Submodule.Quotient.mk (S y + z) := (rfl)

/-- Evaluating the inverse of `cokerCompSnakeMidEquiv` on `[z]` yields `[(0, z)]`. -/
lemma cokerCompSnakeMidEquiv_symm_mk (z : G) :
    (cokerCompSnakeMidEquiv T S).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (0, z) := (rfl)

/-- Under `cokerCompSnakeMidEquiv`, `(F ⧸ range T) → ((F × G) ⧸ range compSnakeMid)` is
`LinearMap.cokerToCokerComp T S`. -/
theorem cokerCompSnakeMidEquiv_comp_snakeCokerMapL_inl (y : F) :
    cokerCompSnakeMidEquiv T S
        (snakeCokerMapL (inl 𝕜 F G) (inl_comp_eq_compSnakeMid_comp_inl T S)
          (Submodule.Quotient.mk y)) =
      (T : E →ₗ[𝕜] F).cokerToCokerComp (S : F →ₗ[𝕜] G) (Submodule.Quotient.mk y) := by
  rw [snakeCokerMapL_mk, inl_apply, cokerCompSnakeMidEquiv_mk, add_zero,
    LinearMap.cokerToCokerComp_mk]; rfl

/-- The index of `compSnakeMid T S` equals the index of `S ∘L T`, over any ring. -/
@[simp]
theorem index_compSnakeMid : (compSnakeMid T S).index = (S.comp T).index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    (kerCompSnakeMidEquiv T S).toLinearEquiv.finrank_eq, (cokerCompSnakeMidEquiv T S).finrank_eq]

end CompRing

section CompFredholm

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]

/-- `compSnakeMid T S` is Fredholm if and only if `S ∘L T` is Fredholm. -/
@[simp]
theorem isFredholm_compSnakeMid_iff [IsTopologicalAddGroup E] [IsTopologicalAddGroup G]
    (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (compSnakeMid T S).IsFredholm ↔ (S.comp T).IsFredholm := by
  let domShear : (E × F) ≃L[𝕜] (E × F) := ContinuousLinearEquiv.equivOfInverse
    ((fst 𝕜 E F).prod (T.comp (fst 𝕜 E F) - snd 𝕜 E F))
    ((fst 𝕜 E F).prod (T.comp (fst 𝕜 E F) - snd 𝕜 E F))
    (fun ⟨_, _⟩ ↦ by simp) (fun ⟨_, _⟩ ↦ by simp)
  let codShear : (F × G) ≃L[𝕜] (G × F) := ContinuousLinearEquiv.equivOfInverse
    ((S.comp (fst 𝕜 F G) + snd 𝕜 F G).prod (fst 𝕜 F G))
    ((snd 𝕜 G F).prod (fst 𝕜 G F - S.comp (snd 𝕜 G F)))
    (fun ⟨_, _⟩ ↦ by simp) (fun ⟨_, _⟩ ↦ by simp)
  have hshear : (codShear : (F × G) →L[𝕜] (G × F)).comp (compSnakeMid T S) =
      ((S.comp T).prodMap (ContinuousLinearMap.id 𝕜 F)).comp
        (domShear : (E × F) →L[𝕜] (E × F)) := by
    apply ext; rintro ⟨x, y⟩; simp [domShear, codShear]
  rw [isFredholm_iff_of_comp_eq domShear codShear hshear,
    isFredholm_prodMap_iff, and_iff_left IsFredholm.id]

/-- Comparing the snake index formula with `IsFredholm.index_comp`: applying
`index_upperTriangular_of_diag` to `compSnakeMid T S` recovers `(S ∘L T).index = T.index + S.index`.
-/
theorem index_comp_of_snake {T : E →L[𝕜] F} {S : F →L[𝕜] G}
    (hT : T.IsFredholm) (hS : S.IsFredholm) : (S.comp T).index = T.index + S.index := by
  rw [← index_compSnakeMid T S, compSnakeMid]
  exact index_upperTriangular_of_diag (-ContinuousLinearMap.id 𝕜 F) hT hS

end CompFredholm

end CompSnake

end ContinuousLinearMap
