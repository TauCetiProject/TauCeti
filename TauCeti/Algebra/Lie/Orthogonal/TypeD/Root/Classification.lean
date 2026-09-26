/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.AllGenerators

/-!
# Root-space lines of the split even orthogonal Lie algebra

This file identifies the nonzero root spaces of the split type-`D` Lie algebra relative to its
diagonal Cartan. The coordinate-difference root `εᵢ - εⱼ` is spanned by the standard paired
diagonal-block matrix, while `εᵢ + εⱼ` and `-εᵢ - εⱼ` are spanned by the standard skew
matrices in the two off-diagonal blocks.

The proof first distinguishes the three families of weights in the dual Cartan and locates their
possible matrix entries. The skew-adjoint block relations then show that the two possible entries
for each root carry only one scalar parameter.

## Main results

* `TauCeti.TypeDStd.rootSpace_typeDWeightSub_eq_span`: the root space of `εᵢ - εⱼ` is the
  line through `differenceRootGenerator i j`.
* `TauCeti.TypeDStd.rootSpace_typeDWeightAdd_eq_span`: the root space of `εᵢ + εⱼ` is the
  line through `sumRootGenerator i j`.
* `TauCeti.TypeDStd.rootSpace_neg_typeDWeightAdd_eq_span`: the root space of `-εᵢ - εⱼ` is
  the line through `negSumRootGenerator i j`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8, 12.
-/

open _root_.Matrix

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-! ## Distinctness of the three root families -/

/-- The coordinate vector of the difference weight `εᵢ - εⱼ`. -/
@[simp]
theorem typeDWeightEquiv_symm_weightSub (i j : ι) :
    (typeDWeightEquiv (K := K)).symm (typeDWeightSub i j) =
      Pi.single i 1 - Pi.single j 1 := by
  rw [typeDWeightSub_def, map_sub, typeDWeightEquiv_symm_epsilon,
    typeDWeightEquiv_symm_epsilon]

/-- The coordinate vector of the sum weight `εᵢ + εⱼ`. -/
@[simp]
theorem typeDWeightEquiv_symm_weightAdd (i j : ι) :
    (typeDWeightEquiv (K := K)).symm (typeDWeightAdd i j) =
      Pi.single i 1 + Pi.single j 1 := by
  rw [typeDWeightAdd_def, map_add, typeDWeightEquiv_symm_epsilon,
    typeDWeightEquiv_symm_epsilon]

/-- Away from characteristic two, the nonzero coordinate-difference weights are pairwise
distinct as ordered pairs. -/
@[simp]
theorem typeDWeightSub_eq_typeDWeightSub_iff (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (a b : ι) :
    typeDWeightSub (K := K) a b = typeDWeightSub i j ↔ a = i ∧ b = j := by
  have : Nontrivial K := nontrivial_of_ne 2 0 h2
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have hfun := congrArg (typeDWeightEquiv (K := K)).symm h
  simp only [typeDWeightEquiv_symm_weightSub] at hfun
  have hi := congrFun hfun i
  have hj := congrFun hfun j
  rw [Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij] at hi
  rw [Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at hj
  refine ⟨?_, ?_⟩
  · by_contra hia
    rw [Pi.single_eq_of_ne (Ne.symm hia)] at hi
    by_cases hib : b = i
    · rw [hib, Pi.single_eq_same] at hi
      exact absurd (by linear_combination -hi) h2
    · rw [Pi.single_eq_of_ne (Ne.symm hib)] at hi
      have h10 : (1 : K) = 0 := by linear_combination -hi
      exact one_ne_zero h10
  · by_contra hjb
    rw [Pi.single_eq_of_ne (Ne.symm hjb)] at hj
    by_cases hja : a = j
    · rw [hja, Pi.single_eq_same] at hj
      exact absurd (by linear_combination hj) h2
    · rw [Pi.single_eq_of_ne (Ne.symm hja)] at hj
      have h10 : (1 : K) = 0 := by linear_combination hj
      exact one_ne_zero h10

/-- Away from characteristic two, two coordinate-sum roots agree exactly when their unordered
pairs of distinct coordinates agree. -/
@[simp]
theorem typeDWeightAdd_eq_typeDWeightAdd_iff (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (a b : ι) :
    typeDWeightAdd (K := K) a b = typeDWeightAdd i j ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  have : Nontrivial K := nontrivial_of_ne 2 0 h2
  refine ⟨fun h => ?_, ?_⟩
  · have hfun := congrArg (typeDWeightEquiv (K := K)).symm h
    simp only [typeDWeightEquiv_symm_weightAdd] at hfun
    have hab : a ≠ b := by
      intro hab
      subst b
      have hi := congrFun hfun i
      rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij] at hi
      by_cases hai : a = i
      · subst a
        simp at hi
      · simp [hai] at hi
    have ha := congrFun hfun a
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab] at ha
    by_cases hai : a = i
    · left
      refine ⟨hai, ?_⟩
      subst a
      have hb := congrFun hfun b
      rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (Ne.symm hab)] at hb
      by_contra hbj
      rw [Pi.single_eq_of_ne hbj] at hb
      have h10 : (1 : K) = 0 := by linear_combination hb
      exact one_ne_zero h10
    · have haj : a = j := by
        by_contra haj
        rw [Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj] at ha
        have h10 : (1 : K) = 0 := by linear_combination ha
        exact one_ne_zero h10
      right
      refine ⟨haj, ?_⟩
      subst a
      have hb := congrFun hfun b
      rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (Ne.symm hab)] at hb
      by_contra hbi
      rw [Pi.single_eq_of_ne hbi] at hb
      have h10 : (1 : K) = 0 := by linear_combination hb
      exact one_ne_zero h10
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact typeDWeightAdd_comm _ _

/-- A coordinate-difference weight is never a coordinate-sum weight away from characteristic
two. -/
theorem typeDWeightSub_ne_typeDWeightAdd (h2 : (2 : K) ≠ 0) (a b i j : ι) :
    typeDWeightSub (K := K) a b ≠ typeDWeightAdd i j := by
  intro h
  have heval := congrArg
    (fun χ : Module.Dual K (typeDDiagonalCartan K ι) =>
      χ (typeDDiagonalEquiv (K := K) (fun _ => 1))) h
  simp [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply] at heval
  norm_num [one_add_one_eq_two] at heval
  exact h2 heval.symm

/-- A negative coordinate-sum weight is never a positive coordinate-sum weight over a domain
away from characteristic two. -/
theorem neg_typeDWeightAdd_ne_typeDWeightAdd [IsDomain K] (h2 : (2 : K) ≠ 0)
    (a b i j : ι) :
    -typeDWeightAdd (K := K) a b ≠ typeDWeightAdd i j := by
  intro h
  have heval := congrArg
    (fun χ : Module.Dual K (typeDDiagonalCartan K ι) =>
      χ (typeDDiagonalEquiv (K := K) (fun _ => 1))) h
  have heval' : -(2 : K) = 2 := by
    simpa [typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using heval
  have h4 : (4 : K) ≠ 0 := by
    have hmul : (2 : K) * 2 ≠ 0 := mul_ne_zero h2 h2
    norm_num at hmul
    exact hmul
  have hzero : (2 : K) + 2 = 0 := neg_eq_iff_add_eq_zero.mp heval'
  norm_num at hzero
  exact h4 hzero

/-- A negative coordinate-sum weight is never a coordinate-difference weight away from
characteristic two. -/
theorem neg_typeDWeightAdd_ne_typeDWeightSub (h2 : (2 : K) ≠ 0) (a b i j : ι) :
    -typeDWeightAdd (K := K) a b ≠ typeDWeightSub i j := by
  intro h
  have heval := congrArg
    (fun χ : Module.Dual K (typeDDiagonalCartan K ι) =>
      χ (typeDDiagonalEquiv (K := K) (fun _ => 1))) h
  have hzero : -(2 : K) = 0 := by
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using heval
  exact h2 (neg_eq_zero.mp hzero)

/-! ## Matrix positions carrying each root -/

/-- The two matrix positions of weight `εᵢ - εⱼ` in the split type-`D` model. -/
theorem typeDMatrixWeight_eq_typeDWeightSub_iff (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) (a b : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a b = typeDWeightSub i j ↔
      (a = .inl i ∧ b = .inl j) ∨ (a = .inr j ∧ b = .inr i) := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [typeDMatrixWeight_inl_inl, Sum.inl.injEq, Sum.inl_ne_inr, false_and,
      or_false]
    exact typeDWeightSub_eq_typeDWeightSub_iff h2 hij a b
  · simp only [typeDMatrixWeight_inl_inr, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false, or_self]
    exact iff_false_intro (Ne.symm (typeDWeightSub_ne_typeDWeightAdd h2 i j a b))
  · simp only [typeDMatrixWeight_inr_inl, Sum.inr.injEq, Sum.inr_ne_inl,
      Sum.inl_ne_inr, false_and, and_false, or_self]
    exact iff_false_intro (neg_typeDWeightAdd_ne_typeDWeightSub h2 a b i j)
  · simp only [typeDMatrixWeight_inr_inr, Sum.inr.injEq, Sum.inr_ne_inl, false_and,
      false_or]
    simpa [and_comm] using typeDWeightSub_eq_typeDWeightSub_iff h2 hij b a

/-- The two matrix positions of weight `εᵢ + εⱼ` in the split type-`D` model. -/
theorem typeDMatrixWeight_eq_typeDWeightAdd_iff [IsDomain K] (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) (a b : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a b = typeDWeightAdd i j ↔
      (a = .inl i ∧ b = .inr j) ∨ (a = .inl j ∧ b = .inr i) := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [typeDMatrixWeight_inl_inl, Sum.inl.injEq, Sum.inl_ne_inr,
      and_false, or_self]
    exact iff_false_intro (typeDWeightSub_ne_typeDWeightAdd h2 a b i j)
  · simp only [typeDMatrixWeight_inl_inr, Sum.inl.injEq, Sum.inr.injEq]
    exact typeDWeightAdd_eq_typeDWeightAdd_iff h2 hij a b
  · simp only [typeDMatrixWeight_inr_inl, Sum.inr_ne_inl, false_and, false_or]
    exact iff_false_intro (neg_typeDWeightAdd_ne_typeDWeightAdd h2 a b i j)
  · simp only [typeDMatrixWeight_inr_inr, Sum.inr_ne_inl, false_and, false_or]
    exact iff_false_intro (typeDWeightSub_ne_typeDWeightAdd h2 b a i j)

/-- The two matrix positions of weight `-εᵢ - εⱼ` in the split type-`D` model. -/
theorem typeDMatrixWeight_eq_neg_typeDWeightAdd_iff [IsDomain K] (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) (a b : ι ⊕ ι) :
    typeDMatrixWeight (K := K) a b = -typeDWeightAdd i j ↔
      (a = .inr i ∧ b = .inl j) ∨ (a = .inr j ∧ b = .inl i) := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [typeDMatrixWeight_inl_inl, Sum.inl_ne_inr, false_and, false_or]
    exact iff_false_intro (Ne.symm (neg_typeDWeightAdd_ne_typeDWeightSub h2 i j a b))
  · simp only [typeDMatrixWeight_inl_inr, Sum.inl_ne_inr, false_and, false_or]
    exact iff_false_intro (Ne.symm (neg_typeDWeightAdd_ne_typeDWeightAdd h2 i j a b))
  · simp only [typeDMatrixWeight_inr_inl, Sum.inr.injEq, Sum.inl.injEq, neg_inj]
    exact typeDWeightAdd_eq_typeDWeightAdd_iff h2 hij a b
  · simp only [typeDMatrixWeight_inr_inr, Sum.inr_ne_inl, and_false, or_self]
    exact iff_false_intro (Ne.symm (neg_typeDWeightAdd_ne_typeDWeightSub h2 i j b a))

/-! ## Root-space lines -/

namespace TypeDStd

/-- Over a domain away from characteristic two, the root space of `εᵢ - εⱼ`, for
`i ≠ j`, is the line through the standard difference-root generator. -/
theorem rootSpace_typeDWeightSub_eq_span [IsDomain K] (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) :
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightSub i j)).toSubmodule =
      K ∙ differenceRootGenerator (K := K) i j := by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    refine ⟨(X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl j), ?_⟩
    have hs := (mem_rootSpace_typeDDiagonalCartan_iff (typeDWeightSub i j) X).mp hX
    apply Subtype.ext
    ext (a | a) (b | b)
    · by_cases hab : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := hab
        simp [val_differenceRootGenerator, differenceRootMatrix_def]
      · have hz := hs (.inl a) (.inl b) (fun hw => by
          have hp := (typeDMatrixWeight_eq_typeDWeightSub_iff h2 hij (.inl a) (.inl b)).mp hw
          simp only [Sum.inl.injEq, Sum.inl_ne_inr, false_and, or_false] at hp
          exact hab hp)
        rw [hz]
        simp only [SetLike.val_smul, val_differenceRootGenerator, Matrix.smul_apply,
          smul_eq_mul, mul_eq_zero]
        right
        have hpos : ¬(i = a ∧ j = b) := fun h => hab ⟨h.1.symm, h.2.symm⟩
        simp [differenceRootMatrix_def, hpos]
    · have hz := hs (.inl a) (.inr b) (fun hw => by
          have := (typeDMatrixWeight_eq_typeDWeightSub_iff h2 hij (.inl a) (.inr b)).mp hw
          simp at this)
      rw [hz]
      simp [val_differenceRootGenerator, differenceRootMatrix_def]
    · have hz := hs (.inr a) (.inl b) (fun hw => by
          have := (typeDMatrixWeight_eq_typeDWeightSub_iff h2 hij (.inr a) (.inl b)).mp hw
          simp at this)
      rw [hz]
      simp [val_differenceRootGenerator, differenceRootMatrix_def]
    · rw [typeD_apply_inr_inr X a b]
      by_cases hab : b = i ∧ a = j
      · obtain ⟨rfl, rfl⟩ := hab
        simp [val_differenceRootGenerator, differenceRootMatrix_def]
      · have hz := hs (.inl b) (.inl a) (fun hw => by
          have hp := (typeDWeightSub_eq_typeDWeightSub_iff h2 hij b a).mp (by simpa using hw)
          exact hab hp)
        rw [hz]
        simp only [typeD_apply_inr_inr, SetLike.val_smul, val_differenceRootGenerator,
          Matrix.smul_apply, smul_eq_mul, neg_zero, neg_eq_zero, mul_eq_zero]
        right
        have hpos : ¬(i = b ∧ j = a) := fun h => hab ⟨h.1.symm, h.2.symm⟩
        simp [differenceRootMatrix_def, hpos]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact differenceRootGenerator_mem_rootSpace i j

/-- Over a domain away from characteristic two, the root space of `εᵢ + εⱼ`, for
`i ≠ j`, is the line through the standard positive sum-root generator. -/
theorem rootSpace_typeDWeightAdd_eq_span [IsDomain K] (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) :
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightAdd i j)).toSubmodule =
      K ∙ sumRootGenerator (K := K) i j := by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    refine ⟨(X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inr j), ?_⟩
    have hs := (mem_rootSpace_typeDDiagonalCartan_iff (typeDWeightAdd i j) X).mp hX
    apply Subtype.ext
    ext (a | a) (b | b)
    · have hz := hs (.inl a) (.inl b) (fun hw => by
          have := (typeDMatrixWeight_eq_typeDWeightAdd_iff h2 hij (.inl a) (.inl b)).mp hw
          simp at this)
      rw [hz]
      simp [val_sumRootGenerator, sumRootMatrix_def]
    · by_cases h₁ : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h₁
        simp [val_sumRootGenerator, sumRootMatrix_def, hij]
      · by_cases h₂ : a = j ∧ b = i
        · rw [typeD_apply_inl_inr X a b, h₂.2, h₂.1]
          simp [val_sumRootGenerator, sumRootMatrix_def, hij]
        · have hz := hs (.inl a) (.inr b) (fun hw => by
              rcases (typeDMatrixWeight_eq_typeDWeightAdd_iff h2 hij (.inl a) (.inr b)).mp hw
                  with h | h
              · exact h₁ ⟨Sum.inl.inj h.1, Sum.inr.inj h.2⟩
              · exact h₂ ⟨Sum.inl.inj h.1, Sum.inr.inj h.2⟩)
          rw [hz]
          have hn₁ : ¬(i = a ∧ j = b) := fun h => h₁ ⟨h.1.symm, h.2.symm⟩
          have hn₂ : ¬(j = a ∧ i = b) := fun h => h₂ ⟨h.1.symm, h.2.symm⟩
          simp [val_sumRootGenerator, sumRootMatrix_def, hn₁, hn₂]
    · have hz := hs (.inr a) (.inl b) (fun hw => by
          have := (typeDMatrixWeight_eq_typeDWeightAdd_iff h2 hij (.inr a) (.inl b)).mp hw
          simp at this)
      rw [hz]
      simp [val_sumRootGenerator, sumRootMatrix_def]
    · have hz := hs (.inr a) (.inr b) (fun hw => by
          have := (typeDMatrixWeight_eq_typeDWeightAdd_iff h2 hij (.inr a) (.inr b)).mp hw
          simp at this)
      rw [hz]
      simp [val_sumRootGenerator, sumRootMatrix_def]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact sumRootGenerator_mem_rootSpace i j

/-- Over a domain away from characteristic two, the root space of `-εᵢ - εⱼ`, for
`i ≠ j`, is the line through the standard negative sum-root generator. -/
theorem rootSpace_neg_typeDWeightAdd_eq_span [IsDomain K] (h2 : (2 : K) ≠ 0)
    {i j : ι} (hij : i ≠ j) :
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (-typeDWeightAdd i j)).toSubmodule =
      K ∙ negSumRootGenerator (K := K) i j := by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    refine ⟨(X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inl j), ?_⟩
    have hs := (mem_rootSpace_typeDDiagonalCartan_iff (-typeDWeightAdd i j) X).mp hX
    apply Subtype.ext
    ext (a | a) (b | b)
    · have hz := hs (.inl a) (.inl b) (fun hw => by
          have := (typeDMatrixWeight_eq_neg_typeDWeightAdd_iff h2 hij (.inl a) (.inl b)).mp hw
          simp at this)
      rw [hz]
      simp [val_negSumRootGenerator, negSumRootMatrix_def]
    · have hz := hs (.inl a) (.inr b) (fun hw => by
          have := (typeDMatrixWeight_eq_neg_typeDWeightAdd_iff h2 hij (.inl a) (.inr b)).mp hw
          simp at this)
      rw [hz]
      simp [val_negSumRootGenerator, negSumRootMatrix_def]
    · by_cases h₁ : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := h₁
        simp [val_negSumRootGenerator, negSumRootMatrix_def, hij]
      · by_cases h₂ : a = j ∧ b = i
        · rw [typeD_apply_inr_inl X a b, h₂.2, h₂.1]
          simp [val_negSumRootGenerator, negSumRootMatrix_def, hij]
        · have hz := hs (.inr a) (.inl b) (fun hw => by
              rcases (typeDMatrixWeight_eq_neg_typeDWeightAdd_iff h2 hij (.inr a) (.inl b)).mp hw
                  with h | h
              · exact h₁ ⟨Sum.inr.inj h.1, Sum.inl.inj h.2⟩
              · exact h₂ ⟨Sum.inr.inj h.1, Sum.inl.inj h.2⟩)
          rw [hz]
          have hn₁ : ¬(i = a ∧ j = b) := fun h => h₁ ⟨h.1.symm, h.2.symm⟩
          have hn₂ : ¬(j = a ∧ i = b) := fun h => h₂ ⟨h.1.symm, h.2.symm⟩
          simp [val_negSumRootGenerator, negSumRootMatrix_def, hn₁, hn₂]
    · have hz := hs (.inr a) (.inr b) (fun hw => by
          have := (typeDMatrixWeight_eq_neg_typeDWeightAdd_iff h2 hij (.inr a) (.inr b)).mp hw
          simp at this)
      rw [hz]
      simp [val_negSumRootGenerator, negSumRootMatrix_def]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact negSumRootGenerator_mem_rootSpace i j

/-! ## Dimensions -/

/-- Over a field away from characteristic two, the root space of a coordinate-difference root
`εᵢ - εⱼ` with `i ≠ j` has dimension one. -/
theorem finrank_rootSpace_typeDWeightSub_eq_one {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j) :
    Module.finrank K
      (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightSub i j)).toSubmodule = 1 := by
  rw [rootSpace_typeDWeightSub_eq_span h2 hij]
  exact finrank_span_singleton (differenceRootGenerator_ne_zero i j)

/-- Over a field away from characteristic two, the root space of a positive coordinate-sum root
`εᵢ + εⱼ` with `i ≠ j` has dimension one. -/
theorem finrank_rootSpace_typeDWeightAdd_eq_one {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j) :
    Module.finrank K
      (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightAdd i j)).toSubmodule = 1 := by
  rw [rootSpace_typeDWeightAdd_eq_span h2 hij]
  exact finrank_span_singleton (sumRootGenerator_ne_zero i j hij)

/-- Over a field away from characteristic two, the root space of a negative coordinate-sum root
`-εᵢ - εⱼ` with `i ≠ j` has dimension one. -/
theorem finrank_rootSpace_neg_typeDWeightAdd_eq_one {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j) :
    Module.finrank K
      (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (-typeDWeightAdd i j)).toSubmodule = 1 := by
  rw [rootSpace_neg_typeDWeightAdd_eq_span h2 hij]
  exact finrank_span_singleton (negSumRootGenerator_ne_zero i j hij)

end TypeDStd

end TauCeti
