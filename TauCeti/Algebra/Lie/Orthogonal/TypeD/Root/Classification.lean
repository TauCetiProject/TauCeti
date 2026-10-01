/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.AllGenerators
import TauCeti.LinearAlgebra.Pi

/-!
# Root-space lines of the split even orthogonal Lie algebra

This file identifies the root spaces for the three standard nonzero root families of the split
type-`D` Lie algebra relative to its diagonal Cartan. The coordinate-difference root `εᵢ - εⱼ` is
spanned by the standard paired diagonal-block matrix, while `εᵢ + εⱼ` and `-εᵢ - εⱼ` are
spanned by the standard skew matrices in the two off-diagonal blocks.

These line descriptions provide the concrete root spaces needed to describe the positive
nilradical, construct a compatible Borel subalgebra, and match the resulting split Cartan data to
the abstract type-`D` root datum.

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

open _root_.Matrix _root_.LieAlgebra.Orthogonal

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-! ## Root-space lines -/

namespace TypeDStd

private theorem rootSpace_entry_eq_zero_of_isRegular_coordinate
    {chi : Module.Dual K (typeDDiagonalCartan K ι)}
    {X : LieAlgebra.Orthogonal.typeD ι K}
    (hX : X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) chi)
    (a b : ι ⊕ ι) (k : ι)
    (hreg : IsRegular
      ((typeDWeightEquiv (K := K)).symm (typeDMatrixWeight a b - chi) k)) :
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
  let A := typeDDiagonalCartanBasis (K := K) (ι := ι) k
  have hcoeff :
      (typeDWeightEquiv (K := K)).symm (typeDMatrixWeight a b - chi) k =
        typeDMatrixWeight a b A - chi A := by
    simp [typeDWeightEquiv_symm_apply, A]
  exact rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX a b A
    (hcoeff ▸ hreg)

private theorem rootSpace_typeDWeightSub_apply_eq_zero
    (h2 : IsRegular (2 : K)) {i j : ι} (hij : i ≠ j)
    (X : LieAlgebra.Orthogonal.typeD ι K)
    (hX : X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightSub i j)) :
    ∀ a b, typeDMatrixWeight (K := K) a b ≠ typeDWeightSub i j →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
  intro a b hne
  rcases a with a | a <;> rcases b with b | b
  · have hp : ¬(a = i ∧ b = j) := by
      rintro ⟨rfl, rfl⟩
      exact hne (typeDMatrixWeight_inl_inl a b)
    obtain ⟨k, hk⟩ := exists_isRegular_single_sub_single_sub h2 hij a b hp
    apply rootSpace_entry_eq_zero_of_isRegular_coordinate hX (.inl a) (.inl b) k
    simpa [typeDWeightSub_def, Pi.single_apply, eq_comm] using hk
  · apply rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX (.inl a) (.inr b)
      (typeDDiagonalEquiv (K := K) (fun _ => 1))
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using h2
  · apply rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX (.inr a) (.inl b)
      (typeDDiagonalEquiv (K := K) (fun _ => 1))
    have hneg2 : IsRegular (-(2 : K)) := by
      simpa using isUnit_neg_one.isRegular.mul h2
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using hneg2
  · have hp : ¬(b = i ∧ a = j) := by
      rintro ⟨rfl, rfl⟩
      exact hne (typeDMatrixWeight_inr_inr a b)
    obtain ⟨k, hk⟩ := exists_isRegular_single_sub_single_sub h2 hij b a hp
    apply rootSpace_entry_eq_zero_of_isRegular_coordinate hX (.inr a) (.inr b) k
    simpa [typeDWeightSub_def, Pi.single_apply, eq_comm] using hk

private theorem rootSpace_typeDWeightAdd_apply_eq_zero
    (h2 : IsRegular (2 : K)) {i j : ι} (hij : i ≠ j)
    (X : LieAlgebra.Orthogonal.typeD ι K)
    (hX : X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightAdd i j)) :
    ∀ a b, typeDMatrixWeight (K := K) a b ≠ typeDWeightAdd i j →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
  intro a b hne
  have hneg2 : IsRegular (-(2 : K)) := by
    simpa using isUnit_neg_one.isRegular.mul h2
  rcases a with a | a <;> rcases b with b | b
  · apply rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX (.inl a) (.inl b)
      (typeDDiagonalEquiv (K := K) (fun _ => 1))
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using hneg2
  · have hp : ¬((a = i ∧ b = j) ∨ (a = j ∧ b = i)) := fun hp => hne (by
      rw [typeDMatrixWeight_inl_inr]
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact typeDWeightAdd_comm _ _)
    obtain ⟨k, hk⟩ := exists_isRegular_single_add_single_sub (K := K) hij a b hp
    apply rootSpace_entry_eq_zero_of_isRegular_coordinate hX (.inl a) (.inr b) k
    simpa [typeDWeightAdd_def, Pi.single_apply, eq_comm] using hk
  · obtain ⟨k, hk⟩ :=
      exists_isRegular_neg_single_add_single_sub_single_add_single h2 hij a b
    apply rootSpace_entry_eq_zero_of_isRegular_coordinate hX (.inr a) (.inl b) k
    simpa [typeDWeightAdd_def, Pi.single_apply, eq_comm] using hk
  · apply rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX (.inr a) (.inr b)
      (typeDDiagonalEquiv (K := K) (fun _ => 1))
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using hneg2

private theorem rootSpace_neg_typeDWeightAdd_apply_eq_zero
    (h2 : IsRegular (2 : K)) {i j : ι} (hij : i ≠ j)
    (X : LieAlgebra.Orthogonal.typeD ι K)
    (hX : X ∈ LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (-typeDWeightAdd i j)) :
    ∀ a b, typeDMatrixWeight (K := K) a b ≠ -typeDWeightAdd i j →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 := by
  intro a b hne
  rcases a with a | a <;> rcases b with b | b
  · apply rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX (.inl a) (.inl b)
      (typeDDiagonalEquiv (K := K) (fun _ => 1))
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using h2
  · apply rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX (.inl a) (.inr b)
      (typeDDiagonalEquiv (K := K) (fun _ => 1))
    have h4 : IsRegular ((2 : K) + 2) := by
      rw [← two_mul]
      exact h2.mul h2
    simpa [typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using h4
  · have hp : ¬((a = i ∧ b = j) ∨ (a = j ∧ b = i)) := fun hp => hne (by
      rw [typeDMatrixWeight_inr_inl]
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact congrArg Neg.neg (typeDWeightAdd_comm _ _))
    obtain ⟨k, hk⟩ := exists_isRegular_single_add_single_sub (K := K) hij a b hp
    apply rootSpace_entry_eq_zero_of_isRegular_coordinate hX (.inr a) (.inl b) k
    convert isUnit_neg_one.isRegular.mul hk using 1
    simp only [typeDMatrixWeight_inr_inl, map_sub, map_neg, typeDWeightAdd_def,
      map_add, typeDWeightEquiv_symm_epsilon, Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
    ring
  · apply rootSpace_typeDDiagonalCartan_apply_eq_zero_of_isRegular hX (.inr a) (.inr b)
      (typeDDiagonalEquiv (K := K) (fun _ => 1))
    simpa [typeDWeightSub_apply, typeDWeightAdd_apply, coe_typeDDiagonalEquiv_apply,
      one_add_one_eq_two] using h2

private theorem smul_differenceRootGenerator_eq_of_support
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (X : LieAlgebra.Orthogonal.typeD ι K)
    (hs : ∀ a b, typeDMatrixWeight (K := K) a b ≠ typeDWeightSub i j →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0) :
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl j) •
      differenceRootGenerator (K := K) i j = X := by
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
      have hpos : ¬(i = a ∧ j = b) := fun h => hab ⟨h.1.symm, h.2.symm⟩
      simp [val_differenceRootGenerator, differenceRootMatrix_def, hpos]
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
  · -- The lower-right block is determined by the transpose of the upper-left block.
    rw [typeD.apply_inr_inr X a b]
    by_cases hab : b = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := hab
      simp [val_differenceRootGenerator, differenceRootMatrix_def]
    · have hz := hs (.inl b) (.inl a) (fun hw => by
        have hp := (typeDWeightSub_eq_typeDWeightSub_iff h2 hij b a).mp (by simpa using hw)
        exact hab hp)
      rw [hz]
      have hpos : ¬(i = b ∧ j = a) := fun h => hab ⟨h.1.symm, h.2.symm⟩
      simp [typeD.apply_inr_inr, val_differenceRootGenerator, differenceRootMatrix_def, hpos]

/-- Over a nontrivial ring in which `2` is regular, the root space of `εᵢ - εⱼ`, for `i ≠ j`,
is the line through the standard difference-root generator. -/
@[simp]
theorem rootSpace_typeDWeightSub_eq_span [Nontrivial K]
    (h2 : IsRegular (2 : K))
    {i j : ι} (hij : i ≠ j) :
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightSub i j)).toSubmodule =
      K ∙ differenceRootGenerator (K := K) i j := by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    exact ⟨(X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl j),
      smul_differenceRootGenerator_eq_of_support h2.ne_zero hij X
        (rootSpace_typeDWeightSub_apply_eq_zero h2 hij X hX)⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact differenceRootGenerator_mem_rootSpace i j

private theorem smul_sumRootGenerator_eq_of_support
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (X : LieAlgebra.Orthogonal.typeD ι K)
    (hs : ∀ a b, typeDMatrixWeight (K := K) a b ≠ typeDWeightAdd i j →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0) :
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inr j) •
      sumRootGenerator (K := K) i j = X := by
  apply Subtype.ext
  ext (a | a) (b | b)
  · have hz := hs (.inl a) (.inl b) (fun hw => by
        have := (typeDMatrixWeight_eq_typeDWeightAdd_iff h2 hij (.inl a) (.inl b)).mp hw
        simp at this)
    rw [hz]
    simp [val_sumRootGenerator, sumRootMatrix_def]
  · -- Skew-symmetry determines the second supported upper-right entry from the first.
    by_cases h₁ : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h₁
      simp [val_sumRootGenerator, sumRootMatrix_def, hij]
    · by_cases h₂ : a = j ∧ b = i
      · rw [typeD.apply_inl_inr X a b, h₂.2, h₂.1]
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

/-- Over a nontrivial ring in which `2` is regular, the root space of `εᵢ + εⱼ`, for `i ≠ j`,
is the line through the standard positive sum-root generator. -/
@[simp]
theorem rootSpace_typeDWeightAdd_eq_span [Nontrivial K]
    (h2 : IsRegular (2 : K))
    {i j : ι} (hij : i ≠ j) :
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightAdd i j)).toSubmodule =
      K ∙ sumRootGenerator (K := K) i j := by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    exact ⟨(X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inr j),
      smul_sumRootGenerator_eq_of_support h2.ne_zero hij X
        (rootSpace_typeDWeightAdd_apply_eq_zero h2 hij X hX)⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact sumRootGenerator_mem_rootSpace i j

private theorem smul_negSumRootGenerator_eq_of_support
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j)
    (X : LieAlgebra.Orthogonal.typeD ι K)
    (hs : ∀ a b, typeDMatrixWeight (K := K) a b ≠ -typeDWeightAdd i j →
      (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0) :
    (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inl j) •
      negSumRootGenerator (K := K) i j = X := by
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
  · -- Skew-symmetry determines the second supported lower-left entry from the first.
    by_cases h₁ : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h₁
      simp [val_negSumRootGenerator, negSumRootMatrix_def, hij]
    · by_cases h₂ : a = j ∧ b = i
      · rw [typeD.apply_inr_inl X a b, h₂.2, h₂.1]
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

/-- Over a nontrivial ring in which `2` is regular, the root space of `-εᵢ - εⱼ`, for `i ≠ j`,
is the line through the standard negative sum-root generator. -/
@[simp]
theorem rootSpace_neg_typeDWeightAdd_eq_span [Nontrivial K]
    (h2 : IsRegular (2 : K))
    {i j : ι} (hij : i ≠ j) :
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (-⇑(typeDWeightAdd i j))).toSubmodule =
      K ∙ negSumRootGenerator (K := K) i j := by
  refine le_antisymm (fun X hX => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    exact ⟨(X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inl j),
      smul_negSumRootGenerator_eq_of_support h2.ne_zero hij X
        (rootSpace_neg_typeDWeightAdd_apply_eq_zero h2 hij X hX)⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact negSumRootGenerator_mem_rootSpace i j

/-! ## Dimensions -/

-- In the three proofs below there is no propositional equality to rewrite: a Lie submodule and
-- its underlying submodule have definitionally the same carrier type. The `change` exposes the
-- underlying submodule so that the corresponding root-space classification can rewrite it.

/-- Over a field away from characteristic two, the root space of a coordinate-difference root
`εᵢ - εⱼ` with `i ≠ j` has dimension one. -/
@[simp]
theorem finrank_rootSpace_typeDWeightSub_eq_one {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j) :
    Module.finrank K (LieAlgebra.rootSpace
      (typeDDiagonalCartan K ι) (typeDWeightSub i j)) = 1 := by
  change Module.finrank K
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightSub i j)).toSubmodule = 1
  rw [rootSpace_typeDWeightSub_eq_span (IsRegular.of_ne_zero h2) hij]
  exact finrank_span_singleton (differenceRootGenerator_ne_zero i j)

/-- Over a field away from characteristic two, the root space of a positive coordinate-sum root
`εᵢ + εⱼ` with `i ≠ j` has dimension one. -/
@[simp]
theorem finrank_rootSpace_typeDWeightAdd_eq_one {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j) :
    Module.finrank K (LieAlgebra.rootSpace
      (typeDDiagonalCartan K ι) (typeDWeightAdd i j)) = 1 := by
  change Module.finrank K
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (typeDWeightAdd i j)).toSubmodule = 1
  rw [rootSpace_typeDWeightAdd_eq_span (IsRegular.of_ne_zero h2) hij]
  exact finrank_span_singleton (sumRootGenerator_ne_zero i j hij)

/-- Over a field away from characteristic two, the root space of a negative coordinate-sum root
`-εᵢ - εⱼ` with `i ≠ j` has dimension one. -/
@[simp]
theorem finrank_rootSpace_neg_typeDWeightAdd_eq_one {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) {i j : ι} (hij : i ≠ j) :
    Module.finrank K (LieAlgebra.rootSpace
      (typeDDiagonalCartan K ι) (-⇑(typeDWeightAdd i j))) = 1 := by
  change Module.finrank K
    (LieAlgebra.rootSpace (typeDDiagonalCartan K ι) (-⇑(typeDWeightAdd i j))).toSubmodule = 1
  rw [rootSpace_neg_typeDWeightAdd_eq_span (IsRegular.of_ne_zero h2) hij]
  exact finrank_span_singleton (negSumRootGenerator_ne_zero i j hij)

end TypeDStd

end TauCeti
