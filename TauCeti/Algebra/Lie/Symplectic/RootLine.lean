/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Lie

/-!
# Recognition of symplectic root lines by matrix support

A symplectic Lie matrix supported at the positions of a standard root matrix is a
unique scalar multiple of that matrix. For short roots, the symplectic equation
forces the two entries to have the prescribed relative sign. The support is tested
on the integral matrix, so the criterion remains valid in characteristic two and
over rings with nilpotents. It is the matrix recognition step in identifying
adjoint root spaces with the images of root-subgroup differentials.

The normalization is `GLSymplecticFin.RootSubgroupIndex.tangentMatrix`; the block
criterion is `Matrix.mem_symplecticLieAlgebra_iff`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

namespace TauCeti.GLSymplecticFin.RootSubgroupIndex

open Matrix

variable {m : ℕ} {R : Type*} [CommRing R]

/-- Every scalar multiple of a root matrix vanishes outside its integral support. -/
theorem tangentMatrix_apply_eq_zero_of_int_eq_zero (root : RootSubgroupIndex m) (c : R)
    (a b : Fin m ⊕ Fin m) (h : root.tangentMatrix (1 : ℤ) a b = 0) :
    root.tangentMatrix c a b = 0 := by
  have hcast := congrFun (congrFun
    (root.map_tangentMatrix (Int.castAddHom R) (1 : ℤ)) a) b
  have hone : root.tangentMatrix (1 : R) a b = 0 := by
    simpa only [Matrix.map_apply, h, map_zero, Int.coe_castAddHom, Int.cast_one,
      Int.cast_zero] using hcast.symm
  have hsmul := congrFun (congrFun ((root.tangentMatrix (R := R)).map_smul c 1) a) b
  simpa [hone] using hsmul

/-- Within the symplectic Lie algebra, integral root support forces the matrix to
be a scalar multiple of the normalized root matrix. -/
private theorem exists_eq_tangentMatrix_of_support (root : RootSubgroupIndex m)
    {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R}
    (hA : A ∈ LieAlgebra.Symplectic.sp (Fin m) R)
    (hs : ∀ a b, root.tangentMatrix (1 : ℤ) a b = 0 → A a b = 0) :
    ∃ c : R, A = root.tangentMatrix c := by
  obtain ⟨hQ, hS, hD⟩ := (mem_symplecticLieAlgebra_iff A).mp hA
  -- The support leaves one entry for long roots and two related entries for short roots.
  cases root with
  | positiveLong i =>
      refine ⟨A (.inl i) (.inr i), ?_⟩
      ext a b
      by_cases h : Sum.inl i = a ∧ Sum.inr i = b
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · have hz := hs a b (by simp [h])
        simp [h, hz]
  | negativeLong i =>
      refine ⟨A (.inr i) (.inl i), ?_⟩
      ext a b
      by_cases h : Sum.inr i = a ∧ Sum.inl i = b
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · have hz := hs a b (by simp [h])
        simp [h, hz]
  | difference i j hij =>
      refine ⟨A (.inl i) (.inl j), ?_⟩
      ext a b
      by_cases h₁ : Sum.inl i = a ∧ Sum.inl j = b
      · obtain ⟨rfl, rfl⟩ := h₁
        simp
      by_cases h₂ : Sum.inr j = a ∧ Sum.inr i = b
      · obtain ⟨rfl, rfl⟩ := h₂
        simp [hD j i]
      · have hz := hs a b (by simp [h₁, h₂])
        simp [h₁, h₂, hz]
  | positiveSum i j hij =>
      refine ⟨A (.inl i) (.inr j), ?_⟩
      ext a b
      by_cases h₁ : Sum.inl i = a ∧ Sum.inr j = b
      · obtain ⟨rfl, rfl⟩ := h₁
        simp [hij.ne']
      by_cases h₂ : Sum.inl j = a ∧ Sum.inr i = b
      · obtain ⟨rfl, rfl⟩ := h₂
        simp [hij.ne, hQ j i]
      · have hz := hs a b (by simp [h₁, h₂])
        simp [h₁, h₂, hz]
  | negativeSum i j hij =>
      refine ⟨A (.inr i) (.inl j), ?_⟩
      ext a b
      by_cases h₁ : Sum.inr i = a ∧ Sum.inl j = b
      · obtain ⟨rfl, rfl⟩ := h₁
        simp [hij.ne']
      by_cases h₂ : Sum.inr j = a ∧ Sum.inl i = b
      · obtain ⟨rfl, rfl⟩ := h₂
        simp [hij.ne, hS j i]
      · have hz := hs a b (by simp [h₁, h₂])
        simp [h₁, h₂, hz]

/-- A symplectic Lie matrix lies on a root line exactly when it vanishes outside
the corresponding integral support. The scalar parameter is unique over every ring. -/
theorem existsUnique_eq_tangentMatrix_iff (root : RootSubgroupIndex m)
    {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R}
    (hA : A ∈ LieAlgebra.Symplectic.sp (Fin m) R) :
    (∃! c : R, A = root.tangentMatrix c) ↔
      ∀ a b, root.tangentMatrix (1 : ℤ) a b = 0 → A a b = 0 := by
  constructor
  · rintro ⟨c, rfl, _⟩ a b h
    exact root.tangentMatrix_apply_eq_zero_of_int_eq_zero c a b h
  · intro hs
    obtain ⟨c, hc⟩ := root.exists_eq_tangentMatrix_of_support hA hs
    exact ⟨c, hc, fun d hd ↦ root.tangentMatrix_injective (hd.symm.trans hc)⟩

end TauCeti.GLSymplecticFin.RootSubgroupIndex
