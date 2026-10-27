/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.Root.Brackets

/-!
# Generation by adjacent special linear root vectors

Adjacent raising and lowering matrices generate the native special linear Lie algebra
over every commutative ring. Consequently, Lie homomorphisms out of this algebra are
determined by their values on these matrices.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

private theorem signedRoot_upper (i : Fin r) :
    specialLinearSignedRoot r A i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne =
      single i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne (1 : A) := by
  apply Subtype.ext
  simp

private theorem signedRoot_lower (i : Fin r) :
    specialLinearSignedRoot r A i.succ i.castSucc (Fin.castSucc_lt_succ (i := i)).ne' =
      single i.succ i.castSucc (Fin.castSucc_lt_succ (i := i)).ne' (1 : A) := by
  apply Subtype.ext
  simp

private theorem sign_smul_mem_iff (S : LieSubalgebra A (sl (Fin (r + 1)) A))
    (i j : Fin (r + 1)) (X : sl (Fin (r + 1)) A) :
    specialLinearRootSign r A i j • X ∈ S ↔ X ∈ S := by
  constructor
  · intro h
    simpa only [smul_smul, specialLinearRootSign_mul_self, one_smul] using
      S.smul_mem (specialLinearRootSign r A i j) h
  · exact S.smul_mem _

private theorem middle_mem (S : LieSubalgebra A (sl (Fin (r + 1)) A))
    (i j k : Fin (r + 1)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hx : specialLinearSignedRoot r A i j hij ∈ S)
    (hy : specialLinearSignedRoot r A j k hjk ∈ S) :
    specialLinearSignedRoot r A i k hik ∈ S := by
  have h := S.lie_mem hx hy
  rw [lie_specialLinearSignedRoot_of_middle_eq r A i j k hij hjk hik] at h
  simpa only [mul_smul, sign_smul_mem_iff] using h

private theorem outer_mem (S : LieSubalgebra A (sl (Fin (r + 1)) A))
    (i j k : Fin (r + 1)) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hx : specialLinearSignedRoot r A i j hij ∈ S)
    (hy : specialLinearSignedRoot r A k i hki ∈ S) :
    specialLinearSignedRoot r A k j hkj ∈ S := by
  have h := S.lie_mem hx hy
  rw [lie_specialLinearSignedRoot_of_outer_eq r A i j k hij hki hkj] at h
  simpa only [neg_smul, neg_mem_iff, mul_smul, sign_smul_mem_iff] using h

private theorem interval_mem (S : LieSubalgebra A (sl (Fin (r + 1)) A))
    (he : ∀ i : Fin r, single i.castSucc i.succ
      (Fin.castSucc_lt_succ (i := i)).ne (1 : A) ∈ S)
    (hf : ∀ i : Fin r, single i.succ i.castSucc
      (Fin.castSucc_lt_succ (i := i)).ne' (1 : A) ∈ S)
    (i j : Fin r) (hij : i ≤ j) :
    specialLinearSignedRoot r A i.castSucc j.succ
        (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne ∈ S ∧
      specialLinearSignedRoot r A j.succ i.castSucc
        (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne' ∈ S := by
  have aux : ∀ n (i j : Fin r) (hij : i ≤ j), j.val = n →
      specialLinearSignedRoot r A i.castSucc j.succ
          (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne ∈ S ∧
        specialLinearSignedRoot r A j.succ i.castSucc
          (show i.castSucc < j.succ from Nat.lt_succ_of_le hij).ne' ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i j hij hj
      by_cases h : i = j
      · subst j
        exact ⟨by simpa only [signedRoot_upper] using he i,
          by simpa only [signedRoot_lower] using hf i⟩
      · have hij' : i.val < j.val := (lt_of_le_of_ne hij h : i < j)
        let k : Fin r := ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
        have hik : i ≤ k := by
          simp only [Fin.le_def]
          dsimp only [k]
          omega
        have hkn : k.val < n := by dsimp only [k]; omega
        have hks : k.succ = j.castSucc := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc]
          dsimp only [k]
          omega
        obtain ⟨hp, hn⟩ := ih k.val hkn i k hik rfl
        simp only [hks] at hp hn
        have he' : specialLinearSignedRoot r A j.castSucc j.succ
            (Fin.castSucc_lt_succ (i := j)).ne ∈ S := by
          simpa only [signedRoot_upper] using he j
        have hf' : specialLinearSignedRoot r A j.succ j.castSucc
            (Fin.castSucc_lt_succ (i := j)).ne' ∈ S := by
          simpa only [signedRoot_lower] using hf j
        exact ⟨middle_mem r A S _ _ _ _ _ _ hp he',
          outer_mem r A S _ _ _ _ _ _ hn hf'⟩
  exact aux j.val i j hij rfl

private theorem roots_mem_of_lt (S : LieSubalgebra A (sl (Fin (r + 1)) A))
    (he : ∀ i : Fin r, single i.castSucc i.succ
      (Fin.castSucc_lt_succ (i := i)).ne (1 : A) ∈ S)
    (hf : ∀ i : Fin r, single i.succ i.castSucc
      (Fin.castSucc_lt_succ (i := i)).ne' (1 : A) ∈ S)
    (i j : Fin (r + 1)) (hij : i < j) :
    specialLinearSignedRoot r A i j hij.ne ∈ S ∧
      specialLinearSignedRoot r A j i hij.ne' ∈ S := by
  let a : Fin r := ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
  let b : Fin r := ⟨j.val - 1, by have := j.isLt; omega⟩
  have ha : a.castSucc = i := rfl
  have hb : b.succ = j := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp only [b]
    have hij' : i.val < j.val := hij
    omega
  have hab : a ≤ b := by
    simp only [Fin.le_def]
    dsimp only [a, b]
    have hij' : i.val < j.val := hij
    omega
  simpa only [ha, hb] using interval_mem r A S he hf a b hab

private theorem eq_top_of_simple_mem (S : LieSubalgebra A (sl (Fin (r + 1)) A))
    (he : ∀ i : Fin r, single i.castSucc i.succ
      (Fin.castSucc_lt_succ (i := i)).ne (1 : A) ∈ S)
    (hf : ∀ i : Fin r, single i.succ i.castSucc
      (Fin.castSucc_lt_succ (i := i)).ne' (1 : A) ∈ S) : S = ⊤ := by
  apply eq_top_iff.mpr
  intro X _
  rw [← (specialLinearRootBasis r A).sum_repr X]
  apply S.sum_mem
  intro p _
  apply S.smul_mem
  cases p with
  | inl i =>
    rw [specialLinearRootBasis_inl, specialLinearCorootBasis_apply]
    obtain ⟨hp, hn⟩ := interval_mem r A S he hf i i le_rfl
    have h := S.lie_mem hp hn
    rw [lie_specialLinearSignedRoot_reverse] at h
    simpa only [mul_smul, sign_smul_mem_iff] using h
  | inr p =>
    rw [specialLinearRootBasis_inr]
    rcases lt_or_gt_of_ne p.property with h | h
    · exact (roots_mem_of_lt r A S he hf _ _ h).1
    · exact (roots_mem_of_lt r A S he hf _ _ h).2

/-- Adjacent raising and lowering matrices generate the special linear Lie algebra. -/
theorem lieSpan_specialLinear_adjacent_single_eq_top :
    LieSubalgebra.lieSpan A (sl (Fin (r + 1)) A)
      (Set.range (fun i : Fin r ↦ single i.castSucc i.succ
        (Fin.castSucc_lt_succ (i := i)).ne (1 : A)) ∪
      Set.range (fun i : Fin r ↦ single i.succ i.castSucc
        (Fin.castSucc_lt_succ (i := i)).ne' (1 : A))) = ⊤ := by
  apply eq_top_of_simple_mem
  · intro i
    exact LieSubalgebra.subset_lieSpan (Or.inl ⟨i, rfl⟩)
  · intro i
    exact LieSubalgebra.subset_lieSpan (Or.inr ⟨i, rfl⟩)

/-- Lie homomorphisms from the special linear algebra agree if they agree on adjacent
raising and lowering matrices. -/
theorem lieHom_ext_specialLinear_adjacent_single {M : Type*} [LieRing M] [LieAlgebra A M]
    (f g : sl (Fin (r + 1)) A →ₗ⁅A⁆ M)
    (he : ∀ i : Fin r, f (single i.castSucc i.succ
        (Fin.castSucc_lt_succ (i := i)).ne (1 : A)) =
      g (single i.castSucc i.succ (Fin.castSucc_lt_succ (i := i)).ne (1 : A)))
    (hf : ∀ i : Fin r, f (single i.succ i.castSucc
        (Fin.castSucc_lt_succ (i := i)).ne' (1 : A)) =
      g (single i.succ i.castSucc (Fin.castSucc_lt_succ (i := i)).ne' (1 : A))) : f = g := by
  apply DFunLike.ext
  intro X
  have hX : X ∈ LieSubalgebra.lieSpan A (sl (Fin (r + 1)) A)
      (Set.range (fun i : Fin r ↦ single i.castSucc i.succ
        (Fin.castSucc_lt_succ (i := i)).ne (1 : A)) ∪
      Set.range (fun i : Fin r ↦ single i.succ i.castSucc
        (Fin.castSucc_lt_succ (i := i)).ne' (1 : A))) := by
    rw [lieSpan_specialLinear_adjacent_single_eq_top]
    trivial
  induction hX using LieSubalgebra.lieSpan_induction with
  | mem Y hY =>
    rcases hY with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact he i
    · exact hf i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]
  | lie x y _ _ hx hy => simp [hx, hy]

end TauCeti
