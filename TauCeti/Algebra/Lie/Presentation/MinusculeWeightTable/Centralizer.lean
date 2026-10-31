/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic

/-!
# Scalar centralizers in a minuscule weight basis

If a finite minuscule table has one highest weight and its reflection graph is connected,
its raising and lowering matrices have scalar joint centralizer over every commutative ring.
The proof first identifies the simultaneous raising kernel, then propagates a scalar value
on the highest-weight vector along the reflection graph. No division is used.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (T : MinusculeWeightTable B ι)

private theorem raisingMatrix_map_mulVec_reflection (i : B) (a : ι)
    (ha : T.weight a i = -1) (v : ι → R) :
    ((T.raisingMatrix i).map (Int.cast : ℤ → R) *ᵥ v) (T.reflection i a) = v a := by
  have hrow : ((T.raisingMatrix i).map (Int.cast : ℤ → R)) (T.reflection i a) =
      Pi.single a 1 := by
    funext b
    by_cases hb : b = a
    · subst b
      simp [ha]
    · have hs : T.reflection i a ≠ T.reflection i b := by
        intro h
        apply hb
        simpa only [T.reflection_apply_apply] using (congrArg (T.reflection i) h).symm
      simp [hs, hb]
  change dotProduct (((T.raisingMatrix i).map (Int.cast : ℤ → R))
    (T.reflection i a)) v = v a
  rw [hrow]
  simp [dotProduct, Pi.single_apply]

/-- If each weight other than `h` has a negative simple coordinate, every vector killed by
all raising matrices is supported at `h`. -/
theorem eq_smul_single_of_raisingMatrix_mulVec_eq_zero (h : ι)
    (hhighest : ∀ a, a ≠ h → ∃ i, T.weight a i = -1) (v : ι → R)
    (hv : ∀ i, (T.raisingMatrix i).map (Int.cast : ℤ → R) *ᵥ v = 0) :
    v = v h • Pi.single h 1 := by
  funext a
  by_cases ha : a = h
  · subst a
    simp
  · obtain ⟨i, hi⟩ := hhighest a ha
    have hz := congrFun (hv i) (T.reflection i a)
    rw [T.raisingMatrix_map_mulVec_reflection i a hi v] at hz
    simpa [Pi.single_apply, ha] using hz

omit [Fintype ι] [DecidableEq ι] in
private theorem reflection_eq_self_of_weight_eq_zero (i : B) (a : ι)
    (ha : T.weight a i = 0) : T.reflection i a = a := by
  apply T.weight_injective
  funext j
  simp [T.weight_reflection, ha]

private theorem mulVec_single_reflection (M : Matrix ι ι R) (c : R) (i : B) (a : ι)
    (hE : Commute M ((T.raisingMatrix i).map (Int.cast : ℤ → R)))
    (hF : Commute M ((T.loweringMatrix i).map (Int.cast : ℤ → R)))
    (ha : M *ᵥ Pi.single a 1 = c • Pi.single a 1) :
    M *ᵥ Pi.single (T.reflection i a) 1 = c • Pi.single (T.reflection i a) 1 := by
  have step (N : Matrix ι ι R) (hN : Commute M N)
      (hc : N *ᵥ Pi.single a 1 = Pi.single (T.reflection i a) 1) :
      M *ᵥ Pi.single (T.reflection i a) 1 = c • Pi.single (T.reflection i a) 1 := by
    rw [← hc, Matrix.mulVec_mulVec, hN.eq, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_smul]
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one a i with hn | hz | hp
  · exact step _ hE (by rw [Matrix.mulVec_single_one, T.raisingMatrix_map_col, ite_eq_left hn])
  · simpa only [T.reflection_eq_self_of_weight_eq_zero i a hz] using ha
  · exact step _ hF (by rw [Matrix.mulVec_single_one, T.loweringMatrix_map_col, ite_eq_left hp])

/-- The joint centralizer of raising and lowering matrices is scalar when the table has a
unique highest weight and every weight is reachable from it by simple reflections. -/
theorem commute_raising_lowering_iff_eq_smul_one (h : ι)
    (hnotneg : ∀ i, T.weight h i ≠ -1)
    (hhighest : ∀ a, a ≠ h → ∃ i, T.weight a i = -1)
    (hconnected : ∀ a, ∃ l : List B, l.foldl (fun b i ↦ T.reflection i b) h = a)
    (M : Matrix ι ι R) :
    (∀ i, Commute M ((T.raisingMatrix i).map (Int.cast : ℤ → R)) ∧
      Commute M ((T.loweringMatrix i).map (Int.cast : ℤ → R))) ↔
      M = M h h • 1 := by
  constructor
  · intro hM
    have hh : M *ᵥ Pi.single h 1 = M h h • Pi.single h 1 := by
      have hk : ∀ i, (T.raisingMatrix i).map (Int.cast : ℤ → R) *ᵥ
          (M *ᵥ Pi.single h 1) = 0 := by
        intro i
        rw [Matrix.mulVec_mulVec, ← (hM i).1.eq, ← Matrix.mulVec_mulVec,
          Matrix.mulVec_single_one, T.raisingMatrix_map_col, ite_eq_right (hnotneg i),
          Matrix.mulVec_zero]
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using
        T.eq_smul_single_of_raisingMatrix_mulVec_eq_zero h hhighest _ hk
    have hcol (a : ι) : M *ᵥ Pi.single a 1 = M h h • Pi.single a 1 := by
      obtain ⟨l, rfl⟩ := hconnected a
      have word (l : List B) (a : ι)
          (ha : M *ᵥ Pi.single a 1 = M h h • Pi.single a 1) :
          M *ᵥ Pi.single (l.foldl (fun b i ↦ T.reflection i b) a) 1 =
            M h h • Pi.single (l.foldl (fun b i ↦ T.reflection i b) a) 1 := by
        induction l generalizing a with
        | nil => exact ha
        | cons i l ih =>
          exact ih _ (T.mulVec_single_reflection M (M h h) i a (hM i).1 (hM i).2 ha)
      exact word l h hh
    ext a b
    have hb := congrFun (hcol b) a
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply, Pi.single_apply]
      using hb
  · intro hM i
    rw [hM]
    constructor <;> exact (Commute.one_left _).smul_left _

end TauCeti.MinusculeWeightTable
