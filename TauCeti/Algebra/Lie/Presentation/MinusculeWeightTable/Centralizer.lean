/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
import TauCeti.Data.List.Involutive

/-!
# Scalar centralizers in a minuscule weight basis

If a finite minuscule table has one highest weight and its reflection graph is connected,
its raising and lowering matrices have scalar joint centralizer over every commutative ring.
The proof first identifies the simultaneous raising kernel, then propagates a scalar value
on the highest-weight vector along the reflection graph. No division is used.

## Main results

* `TauCeti.MinusculeWeightTable.eq_smul_single_of_raisingMatrix_mulVec_eq_zero`: a vector killed
  by every raising matrix is supported at the unique highest weight.
* `TauCeti.MinusculeWeightTable.commute_raising_lowering_iff_eq_smul_one`: the joint centralizer
  of the raising and lowering matrices is scalar.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι R : Type*} [Fintype ι] [DecidableEq ι]
    (T : MinusculeWeightTable B ι)

/-- If each weight other than `h` has a negative simple coordinate, every vector killed by
all raising matrices is supported at `h`. -/
theorem eq_smul_single_of_raisingMatrix_mulVec_eq_zero [NonAssocRing R] (h : ι)
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

variable [CommRing R]

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
  · simpa only [(T.reflection_eq_self_iff i a).2 hz] using ha
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
      exact (predicate_foldl_iff_of_involutive
        (fun b ↦ M *ᵥ Pi.single b 1 = M h h • Pi.single b 1) T.reflection
        T.reflection_apply_apply
        (fun a i ha ↦ T.mulVec_single_reflection M (M h h) i a (hM i).1 (hM i).2 ha) l h).mpr hh
    ext a b
    have hb := congrFun (hcol b) a
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply, Pi.single_apply]
      using hb
  · intro hM i
    rw [hM]
    constructor <;> exact (Commute.one_left _).smul_left _

end TauCeti.MinusculeWeightTable
