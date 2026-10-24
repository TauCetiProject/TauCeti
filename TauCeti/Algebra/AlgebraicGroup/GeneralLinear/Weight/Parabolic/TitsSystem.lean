/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.TitsSystem
public import TauCeti.GroupTheory.TitsSystem.Parabolic.Classification

/-!
# Weight parabolics and the standard general-linear Tits system

For decreasing integer weights on the coordinates of `GLₙ₊₁(k)`, the points of the
weight-parabolic subgroup scheme form the standard parabolic of its Tits system selected
by adjacent coordinates of equal weight. Thus the block-triangular definition and the
BN-pair definition give the same subgroup. The comparison assumes the unit group of the
field is nontrivial, as does the Tits system defined using the diagonal-torus normalizer.

`weightParabolicPoints` records the matrix image of the existing closed-subgroup points
over an arbitrary commutative algebra. Its characteristic lemma expresses membership by
the forbidden matrix entries. Transpositions belong precisely when they exchange equal
weights; this identifies the selected simple reflections without choosing Bruhat factors.

The comparison uses `TitsSystem.standardParabolic_eq_of_subgroupB_le`, the classification
of subgroups containing the upper-triangular group. The final cell criterion transfers
the Bruhat decomposition to the concrete weight-parabolic subgroup.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§28–29.
* T. A. Springer, *Linear Algebraic Groups*, second edition, §8.4.
-/

public section

namespace TauCeti.GeneralLinear

universe u v

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ} (w : Fin N → ℤ)

/-- A coordinate transposition lies in a weight parabolic exactly when its two weights
are equal. Use this as a named rewrite: the general entry-vanishing criterion is the
simplifier normal form for membership. -/
theorem permutationGL_swap_mem_weightParabolicPoints_iff {A : Type v}
    [CommRing A] [Nontrivial A] [Algebra R A] (i j : Fin N) :
    permutationGL (k := A) (Equiv.swap i j) ∈ weightParabolicPoints R w A ↔ w i = w j := by
  rw [mem_weightParabolicPoints_iff]
  constructor
  · intro h
    apply le_antisymm
    · by_contra hle
      have hz := h j i (lt_of_not_ge hle)
      simp [permutationGL_coe] at hz
    · by_contra hle
      have hz := h i j (lt_of_not_ge hle)
      simp [permutationGL_coe] at hz
  · intro hij a b hab
    rw [permutationGL_coe]
    by_cases ha : a = i
    · subst a
      have hb : b ≠ j := fun h ↦ hab.ne (h ▸ hij)
      simpa [eq_comm] using hb
    · by_cases ha' : a = j
      · subst a
        have hb : b ≠ i := fun h ↦ hab.ne (h ▸ hij.symm)
        simpa [ha, Equiv.swap_apply_right, eq_comm] using hb
      · have hab' : a ≠ b := fun h ↦ hab.ne (congrArg w h)
        simp [Equiv.swap_apply_of_ne_of_ne ha ha', hab']

variable {R w}

/-- Decreasing weights make the weight parabolic contain every upper-triangular matrix. -/
theorem upperTriangularGroup_le_weightParabolicPoints {A : Type v} [CommRing A]
    [Algebra R A] (hw : Antitone w) :
    upperTriangularGroup (Fin N) A ≤ weightParabolicPoints R w A := by
  intro g hg
  rw [mem_weightParabolicPoints_iff]
  intro i j hij
  exact (UpperTriangularGroup.mem_iff.mp hg)
    (lt_of_not_ge fun h ↦ (not_lt_of_ge (hw h)) hij)

section Field

variable (k : Type u) [Field k] [Nontrivial kˣ] {n : ℕ} (w : Fin (n + 1) → ℤ)

/-- The simple reflections selected by a decreasing weight filtration: the adjacent
transpositions that exchange coordinates of equal weight. -/
def weightParabolicSimple : Set (glTitsSystem k n).simple :=
  {s | ∃ i : Fin n, w i.castSucc = w i.succ ∧
    (s : (glTitsSystem k n).WeylGroup) =
      QuotientGroup.mk (glTitsSystemSimpleRep k n i)}

/-- The selected simple reflections are exactly the simple Bruhat cells contained in the
weight parabolic. -/
theorem mem_weightParabolicSimple_iff (hw : Antitone w) (s : (glTitsSystem k n).simple) :
    s ∈ weightParabolicSimple k w ↔
      (glTitsSystem k n).bruhatCell s ⊆ weightParabolicPoints k w k := by
  have hB : (glTitsSystem k n).subgroupB ≤ weightParabolicPoints k w k := by
    rw [glTitsSystem_subgroupB]
    exact upperTriangularGroup_le_weightParabolicPoints hw
  have hs := s.property
  simp only [glTitsSystem_simple, Set.mem_range] at hs
  obtain ⟨i, hi⟩ := hs
  have hrep : (glTitsSystemSimpleRep k n i : GL (Fin (n + 1)) k) ∈
      (glTitsSystem k n).bruhatCell s.val := by
    rw [← hi, TitsSystem.bruhatCell_mk]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  constructor
  · rintro ⟨j, hj, hs⟩
    have hrepj : (glTitsSystemSimpleRep k n j : GL (Fin (n + 1)) k) ∈
        (glTitsSystem k n).bruhatCell s.val := by
      rw [hs, TitsSystem.bruhatCell_mk]
      exact DoubleCoset.mem_doubleCoset_self _ _ _
    apply (glTitsSystem k n).bruhatCell_subset_of_mem hB hrepj
    rw [coe_glTitsSystemSimpleRep]
    exact (permutationGL_swap_mem_weightParabolicPoints_iff k w (A := k)
      j.castSucc j.succ).mpr hj
  · intro h
    refine ⟨i, ?_, hi.symm⟩
    have hm := h hrep
    rw [coe_glTitsSystemSimpleRep] at hm
    exact (permutationGL_swap_mem_weightParabolicPoints_iff k w (A := k)
      i.castSucc i.succ).mp hm

/-- The matrix points of a decreasing weight-parabolic subgroup scheme are exactly the
standard parabolic selected by its equal-weight adjacent coordinates. -/
theorem standardParabolic_weightParabolicSimple (hw : Antitone w) :
    (glTitsSystem k n).standardParabolic (weightParabolicSimple k w) =
      weightParabolicPoints k w k := by
  have hB : (glTitsSystem k n).subgroupB ≤ weightParabolicPoints k w k := by
    rw [glTitsSystem_subgroupB]
    exact upperTriangularGroup_le_weightParabolicPoints hw
  convert (glTitsSystem k n).standardParabolic_eq_of_subgroupB_le hB using 2
  ext s
  exact mem_weightParabolicSimple_iff k w hw s

/-- On a Bruhat cell, the block-triangular condition is membership of its Weyl index in
the subgroup generated by equal-weight adjacent transpositions. -/
theorem mem_weightParabolicPoints_iff_of_mem_bruhatCell (hw : Antitone w)
    {g : GL (Fin (n + 1)) k} {σ : (glTitsSystem k n).WeylGroup}
    (hg : g ∈ (glTitsSystem k n).bruhatCell σ) :
    g ∈ weightParabolicPoints k w k ↔
      σ ∈ Subgroup.closure (Subtype.val '' weightParabolicSimple k w) := by
  rw [← standardParabolic_weightParabolicSimple k w hw]
  exact (glTitsSystem k n).mem_standardParabolic_iff_of_mem_bruhatCell hg

end Field

end

end TauCeti.GeneralLinear
