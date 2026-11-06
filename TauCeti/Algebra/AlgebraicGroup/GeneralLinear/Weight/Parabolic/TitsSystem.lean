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
the Bruhat decomposition to the concrete weight-parabolic subgroup. Conversely, every
subgroup containing the upper-triangular group is a weight parabolic: choose a decreasing
weight whose equal adjacent coordinates are those of the transpositions the subgroup contains.

## Main declarations

* `TauCeti.GeneralLinear.bruhatCell_glTitsSystemSimpleRep_subset_iff`: a subgroup containing
  the upper-triangular group contains a simple Bruhat cell exactly when it contains the
  corresponding adjacent transposition.
* `TauCeti.GeneralLinear.standardParabolic_weightParabolicSimple`: the points of a decreasing
  weight parabolic form the standard parabolic of its equal-weight adjacent transpositions.
* `TauCeti.GeneralLinear.exists_antitone_weightParabolicPoints_eq`: every subgroup of
  `GLₙ₊₁(k)` containing the upper-triangular group is the group of points of a decreasing
  weight parabolic.

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

/-- For every set `S` of adjacent coordinate pairs there is a decreasing weight whose adjacent
coordinates have equal weight exactly at `S`: subtract one at each step not in `S`. -/
private theorem exists_antitone_forall_eq_iff {n : ℕ} (S : Set (Fin n)) :
    ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ ∀ i : Fin n, w i.castSucc = w i.succ ↔ i ∈ S := by
  classical
  let c (i : Fin (n + 1)) : Finset (Fin n) := Finset.univ.filter fun j ↦ (j : ℕ) < i ∧ j ∉ S
  have hc {i i' : Fin (n + 1)} (h : i ≤ i') : c i ⊆ c i' := fun j hj ↦ by
    simp only [c, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1.trans_le (Fin.le_iff_val_le_val.mp h), hj.2⟩
  refine ⟨fun i ↦ -((c i).card : ℤ), fun i i' h ↦ by simpa using Finset.card_le_card (hc h),
    fun i ↦ ?_⟩
  simp only [neg_inj, Nat.cast_inj]
  constructor
  · -- If `i ∉ S`, then `i` is counted at `i.succ` but not at `i.castSucc`.
    intro h
    by_contra hi
    have hlt : c i.castSucc ⊂ c i.succ :=
      (Finset.ssubset_iff_of_subset (hc (Fin.castSucc_le_succ i))).mpr ⟨i, by simp [c, hi]⟩
    exact (Finset.card_lt_card hlt).ne h
  · intro hi
    congr 1
    ext j
    simp only [c, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, Fin.val_castSucc]
    refine ⟨fun ⟨hj, hjS⟩ ↦ ⟨by omega, hjS⟩, fun ⟨hj, hjS⟩ ↦ ⟨?_, hjS⟩⟩
    exact lt_of_le_of_ne (by omega) fun h ↦ hjS (Fin.ext h ▸ hi)

section Field

variable (k : Type u) [Field k] [Nontrivial kˣ] {n : ℕ} (w : Fin (n + 1) → ℤ)

/-- The simple reflections selected by a decreasing weight filtration: the adjacent
transpositions that exchange coordinates of equal weight. -/
def weightParabolicSimple : Set (glTitsSystem k n).simple :=
  {s | ∃ i : Fin n, w i.castSucc = w i.succ ∧
    (s : (glTitsSystem k n).WeylGroup) =
      QuotientGroup.mk (glTitsSystemSimpleRep k n i)}

/-- A subgroup of `GLₙ₊₁(k)` containing the upper-triangular group contains the Bruhat cell of
the `i`-th simple reflection exactly when it contains the permutation matrix of the
transposition of `i` and `i + 1`. -/
theorem bruhatCell_glTitsSystemSimpleRep_subset_iff {H : Subgroup (GL (Fin (n + 1)) k)}
    (hB : (glTitsSystem k n).subgroupB ≤ H) (i : Fin n) :
    (glTitsSystem k n).bruhatCell (QuotientGroup.mk (glTitsSystemSimpleRep k n i)) ⊆ H ↔
      permutationGL (k := k) (Equiv.swap i.castSucc i.succ) ∈ H := by
  have hrep : (glTitsSystemSimpleRep k n i : GL (Fin (n + 1)) k) ∈
      (glTitsSystem k n).bruhatCell (QuotientGroup.mk (glTitsSystemSimpleRep k n i)) := by
    rw [TitsSystem.bruhatCell_mk]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [coe_glTitsSystemSimpleRep] at hrep
  exact ⟨fun h ↦ h hrep, (glTitsSystem k n).bruhatCell_subset_of_mem hB hrep⟩

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
  rw [← hi, bruhatCell_glTitsSystemSimpleRep_subset_iff k hB,
    permutationGL_swap_mem_weightParabolicPoints_iff]
  constructor
  · rintro ⟨j, hj, hs⟩
    have hj' := (bruhatCell_glTitsSystemSimpleRep_subset_iff k hB j).mpr
      ((permutationGL_swap_mem_weightParabolicPoints_iff k w j.castSucc j.succ).mpr hj)
    rwa [← hs, ← hi, bruhatCell_glTitsSystemSimpleRep_subset_iff k hB,
      permutationGL_swap_mem_weightParabolicPoints_iff] at hj'
  · exact fun h ↦ ⟨i, h, hi.symm⟩

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

/-- **Subgroups of `GLₙ₊₁(k)` containing the upper-triangular group are block triangular.**
Over a field with a nontrivial unit group, every subgroup of `GLₙ₊₁(k)` containing the
invertible upper-triangular matrices is the group of `k`-points of the weight parabolic of a
decreasing integer weight. -/
theorem exists_antitone_weightParabolicPoints_eq {H : Subgroup (GL (Fin (n + 1)) k)}
    (hH : upperTriangularGroup (Fin (n + 1)) k ≤ H) :
    ∃ w : Fin (n + 1) → ℤ, Antitone w ∧ weightParabolicPoints k w k = H := by
  rw [← glTitsSystem_subgroupB k n] at hH
  -- Select the adjacent transpositions lying in `H`.
  obtain ⟨w, hw, hwS⟩ := exists_antitone_forall_eq_iff
    {i : Fin n | permutationGL (k := k) (Equiv.swap i.castSucc i.succ) ∈ H}
  have hBw : (glTitsSystem k n).subgroupB ≤ weightParabolicPoints k w k := by
    rw [glTitsSystem_subgroupB]
    exact upperTriangularGroup_le_weightParabolicPoints hw
  refine ⟨w, hw, ?_⟩
  -- Both subgroups are the standard parabolic of the same simple reflections.
  rw [← standardParabolic_weightParabolicSimple k w hw,
    ← (glTitsSystem k n).standardParabolic_eq_of_subgroupB_le hH]
  congr 1
  ext s
  obtain ⟨i, hi⟩ : (s : (glTitsSystem k n).WeylGroup) ∈ Set.range fun i : Fin n ↦
      (QuotientGroup.mk (glTitsSystemSimpleRep k n i) : (glTitsSystem k n).WeylGroup) := by
    rw [← glTitsSystem_simple]
    exact s.property
  rw [mem_weightParabolicSimple_iff k w hw, Set.mem_ofPred_eq, ← hi,
    bruhatCell_glTitsSystemSimpleRep_subset_iff k hBw,
    bruhatCell_glTitsSystemSimpleRep_subset_iff k hH,
    permutationGL_swap_mem_weightParabolicPoints_iff, hwS, Set.mem_ofPred_eq]

end Field

end

end TauCeti.GeneralLinear
