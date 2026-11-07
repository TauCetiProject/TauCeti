/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.TitsSystem
import Mathlib.Data.Fintype.Fin
import TauCeti.Data.Fin.Basic

/-!
# Standard block weights for general linear groups

A subset `J` of the adjacent indices of `GLₙ₊₁` specifies which adjacent coordinates
belong to the same block. The standard weight starts at zero and drops by one at each
index outside `J`. Its weight-parabolic ideal therefore forbids precisely the matrix
entries crossing a retained cut below the diagonal.

The resulting ideals form an order embedding of the subsets of `Fin n`, with the ideal
order reversed. In particular distinct labels give distinct subgroup schemes over any
nontrivial commutative base ring. The empty label gives the upper-triangular subgroup,
and the full label gives the whole general linear group. These statements identify the
labels independently of any classification of closed subgroups.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §30.1 (standard parabolics).
* The matrix and Tits-system comparison uses
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.TitsSystem`.
-/

public section

namespace TauCeti.GeneralLinear

universe u v

variable {n : ℕ}

/-- The weight starting at zero and dropping by one at exactly the adjacent indices
outside `J`. Thus `J` records the simple roots retained in the Levi blocks. -/
def standardWeight (J : Finset (Fin n)) (i : Fin (n + 1)) : ℤ :=
  -((Finset.univ.filter fun j : Fin n ↦ j.val < i.val ∧ j ∉ J).card : ℤ)

/-- The counting formula for a standard block weight. -/
theorem standardWeight_apply (J : Finset (Fin n)) (i : Fin (n + 1)) :
    standardWeight J i =
      -((Finset.univ.filter fun j : Fin n ↦ j.val < i.val ∧ j ∉ J).card : ℤ) :=
  (rfl)

/-- Crossing an omitted adjacent pair decreases the normalized weight by one. -/
theorem standardWeight_succ (J : Finset (Fin n)) (i : Fin n) :
    standardWeight J i.succ = standardWeight J i.castSucc - if i ∈ J then 0 else 1 := by
  have hfilter (a : Fin (n + 1)) :
      (Finset.univ.filter fun j : Fin n ↦ j.val < a.val ∧ j ∉ J) =
        (Finset.univ \ J).filter (fun j ↦ j.castSucc < a) := by
    ext j
    simp [and_comm, Fin.lt_def]
  rw [standardWeight_apply, standardWeight_apply, hfilter, hfilter]
  have h := Finset.card_filter_castSucc_lt_succ (Finset.univ \ J) i
  rw [h]
  by_cases hi : i ∈ J <;> simp [hi, sub_eq_add_neg, add_comm]

/-- Standard block weights are decreasing. -/
theorem standardWeight_antitone (J : Finset (Fin n)) : Antitone (standardWeight J) := by
  intro i j hij
  simp only [standardWeight, neg_le_neg_iff, Nat.cast_le]
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ⟨ha.1.trans_le hij, ha.2⟩

/-- A strict weight drop occurs exactly when there is an omitted adjacent index between
the two coordinates. This describes all forbidden matrix entries of the weight parabolic. -/
theorem standardWeight_lt_iff (J : Finset (Fin n)) (i j : Fin (n + 1)) :
    standardWeight J i < standardWeight J j ↔
      ∃ a : Fin n, j.val ≤ a.val ∧ a.val < i.val ∧ a ∉ J := by
  simp only [standardWeight, neg_lt_neg_iff, Nat.cast_lt]
  constructor
  · intro h
    obtain ⟨a, ha, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact ⟨a, le_of_not_gt (fun hja ↦ hb ⟨hja, ha.2⟩), ha.1, ha.2⟩
  · rintro ⟨a, hja, hai, haJ⟩
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact ⟨by omega, hb.2⟩
    · intro heq
      have ha : a ∈ Finset.univ.filter (fun b : Fin n ↦ b.val < i.val ∧ b ∉ J) := by
        simp [hai, haJ]
      rw [← heq] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      omega

/-- Equal weights on adjacent coordinates recover exactly the chosen label. -/
@[simp]
theorem standardWeight_castSucc_eq_succ_iff (J : Finset (Fin n)) (i : Fin n) :
    standardWeight J i.castSucc = standardWeight J i.succ ↔ i ∈ J := by
  have hle := standardWeight_antitone J (Fin.castSucc_le_succ i)
  have hlt := standardWeight_lt_iff J i.succ i.castSucc
  simp only [Fin.val_castSucc, Fin.val_succ] at hlt
  have h : (∃ a : Fin n, i.val ≤ a.val ∧ a.val < i.val + 1 ∧ a ∉ J) ↔ i ∉ J := by
    constructor
    · rintro ⟨a, ha, hb, haJ⟩
      have : a = i := Fin.ext (by omega)
      simpa [this] using haJ
    · exact fun hi ↦ ⟨i, le_rfl, Nat.lt_succ_self _, hi⟩
  rw [h] at hlt
  constructor
  · intro heq
    by_contra hi
    exact (hlt.mpr hi).ne heq.symm
  · intro hi
    exact le_antisymm (le_of_not_gt (fun hdrop ↦ (hlt.mp hdrop) hi)) hle

/-- The first standard weight is zero, including in dimension one. -/
@[simp]
theorem standardWeight_zero (J : Finset (Fin n)) : standardWeight J 0 = 0 := by
  simp [standardWeight]

/-- Omitting every adjacent index gives the strictly decreasing weight `i ↦ -i`. -/
@[simp]
theorem standardWeight_empty (i : Fin (n + 1)) :
    standardWeight (∅ : Finset (Fin n)) i = -(i.val : ℤ) := by
  simp [standardWeight, Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt_succ i.isLt)]

/-- Retaining every adjacent index gives the constant zero weight. -/
@[simp]
theorem standardWeight_univ (i : Fin (n + 1)) :
    standardWeight (Finset.univ : Finset (Fin n)) i = 0 := by
  simp [standardWeight]

variable (R : Type u) [CommRing R]

/-- A matrix lies in the standard weight parabolic exactly when its entries below every
retained cut vanish. The cut indices are the complement of the Levi label `J`. -/
theorem mem_weightParabolicPoints_standardWeight_iff (J : Finset (Fin n))
    {A : Type v} [CommRing A] [Algebra R A] (g : GL (Fin (n + 1)) A) :
    g ∈ weightParabolicPoints R (standardWeight J) A ↔
      ∀ (i j : Fin (n + 1)) (a : Fin n),
        j.val ≤ a.val → a.val < i.val → a ∉ J → (g : Matrix _ _ A) i j = 0 := by
  rw [mem_weightParabolicPoints_iff]
  simp only [standardWeight_lt_iff]
  constructor
  · intro h i j a hja hai haJ
    exact h i j ⟨a, hja, hai, haJ⟩
  · rintro h i j ⟨a, hja, hai, haJ⟩
    exact h i j a hja hai haJ

/-- Enlarging the Levi label removes equations, reversing the inclusion of defining ideals. -/
theorem weightParabolicDefiningHopfIdeal_standardWeight_antitone :
    Antitone fun J : Finset (Fin n) ↦
      weightParabolicDefiningHopfIdeal R (standardWeight J) := by
  intro J K hJK
  apply weightParabolicDefiningHopfIdeal_mono
  intro i j hij
  obtain ⟨a, hja, hai, haK⟩ := (standardWeight_lt_iff K i j).mp hij
  exact (standardWeight_lt_iff J i j).mpr
    ⟨a, hja, hai, fun haJ ↦ haK (hJK haJ)⟩

/-- The empty label defines the upper-triangular subgroup, despite the different additive
normalization of its weights. -/
@[simp]
theorem weightParabolicDefiningHopfIdeal_standardWeight_empty :
    weightParabolicDefiningHopfIdeal R (standardWeight (∅ : Finset (Fin n))) =
      UpperTriangular.definingHopfIdeal R (n + 1) := by
  rw [UpperTriangular.definingHopfIdeal]
  apply le_antisymm <;> apply weightParabolicDefiningHopfIdeal_mono
  all_goals
    intro i j hij
    simpa only [standardWeight_empty, UpperTriangular.weights_lt_weights_iff,
      neg_lt_neg_iff, Nat.cast_lt, Fin.lt_def] using hij

/-- The full label imposes no equations, so it defines the whole general linear group. -/
@[simp]
theorem weightParabolicDefiningHopfIdeal_standardWeight_univ :
    weightParabolicDefiningHopfIdeal R (standardWeight (Finset.univ : Finset (Fin n))) = ⊥ := by
  have hrel : weightParabolicRelationSet R
      (standardWeight (Finset.univ : Finset (Fin n))) = ∅ := by
    ext x
    simp
  apply le_bot_iff.mp
  rw [← HopfIdeal.toIdeal_le_toIdeal]
  simp [weightParabolicDefiningHopfIdeal_toIdeal, hrel]

/-- The defining-ideal order detects the Levi labels over any nontrivial base ring.
The order is reversed because larger closed subgroups have smaller ideals. -/
@[simp]
theorem weightParabolicDefiningHopfIdeal_standardWeight_le_iff [Nontrivial R]
    (J K : Finset (Fin n)) :
    weightParabolicDefiningHopfIdeal R (standardWeight K) ≤
      weightParabolicDefiningHopfIdeal R (standardWeight J) ↔ J ⊆ K := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦
    weightParabolicDefiningHopfIdeal_standardWeight_antitone R h⟩
  have hpoints := weightParabolicPoints_le_of_weightParabolicDefiningHopfIdeal_le R
    (standardWeight J) (standardWeight K) h (A := R)
  have hswap := hpoints ((permutationGL_swap_mem_weightParabolicPoints_iff R
    (standardWeight J) i.castSucc i.succ).mpr
      ((standardWeight_castSucc_eq_succ_iff J i).mpr hi))
  exact (standardWeight_castSucc_eq_succ_iff K i).mp
    ((permutationGL_swap_mem_weightParabolicPoints_iff R
      (standardWeight K) i.castSucc i.succ).mp hswap)

/-- Standard weight-parabolic ideals embed the subset lattice with geometric inclusion,
that is, with the order on Hopf ideals reversed. -/
noncomputable def standardWeightParabolicOrderEmbedding [Nontrivial R] :
    Finset (Fin n) ↪o (HopfIdeal R (coordinateHopfAlgebra R (n + 1)))ᵒᵈ :=
  OrderEmbedding.ofMapLEIff
    (fun J ↦ OrderDual.toDual (weightParabolicDefiningHopfIdeal R (standardWeight J)))
    (fun J K ↦ weightParabolicDefiningHopfIdeal_standardWeight_le_iff R J K)

/-- Evaluation of the standard-parabolic label embedding. -/
@[simp]
theorem standardWeightParabolicOrderEmbedding_apply [Nontrivial R] (J : Finset (Fin n)) :
    standardWeightParabolicOrderEmbedding R J =
      OrderDual.toDual (weightParabolicDefiningHopfIdeal R (standardWeight J)) :=
  (rfl)

end TauCeti.GeneralLinear
