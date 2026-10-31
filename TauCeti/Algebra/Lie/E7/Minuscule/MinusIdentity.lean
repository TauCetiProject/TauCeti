/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Frobenius
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.WeylElement

/-!
# Minus the identity as a root word in the E7 minuscule carrier

The word `W₁² W₄² W₆²`, with zero-based native node indices and
`Wᵢ = xᵢ(1) yᵢ(1)⁻¹ xᵢ(1)`, has matrix `-1`. It belongs to every subgroup
containing the fourteen unit-parameter simple-root points, and is central
there. In particular Frobenius fixes it. This constructs the scalar element
needed for the center of the intrinsic derived subgroup without assuming
that the root points generate the full carrier.
-/

public section

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

noncomputable section

private theorem weight_sum_mod_two (a : Fin 56) :
    (e7MinusculeWeight a 1 + e7MinusculeWeight a 4 + e7MinusculeWeight a 6) % 2 = 1 := by
  have hstep (i : Fin 7) (b : Fin 56)
      (hb : (e7MinusculeWeight b 1 + e7MinusculeWeight b 4 +
        e7MinusculeWeight b 6) % 2 = 1) :
      (e7MinusculeWeight (e7MinusculeReflection i b) 1 +
        e7MinusculeWeight (e7MinusculeReflection i b) 4 +
        e7MinusculeWeight (e7MinusculeReflection i b) 6) % 2 = 1 := by
    rw [← weightTable_weight, ← weightTable_reflection]
    rw [weightTable.weight_reflection, weightTable.weight_reflection,
      weightTable.weight_reflection, weightTable_weight, weightTable_cartanMatrix]
    fin_cases i <;> norm_num [CartanMatrix.E_seven_eq] at * <;> omega
  obtain ⟨l, hl⟩ := exists_e7MinusculeReflections_eq a
  rw [← hl]
  clear a hl
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l i ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact hstep i _ ih

private theorem weight_sign_product (R : Type*) [CommRing R] (a : Fin 56) :
    (if e7MinusculeWeight a 1 = 0 then (1 : R) else -1) *
        (if e7MinusculeWeight a 4 = 0 then (1 : R) else -1) *
        (if e7MinusculeWeight a 6 = 0 then (1 : R) else -1) = -1 := by
  have h := weight_sum_mod_two a
  rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a 1 with h₁ | h₁ | h₁ <;>
    rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a 4 with h₄ | h₄ | h₄ <;>
    rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a 6 with h₆ | h₆ | h₆ <;>
    simp_all

variable (R : Type*) [CommRing R]

/-- The simple Weyl representative formed from unit-parameter root points. -/
def weylElement (i : Fin 7) : points R :=
  rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
    (rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd 1))⁻¹ *
    rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1)

/-- The defining product of the simple Weyl representative. -/
theorem weylElement_def (i : Fin 7) :
    weylElement R i = rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
      (rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd 1))⁻¹ *
      rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) := (rfl)

/-- The matrix of the simple Weyl representative is the minuscule rank-one word. -/
@[simp]
theorem coe_weylElement (i : Fin 7) :
    ((weylElement R i : Matrix.GeneralLinearGroup (Fin 56) R) :
      Matrix (Fin 56) (Fin 56) R) = weightTable.weylMatrix R i := by
  have hinv : (rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd 1))⁻¹ =
      rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) := by
    rw [← map_inv]
    rfl
  have hF : weightTable.loweringMatrix i = loweringMatrix i := by
    ext a b
    rw [weightTable.loweringMatrix_apply, loweringMatrix_apply,
      weightTable_weight, weightTable_reflection]
  rw [weylElement_def, hinv]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_rootSubgroupPoints_inl, coe_rootSubgroupPoints_inr]
  simp [MinusculeWeightTable.weylMatrix_def, weightTable_raisingMatrix, hF,
    sub_eq_add_neg]

/-- The root word whose matrix is minus the identity. -/
def minusIdentity : points R :=
  weylElement R 1 ^ 2 * weylElement R 4 ^ 2 * weylElement R 6 ^ 2

/-- The defining product of the root word for minus the identity. -/
theorem minusIdentity_def :
    minusIdentity R = weylElement R 1 ^ 2 * weylElement R 4 ^ 2 *
      weylElement R 6 ^ 2 := (rfl)

/-- The chosen root word acts as minus the identity on all fifty-six weights. -/
@[simp]
theorem coe_minusIdentity :
    ((minusIdentity R : Matrix.GeneralLinearGroup (Fin 56) R) :
      Matrix (Fin 56) (Fin 56) R) = -1 := by
  simp only [minusIdentity_def, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul,
    Units.val_pow_eq_pow_val]
  rw [coe_weylElement, coe_weylElement, coe_weylElement,
    weightTable.weylMatrix_pow_two, weightTable.weylMatrix_pow_two,
    weightTable.weylMatrix_pow_two, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, weightTable_weight]
  ext a b
  by_cases hab : a = b
  · subst b
    simpa using weight_sign_product R a
  · simp [hab]

/-- Every subgroup containing the unit-parameter root points contains the Weyl word. -/
theorem weylElement_mem (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H) (i : Fin 7) :
    weylElement R i ∈ H :=
  H.mul_mem (H.mul_mem (hroots (.inl i)) (H.inv_mem (hroots (.inr i)))) (hroots (.inl i))

/-- Minus the identity belongs to any subgroup containing the unit root points. -/
theorem minusIdentity_mem (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H) :
    minusIdentity R ∈ H :=
  H.mul_mem (H.mul_mem (H.pow_mem (weylElement_mem R H hroots 1) 2)
    (H.pow_mem (weylElement_mem R H hroots 4) 2))
    (H.pow_mem (weylElement_mem R H hroots 6) 2)

/-- The constructed element is central in the full minuscule carrier. -/
theorem minusIdentity_mem_center : minusIdentity R ∈ Subgroup.center (points R) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_minusIdentity]
  simp

/-- In each subgroup containing the unit root points, the same word is central. -/
theorem minusIdentity_mem_center_subgroup (H : Subgroup (points R))
    (hroots : ∀ k, rootSubgroupPoints k R (Multiplicative.ofAdd 1) ∈ H) :
    (⟨minusIdentity R, minusIdentity_mem R H hroots⟩ : H) ∈ Subgroup.center H := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (minusIdentity_mem_center R) g.val

/-- The root word squares to the identity, including in characteristic two. -/
@[simp]
theorem minusIdentity_pow_two : minusIdentity R ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one]
  rw [coe_minusIdentity]
  simp

/-- The word is trivial exactly when the two scalar signs coincide. -/
theorem minusIdentity_eq_one_iff : minusIdentity R = 1 ↔ (1 : R) = -1 := by
  constructor
  · intro h
    have hm := coe_minusIdentity R
    rw [h] at hm
    have hentry := congrFun (congrFun hm 0) 0
    simpa using hentry
  · intro h
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_one, Units.val_one]
    rw [coe_minusIdentity]
    ext a b
    simp only [Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · exact h.symm
    · exact neg_zero

/-- Every Frobenius fixed subgroup contains the constructed root word. -/
theorem minusIdentity_mem_fixedSubgroup_frobenius (p k : ℕ) [ExpChar R p] :
    minusIdentity R ∈ fixedSubgroup (frobenius p k R) := by
  apply minusIdentity_mem
  intro i
  rw [mem_fixedSubgroup, frobenius_rootSubgroupPoints]
  simp

end

end TauCeti.E7Minuscule
