/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import TauCeti.NumberTheory.Modular.Generators
import TauCeti.GroupTheory.Coprod.Torsion
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.NumberTheory.Modular.Abelianization
import TauCeti.NumberTheory.Modular.FreeProduct

/-!
# Torsion in the modular group

Every element of finite order of `PSL(2, ℤ)` is conjugate to exactly one of `1`, `S`, `R` and
`R²`, where `S = (0 -1; 1 0)` and `R = S T = (0 -1; 1 1)`. Using the free-product presentation
`PSL(2, ℤ) ≃* ℤ/2 ∗ ℤ/3` (`TauCeti.ModularGroup.coprodEquiv`) and the classification of torsion
in a free product (`Monoid.Coprod.isOfFinOrder_iff`), every finite-order element of `PSL(2, ℤ)`
is conjugate into one of the two factors `⟨S⟩ ≅ ℤ/2` or `⟨R⟩ ≅ ℤ/3`. Finally `R` and `R²` are
not conjugate, because their images `4` and `2` in the abelianization `ℤ/6` differ.

In particular the elements of order two are the conjugates of `S`, and those of order three the
conjugates of `R` or of `R² = R⁻¹`. Every nontrivial finite-order element has nontrivial image in
the abelianization, so the commutator subgroup `[PSL(2, ℤ), PSL(2, ℤ)]` is torsion-free.

## Main declarations

* `TauCeti.ModularGroup.isConj_of_isOfFinOrder`,
  `TauCeti.ModularGroup.isOfFinOrder_iff_eq_one_or_isConj`: an element has finite order exactly
  when it is `1` or conjugate to `S`, `R` or `R²`.
* `TauCeti.ModularGroup.isConj_coe_S_iff_orderOf_eq_two`: the elements of order two form the
  conjugacy class of `S`.
* `TauCeti.ModularGroup.orderOf_eq_three_iff_isConj`: the elements of order three form the
  conjugacy classes of `R` and `R²`.
* `TauCeti.ModularGroup.not_isConj_coe_R_coe_R_sq`: these two classes are distinct.
* `TauCeti.ModularGroup.orderOf_mem_of_isOfFinOrder`: every finite-order element has order `1`,
  `2`, or `3`.
* `TauCeti.ModularGroup.instIsMulTorsionFreeCommutator`: the commutator subgroup
  `[PSL(2, ℤ), PSL(2, ℤ)]` is torsion-free.

## References

* J.-P. Serre, *Trees*, Springer, 1980, Chapter I, §4.2.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics
  228, Springer, 2005, §2.3.
-/

public section

open scoped MatrixGroups
open ModularGroup

namespace TauCeti.ModularGroup

/-- A nontrivial element of finite order of `PSL(2, ℤ)` is conjugate to `S`, to `R` or to `R²`. -/
theorem isConj_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g) (h1 : g ≠ 1) :
    IsConj g S ∨ IsConj g R ∨ IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  rcases Monoid.Coprod.isOfFinOrder_iff.mp (coprodEquiv.toMonoidHom.isOfFinOrder hg) with
    ⟨x, -, hconj⟩ | ⟨y, -, hconj⟩
  · have hc : IsConj g (coprodEquiv.symm (Monoid.Coprod.inl x)) := by
      simpa using coprodEquiv.symm.toMonoidHom.map_isConj hconj
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) x.toAdd with hx | hx
    · have hx1 : x = 1 := by rw [← ofAdd_toAdd x, hx, ofAdd_zero]
      exact absurd (isConj_one_left.mp (by simpa [hx1] using hc)) h1
    · have hx1 : x = .ofAdd 1 := by rw [← ofAdd_toAdd x, hx]
      exact Or.inl (by simpa [hx1] using hc)
  · have hc : IsConj g (coprodEquiv.symm (Monoid.Coprod.inr y)) := by
      simpa using coprodEquiv.symm.toMonoidHom.map_isConj hconj
    rcases (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) y.toAdd with hy | hy | hy
    · have hy1 : y = 1 := by rw [← ofAdd_toAdd y, hy, ofAdd_zero]
      exact absurd (isConj_one_left.mp (by simpa [hy1] using hc)) h1
    · have hy1 : y = .ofAdd 1 := by rw [← ofAdd_toAdd y, hy]
      exact Or.inr (Or.inl (by simpa [hy1] using hc))
    · have hy2 : y = .ofAdd ((2 : ℕ) : ZMod 3) := by rw [← ofAdd_toAdd y, hy]; rfl
      rw [hy2, coprodEquiv_symm_inr_ofAdd_natCast] at hc
      exact Or.inr (Or.inr hc)

/-- **The torsion of `PSL(2, ℤ)`**: an element has finite order exactly when it is the identity
or conjugate to `S`, to `R` or to `R²`. -/
theorem isOfFinOrder_iff_eq_one_or_isConj {g : PSL(2, ℤ)} :
    IsOfFinOrder g ↔ g = 1 ∨ IsConj g S ∨ IsConj g R ∨ IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  refine ⟨fun hg ↦ (eq_or_ne g 1).imp_right (isConj_of_isOfFinOrder hg), ?_⟩
  rintro (rfl | h | h | h) <;> refine orderOf_pos_iff.1 ?_
  · simp
  · simp [h.orderOf_eq]
  · simp [h.orderOf_eq]
  · simp [h.orderOf_eq, coe_R_sq]

/-- **The elements of order two of `PSL(2, ℤ)`** are exactly the conjugates of `S`. -/
theorem isConj_coe_S_iff_orderOf_eq_two {g : PSL(2, ℤ)} : IsConj g S ↔ orderOf g = 2 := by
  refine ⟨fun h ↦ by rw [h.orderOf_eq, orderOf_coe_S], fun h ↦ ?_⟩
  have hg : IsOfFinOrder g := orderOf_pos_iff.1 (by omega)
  have h1 : g ≠ 1 := by rintro rfl; simp at h
  rcases isConj_of_isOfFinOrder hg h1 with hS | hR | hR
  · exact hS
  · rw [hR.orderOf_eq, orderOf_coe_R] at h; omega
  · rw [hR.orderOf_eq, coe_R_sq, orderOf_inv, orderOf_coe_R] at h; omega

/-- **The elements of order three of `PSL(2, ℤ)`** are exactly the conjugates of `R` and of
`R² = R⁻¹`. -/
theorem orderOf_eq_three_iff_isConj {g : PSL(2, ℤ)} :
    orderOf g = 3 ↔ IsConj g R ∨ IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hg : IsOfFinOrder g := orderOf_pos_iff.1 (by omega)
    have h1 : g ≠ 1 := by rintro rfl; simp at h
    rcases isConj_of_isOfFinOrder hg h1 with hS | hR
    · rw [hS.orderOf_eq, orderOf_coe_S] at h; omega
    · exact hR
  · rintro (h | h)
    · rw [h.orderOf_eq, orderOf_coe_R]
    · rw [h.orderOf_eq, coe_R_sq, orderOf_inv, orderOf_coe_R]

/-- **`R` and `R²` are not conjugate in `PSL(2, ℤ)`**, although both have order three: their
classes in the abelianization `ℤ/6` are `4` and `2`. -/
theorem not_isConj_coe_R_coe_R_sq : ¬ IsConj (R : PSL(2, ℤ)) ((R : PSL(2, ℤ)) ^ 2) := by
  intro h
  have h' := (abelianizationAddEquiv.toMultiplicativeRight.toMonoidHom.comp
    Group.Abelianization.of).map_isConj h
  have hR :
      abelianizationAddEquiv.toMultiplicativeRight (Group.Abelianization.of (R : PSL(2, ℤ))) =
        .ofAdd 4 :=
    congrArg Multiplicative.ofAdd abelianizationAddEquiv_ofMul_of_coe_R
  simp +decide [isConj_iff_eq, hR] at h'

/-- In `PSL(2, ℤ)`, `U` is not conjugate to `U²`. -/
theorem not_isConj_coe_U_sq : ¬ IsConj (U : PSL(2, ℤ)) ((U : PSL(2, ℤ)) ^ 2) :=
  fun h ↦ not_isConj_coe_R_coe_R_sq
    ((isConj_coe_R_coe_U_sq.trans h.symm).trans isConj_coe_U_coe_R_sq)

/-- In `PSL(2, ℤ)`, `R = S T` and `U = S T⁻¹` are not conjugate. -/
theorem not_isConj_coe_R_coe_U : ¬ IsConj (R : PSL(2, ℤ)) (U : PSL(2, ℤ)) :=
  fun h ↦ not_isConj_coe_R_coe_R_sq (h.trans isConj_coe_U_coe_R_sq)

/-- Every finite-order element of `PSL(2, ℤ)` has order `1`, `2`, or `3`. -/
theorem orderOf_mem_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g) :
    orderOf g ∈ ({1, 2, 3} : Set ℕ) := by
  rcases isOfFinOrder_iff_eq_one_or_isConj.mp hg with rfl | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · simp
  · simp [hc.orderOf_eq]
  · simp [hc.orderOf_eq]
  · simp [hc.orderOf_eq, coe_R_sq]

/-- Every nonidentity finite-order element of `PSL(2, ℤ)` has nontrivial image in the
abelianization (`3`, `4`, or `2` in `ZMod 6`). -/
theorem abelianization_of_ne_one_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g)
    (hne : g ≠ 1) : Group.Abelianization.of g ≠ 1 := by
  intro hab
  have hzero : abelianizationAddEquiv (.ofMul (Group.Abelianization.of g)) = 0 := by simp [hab]
  rcases isOfFinOrder_iff_eq_one_or_isConj.mp hg with rfl | hc | hc | hc
  · exact hne rfl
  · have heq := isConj_iff_eq.mp (Group.Abelianization.of.map_isConj hc)
    rw [heq, abelianizationAddEquiv_ofMul_of_coe_S] at hzero
    revert hzero; decide
  · have heq := isConj_iff_eq.mp (Group.Abelianization.of.map_isConj hc)
    rw [heq, abelianizationAddEquiv_ofMul_of_coe_R] at hzero
    revert hzero; decide
  · have heq := isConj_iff_eq.mp (Group.Abelianization.of.map_isConj hc)
    simp only [heq, map_pow, ofMul_pow, map_nsmul, abelianizationAddEquiv_ofMul_of_coe_R] at hzero
    revert hzero; decide

/-- **The commutator subgroup `[PSL(2, ℤ), PSL(2, ℤ)]` is torsion-free.** Together with
`index_commutator`, this shows the divisibility bound `6 ∣ Γ'.index`
(`TauCeti.ModularGroup.six_dvd_index_of_isMulTorsionFree`) is sharp. -/
instance instIsMulTorsionFreeCommutator : IsMulTorsionFree (commutator PSL(2, ℤ)) :=
  IsMulTorsionFree.of_not_isOfFinOrder fun ⟨g, hg⟩ hne hfin ↦ by
    have hne' : g ≠ 1 := fun h1 ↦ hne (Subtype.ext h1)
    have hker : Group.Abelianization.of g = 1 :=
      MonoidHom.mem_ker.mp ((Group.Abelianization.ker_of PSL(2, ℤ)).symm ▸ hg)
    exact abelianization_of_ne_one_of_isOfFinOrder
      ((commutator PSL(2, ℤ)).subtype.isOfFinOrder hfin) hne' hker

end TauCeti.ModularGroup
