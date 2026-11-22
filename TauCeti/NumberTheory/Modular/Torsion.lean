/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Torsion
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.NumberTheory.Modular.Generators
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.Modular
import TauCeti.GroupTheory.Index.TorsionFree
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.OrderOf
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.NumberTheory.Modular.Abelianization
import TauCeti.NumberTheory.Modular.Stabilizer

/-!
# Torsion in the modular group

Every element of finite order of `PSL(2, ℤ)` is conjugate to exactly one of `1`, `S`, `R` and
`R²`, where `S = (0 -1; 1 0)` and `R = S T = (0 -1; 1 1)`. In the free-product picture
`PSL(2, ℤ) = ℤ/2 ∗ ℤ/3` these are the elements of the two factors, and the statement is the
classification of torsion in a free product. Here it is proved geometrically. A nontrivial element
of finite order has an elliptic representative, since hyperbolic and parabolic elements have
infinite order, so it fixes a point of the upper half-plane. Moving that point into the standard
fundamental domain, it becomes `i` or `ρ`, and the stabilisers of these two points are generated
by `S` and by `R`, respectively. Finally `R` and `R²` are not conjugate, because their images `4`
and `2` in the abelianization `ℤ/6` differ.

In particular the elements of order two are the conjugates of `S`, and those of order three the
conjugates of `R` or of `R² = R⁻¹`. These are the elliptic elements whose fixed points are the
elliptic points of a finite-index subgroup.

## Main declarations

* `TauCeti.ModularGroup.isOfFinOrder_iff_exists_smul_eq_self`: an element has finite order
  exactly when it fixes a point of the upper half-plane.
* `TauCeti.ModularGroup.isOfFinOrder_iff_eq_one_or_isConj`: an element has finite order exactly
  when it is `1` or conjugate to `S`, `R` or `R²`.
* `TauCeti.ModularGroup.isConj_coe_S_iff_orderOf_eq_two`: the elements of order two form the
  conjugacy class of `S`.
* `TauCeti.ModularGroup.orderOf_eq_three_iff_isConj`: the elements of order three form the
  conjugacy classes of `R` and `R²`.
* `TauCeti.ModularGroup.not_isConj_coe_R_coe_R_sq`: these two classes are distinct.

## References

* J.-P. Serre, *Trees*, Springer, 1980, Chapter I, §4.2.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics
  228, Springer, 2005, §2.3.
-/

public section

open scoped MatrixGroups
open UpperHalfPlane ModularGroup

namespace TauCeti.ModularGroup

/-- **Torsion elements of `PSL(2, ℤ)` are elliptic**: an element of finite order fixes a point
of the upper half-plane. -/
theorem exists_smul_eq_self_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g) :
    ∃ z : ℍ, g • z = z := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  by_cases h1 : (γ : PSL(2, ℤ)) = 1
  · exact ⟨I, by rw [h1, one_smul]⟩
  have hell := Matrix.ProjectiveSpecialLinearGroup.isElliptic_of_isOfFinOrder_mk hg h1
  have hd : (Matrix.SpecialLinearGroup.mapGL ℝ γ).val.det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    simp
  have hellR : (Matrix.SpecialLinearGroup.mapGL ℝ γ).IsElliptic := by
    rw [Matrix.GeneralLinearGroup.IsElliptic, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    exact Matrix.IsElliptic.map_intCast hell
  refine ⟨fixedPt _ hellR, ?_⟩
  rw [pslMk_smul]
  exact (gl_smul_eq_self_iff_eq_fixedPt (by rw [hd]; norm_num) hellR).2 rfl

/-- **The elliptic elements of `PSL(2, ℤ)` are its torsion**: an element has finite order exactly
when it fixes a point of the upper half-plane. Point stabilisers are finite, of order at most
`3`. -/
theorem isOfFinOrder_iff_exists_smul_eq_self {g : PSL(2, ℤ)} :
    IsOfFinOrder g ↔ ∃ z : ℍ, g • z = z := by
  refine ⟨exists_smul_eq_self_of_isOfFinOrder, fun ⟨z, hz⟩ ↦ ?_⟩
  have hpos := ellipticOrder_pos (Quotient.mk'' z)
  rw [ellipticOrder_mk] at hpos
  have : Finite (MulAction.stabilizer PSL(2, ℤ) z) := Nat.finite_of_card_ne_zero hpos.ne'
  exact (MulAction.stabilizer PSL(2, ℤ) z).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨g, hz⟩ : MulAction.stabilizer PSL(2, ℤ) z))

/-- A matrix fixing a point of `ℍ`, with nontrivial class in `PSL(2, ℤ)`, has a conjugate other
than `±1` fixing `i` or `ρ`: moving the point into the fundamental domain `𝒟`, it must be one of
the three points `i`, `ρ`, `ρ + 1` with nontrivial stabiliser, and `ρ + 1 = T ρ`. -/
private theorem exists_conj_smul_eq_I_or_eq_ρ {γ : SL(2, ℤ)} {z : ℍ} (hz : γ • z = z)
    (hγ : (γ : PSL(2, ℤ)) ≠ 1) : ∃ h : SL(2, ℤ), h * γ * h⁻¹ ≠ 1 ∧ h * γ * h⁻¹ ≠ -1 ∧
      ((h * γ * h⁻¹) • I = I ∨ (h * γ * h⁻¹) • ρ = ρ) := by
  have hfix (h : SL(2, ℤ)) : (h * γ * h⁻¹) • (h • z) = h • z := by
    rw [mul_smul, mul_smul, inv_smul_smul, hz]
  -- a conjugate of `γ` is not central, since its class in `PSL(2, ℤ)` is a conjugate of `γ ≠ 1`
  have hc (h : SL(2, ℤ)) : h * γ * h⁻¹ ∉ Subgroup.center SL(2, ℤ) := fun hc ↦ hγ <|
    (conj_eq_one_iff (a := (h : PSL(2, ℤ)))).1 <| by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using
        (QuotientGroup.eq_one_iff (h * γ * h⁻¹)).2 hc
  have hne (h : SL(2, ℤ)) : h * γ * h⁻¹ ≠ 1 ∧ h * γ * h⁻¹ ≠ -1 := by
    simpa [Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one, not_or] using hc h
  obtain ⟨h, hh⟩ := exists_smul_mem_fd z
  by_cases hI : h • z = I
  · exact ⟨h, (hne h).1, (hne h).2, Or.inl (hI ▸ hfix h)⟩
  by_cases hρ : h • z = ρ
  · exact ⟨h, (hne h).1, (hne h).2, Or.inr (hρ ▸ hfix h)⟩
  by_cases hρ' : h • z = (1 : ℝ) +ᵥ ρ
  · have hTρ : (T⁻¹ * h) • z = ρ := by
      rw [mul_smul, hρ', inv_smul_eq_iff, modular_T_smul]
    exact ⟨T⁻¹ * h, (hne _).1, (hne _).2, Or.inr (hTρ ▸ hfix _)⟩
  · refine (hc h ?_).elim
    rw [Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
    exact stabilizer_of_ne hh (hfix h) hI hρ hρ'

/-- A nontrivial element of finite order of `PSL(2, ℤ)` is conjugate to `S`, to `R` or to `R²`. -/
theorem isConj_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g) (h1 : g ≠ 1) :
    IsConj g S ∨ IsConj g R ∨ IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  obtain ⟨z, hz⟩ := exists_smul_eq_self_of_isOfFinOrder hg
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [pslMk_smul] at hz
  obtain ⟨h, hne1, hne2, hw⟩ := exists_conj_smul_eq_I_or_eq_ρ hz h1
  have hconj : IsConj (γ : PSL(2, ℤ)) ((h * γ * h⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) :=
    isConj_iff.2 ⟨h, by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  rcases hw with hw | hw
  · have hS := stabilizer_I.1 hw
    simp only [Finset.mem_insert, Finset.mem_singleton, hne1, hne2, false_or] at hS
    left
    rcases hS with hS | hS <;> rw [hS] at hconj
    · exact hconj
    · rwa [Matrix.ProjectiveSpecialLinearGroup.mk_neg] at hconj
  · have hR := stabilizer_ρ.1 hw
    simp only [Finset.mem_insert, Finset.mem_singleton, hne1, hne2, false_or] at hR
    right
    rcases hR with hR | hR | hR | hR <;> rw [hR] at hconj
    · exact Or.inl (by rwa [← R_def] at hconj)
    · exact Or.inl (by rwa [Matrix.ProjectiveSpecialLinearGroup.mk_neg, ← R_def] at hconj)
    · exact Or.inr (by rwa [← R_sq, QuotientGroup.mk_pow] at hconj)
    · exact Or.inr (by
        rwa [Matrix.ProjectiveSpecialLinearGroup.mk_neg, ← R_sq, QuotientGroup.mk_pow] at hconj)

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

/-- **Torsion classification in `PSL(2, ℤ)` (in terms of `S` and `U`).** An element of `PSL(2, ℤ)`
has finite order if and only if it is `1` or conjugate to `S`, `U`, or `U²`. -/
theorem isOfFinOrder_iff_isConj_coe_U {g : PSL(2, ℤ)} :
    IsOfFinOrder g ↔
      g = 1 ∨ IsConj g (S : PSL(2, ℤ)) ∨ IsConj g (U : PSL(2, ℤ)) ∨
        IsConj g ((U : PSL(2, ℤ)) ^ 2) := by
  rw [isOfFinOrder_iff_eq_one_or_isConj]
  refine ⟨?_, ?_⟩
  · rintro (rfl | hc | hc | hc)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inr (hc.trans isConj_coe_R_coe_U_sq)))
    · exact Or.inr (Or.inr (Or.inl (hc.trans isConj_coe_U_coe_R_sq.symm)))
  · rintro (rfl | hc | hc | hc)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inr (hc.trans isConj_coe_U_coe_R_sq)))
    · exact Or.inr (Or.inr (Or.inl (hc.trans isConj_coe_R_coe_U_sq.symm)))

/-- An element of `PSL(2, ℤ)` has order `3` if and only if it is conjugate to `U` or `U²`. -/
theorem orderOf_eq_three_iff_isConj_coe_U {g : PSL(2, ℤ)} :
    orderOf g = 3 ↔ IsConj g (U : PSL(2, ℤ)) ∨ IsConj g ((U : PSL(2, ℤ)) ^ 2) := by
  rw [orderOf_eq_three_iff_isConj]
  exact ⟨fun h ↦ h.elim (fun hc ↦ Or.inr (hc.trans isConj_coe_R_coe_U_sq))
      (fun hc ↦ Or.inl (hc.trans isConj_coe_U_coe_R_sq.symm)),
    fun h ↦ h.elim (fun hc ↦ Or.inr (hc.trans isConj_coe_U_coe_R_sq))
      (fun hc ↦ Or.inl (hc.trans isConj_coe_R_coe_U_sq.symm))⟩

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
`index_commutator`, this shows the divisibility bound `6 ∣ Γ'.index` below is sharp. -/
instance instIsMulTorsionFreeCommutator : IsMulTorsionFree (commutator PSL(2, ℤ)) :=
  IsMulTorsionFree.of_not_isOfFinOrder fun ⟨g, hg⟩ hne hfin ↦ by
    have hne' : g ≠ 1 := fun h1 ↦ hne (Subtype.ext h1)
    have hker : Group.Abelianization.of g = 1 :=
      MonoidHom.mem_ker.mp ((Group.Abelianization.ker_of PSL(2, ℤ)).symm ▸ hg)
    exact abelianization_of_ne_one_of_isOfFinOrder
      ((commutator PSL(2, ℤ)).subtype.isOfFinOrder hfin) hne' hker

/-- Every torsion-free subgroup `Γ' ≤ PSL(2, ℤ)` has index divisible by `6`. -/
theorem six_dvd_index_of_isMulTorsionFree (Γ' : Subgroup PSL(2, ℤ)) [IsMulTorsionFree Γ'] :
    6 ∣ Γ'.index := by
  have h2 := Γ'.orderOf_dvd_index_of_isMulTorsionFree
    (orderOf_pos_iff.mp (by rw [orderOf_coe_S]; decide))
  rw [orderOf_coe_S] at h2
  have h3 := Γ'.orderOf_dvd_index_of_isMulTorsionFree
    (orderOf_pos_iff.mp (by rw [orderOf_coe_R]; decide))
  rw [orderOf_coe_R] at h3
  exact (by decide : 6 = Nat.lcm 2 3) ▸ Nat.lcm_dvd h2 h3

end TauCeti.ModularGroup
