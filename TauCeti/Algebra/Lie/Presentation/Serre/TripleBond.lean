/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond

/-!
# Triple-bond Weyl normalization and braid relations for Serre systems

At a directed Cartan entry minus three, the pinned Weyl unit sends the raising generator
to one sixth of its third raising bracket, and the lowering generator to minus one sixth
of its third lowering bracket. Together with the single-bond normalization at the opposite
directed Cartan entry minus one, these formulas give the length-six braid relation for the
Weyl units at a triple bond. This is an equality in the unit group of the associative
rational algebra, not merely an equality of conjugation actions, so it restricts to an
admissible lattice and extends to any commutative value ring.

These are rational operator identities. They impose no faithfulness or nonvanishing on the
Serre system and divide by six only in the rational algebra, not in a value ring of positive
characteristic. The matrix convention is `⁅H i, E j⁆ = CM i j • E j`.

The formulas use the root-string calculations in
`TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree`, as the double-bond formulas use `WeightTwo`.
For the braid relation, conjugation by the five-letter alternating word fixes the other
root pair: the middle step fixes the intermediate root vector `⁅E j, ⁅E j, E i⁆⁆` because
it is centralized by both `E i` and `F i`, and signed exchange transports the raising
calculation to the lowering operator.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.IsSerreSystem

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HasUniqueDiv.of_module_rat

variable {B A : Type*} [Ring A] [Algebra ℚ A]
  {CM : Matrix B B ℤ} {H E F : B → A}

/-- At a directed Cartan entry minus three, the pinned Weyl unit carries the raising
generator to one sixth of its third raising bracket. -/
theorem weylUnit_conj_of_cartan_eq_neg_three (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hij : CM i j = -3)
    (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF : A) * E j * ↑(weylUnit hE hF)⁻¹ =
      (6⁻¹ : ℚ) • ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆ := by
  have hweight : ⁅H i, E j⁆ = (-3 : ℚ) • E j := by
    simpa [hij] using hs.lie_H_E_smul i j
  by_cases hH : H i = 0
  · simp [hs.E_eq_zero_of_H_eq_zero hH (by omega : CM i j ≠ 0)]
  have ht := hs.isSl2Triple hii hH
  have hne : j ≠ i := ne_of_apply_ne (CM i) (by omega)
  have hlower : ⁅F i, E j⁆ = 0 := by
    rw [← lie_skew, hs.lie_E_F_of_ne j i hne, neg_zero]
  exact ht.weylUnit_conj_of_weight_neg_three hE hF hweight hlower

/-- At a directed Cartan entry minus three, the pinned Weyl unit carries the lowering
generator to minus one sixth of its third lowering bracket. -/
theorem weylUnit_conj_F_of_cartan_eq_neg_three (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hij : CM i j = -3)
    (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF : A) * F j * ↑(weylUnit hE hF)⁻¹ =
      -(6⁻¹ : ℚ) • ⁅F i, ⁅F i, ⁅F i, F j⁆⁆⁆ := by
  have hweight : ⁅H i, F j⁆ = (3 : ℚ) • F j := by
    simpa [hij] using hs.lie_H_F_smul i j
  by_cases hH : H i = 0
  · simp [hs.F_eq_zero_of_H_eq_zero hH (by omega : CM i j ≠ 0)]
  have ht := hs.isSl2Triple hii hH
  have hne : i ≠ j := ne_of_apply_ne (CM i) (by omega)
  exact ht.weylUnit_conj_of_weight_three hE hF hweight (hs.lie_E_F_of_ne i j hne)

/-- At a triple bond with `CM i j = -1`, the middle root vector `⁅E j, ⁅E j, E i⁆⁆` lies in
the joint centralizer of `E i` and `F i`, so conjugation by the Weyl unit at `i` fixes it. -/
private theorem weylUnit_conj_middle_of_tripleBond (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hij : CM i j = -1) (hi : H i ≠ 0)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i)) :
    (weylUnit hEi hFi : A) * ⁅E j, ⁅E j, E i⁆⁆ * ↑(weylUnit hEi hFi)⁻¹ =
      ⁅E j, ⁅E j, E i⁆⁆ := by
  have hne : i ≠ j := by rintro rfl; omega
  have hEi2 : ⁅E i, ⁅E j, E i⁆⁆ = 0 := by
    rw [← lie_skew (E j) (E i), lie_neg, hs.lie_E_lie_E_E_of_eq_neg_one hij, neg_zero]
  have hEcomm : ⁅⁅E j, ⁅E j, E i⁆⁆, E i⁆ = 0 := by
    rw [← lie_skew _ (E i), leibniz_lie, hEi2, lie_zero, add_zero,
      ← lie_skew (E i) (E j), neg_lie, lie_self, neg_zero, neg_zero]
  have hFiEj : ⁅F i, E j⁆ = 0 := by
    rw [← lie_skew, hs.lie_E_F_of_ne j i hne.symm, neg_zero]
  have hFi1 : ⁅F i, ⁅E j, E i⁆⁆ = -E j := by
    rw [leibniz_lie, hFiEj, zero_lie, zero_add, ← lie_skew (F i) (E i), hs.lie_E_F_self,
      lie_neg, ← lie_skew (E j) (H i), neg_neg]
    simpa [hij] using hs.lie_H_E i j
  have hFcomm : ⁅⁅E j, ⁅E j, E i⁆⁆, F i⁆ = 0 := by
    rw [← lie_skew _ (F i), leibniz_lie, hFiEj, zero_lie, zero_add, hFi1,
      lie_neg, lie_self, neg_zero, neg_zero]
  rw [← weylAut_apply_eq_weylUnit_conj (K := ℚ) (hs.isSl2Triple hii hi) hEi hFi]
  exact weylAut_apply_of_lie_eq_zero
    (ad_nilpotent_of_nilpotent (R := ℚ) hEi).exists_pow_apply_eq_zero
    (ad_nilpotent_of_nilpotent (R := ℚ) hFi).exists_pow_apply_eq_zero
    (hs.isSl2Triple hii hi) hEcomm hFcomm

private theorem weylUnit_conj_quintuple_E_of_tripleBond (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -3)
    (hi : H i ≠ 0) (hj : H j ≠ 0)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    (weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi *
        weylUnit hEj hFj * weylUnit hEi hFi).conjAlgEquiv ℚ (E j) = E j := by
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  have maplie (u : Aˣ) (x y : A) :
      u.conjAlgEquiv ℚ ⁅x, y⁆ = ⁅u.conjAlgEquiv ℚ x, u.conjAlgEquiv ℚ y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  have hne : i ≠ j := by rintro rfl; omega
  let y₁ := ⁅E j, E i⁆
  let y₂ := ⁅E j, y₁⁆
  let y₃ := ⁅E j, y₂⁆
  -- String lowering formulas for the four-element j-string generated from E i.
  have ht := hs.isSl2Triple hjj hj
  have hweight : ⁅H j, E i⁆ = (-3 : ℚ) • E i := by simpa [hji] using hs.lie_H_E_smul j i
  have hlower : ⁅F j, E i⁆ = 0 := by rw [← lie_skew, hs.lie_E_F_of_ne i j hne, neg_zero]
  have hf₂ : ⁅F j, y₂⁆ = (4 : ℚ) • y₁ := by
    convert ht.lie_f_pow_succ_toEnd_e hweight hlower 1 using 1 <;>
      norm_num [y₁, y₂, pow_succ', mul_apply_eq_comp]
  have hf₃ : ⁅F j, y₃⁆ = (3 : ℚ) • y₂ := by
    convert ht.lie_f_pow_succ_toEnd_e hweight hlower 2 using 1 <;>
      norm_num [y₁, y₂, y₃, pow_succ', mul_apply_eq_comp]
  have haEj : a.conjAlgEquiv ℚ (E j) = -y₁ := by
    rw [Units.conjAlgEquiv_apply, hs.weylUnit_conj_E_of_cartan_eq_neg_one hii hij hEi hFi,
      ← lie_skew (E i) (E j)]
  have hbEj : b.conjAlgEquiv ℚ (E j) = -F j := hs.conjAlgEquiv_weylUnit_e hjj hj hEj hFj
  have hby₁ : b.conjAlgEquiv ℚ y₁ = -(2⁻¹ : ℚ) • y₂ := by
    rw [maplie, hbEj, b.conjAlgEquiv_apply ℚ (E i),
      hs.weylUnit_conj_of_cartan_eq_neg_three hjj hji hEj hFj,
      neg_lie, lie_smul, hf₃, smul_smul]
    norm_num
  have hay₂ : a.conjAlgEquiv ℚ y₂ = y₂ := by
    simpa only [Units.conjAlgEquiv_apply] using
      hs.weylUnit_conj_middle_of_tripleBond hii hij hi hEi hFi
  have hby₂ : b.conjAlgEquiv ℚ y₂ = (2 : ℚ) • y₁ := by
    rw [maplie, hbEj, hby₁, neg_lie, lie_smul, hf₂, ← neg_smul, smul_smul]
    norm_num
  have hay₁ : a.conjAlgEquiv ℚ y₁ = E j := by
    rw [maplie, haEj, hs.conjAlgEquiv_weylUnit_e hii hi hEi hFi, neg_lie, lie_neg, neg_neg,
      hs.lie_lie_E_E_F_of_ne hne.symm, hij, neg_one_smul, neg_neg]
  simp only [Units.conjAlgEquiv_mul, AlgEquiv.mul_apply]
  change a.conjAlgEquiv ℚ (b.conjAlgEquiv ℚ (a.conjAlgEquiv ℚ
    (b.conjAlgEquiv ℚ (a.conjAlgEquiv ℚ (E j))))) = E j
  rw [haEj, map_neg, hby₁, ← neg_smul, neg_neg, map_smul, hay₂, map_smul, hby₂, smul_smul]
  norm_num [hay₁]

/-- At a triple bond the pinned Weyl units satisfy the length-six braid relation in the
unit group of an associative rational algebra. Only the four root operators at the two
nodes need be nilpotent; no faithfulness or nonvanishing assumption is required. -/
theorem weylUnit_braid_of_cartan_eq_neg_three (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -3)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi *
        weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj =
      weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj *
        weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi := by
  -- Degenerate Serre systems are allowed: a zero Cartan operator kills both nodes on the bond.
  by_cases hj : H j = 0
  · have hi0 : H i = 0 := hs.H_eq_zero_of_H_eq_zero hj (by omega)
    simp [hs.weylUnit_eq_one_of_H_eq_zero hj (by omega) hEi hFi,
      hs.weylUnit_eq_one_of_H_eq_zero hi0 (by omega) hEj hFj]
  have hi : H i ≠ 0 := fun hi0 => hj (hs.H_eq_zero_of_H_eq_zero hi0 (by omega))
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  have hE : (a * b * a * b * a).conjAlgEquiv ℚ (E j) = E j :=
    hs.weylUnit_conj_quintuple_E_of_tripleBond hii hjj hij hji hi hj hEi hFi hEj hFj
  -- Signed exchange preserves each Weyl conjugation, transporting the fixed-point identity to F j.
  have hF : (a * b * a * b * a).conjAlgEquiv ℚ (F j) = F j := by
    have h := hs.neg_swap.weylUnit_conj_quintuple_E_of_tripleBond hii hjj hij hji
      (neg_ne_zero.mpr hi) (neg_ne_zero.mpr hj) hFi.neg hEi.neg hFj.neg hEj.neg
    simp only [Units.conjAlgEquiv_mul, hs.conjAlgEquiv_weylUnit_neg hii hi hEi hFi,
      hs.conjAlgEquiv_weylUnit_neg hjj hj hEj hFj, map_neg, neg_inj] at h ⊢
    exact h
  simpa only [a, b, mul_assoc] using
    (commute_weylUnit_of_conj_eq (a * b * a * b * a) hEj hFj
      (by simpa only [Units.conjAlgEquiv_apply] using hE)
      (by simpa only [Units.conjAlgEquiv_apply] using hF)).eq

end TauCeti.IsSerreSystem
