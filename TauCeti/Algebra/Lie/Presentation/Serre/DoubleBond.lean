/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightTwo
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond

/-!
# Double-bond Weyl normalization and braid relations for Serre systems

In any associative rational algebra, a Serre system with `CM i i = 2` and `CM i j = -2`
has the following normalization: conjugation by the pinned Weyl unit at `i` sends `E j` to
one half of its second raising bracket, and `F j` to one half of its second lowering
bracket. Only `E i` and `F i` need to be nilpotent.
Here the Cartan convention is that of `IsSerreSystem`: `CM i j` is the eigenvalue of
`ad (H i)` on `E j`. No nonvanishing or faithfulness assumption on the system is needed.

The normalization applies the three-element string calculation in
`TauCeti.Algebra.Lie.Sl2.Weyl.WeightTwo` using the Serre relations. Together with the
single-bond normalization it gives the length-four braid relation for the Weyl units
at a double bond. This is an equality of units, not just of their conjugation actions.
It can therefore be restricted to an admissible lattice and extended to any value ring.

The braid proof shows that conjugation by the three-letter word fixes the other root
pair. The raising calculation suffices: the signed exchange of a Serre system and
`IsSl2Triple.weylAut_neg_symm` give the lowering calculation without a separate
highest-weight string formula.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.IsSerreSystem

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HasUniqueDiv.of_module_rat

variable {B A : Type*} [Ring A] [Algebra ℚ A]
  {CM : Matrix B B ℤ} {H E F : B → A}

/-- At a directed Cartan entry minus two, the pinned Weyl unit of a Serre system carries
`E j` to one half of its second raising bracket. The matrix convention is `⁅H i, E j⁆ =
CM i j • E j`. -/
theorem weylUnit_conj_of_cartan_eq_neg_two (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hij : CM i j = -2)
    (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF : A) * E j * ↑(weylUnit hE hF)⁻¹ =
      (2⁻¹ : ℚ) • ⁅E i, ⁅E i, E j⁆⁆ := by
  have hweight : ⁅H i, E j⁆ = (-2 : ℚ) • E j := by
    simpa [hij] using hs.lie_H_E_smul i j
  by_cases hH : H i = 0
  · simp [hs.E_eq_zero_of_H_eq_zero hH (by omega : CM i j ≠ 0)]
  have ht := hs.isSl2Triple hii hH
  have hne : j ≠ i := ne_of_apply_ne (CM i) (by omega)
  have hlower : ⁅F i, E j⁆ = 0 := by
    rw [← lie_skew, hs.lie_E_F_of_ne j i hne, neg_zero]
  exact ht.weylUnit_conj_of_lie_eq_neg_two_smul hE hF hweight hlower

/-- At a directed Cartan entry minus two, the pinned Weyl unit carries the lowering
generator to one half of its second lowering bracket. -/
theorem weylUnit_conj_F_of_cartan_eq_neg_two (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hij : CM i j = -2)
    (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF : A) * F j * ↑(weylUnit hE hF)⁻¹ =
      (2⁻¹ : ℚ) • ⁅F i, ⁅F i, F j⁆⁆ := by
  have hweight : ⁅H i, F j⁆ = (2 : ℚ) • F j := by
    simpa [hij] using hs.lie_H_F_smul i j
  by_cases hH : H i = 0
  · simp [hs.F_eq_zero_of_H_eq_zero hH (by omega : CM i j ≠ 0)]
  have ht := hs.isSl2Triple hii hH
  have hne : i ≠ j := ne_of_apply_ne (CM i) (by omega)
  exact ht.weylUnit_conj_of_lie_eq_two_smul hE hF hweight (hs.lie_E_F_of_ne i j hne)

private theorem weylUnit_conj_triple_E_of_doubleBond (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -2)
    (hi : H i ≠ 0) (hj : H j ≠ 0)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    (weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi).conjAlgEquiv ℚ (E j) = E j := by
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  have hne : i ≠ j := by rintro rfl; omega
  have haEj : a.conjAlgEquiv ℚ (E j) = ⁅E i, E j⁆ := by
    simpa only [Units.conjAlgEquiv_apply] using
      hs.weylUnit_conj_E_of_cartan_eq_neg_one hii hij hEi hFi
  have hbEi : b.conjAlgEquiv ℚ (E i) = (2⁻¹ : ℚ) • ⁅E j, ⁅E j, E i⁆⁆ := by
    simpa only [Units.conjAlgEquiv_apply] using
      hs.weylUnit_conj_of_cartan_eq_neg_two hjj hji hEj hFj
  have haEi : a.conjAlgEquiv ℚ (E i) = -F i := hs.conjAlgEquiv_weylUnit_e hii hi hEi hFi
  have hbEj : b.conjAlgEquiv ℚ (E j) = -F j := hs.conjAlgEquiv_weylUnit_e hjj hj hEj hFj
  have maplie (u : Aˣ) (x y : A) :
      u.conjAlgEquiv ℚ ⁅x, y⁆ = ⁅u.conjAlgEquiv ℚ x, u.conjAlgEquiv ℚ y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  -- The intermediate root has zero j-weight; the remaining bracket contracts its string.
  have hbr : ⁅⁅E j, ⁅E j, E i⁆⁆, F j⁆ = (-2 : ℚ) • ⁅E j, E i⁆ := by
    have hw : ⁅H j, ⁅E j, E i⁆⁆ = 0 := by
      rw [leibniz_lie, hs.lie_H_E, hs.lie_H_E]
      simp only [hjj, hji, lie_zsmul, zsmul_lie]
      abel
    have hb : ⁅⁅E j, E i⁆, F j⁆ = CM j i • E i := by
      rw [← lie_skew (E j) (E i), neg_lie,
        hs.lie_lie_E_E_F_of_ne hne, neg_neg]
    rw [lie_lie, hb, hs.lie_E_F_self, ← lie_skew _ (H j), hw]
    simp only [neg_zero, sub_zero, hji, lie_zsmul]
    norm_num [← Int.cast_smul_eq_zsmul ℚ]
  simp only [Units.conjAlgEquiv_mul, AlgEquiv.mul_apply]
  change a.conjAlgEquiv ℚ (b.conjAlgEquiv ℚ (a.conjAlgEquiv ℚ (E j))) = E j
  rw [haEj, maplie, hbEi, hbEj, smul_lie, lie_neg, hbr]
  simp only [map_neg, map_smul, maplie, haEj, haEi, lie_neg]
  rw [← lie_skew (E i) (E j), neg_lie, hs.lie_lie_E_E_F_of_ne hne.symm]
  simp [hij, smul_smul]

/-- At a double bond the pinned Weyl units satisfy the length-four braid relation in the
unit group of an associative rational algebra. Only the four root operators at the two
nodes need be nilpotent; no faithfulness or nonvanishing assumption is required. -/
theorem weylUnit_braid_of_cartan_eq_neg_two (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -2)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj =
      weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi := by
  -- Degenerate Serre systems are allowed: a zero Cartan operator kills this entire bond.
  by_cases hj : H j = 0
  · have hi0 : H i = 0 := hs.H_eq_zero_of_H_eq_zero hj (by omega)
    simp [hs.weylUnit_eq_one_of_H_eq_zero hj (by omega) hEi hFi,
      hs.weylUnit_eq_one_of_H_eq_zero hi0 (by omega) hEj hFj]
  have hi : H i ≠ 0 := fun hi0 => hj (hs.H_eq_zero_of_H_eq_zero hi0 (by omega))
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  have hE : (a * b * a).conjAlgEquiv ℚ (E j) = E j :=
    hs.weylUnit_conj_triple_E_of_doubleBond hii hjj hij hji hi hj hEi hFi hEj hFj
  -- Signed exchange preserves each Weyl conjugation, transporting the fixed-point identity to F j.
  have hF : (a * b * a).conjAlgEquiv ℚ (F j) = F j := by
    have h := hs.neg_swap.weylUnit_conj_triple_E_of_doubleBond hii hjj hij hji
      (neg_ne_zero.mpr hi) (neg_ne_zero.mpr hj) hFi.neg hEi.neg hFj.neg hEj.neg
    simp only [Units.conjAlgEquiv_mul, hs.conjAlgEquiv_weylUnit_neg hii hi hEi hFi,
      hs.conjAlgEquiv_weylUnit_neg hjj hj hEj hFj, map_neg, neg_inj] at h ⊢
    exact h
  simpa only [a, b, mul_assoc] using
    (commute_weylUnit_of_conj_eq (a * b * a) hEj hFj
      (by simpa only [Units.conjAlgEquiv_apply] using hE)
      (by simpa only [Units.conjAlgEquiv_apply] using hF)).eq

end TauCeti.IsSerreSystem
