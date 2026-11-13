/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond
import Mathlib.Algebra.Ring.Action.ConjAct

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
    let a := weylUnit hEi hFi
    let b := weylUnit hEj hFj
    ((a * b * a * b * a : Aˣ) : A) * E j * ↑(a * b * a * b * a)⁻¹ = E j := by
  dsimp only
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  let c (u : Aˣ) := MulSemiringAction.toAlgEquiv ℚ A (ConjAct.toConjAct u)
  have hc (u : Aˣ) (x : A) : c u x = (u : A) * x * ↑u⁻¹ := by
    simp only [c, MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct]
  have maplie (u : Aˣ) (x y : A) : c u ⁅x, y⁆ = ⁅c u x, c u y⁆ := by
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
  have haEj : c a (E j) = -y₁ := by
    rw [hc, hs.weylUnit_conj_E_of_cartan_eq_neg_one hii hij hEi hFi, ← lie_skew (E i) (E j)]
  have hbEj : c b (E j) = -F j := by
    simpa only [hc, b, coe_weylUnit, coe_inv_weylUnit] using weylUnit_conj_e ht hEj hFj
  have hby₁ : c b y₁ = -(2⁻¹ : ℚ) • y₂ := by
    rw [maplie, hbEj, hc b (E i), hs.weylUnit_conj_of_cartan_eq_neg_three hjj hji hEj hFj,
      neg_lie, lie_smul, hf₃, smul_smul]
    norm_num
  have hay₂ : c a y₂ = y₂ := hs.weylUnit_conj_middle_of_tripleBond hii hij hi hEi hFi
  have hby₂ : c b y₂ = (2 : ℚ) • y₁ := by
    rw [maplie, hbEj, hby₁, neg_lie, lie_smul, hf₂, ← neg_smul, smul_smul]
    norm_num
  have hay₁ : c a y₁ = E j := by
    have haEi : c a (E i) = -F i := by
      simpa only [hc, a, coe_weylUnit, coe_inv_weylUnit] using
        weylUnit_conj_e (hs.isSl2Triple hii hi) hEi hFi
    rw [maplie, haEj, haEi, neg_lie, lie_neg, neg_neg,
      hs.lie_lie_E_E_F_of_ne hne.symm, hij, neg_one_smul, neg_neg]
  have hfix : c a (c b (c a (c b (c a (E j))))) = E j := by
    rw [haEj, map_neg, hby₁, ← neg_smul, neg_neg, map_smul, hay₂, map_smul, hby₂, smul_smul]
    norm_num [hay₁]
  simpa only [hc, Units.val_mul, Units.val_inv, mul_inv_rev, mul_assoc] using hfix

private theorem weylUnit_conj_quintuple_F_of_tripleBond (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -3)
    (hi : H i ≠ 0) (hj : H j ≠ 0)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    let a := weylUnit hEi hFi
    let b := weylUnit hEj hFj
    ((a * b * a * b * a : Aˣ) : A) * F j * ↑(a * b * a * b * a)⁻¹ = F j := by
  dsimp only
  let c (u : Aˣ) := MulSemiringAction.toAlgEquiv ℚ A (ConjAct.toConjAct u)
  have hc (u : Aˣ) (x : A) : c u x = (u : A) * x * ↑u⁻¹ := by
    simp only [c, MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct]
  -- Signed exchange preserves each Weyl conjugation, transporting the fixed-point identity to F j.
  have hcneg {k : B} (hkk : CM k k = 2) (hk : H k ≠ 0)
      (hEk : IsNilpotent (E k)) (hFk : IsNilpotent (F k)) :
      c (weylUnit hFk.neg hEk.neg) = c (weylUnit hEk hFk) := by
    ext x
    rw [hc, hc, ← weylAut_apply_eq_weylUnit_conj (K := ℚ)
      (hs.isSl2Triple hkk hk).neg_symm, ← weylAut_apply_eq_weylUnit_conj (K := ℚ)
      (hs.isSl2Triple hkk hk)]
    exact (hs.isSl2Triple hkk hk).weylAut_neg_symm _ _ _ _ x
  have h : c (weylUnit hFi.neg hEi.neg) (c (weylUnit hFj.neg hEj.neg)
      (c (weylUnit hFi.neg hEi.neg) (c (weylUnit hFj.neg hEj.neg)
        (c (weylUnit hFi.neg hEi.neg) (-F j))))) = -F j := by
    simpa only [hc, Units.val_mul, Units.val_inv, mul_inv_rev, mul_assoc] using
      hs.neg_swap.weylUnit_conj_quintuple_E_of_tripleBond hii hjj hij hji
        (neg_ne_zero.mpr hi) (neg_ne_zero.mpr hj) hFi.neg hEi.neg hFj.neg hEj.neg
  rw [hcneg hii hi hEi hFi, hcneg hjj hj hEj hFj] at h
  have hF : c (weylUnit hEi hFi) (c (weylUnit hEj hFj)
      (c (weylUnit hEi hFi) (c (weylUnit hEj hFj) (c (weylUnit hEi hFi) (F j))))) = F j := by
    simpa only [map_neg, neg_inj] using h
  simpa only [hc, Units.val_mul, Units.val_inv, mul_inv_rev, mul_assoc] using hF

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
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  let c (u : Aˣ) := MulSemiringAction.toAlgEquiv ℚ A (ConjAct.toConjAct u)
  have hc (u : Aˣ) (x : A) : c u x = (u : A) * x * ↑u⁻¹ := by
    simp only [c, MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct]
  -- Degenerate Serre systems are allowed: a zero Cartan operator kills both nodes on the bond.
  by_cases hj : H j = 0
  · have hEi0 : E i = 0 := hs.E_eq_zero_of_H_eq_zero hj (by omega : CM j i ≠ 0)
    have hFi0 : F i = 0 := hs.F_eq_zero_of_H_eq_zero hj (by omega : CM j i ≠ 0)
    have hi0 : H i = 0 := by rw [← hs.lie_E_F_self i, hEi0, zero_lie]
    have hEj0 : E j = 0 := hs.E_eq_zero_of_H_eq_zero hi0 (by omega : CM i j ≠ 0)
    have hFj0 : F j = 0 := hs.F_eq_zero_of_H_eq_zero hi0 (by omega : CM i j ≠ 0)
    apply Units.ext
    simp [hEi0, hFi0, hEj0, hFj0]
  have hi : H i ≠ 0 := fun hi0 => hj <| by
    rw [← hs.lie_E_F_self j, hs.E_eq_zero_of_H_eq_zero hi0 (by omega : CM i j ≠ 0), zero_lie]
  let d := (c (a * b * a * b * a)).toRingHom
  have hdE : d (E j) = E j :=
    (hc (a * b * a * b * a) (E j)).trans
      (hs.weylUnit_conj_quintuple_E_of_tripleBond hii hjj hij hji hi hj hEi hFi hEj hFj)
  have hdF : d (F j) = F j :=
    (hc (a * b * a * b * a) (F j)).trans
      (hs.weylUnit_conj_quintuple_F_of_tripleBond hii hjj hij hji hi hj hEi hFi hEj hFj)
  -- Exponentiating upgrades fixed points on E j and F j to commutation with the unit b itself.
  have hd : d (b : A) = (b : A) := by
    simp only [b, coe_weylUnit, map_mul, hEj.map_exp d, hFj.neg.map_exp d, map_neg, hdE, hdF]
  have hu : (a * b * a * b * a) * b * (a * b * a * b * a)⁻¹ = b := by
    apply Units.ext
    simpa only [d, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      hc, Units.val_mul] using hd
  calc
    _ = b * (a * b * a * b * a) := mul_inv_eq_iff_eq_mul.mp hu
    _ = _ := by simp only [a, b, mul_assoc]

end TauCeti.IsSerreSystem
