/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree
import TauCeti.Algebra.Lie.Presentation.Serre.Braid
import TauCeti.Algebra.Lie.Presentation.Serre.SingleBond
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Triple-bond Weyl normalization and braid relations for Serre systems

At a directed Cartan entry minus three, the pinned Weyl unit sends the raising generator
to one sixth of its third raising bracket, and the lowering generator to minus one sixth
of its third lowering bracket. Together with the single-bond normalization at the reversed
entry, this gives the length-six braid relation for the Weyl units at a triple bond. This
is an equality of units, not just of their conjugation actions, so it can be restricted to
an admissible lattice and extended to any value ring.

These are rational operator identities. They impose no faithfulness or nonvanishing on the
Serre system and divide by six only in the rational algebra, not in a value ring of positive
characteristic. The matrix convention is `⁅H i, E j⁆ = CM i j • E j`.

The formulas use the root-string calculations in
`TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree`, as the double-bond formulas use `WeightTwo`.
The braid proof follows the double-bond proof in
`TauCeti.Algebra.Lie.Presentation.Serre.DoubleBond`: conjugation by the five-letter word
`a b a b a` fixes the raising generator at the node of `b`, and
`TauCeti.IsSerreSystem.weylUnit_braid_of_conj_E_eq` gives the braid relation from this.
Writing `v₁, v₂, v₃` for the iterated raising brackets of `E i` by `E j`, the raising
generator passes through `⁅E i, E j⁆`, `v₂ / 2`, `v₂ / 2`, `v₁` and back to `E j`, using the
string coefficients `3, 4, 3` of lowering along the four-element string.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.IsSerreSystem

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

/-- Lowering the iterated raising brackets of `E i` at a directed Cartan entry minus three:
the coefficients along the four-element string are `3, 4, 3`, and the last two are recorded. -/
private theorem lie_F_lie_E_string_of_cartan_eq_neg_three (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hjj : CM j j = 2) (hji : CM j i = -3) (hj : H j ≠ 0) :
    ⁅F j, ⁅E j, ⁅E j, E i⁆⁆⁆ = (4 : ℚ) • ⁅E j, E i⁆ ∧
      ⁅F j, ⁅E j, ⁅E j, ⁅E j, E i⁆⁆⁆⁆ = (3 : ℚ) • ⁅E j, ⁅E j, E i⁆⁆ := by
  have tj := hs.isSl2Triple hjj hj
  have hne : i ≠ j := by intro h; subst j; omega
  have hyh : ⁅H j, E i⁆ = (-3 : ℚ) • E i := by simpa [hji] using hs.lie_H_E_smul j i
  have hyf : ⁅F j, E i⁆ = 0 := by rw [← lie_skew, hs.lie_E_F_of_ne i j hne, neg_zero]
  constructor
  · convert tj.lie_f_pow_succ_toEnd_e hyh hyf 1 using 1 <;>
      norm_num [pow_succ', mul_apply_eq_comp]
  · convert tj.lie_f_pow_succ_toEnd_e hyh hyf 2 using 1 <;>
      norm_num [pow_succ', mul_apply_eq_comp]

/-- At a triple bond, conjugation by the five-letter word `a b a b a` in the Weyl units `a` at
`i` and `b` at `j` fixes the raising generator at `j`. -/
private theorem weylUnit_conj_five_E_of_tripleBond (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -3)
    (hi : H i ≠ 0) (hj : H j ≠ 0)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    let a := weylUnit hEi hFi
    let b := weylUnit hEj hFj
    ConjAct.toConjAct ((a * b) ^ 2 * a) • E j = E j := by
  dsimp only
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  let c (u : Aˣ) := MulSemiringAction.toAlgEquiv ℚ A (ConjAct.toConjAct u)
  have hc (u : Aˣ) (x : A) : c u x = (u : A) * x * ↑u⁻¹ := by
    simp only [c, MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct]
  have maplie (u : Aˣ) (x y : A) : c u ⁅x, y⁆ = ⁅c u x, c u y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  have hne : i ≠ j := by intro h; subst j; omega
  have haEj : c a (E j) = ⁅E i, E j⁆ :=
    hs.weylUnit_conj_E_of_cartan_eq_neg_one hii hij hEi hFi
  have haEi : c a (E i) = -F i := by
    simpa only [hc, a, coe_weylUnit, coe_inv_weylUnit] using
      weylUnit_conj_e (hs.isSl2Triple hii hi) hEi hFi
  have hbEi : c b (E i) = (6⁻¹ : ℚ) • ⁅E j, ⁅E j, ⁅E j, E i⁆⁆⁆ :=
    hs.weylUnit_conj_of_cartan_eq_neg_three hjj hji hEj hFj
  have hbEj : c b (E j) = -F j := by
    simpa only [hc, b, coe_weylUnit, coe_inv_weylUnit] using
      weylUnit_conj_e (hs.isSl2Triple hjj hj) hEj hFj
  obtain ⟨hf₂, hf₃⟩ := hs.lie_F_lie_E_string_of_cartan_eq_neg_three hjj hji hj
  -- The bracket of the reflected generators at the `i`-th node returns `E j`.
  have hback : ⁅⁅E i, E j⁆, -F i⁆ = E j := by
    rw [lie_neg, ← lie_skew (E i) (E j), neg_lie, neg_neg,
      hs.lie_lie_E_E_F_of_ne hne.symm, hij]
    simp
  have hf₃' : ⁅⁅E j, ⁅E j, ⁅E j, E i⁆⁆⁆, F j⁆ = -((3 : ℚ) • ⁅E j, ⁅E j, E i⁆⁆) := by
    rw [← lie_skew, hf₃]
  have hswap : ⁅⁅E i, E j⁆, E j⁆ = ⁅E j, ⁅E j, E i⁆⁆ := by
    rw [← lie_skew (E j) (E i), lie_neg, ← lie_skew (E j) ⁅E i, E j⁆, neg_neg]
  have h₁ : c b (c a (E j)) = (2⁻¹ : ℚ) • ⁅E j, ⁅E j, E i⁆⁆ := by
    rw [haEj, maplie, hbEi, hbEj, smul_lie, lie_neg, hf₃']
    module
  have h₂ : c a ⁅E j, ⁅E j, E i⁆⁆ = ⁅E j, ⁅E j, E i⁆⁆ := by
    rw [maplie, maplie, haEj, haEi, hback, hswap]
  have h₃ : c b ⁅E j, ⁅E j, E i⁆⁆ = (2 : ℚ) • ⁅E j, E i⁆ := by
    rw [maplie, maplie, hbEj, hbEi]
    simp only [neg_lie, lie_neg, lie_smul, hf₃, hf₂]
    module
  have h₄ : c a ⁅E j, E i⁆ = E j := by
    rw [maplie, haEj, haEi, hback]
  have hfix : c a (c b (c a (c b (c a (E j))))) = E j := by
    rw [h₁, map_smul, h₂, map_smul, h₃, smul_smul, map_smul, h₄]
    norm_num
  simpa only [c, MulSemiringAction.toAlgEquiv_apply, sq, ConjAct.toConjAct_mul, mul_smul] using
    hfix

/-- At a triple bond the pinned Weyl units satisfy the length-six braid relation in the
unit group of an associative rational algebra. Only the four root operators at the two
nodes need be nilpotent; no faithfulness or nonvanishing assumption is required. -/
theorem weylUnit_braid_of_cartan_eq_neg_three (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -3)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj *
        weylUnit hEi hFi * weylUnit hEj hFj =
      weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi *
        weylUnit hEj hFj * weylUnit hEi hFi := by
  simpa only [pow_succ, pow_zero, one_mul, ← mul_assoc] using
    hs.weylUnit_braid_of_conj_E_eq hii hjj (by omega) (by omega) hEi hFi hEj hFj 2
      fun hs' => hs'.weylUnit_conj_five_E_of_tripleBond hii hjj hij hji

end TauCeti.IsSerreSystem
