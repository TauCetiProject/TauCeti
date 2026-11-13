/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism
import TauCeti.Algebra.Lie.Sl2.Weyl.WeightOne
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree

/-!
# Triple-bond Weyl normalization and the braid relation for Serre operators

The pinned Weyl units of a nilpotent rational Serre system satisfy the length-six
braid relation at a triple bond. The result is equality of units in the associative
algebra, not just equality of their conjugation actions. It can therefore be restricted
to an admissible lattice and extended to arbitrary coefficient rings.

At a directed Cartan entry minus three, conjugation carries the raising generator
to one sixth of its third raising bracket and the lowering generator to minus one
sixth of its third lowering bracket. These normalization identities divide by six
only in the rational algebra, not in a value ring of positive characteristic.

The calculation follows the long-root string in the rank-two subsystem: the five-letter
word starting and ending at the short node fixes both long-node root operators.
Functoriality of the nilpotent exponential then makes that word commute with the
long-node Weyl unit. The signed exchange of a Serre system supplies the lowering case.
No faithfulness, finite-dimensionality or nonvanishing assumption is imposed.
The unit-level exponentiation step shares `TauCeti.weylUnit_conj_eq_of_conj` with the
single-bond argument in `TauCeti.Algebra.Lie.Presentation.Serre.SingleBond`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.IsSerreSystem

open LieAlgebra

section Lie

variable {B L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {CM : Matrix B B ℤ} {H E F : B → L}

private theorem lie_H_triple_E (hs : IsSerreSystem ℚ CM H E F) (k i j : B) :
    ⁅H k, ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆⁆ =
      (3 * CM k i + CM k j) • ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆ := by
  rw [leibniz_lie (H k) (E i) ⁅E i, ⁅E i, E j⁆⁆,
    leibniz_lie (H k) (E i) ⁅E i, E j⁆, leibniz_lie (H k) (E i) (E j)]
  simp only [hs.lie_H_E, zsmul_lie, lie_zsmul, lie_add]
  module

-- The two long roots at the far end of the short-node string form a length-two
-- string for the long node. Record its orientation, including the returning minus sign.
private theorem long_node_string (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hjj : CM j j = 2) (hji : CM j i = -1) (hj : H j ≠ 0)
    (hfa : ⁅F j, E i⁆ = 0)
    (hej : IsNilpotent (ad ℚ L (E j))) (hfj : IsNilpotent (ad ℚ L (F j))) :
    let b := weylAut (hs.isSl2Triple hjj hj)
      hej.exists_pow_apply_eq_zero hfj.exists_pow_apply_eq_zero
    let c := (6⁻¹ : ℚ) • ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆
    b c = ⁅E j, c⁆ ∧ b ⁅E j, c⁆ = -c := by
  let tj := hs.isSl2Triple hjj hj
  let b := weylAut tj hej.exists_pow_apply_eq_zero hfj.exists_pow_apply_eq_zero
  let c := (6⁻¹ : ℚ) • ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆
  let d := ⁅E j, c⁆
  have hjc : ⁅H j, c⁆ = -c := by
    dsimp only [c]
    rw [lie_smul, lie_H_triple_E hs, hji, hjj]
    module
  have hfjc : ⁅F j, c⁆ = 0 := by
    dsimp only [c]
    rw [lie_smul, leibniz_lie (F j) (E i) ⁅E i, ⁅E i, E j⁆⁆, hfa, zero_lie, zero_add,
      leibniz_lie (F j) (E i) ⁅E i, E j⁆, hfa, zero_lie, zero_add,
      leibniz_lie (F j) (E i) (E j), hfa, zero_lie, zero_add,
      ← lie_skew (F j) (E j), hs.lie_E_F_self, lie_neg,
      ← lie_skew (E i) (H j), hs.lie_H_E, hji]
    simp
  have heec : ⁅E j, ⁅E j, c⁆⁆ = 0 := by
    simpa [pow_succ', mul_apply_eq_comp] using tj.pow_ad_apply_eq_zero_of_weight_neg_nat hej 1
      (by simpa using hjc) hfjc
  have hbc : b c = d := tj.weylAut_apply_of_lie_h_eq_neg hej hfj hjc hfjc heec
  have hjd : ⁅H j, d⁆ = d := by
    dsimp only [d]
    rw [leibniz_lie, hs.lie_H_E j j, hjj, hjc]
    simp only [smul_lie, lie_neg]
    module
  have hfjd : ⁅F j, d⁆ = c := by
    dsimp only [d]
    rw [leibniz_lie (F j) (E j) c, ← lie_skew (F j) (E j), tj.lie_e_f, neg_lie,
      hjc, neg_neg, hfjc, lie_zero, add_zero]
  have hbd : b d = -c := by
    have h := tj.neg_symm.weylAut_apply_of_lie_h_eq_neg
      (by simpa using hfj.neg) (by simpa using hej.neg)
      (y := d) (by simp [hjd]) (by simp [d, heec]) (by simp [hfjd, hfjc])
    rw [tj.weylAut_neg_symm] at h
    simpa [hfjd] using h
  exact ⟨hbc, hbd⟩

private theorem fivefold_fixes_long_raising (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -3) (hji : CM j i = -1)
    (hi : H i ≠ 0) (hj : H j ≠ 0)
    (hei : IsNilpotent (ad ℚ L (E i))) (hfi : IsNilpotent (ad ℚ L (F i)))
    (hej : IsNilpotent (ad ℚ L (E j))) (hfj : IsNilpotent (ad ℚ L (F j))) :
    let a := weylAut (hs.isSl2Triple hii hi)
      hei.exists_pow_apply_eq_zero hfi.exists_pow_apply_eq_zero
    let b := weylAut (hs.isSl2Triple hjj hj)
      hej.exists_pow_apply_eq_zero hfj.exists_pow_apply_eq_zero
    a (b (a (b (a (E j))))) = E j := by
  let ti := hs.isSl2Triple hii hi
  let a := weylAut ti hei.exists_pow_apply_eq_zero hfi.exists_pow_apply_eq_zero
  let c := (6⁻¹ : ℚ) • ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆
  let d := ⁅E j, c⁆
  have hne : i ≠ j := by intro h; subst j; omega
  have hw : ⁅H i, E j⁆ = (-3 : ℚ) • E j := by
    simpa [hij, ← Int.cast_smul_eq_zsmul ℚ] using hs.lie_H_E i j
  have hfi0 : ⁅F i, E j⁆ = 0 := by
    rw [← lie_skew, hs.lie_E_F_of_ne j i hne.symm, neg_zero]
  have ha : a (E j) = c := ti.weylAut_apply_of_weight_neg_three hei hfi hw hfi0
  have hfc : ⁅F i, c⁆ = (2⁻¹ : ℚ) • ⁅E i, ⁅E i, E j⁆⁆ := by
    have h := ti.lie_f_pow_succ_toEnd_e hw hfi0 2
    norm_num [pow_succ', mul_apply_eq_comp] at h
    simp only [c, lie_smul, h]
    module
  -- The highest long root d has short-node weight zero. Its lowering bracket
  -- vanishes by the long-node Serre relation, so the whole short-node triple fixes it.
  have hbc2 : ⁅E j, ⁅E i, ⁅E i, E j⁆⁆⁆ = 0 := by
    have hbb : ⁅E j, ⁅E i, E j⁆⁆ = 0 := by
      rw [← lie_skew (E i) (E j), lie_neg, hs.lie_E_lie_E_E_of_eq_neg_one hji, neg_zero]
    have h := congrArg (fun z => ⁅E i, z⁆) hbb
    rw [leibniz_lie, lie_self, zero_add, lie_zero] at h
    exact h
  have hfd : ⁅F i, d⁆ = 0 := by
    dsimp only [d]
    rw [leibniz_lie, hfi0, zero_lie, zero_add, hfc, lie_smul, hbc2, smul_zero]
  have hhc : ⁅H i, c⁆ = (3 : ℚ) • c := by
    dsimp only [c]
    rw [lie_smul, lie_H_triple_E hs, hii, hij]
    module
  have hhd : ⁅H i, d⁆ = (0 : ℚ) • d := by
    dsimp only [d]
    rw [leibniz_lie, hw, hhc]
    simp only [smul_lie, lie_smul]
    module
  have hed : ⁅E i, d⁆ = 0 := by
    simpa using ti.pow_ad_apply_eq_zero_of_weight_neg_nat hei 0 hhd hfd
  have had : a d = d := weylAut_apply_of_lie_eq_zero
    hei.exists_pow_apply_eq_zero hfi.exists_pow_apply_eq_zero ti
    (by rw [← lie_skew d (E i), hed, neg_zero])
    (by rw [← lie_skew d (F i), hfd, neg_zero])
  obtain ⟨hbc, hbd⟩ := long_node_string hs hjj hji hj
    (by rw [← lie_skew, hs.lie_E_F_of_ne i j hne, neg_zero]) hej hfj
  -- Returning down the short-node string contributes the second minus sign.
  have hac : a c = -E j := by
    conv_lhs => dsimp only [c]
    rw [map_smul, LieEquiv.map_lie, LieEquiv.map_lie, LieEquiv.map_lie,
      weylAut_apply_e, ha]
    have h1 := ti.lie_f_pow_succ_toEnd_e hw hfi0 0
    have h2 := ti.lie_f_pow_succ_toEnd_e hw hfi0 1
    norm_num [pow_succ', mul_apply_eq_comp] at h1 h2
    simp only [neg_lie, lie_neg, lie_smul, hfc, h2, h1]
    module
  dsimp only
  rw [ha, hbc, had, hbd, map_neg, hac, neg_neg]

end Lie

section Associative

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

/-- At a triple bond, the pinned Weyl units satisfy the length-six braid relation.
Only the four root operators at the two nodes need be nilpotent. -/
theorem weylUnit_braid_of_cartan_eq_neg_three (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -3) (hji : CM j i = -1)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi *
        weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj =
      weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj *
        weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi := by
  -- A zero short-node Cartan operator forces the entire rank-two system to vanish.
  by_cases hi : H i = 0
  · have hEj0 : E j = 0 := by
      have h := hs.lie_H_E i j
      rw [hi, zero_lie, hij, ← Int.cast_smul_eq_zsmul ℚ] at h
      exact (smul_eq_zero.mp h.symm).resolve_left (by norm_num)
    have hFj0 : F j = 0 := by
      have h := hs.lie_H_F i j
      simp only [hi, zero_lie, hij, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_neg,
        Int.cast_ofNat, neg_smul, neg_neg] at h
      exact (smul_eq_zero.mp h.symm).resolve_left (by norm_num)
    have hj : H j = 0 := by rw [← hs.lie_E_F_self j, hEj0, zero_lie]
    have hEi0 : E i = 0 := by simpa [hj, hji] using hs.lie_H_E j i
    have hFi0 : F i = 0 := by simpa [hj, hji] using (hs.lie_H_F j i).symm
    apply Units.ext
    simp [hEi0, hFi0, hEj0, hFj0]
  have hj : H j ≠ 0 := by
    intro hz
    have he : E i = 0 := by simpa [hz, hji] using hs.lie_H_E j i
    exact hi (by rw [← hs.lie_E_F_self i, he, zero_lie])
  let hei := ad_nilpotent_of_nilpotent (R := ℚ) hEi
  let hfi := ad_nilpotent_of_nilpotent (R := ℚ) hFi
  let hej := ad_nilpotent_of_nilpotent (R := ℚ) hEj
  let hfj := ad_nilpotent_of_nilpotent (R := ℚ) hFj
  -- The signed exchange gives the same Weyl automorphisms on the lowering operators.
  have hE := fivefold_fixes_long_raising hs hii hjj hij hji hi hj hei hfi hej hfj
  have hF := fivefold_fixes_long_raising hs.neg_swap hii hjj hij hji
    (neg_ne_zero.mpr hi) (neg_ne_zero.mpr hj)
    (by simpa using hfi.neg) (by simpa using hei.neg)
    (by simpa using hfj.neg) (by simpa using hej.neg)
  dsimp only at hE hF
  simp only [(hs.isSl2Triple hii hi).weylAut_neg_symm
      hei.exists_pow_apply_eq_zero hfi.exists_pow_apply_eq_zero,
    (hs.isSl2Triple hjj hj).weylAut_neg_symm
      hej.exists_pow_apply_eq_zero hfj.exists_pow_apply_eq_zero, map_neg, neg_inj] at hF
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  let w := a * b * a * b * a
  have hwE : (w : A) * E j * ↑w⁻¹ = E j := by
    simpa only [weylAut_apply_eq_weylUnit_conj (hs.isSl2Triple hii hi) hEi hFi,
      weylAut_apply_eq_weylUnit_conj (hs.isSl2Triple hjj hj) hEj hFj,
      w, a, b, Units.val_mul, mul_inv_rev, mul_assoc] using hE
  have hwF : (w : A) * F j * ↑w⁻¹ = F j := by
    simpa only [weylAut_apply_eq_weylUnit_conj (hs.isSl2Triple hii hi) hEi hFi,
      weylAut_apply_eq_weylUnit_conj (hs.isSl2Triple hjj hj) hEj hFj,
      w, a, b, Units.val_mul, mul_inv_rev, mul_assoc] using hF
  -- Exponentiation turns the operator equalities into commutation with the actual Weyl unit.
  have hcomm : w * b * w⁻¹ = b :=
    weylUnit_conj_eq_of_conj hEj hFj hEj hFj w hwE hwF
  have heq : w * b = b * w := (mul_inv_eq_iff_eq_mul).mp hcomm
  simpa only [w, mul_assoc] using heq

end Associative

end TauCeti.IsSerreSystem
