/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.OuterAut
public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightOne

/-!
# Single-bond Weyl braid relations and shared Weyl-conjugation helpers for Serre operators

In an associative rational algebra, the pinned Weyl units of a nilpotent Serre system
satisfy the length-three braid relation at every single bond. This is an equality of units,
not merely of their conjugation actions or their images modulo a torus. It supplies the
rational operator identity from which integral lattice identities can be transported.

This file also provides shared conjugation helpers (`weylUnit_eq_one_of_H_eq_zero`,
`conjAlgEquiv_weylUnit_e`, `conjAlgEquiv_weylUnit_f`, and `conjAlgEquiv_weylUnit_neg`)
reused in the double- and triple-bond braid calculations.

The root-string formulas come from `IsSl2Triple.weylUnit_conj_of_lie_h_eq_neg` and its
highest-weight counterpart. Serre's nested-bracket identities then identify the conjugated
raising and lowering operators; functoriality of the nilpotent exponential (`conj_weylUnit`)
identifies the Weyl units themselves. The Geck single-bond sign comparison in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.SingleBond`
is derived from `TauCeti.IsSerreSystem.weylUnit_conj_E_of_cartan_eq_neg_one`.
No faithfulness, weight basis or finite-dimensionality is required.

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

/-- In a rational Serre system, a zero Cartan generator at `i` forces the pinned Weyl unit at
every node `j` with `CM i j ≠ 0` to be `1`. -/
theorem weylUnit_eq_one_of_H_eq_zero (hs : IsSerreSystem ℚ CM H E F) {i j : B}
    (hH : H i = 0) (hij : CM i j ≠ 0) (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    weylUnit hEj hFj = 1 :=
  weylUnit_of_eq_zero hEj hFj
    (hs.E_eq_zero_of_H_eq_zero hH hij) (hs.F_eq_zero_of_H_eq_zero hH hij)

/-- At a nondegenerate node with `CM i i = 2`, conjugation by the pinned Weyl unit sends `E i`
to `-F i`. -/
theorem conjAlgEquiv_weylUnit_e (hs : IsSerreSystem ℚ CM H E F) {i : B}
    (hii : CM i i = 2) (hi : H i ≠ 0) (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF).conjAlgEquiv ℚ (E i) = -F i := by
  simpa only [Units.conjAlgEquiv_apply, coe_weylUnit, coe_inv_weylUnit] using
    weylUnit_conj_e (hs.isSl2Triple hii hi) hE hF

/-- At a nondegenerate node with `CM i i = 2`, conjugation by the pinned Weyl unit sends `F i`
to `-E i`. -/
theorem conjAlgEquiv_weylUnit_f (hs : IsSerreSystem ℚ CM H E F) {i : B}
    (hii : CM i i = 2) (hi : H i ≠ 0) (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF).conjAlgEquiv ℚ (F i) = -E i := by
  simpa only [Units.conjAlgEquiv_apply, coe_weylUnit, coe_inv_weylUnit] using
    weylUnit_conj_f (hs.isSl2Triple hii hi) hE hF

/-- Signed exchange (`E ↦ -F`, `F ↦ -E`) preserves the conjugation algebra equivalence of the
pinned Weyl unit at any nondegenerate node of a Serre system with `CM i i = 2`. -/
theorem conjAlgEquiv_weylUnit_neg (hs : IsSerreSystem ℚ CM H E F) {i : B}
    (hii : CM i i = 2) (hi : H i ≠ 0) (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hF.neg hE.neg).conjAlgEquiv ℚ = (weylUnit hE hF).conjAlgEquiv ℚ := by
  ext x
  simpa only [Units.conjAlgEquiv_apply] using
    (hs.isSl2Triple hii hi).weylUnit_neg_symm_conj hE hF x

/-- At a directed Cartan entry minus one, the pinned Weyl unit sends the other raising
operator to the ordered raising commutator. -/
theorem weylUnit_conj_E_of_cartan_eq_neg_one (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hij : CM i j = -1)
    (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF : A) * E j * ↑(weylUnit hE hF)⁻¹ = ⁅E i, E j⁆ := by
  have hw : ⁅H i, E j⁆ = -E j := by simpa [hij] using hs.lie_H_E i j
  by_cases hH : H i = 0
  · have hz : E j = 0 := by simpa [hH] using hw.symm
    simp [hz]
  have ht := hs.isSl2Triple hii hH
  have hne : j ≠ i := by intro h; subst j; omega
  exact ht.weylUnit_conj_of_lie_h_eq_neg hE hF hw
    (by rw [← lie_skew, hs.lie_E_F_of_ne j i hne, neg_zero])
    (hs.lie_E_lie_E_E_of_eq_neg_one hij)

/-- At a directed Cartan entry minus one, the pinned Weyl unit sends the other lowering
operator to the negative of the ordered lowering commutator. -/
theorem weylUnit_conj_F_of_cartan_eq_neg_one (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hij : CM i j = -1)
    (hE : IsNilpotent (E i)) (hF : IsNilpotent (F i)) :
    (weylUnit hE hF : A) * F j * ↑(weylUnit hE hF)⁻¹ = -⁅F i, F j⁆ := by
  have hw : ⁅H i, F j⁆ = F j := by simpa [hij] using hs.lie_H_F i j
  by_cases hH : H i = 0
  · have hz : F j = 0 := by simpa [hH] using hw.symm
    simp [hz]
  have ht := hs.isSl2Triple hii hH
  have hne : i ≠ j := by intro h; subst j; omega
  exact ht.weylUnit_conj_of_lie_h_eq_self hE hF hw
    (hs.lie_E_F_of_ne i j hne) (hs.lie_F_lie_F_F_of_eq_neg_one hij)

/-- At a single bond the pinned Weyl units satisfy the length-three braid relation in the
unit group of the associative rational algebra. Only the four root operators at the two
nodes need be nilpotent; the Serre system need not be faithful or nonzero. -/
theorem weylUnit_braid_of_cartan_eq_neg_one (hs : IsSerreSystem ℚ CM H E F)
    {i j : B} (hii : CM i i = 2) (hjj : CM j j = 2)
    (hij : CM i j = -1) (hji : CM j i = -1)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) :
    weylUnit hEi hFi * weylUnit hEj hFj * weylUnit hEi hFi =
      weylUnit hEj hFj * weylUnit hEi hFi * weylUnit hEj hFj := by
  -- A zero Cartan operator forces all four root operators to vanish at a single bond.
  by_cases hj : H j = 0
  · have hi0 : H i = 0 := hs.H_eq_zero_of_H_eq_zero hj (by omega)
    simp [hs.weylUnit_eq_one_of_H_eq_zero hj (by omega) hEi hFi,
      hs.weylUnit_eq_one_of_H_eq_zero hi0 (by omega) hEj hFj]
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  have hne : i ≠ j := by rintro rfl; omega
  have maplie (u : Aˣ) (x y : A) :
      u.conjAlgEquiv ℚ ⁅x, y⁆ = ⁅u.conjAlgEquiv ℚ x, u.conjAlgEquiv ℚ y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  -- Conjugation by b * a takes the j-th raising and lowering operators to the i-th ones.
  have hE : (b * a).conjAlgEquiv ℚ (E j) = E i := by
    rw [Units.conjAlgEquiv_mul, AlgEquiv.mul_apply, a.conjAlgEquiv_apply ℚ,
      hs.weylUnit_conj_E_of_cartan_eq_neg_one hii hij hEi hFi, maplie,
      b.conjAlgEquiv_apply ℚ (E i),
      hs.weylUnit_conj_E_of_cartan_eq_neg_one hjj hji hEj hFj,
      hs.conjAlgEquiv_weylUnit_e hjj hj hEj hFj, ← lie_skew (E j) (E i)]
    simpa only [neg_lie, lie_neg, neg_neg, hji, neg_one_zsmul] using
      hs.lie_lie_E_E_F_of_ne hne
  have hF : (b * a).conjAlgEquiv ℚ (F j) = F i := by
    rw [Units.conjAlgEquiv_mul, AlgEquiv.mul_apply, a.conjAlgEquiv_apply ℚ,
      hs.weylUnit_conj_F_of_cartan_eq_neg_one hii hij hEi hFi, map_neg, maplie,
      b.conjAlgEquiv_apply ℚ (F i),
      hs.weylUnit_conj_F_of_cartan_eq_neg_one hjj hji hEj hFj,
      hs.conjAlgEquiv_weylUnit_f hjj hj hEj hFj, ← lie_skew (F j) (F i)]
    simpa only [neg_lie, lie_neg, neg_neg, hji, neg_one_zsmul] using
      hs.lie_lie_F_F_E_of_ne hne
  have hu : (b * a) * b * (b * a)⁻¹ = a :=
    conj_weylUnit (b * a) hEj hFj hEi hFi
      (by simpa only [Units.conjAlgEquiv_apply] using hE)
      (by simpa only [Units.conjAlgEquiv_apply] using hF)
  calc
    a * b * a = ((b * a) * b * (b * a)⁻¹) * b * a := by rw [hu]
    _ = b * a * b := by group

end TauCeti.IsSerreSystem
