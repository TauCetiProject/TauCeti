/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightOne
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Single-bond Weyl braid relations for Serre operators

In an associative rational algebra, the pinned Weyl units of a nilpotent Serre system
satisfy the length-three braid relation at every single bond. This is an equality of units,
not merely of their conjugation actions or their images modulo a torus. It supplies the
rational operator identity from which integral lattice identities can be transported.

The root-string formulas come from `IsSl2Triple.weylUnit_conj_of_lie_h_eq_neg` and its
highest-weight counterpart. Serre's nested-bracket identities then identify the conjugated
raising and lowering operators; functoriality of the nilpotent exponential identifies the
Weyl units themselves. The Geck single-bond sign comparison in
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

section Degenerate

variable {B R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsAddTorsionFree L]
  {CM : Matrix B B ℤ} {H E F : B → L}

/-- In a torsion-free Serre system, at a bond whose two Cartan entries are nonzero, a zero Cartan
generator at the node `j` forces the raising and lowering generators at both nodes to vanish. -/
theorem eq_zero_of_H_eq_zero_of_cartan_ne_zero (hs : IsSerreSystem R CM H E F) {i j : B}
    (hij : CM i j ≠ 0) (hji : CM j i ≠ 0) (hj : H j = 0) :
    E i = 0 ∧ F i = 0 ∧ E j = 0 ∧ F j = 0 := by
  have hEi0 : E i = 0 := hs.E_eq_zero_of_H_eq_zero hj hji
  have hi0 : H i = 0 := by rw [← hs.lie_E_F_self i, hEi0, zero_lie]
  exact ⟨hEi0, hs.F_eq_zero_of_H_eq_zero hj hji, hs.E_eq_zero_of_H_eq_zero hi0 hij,
    hs.F_eq_zero_of_H_eq_zero hi0 hij⟩

end Degenerate

variable {B A : Type*} [Ring A] [Algebra ℚ A]
  {CM : Matrix B B ℤ} {H E F : B → A}

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

/-- At a node with `CM k k = 2`, the Weyl unit of the signed exchange `hs.neg_swap` acts by the
same conjugation as the Weyl unit of `hs`. No nonvanishing of `H k` is needed: if `H k = 0` then
`E k` and `F k` vanish. The statement uses the conjugation action so that it rewrites inside
conjugation by a word in Weyl units. -/
theorem toConjAct_weylUnit_neg_swap_smul (hs : IsSerreSystem ℚ CM H E F) {k : B}
    (hkk : CM k k = 2) (hEk : IsNilpotent (E k)) (hFk : IsNilpotent (F k)) (y : A) :
    ConjAct.toConjAct (weylUnit hFk.neg hEk.neg) • y =
      ConjAct.toConjAct (weylUnit hEk hFk) • y := by
  simp only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  by_cases hk : H k = 0
  · simp [hs.E_eq_zero_of_H_eq_zero hk (by omega : CM k k ≠ 0),
      hs.F_eq_zero_of_H_eq_zero hk (by omega : CM k k ≠ 0)]
  exact weylUnit_neg_symm_conj (hs.isSl2Triple hkk hk) hEk hFk y

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
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  let c (u : Aˣ) : A →+* A :=
    MulSemiringAction.toRingHom (ConjAct Aˣ) A (ConjAct.toConjAct u)
  have hc (u : Aˣ) (x : A) : c u x = (u : A) * x * ↑u⁻¹ := by
    simp only [c, MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct]
  have hne : i ≠ j := by intro h; subst j; omega
  have haE : c a (E j) = ⁅E i, E j⁆ :=
    hs.weylUnit_conj_E_of_cartan_eq_neg_one hii hij hEi hFi
  have haF : c a (F j) = -⁅F i, F j⁆ :=
    hs.weylUnit_conj_F_of_cartan_eq_neg_one hii hij hEi hFi
  have hbE : c b (E i) = ⁅E j, E i⁆ :=
    hs.weylUnit_conj_E_of_cartan_eq_neg_one hjj hji hEj hFj
  have hbF : c b (F i) = -⁅F j, F i⁆ :=
    hs.weylUnit_conj_F_of_cartan_eq_neg_one hjj hji hEj hFj
  -- A zero Cartan operator forces all four root operators to vanish at a single bond.
  by_cases hH : H j = 0
  · obtain ⟨hEi0, hFi0, hEj0, hFj0⟩ :=
      hs.eq_zero_of_H_eq_zero_of_cartan_ne_zero (i := i) (by omega) (by omega) hH
    apply Units.ext
    simp [hEi0, hFi0, hEj0, hFj0]
  have ht := hs.isSl2Triple hjj hH
  have hbEj : c b (E j) = -F j := by
    simpa only [hc, b, coe_weylUnit, coe_inv_weylUnit] using weylUnit_conj_e ht hEj hFj
  have hbFj : c b (F j) = -E j := by
    simpa only [hc, b, coe_weylUnit, coe_inv_weylUnit] using weylUnit_conj_f ht hEj hFj
  -- Conjugation by b * a takes the j-th raising and lowering operators to the i-th ones.
  have maplie (u : Aˣ) (x y : A) : c u ⁅x, y⁆ = ⁅c u x, c u y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  have hE : c b (c a (E j)) = E i := by
    rw [haE, maplie, hbE, hbEj, ← lie_skew (E j) (E i)]
    simpa only [neg_lie, lie_neg, neg_neg, hji, neg_one_zsmul] using
      hs.lie_lie_E_E_F_of_ne hne
  have hF : c b (c a (F j)) = F i := by
    rw [haF, map_neg, maplie, hbF, hbFj, ← lie_skew (F j) (F i)]
    simpa only [neg_lie, lie_neg, neg_neg, hji, neg_one_zsmul] using
      hs.lie_lie_F_F_E_of_ne hne
  -- Exponentiate this operator comparison, retaining the units rather than only their action.
  have hu : b * a * b * (b * a)⁻¹ = a :=
    conj_weylUnit_eq_of_conj_eq hEj hFj hEi hFi
      (by simpa only [hc, Units.val_mul, Units.val_inv, mul_inv_rev, mul_assoc] using hE)
      (by simpa only [hc, Units.val_mul, Units.val_inv, mul_inv_rev, mul_assoc] using hF)
  calc
    _ = (b * a * b * (b * a)⁻¹) * b * a := by rw [hu]
    _ = b * a * b := by group

end TauCeti.IsSerreSystem
