/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree

/-!
# Triple-bond Weyl normalization for Serre systems

At a directed Cartan entry minus three, the pinned Weyl unit sends the raising generator
to one sixth of its third raising bracket, and the lowering generator to minus one sixth
of its third lowering bracket. Both signs are needed to conjugate the Weyl representative
at the adjacent node, and hence to establish the triple-bond braid relation.

These are rational operator identities. They impose no faithfulness or nonvanishing on the
Serre system and divide by six only in the rational algebra, not in a value ring of positive
characteristic. The matrix convention is `⁅H i, E j⁆ = CM i j • E j`.

The formulas use the root-string calculations in
`TauCeti.Algebra.Lie.Sl2.Weyl.WeightThree`, as the double-bond formulas use `WeightTwo`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.IsSerreSystem

attribute [local instance 100] LieRing.ofAssociativeRing

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
    rw [hs.lie_H_E, hij, ← Int.cast_smul_eq_zsmul ℚ]
    norm_num
  by_cases hH : H i = 0
  · have hz : E j = 0 := by
      have hw : (-3 : ℚ) • E j = 0 := by rw [← hweight, hH, zero_lie]
      exact (smul_eq_zero.mp hw).resolve_left (by norm_num)
    simp [hz]
  have ht : IsSl2Triple (H i) (E i) (F i) :=
    { h_ne_zero := hH
      lie_e_f := hs.lie_E_F_self i
      lie_h_e_nsmul := by simpa [hii, two_smul] using hs.lie_H_E i i
      lie_h_f_nsmul := by simpa [hii, two_smul] using hs.lie_H_F i i }
  have hne : j ≠ i := by
    intro h
    subst j
    omega
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
    rw [hs.lie_H_F, hij, ← Int.cast_smul_eq_zsmul ℚ]
    norm_num
  by_cases hH : H i = 0
  · have hz : F j = 0 := by
      have hw : (3 : ℚ) • F j = 0 := by rw [← hweight, hH, zero_lie]
      exact (smul_eq_zero.mp hw).resolve_left (by norm_num)
    simp [hz]
  have ht : IsSl2Triple (H i) (E i) (F i) :=
    { h_ne_zero := hH
      lie_e_f := hs.lie_E_F_self i
      lie_h_e_nsmul := by simpa [hii, two_smul] using hs.lie_H_E i i
      lie_h_f_nsmul := by simpa [hii, two_smul] using hs.lie_H_F i i }
  have hne : i ≠ j := by
    intro h
    subst j
    omega
  exact ht.weylUnit_conj_of_weight_three hE hF hweight (hs.lie_E_F_of_ne i j hne)

end TauCeti.IsSerreSystem
