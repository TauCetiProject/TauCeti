/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.WeightTwo

/-!
# Double-bond Weyl normalization for Serre systems

In any associative rational algebra, a Serre system with `CM i i = 2` and `CM i j = -2`
has the following normalization: conjugation by the pinned Weyl unit at `i` sends `E j` to
one half of its second raising bracket. Only `E i` and `F i` need to be nilpotent.
Here the Cartan convention is that of `IsSerreSystem`: `CM i j` is the eigenvalue of
`ad (H i)` on `E j`. No nonvanishing or faithfulness assumption on the system is needed.

This applies the three-element string calculation in
`TauCeti.Algebra.Lie.Sl2.Weyl.WeightTwo` using the Serre relations.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.IsSerreSystem

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

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
    rw [hs.lie_H_E, hij, ← Int.cast_smul_eq_zsmul ℚ]
    norm_num
  by_cases hH : H i = 0
  · have hz : E j = 0 := by
      have hw : (-2 : ℚ) • E j = 0 := by rw [← hweight, hH, zero_lie]
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
  have hthird : ⁅E i, ⁅E i, ⁅E i, E j⁆⁆⁆ = 0 := by
    have hz := hs.ad_pow_lie_E_E i j
    norm_num [hij] at hz
    simpa only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp, ad_apply] using hz
  exact ht.weylUnit_conj_of_lie_eq_neg_two_smul hE hF hweight hlower hthird

end TauCeti.IsSerreSystem
