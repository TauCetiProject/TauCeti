/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism

/-!
# Weyl reflection on a three-element root string

For an `sl₂` triple, the pinned Weyl automorphism carries a lowest-weight vector of weight
minus two to its second raising bracket divided by two. This fixes the normalization of the
reflected root vector at a double bond, rather than only identifying its weight space.
The associative form identifies the same vector with conjugation by the pinned Weyl unit.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §7.

The exponential calculations use `TauCeti.expAd` and the pinned Weyl convention of
`TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism`.
-/

public section

namespace IsSl2Triple

open TauCeti LieAlgebra

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L]
  {h e f y : L}

/-- On a lowest-weight vector of weight minus two whose third raising bracket vanishes,
the pinned Weyl automorphism is the divided second raising bracket. -/
theorem weylAut_apply_of_lie_eq_neg_two_smul (t : IsSl2Triple h e f)
    (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f))
    (hhy : ⁅h, y⁆ = (-2 : ℚ) • y) (hfy : ⁅f, y⁆ = 0)
    (heeey : ⁅e, ⁅e, ⁅e, y⁆⁆⁆ = 0) :
    weylAut t he hf y = (2⁻¹ : ℚ) • ⁅e, ⁅e, y⁆⁆ := by
  have hf' : IsNilpotent (ad K L (-f)) := by simpa only [map_neg] using hf.neg
  have hfey : ⁅f, ⁅e, y⁆⁆ = (2 : ℚ) • y := by
    simpa only [t.lie_e_f, hhy, hfy, lie_zero, zero_sub, neg_smul, neg_inj] using
      (lie_lie (m := y) (x := e) (y := f)).symm
  have hhey : ⁅h, ⁅e, y⁆⁆ = 0 := by
    rw [leibniz_lie, t.lie_h_e_smul ℚ, smul_lie, hhy, lie_smul]
    module
  have hfeey : ⁅f, ⁅e, ⁅e, y⁆⁆⁆ = (2 : ℚ) • ⁅e, y⁆ := by
    have hc := lie_lie (m := ⁅e, y⁆) (x := e) (y := f)
    rw [t.lie_e_f, hhey, hfey, lie_smul] at hc
    exact (sub_eq_zero.mp hc.symm).symm
  have hE0 : expAd e he y = y + ⁅e, y⁆ + (2⁻¹ : ℚ) • ⁅e, ⁅e, y⁆⁆ :=
    expAd_apply_of_lie_lie_lie_eq_zero he heeey
  have hF0 : expAd (-f) hf' y = y :=
    expAd_apply_of_lie_eq_zero hf' (by rw [neg_lie, hfy, neg_zero])
  have hF1 : expAd (-f) hf' ⁅e, y⁆ = ⁅e, y⁆ - (2 : ℚ) • y := by
    rw [expAd_apply_of_lie_lie_eq_zero hf' (by simp [neg_lie, hfey, hfy]),
      neg_lie, hfey]
    exact (sub_eq_add_neg _ _).symm
  have hF2 : expAd (-f) hf' ⁅e, ⁅e, y⁆⁆ =
      ⁅e, ⁅e, y⁆⁆ - (2 : ℚ) • ⁅e, y⁆ + (2 : ℚ) • y := by
    rw [expAd_apply_of_lie_lie_lie_eq_zero hf' (by simp [neg_lie, hfeey, hfey, hfy])]
    simp only [neg_lie, hfeey, hfey, lie_smul, lie_neg, smul_neg, neg_neg, smul_smul]
    module
  have hmiddle : expAd (-f) hf' (expAd e he y) =
      (2⁻¹ : ℚ) • ⁅e, ⁅e, y⁆⁆ := by
    rw [hE0, map_add, map_add, map_rat_smul, hF0, hF1, hF2]
    module
  have hE2 : expAd e he ⁅e, ⁅e, y⁆⁆ = ⁅e, ⁅e, y⁆⁆ :=
    expAd_apply_of_lie_eq_zero he heeey
  rw [weylAut_apply he hf t, hmiddle, map_rat_smul, hE2]

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A] {H E F Y : A}

/-- The pinned Weyl unit conjugates a lowest-weight vector of weight minus two to its
divided second raising bracket. -/
theorem weylUnit_conj_of_lie_eq_neg_two_smul (t : IsSl2Triple H E F)
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hHY : ⁅H, Y⁆ = (-2 : ℚ) • Y) (hFY : ⁅F, Y⁆ = 0)
    (hEEEY : ⁅E, ⁅E, ⁅E, Y⁆⁆⁆ = 0) :
    (weylUnit hE hF : A) * Y * ↑(weylUnit hE hF)⁻¹ =
      (2⁻¹ : ℚ) • ⁅E, ⁅E, Y⁆⁆ := by
  rw [← weylAut_apply_eq_weylUnit_conj (K := ℚ) t hE hF]
  exact t.weylAut_apply_of_lie_eq_neg_two_smul _ _ hHY hFY hEEEY

end Associative

end IsSl2Triple
