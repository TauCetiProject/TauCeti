/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism

/-!
# The Weyl automorphism on a two-dimensional root string

For an `sl₂` triple, a lowest-weight vector of weight minus one whose raising string has
length two is sent to its raising bracket by the pinned Weyl automorphism. This determines
the parameter sign when transporting a simple root subgroup across a single bond.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §7.
-/

public section

namespace TauCeti

open LieAlgebra

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L]
  {h e f : L}

/-- The pinned Weyl automorphism sends a lowest-weight vector of weight minus one on a
length-two raising string to its raising bracket. -/
theorem _root_.IsSl2Triple.weylAut_apply_of_lie_h_eq_neg (t : IsSl2Triple h e f)
    (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f)) {y : L}
    (hhy : ⁅h, y⁆ = -y) (hfy : ⁅f, y⁆ = 0) (heey : ⁅e, ⁅e, y⁆⁆ = 0) :
    weylAut t he hf y = ⁅e, y⁆ := by
  have hf' : IsNilpotent (ad K L (-f)) := by simpa using hf.neg
  have hfey : ⁅f, ⁅e, y⁆⁆ = y := by
    rw [leibniz_lie, ← lie_skew f e, t.lie_e_f, neg_lie, hhy, hfy, lie_zero, neg_neg,
      add_zero]
  have hnegfy : ⁅-f, y⁆ = 0 := by simp only [neg_lie, hfy, neg_zero]
  have hnegfey : ⁅-f, ⁅e, y⁆⁆ = -y := by rw [neg_lie, hfey]
  have hE : expAd e he y = y + ⁅e, y⁆ :=
    expAd_apply_of_lie_lie_eq_zero he heey
  have hFy : expAd (-f) hf' y = y := expAd_apply_of_lie_eq_zero hf' hnegfy
  have hFEy : expAd (-f) hf' ⁅e, y⁆ = ⁅e, y⁆ - y := by
    rw [expAd_apply_of_lie_lie_eq_zero hf'
      (by rw [hnegfey, lie_neg, hnegfy, neg_zero]), hnegfey, sub_eq_add_neg]
  have hF : expAd (-f) hf' (y + ⁅e, y⁆) = ⁅e, y⁆ := by
    rw [map_add, hFy, hFEy]
    abel
  rw [weylAut_apply he hf t, hE, hF, expAd_apply_of_lie_eq_zero he heey]

section Associative

variable {A : Type*} [Ring A] [Algebra ℚ A] {H E F Y : A}

-- Conjugation and the Lie bracket use the same associative algebra structure.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Conjugation by the pinned Weyl unit sends a lowest-weight element of weight minus one
on a length-two raising string to its raising commutator. -/
theorem _root_.IsSl2Triple.weylUnit_conj_of_lie_h_eq_neg (t : IsSl2Triple H E F)
    (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hHY : ⁅H, Y⁆ = -Y) (hFY : ⁅F, Y⁆ = 0) (hEEY : ⁅E, ⁅E, Y⁆⁆ = 0) :
    (weylUnit hE hF : A) * Y * (((weylUnit hE hF)⁻¹ : Aˣ) : A) = ⁅E, Y⁆ := by
  rw [← weylAut_apply_eq_weylUnit_conj (K := ℚ) t hE hF]
  exact t.weylAut_apply_of_lie_h_eq_neg _ _ hHY hFY hEEY

end Associative

end TauCeti
