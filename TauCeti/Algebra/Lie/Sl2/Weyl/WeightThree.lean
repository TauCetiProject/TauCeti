/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism
public import TauCeti.Algebra.Lie.Sl2.WeightString

/-!
# Weyl normalization on a four-element root string

For a lowest-weight vector of weight minus three, the pinned Weyl automorphism sends it to
one sixth of its third raising bracket. This fixes the parameter normalization at a triple
bond, rather than merely identifying the reflected weight. The corresponding conjugation
identity applies to nilpotent operators in any rational associative algebra.

The construction uses `TauCeti.weylAut` and its alternative lowering–raising–lowering
factorization. The four string vectors need not be independent or nonzero.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§7 and 25.2.
-/

public section

open LieAlgebra

namespace IsSl2Triple

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L]
  {h e f : L}

/-- On a lowest-weight vector of weight minus three, the pinned Weyl automorphism is one sixth
of the third raising bracket. -/
theorem weylAut_apply_of_weight_neg_three (t : IsSl2Triple h e f)
    (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f)) {y : L}
    (hyh : ⁅h, y⁆ = (-3 : ℚ) • y) (hyf : ⁅f, y⁆ = 0) :
    TauCeti.weylAut t he.exists_pow_apply_eq_zero hf.exists_pow_apply_eq_zero y =
      (6⁻¹ : ℚ) • ⁅e, ⁅e, ⁅e, y⁆⁆⁆ := by
  let y₁ := ⁅e, y⁆
  let y₂ := ⁅e, y₁⁆
  let y₃ := ⁅e, y₂⁆
  -- Specialize the string coefficients to 3, 4, 3.
  have hf₁ : ⁅f, y₁⁆ = (3 : ℚ) • y := by
    simpa using t.lie_f_pow_succ_toEnd_e hyh hyf 0
  have hf₂ : ⁅f, y₂⁆ = (4 : ℚ) • y₁ := by
    convert t.lie_f_pow_succ_toEnd_e hyh hyf 1 using 1 <;>
      norm_num [y₁, y₂, pow_succ', mul_apply_eq_comp]
  have hf₃ : ⁅f, y₃⁆ = (3 : ℚ) • y₂ := by
    convert t.lie_f_pow_succ_toEnd_e hyh hyf 2 using 1 <;>
      norm_num [y₁, y₂, y₃, pow_succ', mul_apply_eq_comp]
  have hye : ⁅e, ⁅e, ⁅e, ⁅e, y⁆⁆⁆⁆ = 0 := by
    simpa [pow_succ', mul_apply_eq_comp] using
      t.pow_ad_apply_eq_zero_of_weight_neg_nat he 3 hyh hyf
  have hnf : IsNilpotent (ad K L (-f)) := by simpa using hf.neg
  have he' := he.exists_pow_apply_eq_zero
  have hnf' := hnf.exists_pow_apply_eq_zero
  have h₀ : TauCeti.expAd (-f) hnf' y = y :=
    TauCeti.expAd_apply_of_lie_eq_zero hnf' (by simp [hyf])
  have h₁ : TauCeti.expAd (-f) hnf' y₁ = y₁ - (3 : ℚ) • y := by
    rw [TauCeti.expAd_apply_of_lie_lie_eq_zero hnf' (by simp [hf₁, hyf]),
      neg_lie, hf₁]
    module
  have h₂ : TauCeti.expAd (-f) hnf' y₂ =
      y₂ - (4 : ℚ) • y₁ + (6 : ℚ) • y := by
    rw [TauCeti.expAd_apply_of_lie_lie_lie_eq_zero hnf'
      (by simp [hf₂, hf₁, hyf])]
    simp only [neg_lie, lie_neg, lie_smul, hf₂, hf₁]
    module
  -- Expand only on these vectors: no global nilpotency exponent is needed.
  have h₃ : TauCeti.expAd (-f) hnf' y₃ =
      y₃ - (3 : ℚ) • y₂ + (6 : ℚ) • y₁ - (6 : ℚ) • y := by
    rw [TauCeti.expAd_apply_of_lie_lie_lie_lie_eq_zero hnf'
      (by simp [hf₃, hf₂, hf₁, hyf])]
    simp only [neg_lie, lie_neg, lie_smul, hf₃, hf₂, hf₁]
    module
  have he₀ : TauCeti.expAd e he' y =
      y + y₁ + (2⁻¹ : ℚ) • y₂ + (6⁻¹ : ℚ) • y₃ :=
    TauCeti.expAd_apply_of_lie_lie_lie_lie_eq_zero he' hye
  rw [TauCeti.weylAut_apply_eq_expAd_neg_expAd_expAd_neg he' hf.exists_pow_apply_eq_zero hnf' t,
    h₀, he₀]
  simp only [map_add, map_rat_smul, h₀, h₁, h₂, h₃]
  module

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A] {H E F : A}

/-- Conjugation by the pinned Weyl unit sends a lowest-weight minus-three operator to one sixth
of its third raising bracket. The division takes place in the rational algebra. -/
theorem weylUnit_conj_of_weight_neg_three (t : IsSl2Triple H E F)
    (hE : IsNilpotent E) (hF : IsNilpotent F) {y : A}
    (hyh : ⁅H, y⁆ = (-3 : ℚ) • y) (hyf : ⁅F, y⁆ = 0) :
    ((TauCeti.weylUnit hE hF : Aˣ) : A) * y *
        (((TauCeti.weylUnit hE hF)⁻¹ : Aˣ) : A) =
      (6⁻¹ : ℚ) • ⁅E, ⁅E, ⁅E, y⁆⁆⁆ := by
  rw [← TauCeti.weylAut_apply_eq_weylUnit_conj (K := ℚ) t hE hF]
  exact t.weylAut_apply_of_weight_neg_three (LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) hE)
    (LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) hF) hyh hyf

end Associative

end IsSl2Triple
