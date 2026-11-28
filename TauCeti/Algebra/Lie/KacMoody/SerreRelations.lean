/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Algebra.Lie.Sl2.WeightString

/-!
# Serre commutator relations for generalized Cartan matrices

For a generalized Cartan matrix `A` and families `C`, `E`, `F` in a Lie algebra `L` over an
arbitrary commutative ring `K` satisfying the Chevalley generator-bracket identities
`⁅C i, E j⁆ = Aᵢⱼ • E j`, `⁅C i, F j⁆ = -Aᵢⱼ • F j`, `⁅E i, F i⁆ = C i`, and `⁅E i, F j⁆ = 0`
for `i ≠ j`, every `F k` commutes with each raising Serre element
`(ad (E i)) ^ (-Aᵢⱼ) ⁅E i, E j⁆` (`TauCeti.KacMoody.lie_ad_pow_lie_eq_zero`). Neither Serre's
relations nor `⁅C i, C j⁆ = 0` is assumed.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.3.
-/

public section

open LieAlgebra

namespace TauCeti

namespace KacMoody

/-- For a generalized Cartan matrix, every `F k` commutes with each raising Serre element
`(ad (E i)) ^ (-Aᵢⱼ) ⁅E i, E j⁆`, whenever `C`, `E`, and `F` satisfy the Chevalley
generator-bracket identities over a commutative ring `K` (Kac, §3.3). Neither Serre's relations
nor `⁅C i, C j⁆ = 0` is used. -/
theorem lie_ad_pow_lie_eq_zero {I K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {A : Matrix I I ℤ} (hA : A.IsGeneralizedCartan) {C E F : I → L}
    (hCE : ∀ i j, ⁅C i, E j⁆ = A i j • E j)
    (hCF : ∀ i j, ⁅C i, F j⁆ = -(A i j • F j))
    (hself : ∀ i, ⁅E i, F i⁆ = C i)
    (hne : ∀ i j, i ≠ j → ⁅E i, F j⁆ = 0) (i j k : I) :
    ⁅F k, (ad K L (E i) ^ (-A i j).toNat) ⁅E i, E j⁆⁆ = 0 := by
  obtain rfl | hij := eq_or_ne i j
  · simp
  have hFE (a b : I) (hab : a ≠ b) : ⁅F b, E a⁆ = 0 := by
    rw [← lie_skew, hne a b hab, neg_zero]
  rw [← ad_pow_succ_apply]
  obtain rfl | hki := eq_or_ne k i
  · by_cases h0 : C k = 0
    · rw [TauCeti.LieAlgebra.lie_ad_pow_of_lie_eq_zero
          (by rw [← lie_skew, hself, h0, neg_zero]),
        hFE j k hij.symm, map_zero]
    have t : IsSl2Triple (C k) (E k) (F k) :=
      { h_ne_zero := h0
        lie_e_f := hself k
        lie_h_e_nsmul := by rw [hCE, hA.diag, two_zsmul, two_smul]
        lie_h_f_nsmul := by rw [hCF, hA.diag, two_zsmul, two_smul] }
    have hstring := t.lie_f_pow_succ_toEnd_e (y := E j) (μ := (A k j : K))
      (by rw [hCE, Int.cast_smul_eq_zsmul]) (hFE j k hij.symm) (-A k j).toNat
    rw [← ad_eq_toEnd] at hstring
    rw [hstring]
    have hn : (((-A k j).toNat : ℕ) : K) = -(A k j : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.neg_nonneg.mpr (hA.offDiag_nonpos k j hij)),
        Int.cast_neg]
    rw [hn, sub_neg_eq_add, neg_add_cancel, mul_zero, zero_smul]
  rw [TauCeti.LieAlgebra.lie_ad_pow_of_lie_eq_zero (hFE i k hki.symm)]
  obtain rfl | hkj := eq_or_ne k j
  · rw [← lie_skew, hself, pow_succ, mul_apply_eq_comp, map_neg, ad_apply,
      lie_skew, hCE]
    rcases h_neg : (-A i k).toNat with _ | n
    · have hik : A i k = 0 := le_antisymm (hA.offDiag_nonpos i k hij) (by omega)
      simp [(hA.zero_comm i k).mp hik]
    · rw [map_zsmul, pow_succ, mul_apply_eq_comp, ad_apply, lie_self, map_zero, zsmul_zero]
  · rw [hFE j k hkj.symm, map_zero]

end KacMoody

end TauCeti
