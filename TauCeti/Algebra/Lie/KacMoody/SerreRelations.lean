/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Basic

import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Algebra.Lie.Sl2.WeightString

/-!
# Vanishing of brackets with Serre elements under Chevalley relations

For a generalized Cartan matrix `A`, every lowering generator `F k` commutes with each raising Serre
element `(ad (E i)) ^ (-Aᵢⱼ) ⁅E i, E j⁆` in any Lie algebra carrying a realization of the
Chevalley relations (`TauCeti.KacMoody.lie_ad_pow_lie_eq_zero`), without assuming either Serre
relation (Kac, §3.3).

This shared lemma is used both to prove that the raising Serre elements vanish in Kac's word
representation (`TauCeti.Algebra.Lie.KacMoody.CartanInjective`) and to prove `ad fₖ`-invariance
of the Serre ideal in the auxiliary Kac–Moody presentation
(`TauCeti.Algebra.Lie.KacMoody.Auxiliary`).

## Main results

* `TauCeti.KacMoody.lie_ad_pow_lie_eq_zero`: for a generalized Cartan matrix, every `F k` commutes
  with `(ad (E i)) ^ (-Aᵢⱼ) ⁅E i, E j⁆` under the Chevalley relations alone.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.3.
-/

public section

open LieAlgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  {R : CartanRealization (A.map (Int.cast : ℤ → K)) H}

section SerreElement

variable {L : Type*} [LieRing L] [LieAlgebra K L] {φ : H →ₗ[K] L} {E F : I → L}

/-- For a generalized Cartan matrix, every `F k` commutes with each raising Serre element
`(ad (E i)) ^ (-Aᵢⱼ) ⁅E i, E j⁆`, as soon as `φ`, `E` and `F` satisfy the Chevalley relations
(Kac, §3.3). Neither Serre relation is used. -/
theorem lie_ad_pow_lie_eq_zero (hdiag : ∀ i, A i i = 2)
    (hneg : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 → A j i = 0)
    (hφE : ∀ x j, ⁅φ x, E j⁆ = R.root j x • E j) (hφF : ∀ x j, ⁅φ x, F j⁆ = -(R.root j x • F j))
    (hself : ∀ i, ⁅E i, F i⁆ = φ (R.coroot i)) (hne : ∀ i j, i ≠ j → ⁅E i, F j⁆ = 0)
    (i j k : I) : ⁅F k, (ad K L (E i) ^ (-A i j).toNat) ⁅E i, E j⁆⁆ = 0 := by
  obtain rfl | hij := eq_or_ne i j
  · simp
  have hFE (a b : I) (hab : a ≠ b) : ⁅F b, E a⁆ = 0 := by rw [← lie_skew, hne a b hab, neg_zero]
  have hroot (a b : I) : R.root b (R.coroot a) = (A a b : K) := by simp
  rw [← ad_pow_succ_apply]
  obtain rfl | hki := eq_or_ne k i
  · by_cases h0 : φ (R.coroot k) = 0
    · rw [TauCeti.LieAlgebra.lie_ad_pow_of_lie_eq_zero (by rw [← lie_skew, hself, h0, neg_zero]),
        hFE j k hij.symm, map_zero]
    have t : IsSl2Triple (φ (R.coroot k)) (E k) (F k) :=
      { h_ne_zero := h0
        lie_e_f := hself k
        lie_h_e_nsmul := by rw [hφE, hroot, hdiag]; simp [two_smul]
        lie_h_f_nsmul := by rw [hφF, hroot, hdiag]; simp [two_smul] }
    have hstring := t.lie_f_pow_succ_toEnd_e (y := E j) (μ := (A k j : K))
      (by rw [hφE, hroot]) (hFE j k hij.symm) (-A k j).toNat
    rw [← ad_eq_toEnd] at hstring
    rw [hstring]
    have hn : (((-A k j).toNat : ℕ) : K) = -(A k j : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith [hneg k j hij]), Int.cast_neg]
    rw [hn, sub_neg_eq_add, neg_add_cancel, mul_zero, zero_smul]
  rw [TauCeti.LieAlgebra.lie_ad_pow_of_lie_eq_zero (hFE i k hki.symm)]
  obtain rfl | hkj := eq_or_ne k j
  · rw [← lie_skew, hself, pow_succ, mul_apply_eq_comp, map_neg, ad_apply, lie_skew, hφE,
      hroot]
    rcases h : (-A i k).toNat with _ | n
    · have hik : A i k = 0 := le_antisymm (hneg i k hij) (by omega)
      simp [hzero i k hik]
    · rw [map_smul, pow_succ, mul_apply_eq_comp, ad_apply, lie_self, map_zero, smul_zero]
  · rw [hFE j k hkj.symm, map_zero]

end SerreElement

end KacMoody

end TauCeti
