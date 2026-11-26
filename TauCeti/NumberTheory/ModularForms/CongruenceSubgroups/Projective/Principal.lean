/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.SignedQuotient
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective.Basic
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.SignedQuotient

/-!
# The projective principal congruence quotient `PSL₂(ℤ) ⧸ GammaProjective N`

The principal congruence subgroup `Γ(N)` does not contain `-I` for `N ≥ 3`, so its projective
image `GammaProjective N` has half its index: the quotient `PSL₂(ℤ) ⧸ GammaProjective N` is
canonically isomorphic to the signed finite quotient
`TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) = SL₂(ℤ/Nℤ) ⧸ {±I}`, of order `|SL₂(ℤ/Nℤ)| / 2`
for `N ≥ 3` (and `1`, `6` at `N = 1, 2`). At `N = 3` the two indices are `24` and `12`.

This module also records the order obstructions in `PSL₂(ℤ)`: if `Γ(N) ≤ Γ.liftSL` (equivalently
`GammaProjective N ≤ Γ`), then `[PSL₂(ℤ) : Γ]` and `|PSL₂(ℤ) ⧸ Γ.normalCore|` both divide
`|SL₂(ℤ/Nℤ) ⧸ {±I}| = (GammaProjective N).index`, via the canonical surjection
`TauCeti.CongruenceSubgroup.signedQuotientToQuotientNormalCore`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.2 (the index of `Γ(N)` and of `±Γ(N)`).
-/

public section

open scoped MatrixGroups

namespace TauCeti.CongruenceSubgroup

/-! ### Finite quotient `PSL₂(ℤ) ⧸ GammaProjective N ≃* SL₂(ℤ/Nℤ) ⧸ {±I}` and indices -/

/-- Reduction modulo `N` descended from `PSL₂(ℤ)` to the signed quotient
`TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) = SL₂(ℤ/Nℤ) ⧸ {±I}`. -/
noncomputable def psl2zToSignedQuotient (N : ℕ) :
    PSL(2, ℤ) →* TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ))
    ((QuotientGroup.mk' (Subgroup.zpowers (-1 : SL(2, ZMod N)))).comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))))
    fun _ hx ↦ by
      rw [CongruenceSubgroup.ker_mk'_comp_map_intCast_zmod]
      exact Subgroup.mem_sup_right (Matrix.SpecialLinearGroup.center_eq_zpowers_neg_one.le hx)

/-- `psl2zToSignedQuotient N` evaluates on coset representatives by entrywise reduction modulo `N`.
-/
@[simp]
theorem psl2zToSignedQuotient_mk (N : ℕ) (g : SL(2, ℤ)) :
    psl2zToSignedQuotient N (QuotientGroup.mk g) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g) := by
  rw [psl2zToSignedQuotient]; rfl

/-- By strong approximation for `SL₂(ℤ)`, `psl2zToSignedQuotient N` is surjective at every level. -/
theorem psl2zToSignedQuotient_surjective (N : ℕ) :
    Function.Surjective (psl2zToSignedQuotient N) := by
  have h : Function.Surjective
      ((psl2zToSignedQuotient N) ∘ (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) := by
    rw [← MonoidHom.coe_comp, psl2zToSignedQuotient, QuotientGroup.lift_comp_mk']
    exact CongruenceSubgroup.mk'_comp_map_intCast_zmod_surjective
  exact h.of_comp

/-- The kernel of `PSL₂(ℤ) →* SL₂(ℤ/Nℤ) ⧸ {±I}` is precisely `GammaProjective N`. -/
theorem ker_psl2zToSignedQuotient (N : ℕ) :
    (psl2zToSignedQuotient N).ker = GammaProjective N := by
  apply Subgroup.liftSL_injective
  rw [Subgroup.liftSL_def, MonoidHom.comap_ker, psl2zToSignedQuotient,
    QuotientGroup.lift_comp_mk', CongruenceSubgroup.ker_mk'_comp_map_intCast_zmod,
    liftSL_GammaProjective, Subgroup.withCenter_def,
    ← Matrix.SpecialLinearGroup.center_eq_zpowers_neg_one, sup_comm]

/-- **Canonical isomorphism `PSL₂(ℤ) ⧸ GammaProjective N ≃* SL₂(ℤ/Nℤ) ⧸ {±I}`.** -/
noncomputable def quotientGammaProjectiveEquiv (N : ℕ) :
    (PSL(2, ℤ) ⧸ GammaProjective N) ≃* TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) :=
  QuotientGroup.liftEquiv (GammaProjective N)
    (psl2zToSignedQuotient_surjective N) (ker_psl2zToSignedQuotient N).symm

/-- Evaluation of `quotientGammaProjectiveEquiv N` on coset representatives. -/
@[simp]
theorem quotientGammaProjectiveEquiv_mk (N : ℕ) (x : PSL(2, ℤ)) :
    quotientGammaProjectiveEquiv N (QuotientGroup.mk x) = psl2zToSignedQuotient N x :=
  QuotientGroup.liftEquiv_mk _ _ _ x

/-- At every level `N : ℕ`, `[PSL₂(ℤ) : GammaProjective N] = |SL₂(ℤ/Nℤ) ⧸ {±I}|`. -/
theorem GammaProjective_index_eq_card (N : ℕ) :
    (GammaProjective N).index = Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)) := by
  rw [Subgroup.index_eq_card, Nat.card_congr (quotientGammaProjectiveEquiv N).toEquiv]

/-- **The projective index of `Γ(N)`** for `N ≥ 3`: since `-I ∉ Γ(N)`, `GammaProjective N` has
index `|SL₂(ℤ/Nℤ)| / 2`. -/
theorem two_mul_GammaProjective_index {N : ℕ} (hN : 3 ≤ N) :
    2 * (GammaProjective N).index = Nat.card SL(2, ZMod N) := by
  rw [GammaProjective_index_eq_card,
    TauCeti.Matrix.SignedQuotient.two_mul_card_fin_two_zmod hN]

/-- `GammaProjective 3` has index `12`, half the index of `Γ(3)`, since `-I ∉ Γ(3)`. -/
theorem GammaProjective_index_three : (GammaProjective 3).index = 12 := by
  have h := two_mul_GammaProjective_index le_rfl
  rw [← CongruenceSubgroup.index_Gamma, CongruenceSubgroup.index_Gamma_three] at h
  omega

/-- **The order of `SL₂(ℤ/Nℤ)/{±1}`** for `N ≥ 3`: `GammaProjective N` has index
`(N³/2) ∏_{p ∣ N} (1 - 1/p²)`, here with the denominators cleared. -/
theorem two_mul_GammaProjective_index_mul_prod_primeFactors_sq {N : ℕ} (hN : 3 ≤ N) :
    2 * (GammaProjective N).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [two_mul_GammaProjective_index hN]
  exact natCard_SL_fin_two_zmod_mul_prod_primeFactors N

/-- `GammaProjective 1` is all of `PSL₂(ℤ)`, of index `1`. -/
theorem GammaProjective_index_one : (GammaProjective 1).index = 1 := by
  rw [GammaProjective_def, CongruenceSubgroup.Gamma_one_top,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), Subgroup.index_top]

/-- `GammaProjective 2` has index `6 = |SL₂(𝔽₂)|`: since `-I ∈ Γ(2)`, projecting does not halve
the index. -/
theorem GammaProjective_index_two : (GammaProjective 2).index = 6 := by
  rw [GammaProjective_index_eq_card, TauCeti.Matrix.SignedQuotient.card_fin_two_zmod_two]

/-- `GammaProjective 6` has index `72 = |SL₂(𝔽₂)| · |SL₂(𝔽₃)| / 2`. -/
theorem GammaProjective_index_six : (GammaProjective 6).index = 72 := by
  have h := two_mul_GammaProjective_index (N := 6) (by norm_num)
  have hc : Nat.card SL(2, ZMod 6) = 144 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Matrix.natCard_SL_zmod_mul (by norm_num),
      natCard_SL_fin_two_zmod, natCard_SL_fin_two_zmod]
    norm_num
  omega

/-- `GammaProjective 8` has index `192 = |SL₂(ℤ/8ℤ)| / 2`. -/
theorem GammaProjective_index_eight : (GammaProjective 8).index = 192 := by
  have h := two_mul_GammaProjective_index (N := 8) (by norm_num)
  have hc : Nat.card SL(2, ZMod 8) = 384 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Matrix.natCard_SL_zmod_pow three_ne_zero,
      natCard_SL_fin_two_zmod, Fintype.card_fin]
    norm_num
  omega

/-- `GammaProjective 10` has index `360 = |SL₂(𝔽₂)| · |SL₂(𝔽₅)| / 2`. -/
theorem GammaProjective_index_ten : (GammaProjective 10).index = 360 := by
  have h := two_mul_GammaProjective_index (N := 10) (by norm_num)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : Nat.card SL(2, ZMod 10) = 720 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, Matrix.natCard_SL_zmod_mul (by norm_num),
      natCard_SL_fin_two_zmod, natCard_SL_fin_two_zmod]
    norm_num
  omega

/-- `GammaProjective 12` has index `576 = |SL₂(ℤ/4ℤ)| · |SL₂(𝔽₃)| / 2`. -/
theorem GammaProjective_index_twelve : (GammaProjective 12).index = 576 := by
  have h := two_mul_GammaProjective_index (N := 12) (by norm_num)
  have hc : Nat.card SL(2, ZMod 12) = 1152 := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Matrix.natCard_SL_zmod_mul (by norm_num),
      Matrix.natCard_SL_zmod_pow two_ne_zero, natCard_SL_fin_two_zmod, natCard_SL_fin_two_zmod,
      Fintype.card_fin]
    norm_num
  omega

/-! ### Order obstructions in `PSL₂(ℤ)` -/

/-- **Order obstruction on the index in `PSL₂(ℤ)`:** if `Γ(N) ≤ Γ.liftSL` (equivalently
`GammaProjective N ≤ Γ`), then
`[PSL₂(ℤ) : Γ] ∣ (GammaProjective N).index = |SL₂(ℤ/Nℤ) ⧸ {±I}|`. -/
theorem index_dvd_of_Gamma_le_liftSL {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    Γ.index ∣ Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)) := by
  rw [← GammaProjective_index_eq_card]
  exact Subgroup.index_dvd_of_le (GammaProjective_le_iff.mpr h)

/-- When `Γ(N) ≤ Γ.liftSL`, the canonical surjective homomorphism
`SL₂(ℤ/Nℤ) ⧸ {±I} →* PSL₂(ℤ) ⧸ Γ.normalCore` obtained from `GammaProjective N ≤ Γ.normalCore` and
`quotientGammaProjectiveEquiv N`. -/
noncomputable def signedQuotientToQuotientNormalCore {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N) →* PSL(2, ℤ) ⧸ Γ.normalCore :=
  (QuotientGroup.map (GammaProjective N) Γ.normalCore (MonoidHom.id _)
    (Subgroup.normal_le_normalCore.mpr (GammaProjective_le_iff.mpr h))).comp
    (quotientGammaProjectiveEquiv N).symm.toMonoidHom

/-- Evaluation of `signedQuotientToQuotientNormalCore` on reductions of elements of `PSL₂(ℤ)`. -/
@[simp]
theorem signedQuotientToQuotientNormalCore_psl2zToSignedQuotient {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) (x : PSL(2, ℤ)) :
    signedQuotientToQuotientNormalCore h (psl2zToSignedQuotient N x) = QuotientGroup.mk x := by
  rw [signedQuotientToQuotientNormalCore, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← quotientGammaProjectiveEquiv_mk, MulEquiv.symm_apply_apply]
  rfl

/-- The canonical homomorphism `SL₂(ℤ/Nℤ) ⧸ {±I} →* PSL₂(ℤ) ⧸ Γ.normalCore` is surjective. -/
theorem signedQuotientToQuotientNormalCore_surjective {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    Function.Surjective (signedQuotientToQuotientNormalCore h) :=
  (QuotientGroup.map_surjective_of_surjective _ _ (MonoidHom.id _)
    (QuotientGroup.mk'_surjective _)
    (Subgroup.normal_le_normalCore.mpr (GammaProjective_le_iff.mpr h))).comp
    (quotientGammaProjectiveEquiv N).symm.surjective

/-- **Order obstruction on the monodromy / normal-core quotient in `PSL₂(ℤ)`:** if
`Γ(N) ≤ Γ.liftSL`, then `|PSL₂(ℤ) ⧸ Γ.normalCore| ∣ |SL₂(ℤ/Nℤ) ⧸ {±I}|`
(`= (GammaProjective N).index`). -/
theorem card_quotient_normalCore_dvd_of_Gamma_le_liftSL {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    Nat.card (PSL(2, ℤ) ⧸ Γ.normalCore) ∣
      Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)) :=
  Subgroup.card_dvd_of_surjective (signedQuotientToQuotientNormalCore_surjective h)

end TauCeti.CongruenceSubgroup
