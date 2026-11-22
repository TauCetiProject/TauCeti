/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.SignedQuotient
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective.Basic
import TauCeti.Algebra.Group.Subgroup.ZPowers
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
  (TauCeti.Matrix.SignedQuotient.map (Int.castRingHom (ZMod N))).comp
    (TauCeti.Matrix.SignedQuotient.equivPSL ℤ).symm.toMonoidHom

/-- `psl2zToSignedQuotient N` evaluates on coset representatives by entrywise reduction modulo `N`.
-/
@[simp]
theorem psl2zToSignedQuotient_mk (N : ℕ) (g : SL(2, ℤ)) :
    psl2zToSignedQuotient N (QuotientGroup.mk g) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g) := by
  rw [psl2zToSignedQuotient, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← TauCeti.Matrix.SignedQuotient.equivPSL_mk ℤ g, MulEquiv.symm_apply_apply,
    TauCeti.Matrix.SignedQuotient.map_mk]

/-- By strong approximation for `SL₂(ℤ)`, `psl2zToSignedQuotient N` is surjective at every level. -/
theorem psl2zToSignedQuotient_surjective (N : ℕ) :
    Function.Surjective (psl2zToSignedQuotient N) :=
  (TauCeti.Matrix.SignedQuotient.map_surjective
    Matrix.SpecialLinearGroup.map_intCast_zmod_surjective).comp
    (TauCeti.Matrix.SignedQuotient.equivPSL ℤ).symm.surjective

/-- The kernel of `PSL₂(ℤ) →* SL₂(ℤ/Nℤ) ⧸ {±I}` is precisely `GammaProjective N`. -/
theorem ker_psl2zToSignedQuotient (N : ℕ) :
    (psl2zToSignedQuotient N).ker = GammaProjective N := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, psl2zToSignedQuotient_mk, QuotientGroup.eq_one_iff,
    TauCeti.Matrix.SpecialLinearGroup.negOneSubgroup_def, Subgroup.mem_zpowers_neg_one_iff,
    mem_GammaProjective_mk, CongruenceSubgroup.Gamma_mem', CongruenceSubgroup.Gamma_mem']
  have hneg : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (-g) =
      -Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g :=
    Matrix.SpecialLinearGroup.coe_int_neg (R := ZMod N) g
  rw [hneg, neg_eq_iff_eq_neg]

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

/-- At level `1`, `GammaProjective 1 = ⊤`, so `[PSL₂(ℤ) : GammaProjective 1] = 1`. -/
@[simp]
theorem GammaProjective_index_one : (GammaProjective 1).index = 1 := by
  rw [GammaProjective_index_eq_card, TauCeti.Matrix.SignedQuotient.card_fin_two_zmod_one]

/-- At level `2`, `[PSL₂(ℤ) : GammaProjective 2] = |SL₂(𝔽₂)| = 6` since `-I = I` modulo `2`. -/
@[simp]
theorem GammaProjective_index_two : (GammaProjective 2).index = 6 := by
  rw [GammaProjective_index_eq_card, TauCeti.Matrix.SignedQuotient.card_fin_two_zmod_two]

/-- **The projective index of `Γ(N)`** for `N ≥ 3`: since `-I ∉ Γ(N)`, the image of `Γ(N)` in
`PSL₂(ℤ)` has index `|SL₂(ℤ/Nℤ)| / 2`. -/
theorem two_mul_index_map_Gamma {N : ℕ} (hN : 3 ≤ N) :
    2 * ((CongruenceSubgroup.Gamma N).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = Nat.card SL(2, ZMod N) := by
  rw [← GammaProjective_def, GammaProjective_index_eq_card,
    TauCeti.Matrix.SignedQuotient.two_mul_card_fin_two_zmod hN]

/-- **Cleared Euler product for `[PSL₂(ℤ) : GammaProjective N]`** (`N ≥ 3`):
`2 · [PSL₂(ℤ) : GammaProjective N] · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`. -/
theorem two_mul_GammaProjective_index_mul_prod_primeFactors_sq {N : ℕ} (hN : 3 ≤ N) :
    2 * (GammaProjective N).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [GammaProjective_index_eq_card,
    TauCeti.Matrix.SignedQuotient.two_mul_card_fin_two_zmod_mul_prod_primeFactors_sq hN]

/-- The image of `Γ(3)` in `PSL₂(ℤ)` has index `12`, half the index of `Γ(3)`, since `-I ∉ Γ(3)`. -/
theorem index_map_Gamma_three :
    ((CongruenceSubgroup.Gamma 3).map
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index = 12 := by
  have h := two_mul_index_map_Gamma le_rfl
  rw [← CongruenceSubgroup.index_Gamma, CongruenceSubgroup.index_Gamma_three] at h
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
