/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Subgroup.IsSubnormal
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Principal
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective
import Mathlib.Algebra.Field.ZMod
import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Order and composition-factor obstructions for principal modular quotients

This file establishes the finite group-theoretic obstructions — both by group order and by
Jordan–Hölder composition factors — that principal congruence quotients place on congruence
subgroups of `SL₂(ℤ)` and `PSL₂(ℤ)`:

* **Order obstructions**: if `Γ(N) ≤ Δ` (respectively `Γ(N) ≤ Γ.liftSL`), then
  `|SL₂(ℤ) ⧸ Δ.normalCore| ∣ |SL₂(ℤ/Nℤ)|` (respectively
  `|PSL₂(ℤ) ⧸ Γ.normalCore| ∣ |SL₂(ℤ/Nℤ) ⧸ {±I}| = (GammaProjective N).index`).
* **Composition-factor obstructions**: for `N ≠ 0`, every nonabelian simple subnormal section of
  `SL₂(ℤ) ⧸ Δ.normalCore` or `PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to `PSL₂(𝔽_ℓ)` for a prime
  `ℓ ≥ 5` dividing `N` (with level-free forms for arbitrary congruence subgroups, and prime-level
  divisibility `ℓ ∣ N` when `PSL₂(𝔽_ℓ)` occurs).
* **Alternating and symmetric noncongruence criteria**: if `PSL₂(ℤ) ⧸ Γ.normalCore` admits
  `alternatingGroup α` (`6 ≤ Nat.card α`) as a subnormal section — in particular if it is
  isomorphic to `A_n` or `S_n` for `n ≥ 6` — then `Γ.liftSL` is noncongruence.
* **Explicit checks** at levels `N ∈ {6, 10, 11, 12}`, including the level-`11` separation showing
  `|PSL₂(𝔽₅)| = 60 ∣ 660 = (GammaProjective 11).index` while `PSL₂(𝔽₅)` cannot appear at level `11`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005, §1.2.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton, 1971,
  §1.6.
* Klaus Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964), 529–535.
* Ling Long, *Finite index subgroups of the modular group and their modular forms*, in *Modular
  Forms and String Duality*, Fields Inst. Commun. 54, Amer. Math. Soc., 2008, 83–102.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CongruenceSubgroup

attribute [local instance] Gamma_normal

/-! ### Order and composition-factor obstructions in `SL₂(ℤ)` -/

/-- If `Γ(N) ≤ Δ`, then `[SL₂(ℤ) : Δ] ∣ |SL₂(ℤ/Nℤ)|`. -/
theorem index_dvd_card_sl_zmod_of_Gamma_le {N : ℕ} {Δ : Subgroup SL(2, ℤ)} (h : Gamma N ≤ Δ) :
    Δ.index ∣ Nat.card SL(2, ZMod N) := by
  rw [← index_Gamma]; exact Subgroup.index_dvd_of_le h

/-- When `Γ(N) ≤ Δ`, the canonical surjective homomorphism `SL₂(ℤ/Nℤ) →* SL₂(ℤ) ⧸ Δ.normalCore`
obtained by composing `(quotientGammaEquiv N).symm` with the quotient map from `Γ(N)` to
`Δ.normalCore`. -/
noncomputable def slZModToQuotientNormalCore {N : ℕ} {Δ : Subgroup SL(2, ℤ)} (h : Gamma N ≤ Δ) :
    SL(2, ZMod N) →* SL(2, ℤ) ⧸ Δ.normalCore :=
  (QuotientGroup.map (Gamma N) Δ.normalCore (MonoidHom.id _)
    (Subgroup.normal_le_normalCore.mpr h)).comp (quotientGammaEquiv N).symm.toMonoidHom

@[simp]
theorem slZModToQuotientNormalCore_map_intCast {N : ℕ} {Δ : Subgroup SL(2, ℤ)} (h : Gamma N ≤ Δ)
    (γ : SL(2, ℤ)) :
    slZModToQuotientNormalCore h (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) =
      QuotientGroup.mk γ := by
  rw [slZModToQuotientNormalCore, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← quotientGammaEquiv_mk, MulEquiv.symm_apply_apply]
  rfl

/-- The canonical reduction homomorphism `SL₂(ℤ/Nℤ) →* SL₂(ℤ) ⧸ Δ.normalCore` is surjective. -/
theorem slZModToQuotientNormalCore_surjective {N : ℕ} {Δ : Subgroup SL(2, ℤ)} (h : Gamma N ≤ Δ) :
    Function.Surjective (slZModToQuotientNormalCore h) := fun x ↦ by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ,
    slZModToQuotientNormalCore_map_intCast h γ⟩

/-- **Order obstruction in `SL₂(ℤ)`:** if `Γ(N) ≤ Δ`, then
`|SL₂(ℤ) ⧸ Δ.normalCore| ∣ |SL₂(ℤ/Nℤ)|`. -/
theorem card_quotient_normalCore_dvd_of_Gamma_le {N : ℕ} {Δ : Subgroup SL(2, ℤ)}
    (h : Gamma N ≤ Δ) :
    Nat.card (SL(2, ℤ) ⧸ Δ.normalCore) ∣ Nat.card SL(2, ZMod N) :=
  Subgroup.card_dvd_of_surjective (slZModToQuotientNormalCore_surjective h)

/-- **Level-`N` composition-factor obstruction in `SL₂(ℤ)`:** if `Γ(N) ≤ Δ` with `N ≠ 0`, then
every nonabelian simple subnormal section `S` of `SL₂(ℤ) ⧸ Δ.normalCore` is isomorphic to
`PSL(2, ZMod ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_and_mulEquiv_of_Gamma_le {N : ℕ} (hN : N ≠ 0) {Δ : Subgroup SL(2, ℤ)}
    (h : Gamma N ≤ Δ) {S : Type*} [Group S] [IsSimpleGroup S] (hcomm : ¬ IsMulCommutative S)
    (hsec : TauCeti.HasSubnormalSection (SL(2, ℤ) ⧸ Δ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hcomm
    (hsec.of_surjective (slZModToQuotientNormalCore_surjective h))

/-- **Composition-factor obstruction for congruence subgroups of `SL₂(ℤ)`:** if `Δ ≤ SL₂(ℤ)` is a
congruence subgroup, then every nonabelian simple subnormal section `S` of `SL₂(ℤ) ⧸ Δ.normalCore`
is isomorphic to `PSL(2, ZMod ℓ)` for some prime `ℓ ≥ 5`. -/
theorem compositionFactor_quotient_normalCore_of_isCongruenceSubgroup {Δ : Subgroup SL(2, ℤ)}
    (hΔ : IsCongruenceSubgroup Δ) {S : Type*} [Group S] [IsSimpleGroup S]
    (hcomm : ¬ IsMulCommutative S)
    (hsec : TauCeti.HasSubnormalSection (SL(2, ℤ) ⧸ Δ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  let ⟨_, hN, hle⟩ := hΔ
  let ⟨ℓ, hℓ, h5, _, heq⟩ := exists_prime_dvd_and_mulEquiv_of_Gamma_le hN hle hcomm hsec
  ⟨ℓ, hℓ, h5, heq⟩

/-- **Noncongruence criterion via alternating subnormal sections in `SL₂(ℤ)`:** if
`SL₂(ℤ) ⧸ Δ.normalCore` admits `alternatingGroup α` (`6 ≤ Nat.card α`) as a subnormal section,
then `Δ` is not a congruence subgroup. -/
theorem not_isCongruenceSubgroup_of_hasSubnormalSection_alternatingGroup {Δ : Subgroup SL(2, ℤ)}
    {α : Type*} [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α)
    (hsec : TauCeti.HasSubnormalSection (SL(2, ℤ) ⧸ Δ.normalCore) (alternatingGroup α)) :
    ¬ IsCongruenceSubgroup Δ := fun ⟨_, hN, hle⟩ ↦
  Matrix.SpecialLinearGroup.not_hasSubnormalSection_alternatingGroup hN hα
    (hsec.of_surjective (slZModToQuotientNormalCore_surjective hle))

end CongruenceSubgroup

namespace TauCeti.CongruenceSubgroup

/-! ### Order and composition-factor obstructions in `PSL₂(ℤ)` -/

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
    Function.Surjective (signedQuotientToQuotientNormalCore h) := fun y ↦ by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨psl2zToSignedQuotient N x, signedQuotientToQuotientNormalCore_psl2zToSignedQuotient h x⟩

/-- **Order obstruction on the monodromy / normal-core quotient in `PSL₂(ℤ)`:** if
`Γ(N) ≤ Γ.liftSL`, then `|PSL₂(ℤ) ⧸ Γ.normalCore| ∣ |SL₂(ℤ/Nℤ) ⧸ {±I}|`
(`= (GammaProjective N).index`). -/
theorem card_quotient_normalCore_dvd_of_Gamma_le_liftSL {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    Nat.card (PSL(2, ℤ) ⧸ Γ.normalCore) ∣
      Nat.card (TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)) :=
  Subgroup.card_dvd_of_surjective (signedQuotientToQuotientNormalCore_surjective h)

/-- Variant of `card_quotient_normalCore_dvd_of_Gamma_le_liftSL` written directly in terms of
`(GammaProjective N).index`. -/
theorem card_quotient_normalCore_dvd_GammaProjective_index {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    Nat.card (PSL(2, ℤ) ⧸ Γ.normalCore) ∣ (GammaProjective N).index := by
  rw [GammaProjective_index_eq_card]
  exact card_quotient_normalCore_dvd_of_Gamma_le_liftSL h

/-- **Level-`N` composition-factor obstruction in `PSL₂(ℤ)`:** if `Γ(N) ≤ Γ.liftSL` with `N ≠ 0`,
then every nonabelian simple subnormal section `S` of `PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to
`PSL(2, ZMod ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL {N : ℕ} (hN : N ≠ 0)
    {Γ : Subgroup PSL(2, ℤ)} (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL)
    {S : Type*} [Group S] [IsSimpleGroup S] (hcomm : ¬ IsMulCommutative S)
    (hsec : TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hcomm
    ((hsec.of_surjective (signedQuotientToQuotientNormalCore_surjective h)).of_surjective
      (QuotientGroup.mk'_surjective
        (TauCeti.Matrix.SpecialLinearGroup.negOneSubgroup (Fin 2) (ZMod N))))

/-- Direct subquotient form of `exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL`: for any
subnormal `K ≤ H ≤ PSL₂(ℤ) ⧸ Γ.normalCore` with `K.subgroupOf H` normal and `H ⧸ K.subgroupOf H`
nonabelian simple, if `Γ(N) ≤ Γ.liftSL` (`N ≠ 0`), then `H ⧸ K.subgroupOf H ≃* PSL(2, ZMod ℓ)` for
a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_and_subquotient_mulEquiv_of_Gamma_le_liftSL {N : ℕ} (hN : N ≠ 0)
    {Γ : Subgroup PSL(2, ℤ)} (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL)
    {H K : Subgroup (PSL(2, ℤ) ⧸ Γ.normalCore)} (hH : H.IsSubnormal) (hKH : K ≤ H)
    [(K.subgroupOf H).Normal] [IsSimpleGroup (H ⧸ K.subgroupOf H)]
    (hcomm : ¬ IsMulCommutative (H ⧸ K.subgroupOf H)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty ((H ⧸ K.subgroupOf H) ≃* PSL(2, ZMod ℓ)) :=
  exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL hN h hcomm
    (TauCeti.HasSubnormalSection.mk_quotient hH hKH)

/-- **Composition-factor obstruction for projective congruence subgroups:** if `Γ.liftSL` is a
congruence subgroup of `SL₂(ℤ)`, then every nonabelian simple subnormal section `S` of
`PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to `PSL(2, ZMod ℓ)` for some prime `ℓ ≥ 5`. -/
theorem compositionFactor_quotient_normalCore_of_isCongruenceSubgroup_liftSL
    {Γ : Subgroup PSL(2, ℤ)} (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL)
    {S : Type*} [Group S] [IsSimpleGroup S] (hcomm : ¬ IsMulCommutative S)
    (hsec : TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  let ⟨_, hN, hle⟩ := hΓ
  let ⟨ℓ, hℓ, h5, _, heq⟩ := exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL hN hle hcomm hsec
  ⟨ℓ, hℓ, h5, heq⟩

/-- **Prime-level divisibility criterion:** if `PSL₂(ℤ) ⧸ Γ.normalCore` admits `PSL(2, ZMod ℓ)`
(`ℓ` prime, `5 ≤ ℓ`) as a subnormal section and `Γ(N) ≤ Γ.liftSL` with `N ≠ 0`, then `ℓ ∣ N`. -/
theorem dvd_of_hasSubnormalSection_psl_zmod_of_Gamma_le_liftSL {N ℓ : ℕ} (hN : N ≠ 0)
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL)
    (hsec : TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) PSL(2, ZMod ℓ)) :
    ℓ ∣ N := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : IsSimpleGroup PSL(2, ZMod ℓ) :=
    Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_four_le_natCard (F := ZMod ℓ)
      (by rw [Nat.card_zmod]; omega)
  have hnotcomm : ¬ IsMulCommutative PSL(2, ZMod ℓ) := fun _ ↦ by
    have := (TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_fin_two_iff (F := ZMod ℓ)).mp
      inferInstance |>.2
    rw [Nat.card_zmod] at this; omega
  obtain ⟨q, hq, -, hqN, ⟨e⟩⟩ :=
    exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL hN h hnotcomm hsec
  rwa [Matrix.ProjectiveSpecialLinearGroup.eq_of_fin_two_zmod_mulEquiv hℓ hq e]

/-! ### Alternating and symmetric monodromy noncongruence criteria -/

/-- **Alternating-section noncongruence theorem:** if `PSL₂(ℤ) ⧸ Γ.normalCore` admits
`alternatingGroup α` (`6 ≤ Nat.card α`) as a subnormal section, then `Γ.liftSL` is not a
congruence subgroup of `SL₂(ℤ)`. -/
theorem not_isCongruenceSubgroup_liftSL_of_hasSubnormalSection_alternatingGroup
    {Γ : Subgroup PSL(2, ℤ)} {α : Type*} [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α)
    (hsec : TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) (alternatingGroup α)) :
    ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL := fun ⟨N, hN, hle⟩ ↦
  Matrix.SpecialLinearGroup.not_hasSubnormalSection_alternatingGroup hN hα
    ((hsec.of_surjective (signedQuotientToQuotientNormalCore_surjective hle)).of_surjective
      (QuotientGroup.mk'_surjective
        (TauCeti.Matrix.SpecialLinearGroup.negOneSubgroup (Fin 2) (ZMod N))))

/-- **Alternating monodromy noncongruence theorem (`A_n`, `n ≥ 6`):** if
`(PSL₂(ℤ) ⧸ Γ.normalCore) ≃* alternatingGroup α` with `6 ≤ Nat.card α`, then `Γ.liftSL` is not a
congruence subgroup. -/
theorem not_isCongruenceSubgroup_liftSL_of_quotient_normalCore_mulEquiv_alternatingGroup
    {Γ : Subgroup PSL(2, ℤ)} {α : Type*} [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α)
    (e : (PSL(2, ℤ) ⧸ Γ.normalCore) ≃* alternatingGroup α) :
    ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL :=
  not_isCongruenceSubgroup_liftSL_of_hasSubnormalSection_alternatingGroup hα
    ((TauCeti.HasSubnormalSection.refl (alternatingGroup α)).congr_left e.symm)

/-- **Symmetric monodromy noncongruence theorem (`S_n`, `n ≥ 6`):** if
`(PSL₂(ℤ) ⧸ Γ.normalCore) ≃* Equiv.Perm α` with `6 ≤ Nat.card α`, then `Γ.liftSL` is not a
congruence subgroup, because `alternatingGroup α ⊴ Equiv.Perm α` is a nonabelian simple subnormal
section not isomorphic to any `PSL₂(𝔽_ℓ)`. -/
theorem not_isCongruenceSubgroup_liftSL_of_quotient_normalCore_mulEquiv_perm
    {Γ : Subgroup PSL(2, ℤ)} {α : Type*} [Finite α] (hα : 6 ≤ Nat.card α)
    (e : (PSL(2, ℤ) ⧸ Γ.normalCore) ≃* Equiv.Perm α) :
    ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL := by
  classical
  cases nonempty_fintype α
  exact not_isCongruenceSubgroup_liftSL_of_hasSubnormalSection_alternatingGroup hα <|
    ((TauCeti.HasSubnormalSection.refl (alternatingGroup α)).of_isSubnormal
      (inferInstance : (alternatingGroup α).Normal).isSubnormal).congr_left e.symm

/-! ### Explicit arithmetic obstruction checks -/

/-- `7` does not divide `(GammaProjective 6).index = 72`, ruling out `GammaProjective 6` inside any
index-`7` subgroup. -/
theorem not_seven_dvd_GammaProjective_index_six : ¬ 7 ∣ (GammaProjective 6).index := by
  rw [GammaProjective_index_six]; omega

/-- `7` does not divide `(GammaProjective 10).index = 360`. -/
theorem not_seven_dvd_GammaProjective_index_ten : ¬ 7 ∣ (GammaProjective 10).index := by
  rw [GammaProjective_index_ten]; omega

/-- `7` does not divide `(GammaProjective 12).index = 576`. -/
theorem not_seven_dvd_GammaProjective_index_twelve : ¬ 7 ∣ (GammaProjective 12).index := by
  rw [GammaProjective_index_twelve]; omega

/-- `|PSL₂(𝔽₅)| = 60` divides `(GammaProjective 11).index = 660`, showing that the order
obstruction alone does not rule out `PSL₂(𝔽₅)` (`≃* A₅`) at level `11`. -/
theorem card_psl_zmod_five_dvd_GammaProjective_index_eleven :
    Nat.card PSL(2, ZMod 5) ∣ (GammaProjective 11).index := by
  have h5 := Matrix.ProjectiveSpecialLinearGroup.two_mul_card_fin_two_zmod_prime
    Nat.prime_five (by decide)
  rw [GammaProjective_index_eleven, show Nat.card PSL(2, ZMod 5) = 60 by omega]
  decide

/-- **Separation of the composition-factor obstruction from the order obstruction (`N = 11`,
`ℓ = 5`):** although `|PSL₂(𝔽₅)| = 60 ∣ 660 = (GammaProjective 11).index`, `PSL₂(𝔽₅)` cannot occur
as a subnormal section of `PSL₂(ℤ) ⧸ Γ.normalCore` whenever `Γ(11) ≤ Γ.liftSL`, since `5 ∤ 11`. -/
theorem not_hasSubnormalSection_psl_zmod_five_of_Gamma_eleven_le_liftSL
    {Γ : Subgroup PSL(2, ℤ)} (h : CongruenceSubgroup.Gamma 11 ≤ Γ.liftSL) :
    ¬ TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) PSL(2, ZMod 5) := fun hsec ↦
  by have := dvd_of_hasSubnormalSection_psl_zmod_of_Gamma_le_liftSL (N := 11) (ℓ := 5)
      (by decide) Nat.prime_five le_rfl h hsec; omega

end TauCeti.CongruenceSubgroup
