/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Subgroup.IsSubnormal
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective
import Mathlib.Algebra.Field.ZMod
import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Principal congruence quotients and order and composition-factor obstructions

This file completes the index tower `Γ(N) ≤ Γ₁(N) ≤ Γ₀(N) ≤ SL₂(ℤ)` and establishes the finite
group-theoretic obstructions — both by group order and by Jordan–Hölder composition factors — that
principal congruence quotients place on congruence subgroups of `SL₂(ℤ)` and `PSL₂(ℤ)`.

## Main definitions and results

### Principal congruence quotients and indices (`CongruenceSubgroup`)
* `CongruenceSubgroup.quotientGammaEquiv`: the canonical isomorphism
  `(SL(2, ℤ) ⧸ Gamma N) ≃* SL(2, ZMod N)` induced by reduction modulo `N`.
* `CongruenceSubgroup.gamma1UpperRightHom` and `CongruenceSubgroup.gamma1QuotientGammaEquiv`: the
  surjective upper-right-entry homomorphism `Γ₁(N) →* Multiplicative (ZMod N)` with kernel
  `Γ(N) ≤ Γ₁(N)`, giving `(Gamma1 N ⧸ (Gamma N).subgroupOf (Gamma1 N)) ≃* Multiplicative (ZMod N)`.
* `CongruenceSubgroup.Gamma_relIndex_Gamma1` and
  `CongruenceSubgroup.index_Gamma_eq_card_zmod_mul_Gamma1_index`: `[Γ₁(N) : Γ(N)] = |ZMod N|`
  (`= N` for `N ≠ 0`) and `[SL₂(ℤ) : Γ(N)] = |ZMod N| · [SL₂(ℤ) : Γ₁(N)]`.
* `CongruenceSubgroup.index_Gamma_prime`, `CongruenceSubgroup.index_Gamma_prime_pow`,
  `CongruenceSubgroup.index_Gamma_eq_prod_factorization`, and
  `CongruenceSubgroup.index_Gamma_mul_prod_primeFactors_sq`: explicit prime, prime-power,
  prime-factorization, and cleared Euler-product formulas for `[SL₂(ℤ) : Γ(N)]`.

### Order and composition-factor obstructions
* `CongruenceSubgroup.slZModToQuotientNormalCore` and
  `TauCeti.CongruenceSubgroup.signedQuotientToQuotientNormalCore`: the canonical surjective
  homomorphisms `SL₂(ℤ/Nℤ) →* SL₂(ℤ) ⧸ Δ.normalCore` (for `Γ(N) ≤ Δ`) and
  `SL₂(ℤ/Nℤ) ⧸ {±I} →* PSL₂(ℤ) ⧸ Γ.normalCore` (for `Γ(N) ≤ Γ.liftSL`).
* `CongruenceSubgroup.card_quotient_normalCore_dvd_of_Gamma_le` and
  `TauCeti.CongruenceSubgroup.card_quotient_normalCore_dvd_of_Gamma_le_liftSL`: if `Γ(N) ≤ Δ`
  (respectively `Γ(N) ≤ Γ.liftSL`), then `|SL₂(ℤ) ⧸ Δ.normalCore| ∣ |SL₂(ℤ/Nℤ)|` (respectively
  `|PSL₂(ℤ) ⧸ Γ.normalCore| ∣ |SL₂(ℤ/Nℤ) ⧸ {±I}| = (GammaProjective N).index`).
* `CongruenceSubgroup.exists_prime_dvd_and_mulEquiv_of_Gamma_le` and
  `TauCeti.CongruenceSubgroup.exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL`: if `Γ(N) ≤ Δ`
  (respectively `Γ(N) ≤ Γ.liftSL`) with `N ≠ 0`, every nonabelian simple subnormal section of
  `SL₂(ℤ) ⧸ Δ.normalCore` (respectively `PSL₂(ℤ) ⧸ Γ.normalCore`) is isomorphic to `PSL₂(𝔽_ℓ)` for
  a prime `ℓ ≥ 5` dividing `N`.
* `CongruenceSubgroup.compositionFactor_quotient_normalCore_of_isCongruenceSubgroup` and
  `TauCeti.CongruenceSubgroup.compositionFactor_quotient_normalCore_of_isCongruenceSubgroup_liftSL`:
  level-free composition-factor obstructions for arbitrary congruence subgroups: every nonabelian
  simple subnormal section of the normal-core quotient is isomorphic to `PSL₂(𝔽_ℓ)` for some prime
  `ℓ ≥ 5`.
* `TauCeti.CongruenceSubgroup.dvd_of_hasSubnormalSection_psl_zmod_of_Gamma_le_liftSL`: if
  `PSL₂(ℤ) ⧸ Γ.normalCore` has `PSL₂(𝔽_ℓ)` (`ℓ` prime, `ℓ ≥ 5`) as a subnormal section and
  `Γ(N) ≤ Γ.liftSL` with `N ≠ 0`, then `ℓ ∣ N`.
* Alternating and symmetric monodromy noncongruence criteria
  (`not_isCongruenceSubgroup_liftSL_of_hasSubnormalSection_alternatingGroup`,
  `not_isCongruenceSubgroup_liftSL_of_quotient_normalCore_mulEquiv_alternatingGroup`, and
  `not_isCongruenceSubgroup_liftSL_of_quotient_normalCore_mulEquiv_perm`): if
  `PSL₂(ℤ) ⧸ Γ.normalCore` admits `alternatingGroup α` (`6 ≤ Nat.card α`) as a subnormal section —
  in particular if `PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to `A_n` or `S_n` for `n ≥ 6` — then
  `Γ.liftSL` is noncongruence.
* Explicit arithmetic checks at levels `N ∈ {6, 8, 10, 11, 12}`, including non-divisibility by `7`
  at `N ∈ {6, 10, 12}` and the level-`11` separation showing `|PSL₂(𝔽₅)| = 60 ∣ 660 =
  (GammaProjective 11).index` while `PSL₂(𝔽₅)` cannot appear as a subnormal section at level `11`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics
  228, Springer, 2005, §1.2.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §1.6.
* Klaus Wohlfahrt, *An extension of F. Klein's level concept*, Illinois J. Math. 8 (1964),
  529–535.
* Ling Long, *Finite index subgroups of the modular group and their modular forms*, in *Modular
  Forms and String Duality*, Fields Inst. Commun. 54, Amer. Math. Soc., 2008, 83–102.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CongruenceSubgroup

attribute [local instance] Gamma_normal

/-! ### Principal quotients, `Γ₁(N) ⧸ Γ(N) ≃* Multiplicative (ZMod N)`, and index formulas -/

/-- **Canonical isomorphism `(SL(2, ℤ) ⧸ Γ(N)) ≃* SL(2, ZMod N)`** induced by entrywise reduction
modulo `N` and strong approximation (`Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`). -/
noncomputable def quotientGammaEquiv (N : ℕ) :
    (SL(2, ℤ) ⧸ Gamma N) ≃* SL(2, ZMod N) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))
    Matrix.SpecialLinearGroup.map_intCast_zmod_surjective

@[simp]
theorem quotientGammaEquiv_mk (N : ℕ) (γ : SL(2, ℤ)) :
    quotientGammaEquiv N (QuotientGroup.mk γ) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ := by
  rw [quotientGammaEquiv]
  rfl

/-- The upper-right-entry homomorphism `Γ₁(N) →* Multiplicative (ZMod N)` sending `γ` to
`Multiplicative.ofAdd (γ 0 1 : ZMod N)`. Since matrices in `Γ₁(N)` are congruent to `!![1, *; 0, 1]`
modulo `N`, matrix multiplication adds their upper-right entries modulo `N`. -/
def gamma1UpperRightHom (N : ℕ) : Gamma1 N →* Multiplicative (ZMod N) where
  toFun g := Multiplicative.ofAdd (g.1 0 1 : ZMod N)
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    obtain ⟨hA00, -, -⟩ := (Gamma1_mem N A).mp hA
    obtain ⟨-, hB11, -⟩ := (Gamma1_mem N B).mp hB
    have h01 := (Matrix.two_mul_expl A.1 B.1).2.1
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, coe_mul, h01, Int.cast_add, Int.cast_mul, hA00, hB11,
      one_mul, mul_one]
    exact add_comm _ _

theorem gamma1UpperRightHom_apply (N : ℕ) (g : Gamma1 N) :
    gamma1UpperRightHom N g = Multiplicative.ofAdd (g.1 0 1 : ZMod N) := by
  rw [gamma1UpperRightHom]
  rfl

@[simp]
theorem toAdd_gamma1UpperRightHom_apply (N : ℕ) (g : Gamma1 N) :
    Multiplicative.toAdd (gamma1UpperRightHom N g) = (g.1 0 1 : ZMod N) := by
  rw [gamma1UpperRightHom_apply, toAdd_ofAdd]

/-- Powers of the translation matrix `ModularGroup.T` witness surjectivity of
`gamma1UpperRightHom N` at every level `N : ℕ`. -/
theorem gamma1UpperRightHom_surjective (N : ℕ) :
    Function.Surjective (gamma1UpperRightHom N) := fun x ↦ by
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
  refine ⟨⟨ModularGroup.T ^ z, T_zpow_mem_Gamma1 N z⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  simp [ModularGroup.coe_T_zpow, hz]

/-- Inside `Γ₁(N)`, the kernel of the upper-right entry modulo `N` is `Γ(N)`. -/
theorem ker_gamma1UpperRightHom (N : ℕ) :
    (gamma1UpperRightHom N).ker = (Gamma N).subgroupOf (Gamma1 N) := by
  ext ⟨A, hA⟩
  obtain ⟨hA00, hA11, hA10⟩ := (Gamma1_mem N A).mp hA
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Gamma_mem,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_gamma1UpperRightHom_apply, toAdd_one]
  exact ⟨fun hA01 ↦ ⟨hA00, hA01, hA10, hA11⟩, fun h ↦ h.2.1⟩

/-- **Canonical isomorphism `(Γ₁(N) ⧸ Γ(N)) ≃* Multiplicative (ZMod N)`.** -/
noncomputable def gamma1QuotientGammaEquiv (N : ℕ) :
    (Gamma1 N ⧸ (Gamma N).subgroupOf (Gamma1 N)) ≃* Multiplicative (ZMod N) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_gamma1UpperRightHom N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (gamma1UpperRightHom N)
      (gamma1UpperRightHom_surjective N))

@[simp]
theorem gamma1QuotientGammaEquiv_mk (N : ℕ) (g : Gamma1 N) :
    gamma1QuotientGammaEquiv N (QuotientGroup.mk g) = gamma1UpperRightHom N g := by
  rw [gamma1QuotientGammaEquiv]
  rfl

/-- At every level `N : ℕ`, `[Γ₁(N) : Γ(N)] = |ZMod N|` (`= N` for `N ≠ 0`, and `0` at `N = 0`). -/
theorem Gamma_relIndex_Gamma1 (N : ℕ) :
    (Gamma N).relIndex (Gamma1 N) = Nat.card (ZMod N) := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card,
    Nat.card_congr (gamma1QuotientGammaEquiv N).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

/-- For `N ≠ 0`, `[Γ₁(N) : Γ(N)] = N`. -/
theorem Gamma_relIndex_Gamma1_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    (Gamma N).relIndex (Gamma1 N) = N := by
  have : NeZero N := ⟨hN⟩
  rw [Gamma_relIndex_Gamma1, Nat.card_zmod]

/-- Tower relation `[SL₂(ℤ) : Γ(N)] = |ZMod N| · [SL₂(ℤ) : Γ₁(N)]`, valid at every level `N : ℕ`. -/
theorem index_Gamma_eq_card_zmod_mul_Gamma1_index (N : ℕ) :
    (Gamma N).index = Nat.card (ZMod N) * (Gamma1 N).index := by
  rw [← Subgroup.relIndex_mul_index (Gamma_le_Gamma1 N), Gamma_relIndex_Gamma1]

/-- For a prime `p`, `[SL₂(ℤ) : Γ(p)] = p(p² - 1)`. -/
theorem index_Gamma_prime {p : ℕ} (hp : p.Prime) :
    (Gamma p).index = p * (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_prime hp]

/-- For a prime `p` and `1 ≤ k`, `[SL₂(ℤ) : Γ(p^k)] = p^{3k - 2}(p² - 1)`. -/
theorem index_Gamma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (Gamma (p ^ k)).index = p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_prime_pow hp hk]

/-- For `N ≠ 0`, `[SL₂(ℤ) : Γ(N)] = ∏_{p^k ∥ N} p^{3k - 2}(p² - 1)`. -/
theorem index_Gamma_eq_prod_factorization {N : ℕ} (hN : N ≠ 0) :
    (Gamma N).index = N.factorization.prod fun p k ↦ p ^ (3 * k - 2) * (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_eq_prod_factorization hN]

/-- **Cleared Euler product for `[SL₂(ℤ) : Γ(N)]`** (valid for every `N : ℕ`):
`[SL₂(ℤ) : Γ(N)] · ∏_{p ∣ N} p² = N³ · ∏_{p ∣ N} (p² - 1)`. -/
theorem index_Gamma_mul_prod_primeFactors_sq (N : ℕ) :
    (Gamma N).index * ∏ p ∈ N.primeFactors, p ^ 2 =
      N ^ 3 * ∏ p ∈ N.primeFactors, (p ^ 2 - 1) := by
  rw [index_Gamma, card_fin_two_zmod_mul_prod_primeFactors_sq]

/-! ### Order and composition-factor obstructions in `SL₂(ℤ)` -/

/-- If `Γ(N) ≤ Δ`, then `[SL₂(ℤ) : Δ] ∣ |SL₂(ℤ/Nℤ)|`. -/
theorem index_dvd_card_sl_zmod_of_Gamma_le {N : ℕ} {Δ : Subgroup SL(2, ℤ)} (h : Gamma N ≤ Δ) :
    Δ.index ∣ Nat.card SL(2, ZMod N) := by
  rw [← index_Gamma]
  exact Subgroup.index_dvd_of_le h

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

theorem slZModToQuotientNormalCore_surjective {N : ℕ} {Δ : Subgroup SL(2, ℤ)} (h : Gamma N ≤ Δ) :
    Function.Surjective (slZModToQuotientNormalCore h) := fun x ↦ by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ,
    slZModToQuotientNormalCore_map_intCast h γ⟩

/-- **Order obstruction in `SL₂(ℤ)`:** if `Γ(N) ≤ Δ`, then
`|SL₂(ℤ) ⧸ Δ.normalCore| ∣ |SL₂(ℤ/Nℤ)|`. -/
theorem card_quotient_normalCore_dvd_of_Gamma_le {N : ℕ} {Δ : Subgroup SL(2, ℤ)}
    (h : Gamma N ≤ Δ) :
    Nat.card (SL(2, ℤ) ⧸ Δ.normalCore) ∣ Nat.card SL(2, ZMod N) := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (slZModToQuotientNormalCore h) (slZModToQuotientNormalCore_surjective h)).toEquiv]
  exact (slZModToQuotientNormalCore h).ker.card_quotient_dvd_card

/-- **Level-`N` composition-factor obstruction in `SL₂(ℤ)`:** if `Γ(N) ≤ Δ` with `N ≠ 0`, then
every nonabelian simple subnormal section `S` of `SL₂(ℤ) ⧸ Δ.normalCore` is isomorphic to
`PSL(2, ZMod ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_and_mulEquiv_of_Gamma_le {N : ℕ} (hN : N ≠ 0) {Δ : Subgroup SL(2, ℤ)}
    (h : Gamma N ≤ Δ) {S : Type*} [Group S] [IsSimpleGroup S] (hcomm : ¬ IsMulCommutative S)
    (hsec : Subgroup.HasSubnormalSection (SL(2, ℤ) ⧸ Δ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hcomm
    (hsec.of_surjective (slZModToQuotientNormalCore_surjective h))

/-- **Composition-factor obstruction for congruence subgroups of `SL₂(ℤ)`:** if `Δ ≤ SL₂(ℤ)` is a
congruence subgroup, then every nonabelian simple subnormal section `S` of `SL₂(ℤ) ⧸ Δ.normalCore`
is isomorphic to `PSL(2, ZMod ℓ)` for some prime `ℓ ≥ 5`. -/
theorem compositionFactor_quotient_normalCore_of_isCongruenceSubgroup {Δ : Subgroup SL(2, ℤ)}
    (hΔ : IsCongruenceSubgroup Δ) {S : Type*} [Group S] [IsSimpleGroup S]
    (hcomm : ¬ IsMulCommutative S)
    (hsec : Subgroup.HasSubnormalSection (SL(2, ℤ) ⧸ Δ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) := by
  obtain ⟨N, hN, hle⟩ := hΔ
  obtain ⟨ℓ, hℓ, h5, -, heq⟩ := exists_prime_dvd_and_mulEquiv_of_Gamma_le hN hle hcomm hsec
  exact ⟨ℓ, hℓ, h5, heq⟩

/-- **Noncongruence criterion via alternating subnormal sections in `SL₂(ℤ)`:** if
`SL₂(ℤ) ⧸ Δ.normalCore` admits `alternatingGroup α` (`6 ≤ Nat.card α`) as a subnormal section,
then `Δ` is not a congruence subgroup. -/
theorem not_isCongruenceSubgroup_of_hasSubnormalSection_alternatingGroup {Δ : Subgroup SL(2, ℤ)}
    {α : Type*} [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α)
    (hsec : Subgroup.HasSubnormalSection (SL(2, ℤ) ⧸ Δ.normalCore) (alternatingGroup α)) :
    ¬ IsCongruenceSubgroup Δ := by
  rintro ⟨N, hN, hle⟩
  exact Matrix.SpecialLinearGroup.not_hasSubnormalSection_alternatingGroup hN hα
    (hsec.of_surjective (slZModToQuotientNormalCore_surjective hle))

end CongruenceSubgroup

namespace TauCeti.CongruenceSubgroup

/-! ### Order and composition-factor obstructions in `PSL₂(ℤ)` -/

/-- **Order obstruction on the index in `PSL₂(ℤ)`:** if `Γ(N) ≤ Γ.liftSL` (equivalently
`GammaProjective N ≤ Γ`), then
`[PSL₂(ℤ) : Γ] ∣ (GammaProjective N).index = |SL₂(ℤ/Nℤ) ⧸ {±I}|`. -/
theorem index_dvd_of_Gamma_le_liftSL {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    Γ.index ∣ Nat.card (Matrix.SignedQuotient (Fin 2) (ZMod N)) := by
  rw [← GammaProjective_index_eq_card]
  exact Subgroup.index_dvd_of_le (GammaProjective_le_iff.mpr h)

/-- When `Γ(N) ≤ Γ.liftSL`, the canonical surjective homomorphism
`SL₂(ℤ/Nℤ) ⧸ {±I} →* PSL₂(ℤ) ⧸ Γ.normalCore` obtained from `GammaProjective N ≤ Γ.normalCore` and
`quotientGammaProjectiveEquiv N`. -/
noncomputable def signedQuotientToQuotientNormalCore {N : ℕ} {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL) :
    Matrix.SignedQuotient (Fin 2) (ZMod N) →* PSL(2, ℤ) ⧸ Γ.normalCore :=
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
    Nat.card (PSL(2, ℤ) ⧸ Γ.normalCore) ∣ Nat.card (Matrix.SignedQuotient (Fin 2) (ZMod N)) := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (signedQuotientToQuotientNormalCore h)
    (signedQuotientToQuotientNormalCore_surjective h)).toEquiv]
  exact (signedQuotientToQuotientNormalCore h).ker.card_quotient_dvd_card

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
    (hsec : Subgroup.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  exists_prime_dvd_psl_mulEquiv_of_hasSubnormalSection hN hcomm
    ((hsec.of_surjective (signedQuotientToQuotientNormalCore_surjective h)).of_surjective
      (QuotientGroup.mk'_surjective (negOneSubgroup (Fin 2) (ZMod N))))

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
    (Subgroup.HasSubnormalSection.mk_quotient hH hKH)

/-- **Composition-factor obstruction for projective congruence subgroups:** if `Γ.liftSL` is a
congruence subgroup of `SL₂(ℤ)`, then every nonabelian simple subnormal section `S` of
`PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to `PSL(2, ZMod ℓ)` for some prime `ℓ ≥ 5`. -/
theorem compositionFactor_quotient_normalCore_of_isCongruenceSubgroup_liftSL
    {Γ : Subgroup PSL(2, ℤ)} (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL)
    {S : Type*} [Group S] [IsSimpleGroup S] (hcomm : ¬ IsMulCommutative S)
    (hsec : Subgroup.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) := by
  obtain ⟨N, hN, hle⟩ := hΓ
  obtain ⟨ℓ, hℓ, h5, -, heq⟩ := exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL hN hle hcomm hsec
  exact ⟨ℓ, hℓ, h5, heq⟩

/-- **Prime-level divisibility criterion:** if `PSL₂(ℤ) ⧸ Γ.normalCore` admits `PSL(2, ZMod ℓ)`
(`ℓ` prime, `5 ≤ ℓ`) as a subnormal section and `Γ(N) ≤ Γ.liftSL` with `N ≠ 0`, then `ℓ ∣ N`. -/
theorem dvd_of_hasSubnormalSection_psl_zmod_of_Gamma_le_liftSL {N ℓ : ℕ} (hN : N ≠ 0)
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {Γ : Subgroup PSL(2, ℤ)}
    (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL)
    (hsec : Subgroup.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) PSL(2, ZMod ℓ)) :
    ℓ ∣ N := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h4 : 4 ≤ Nat.card (ZMod ℓ) := by
    rw [Nat.card_zmod]
    omega
  have : IsSimpleGroup PSL(2, ZMod ℓ) :=
    Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_four_le_natCard (F := ZMod ℓ) h4
  have hnotcomm : ¬ IsMulCommutative PSL(2, ZMod ℓ) := fun _ ↦ by
    have hsolv : Group.IsSolvable PSL(2, ZMod ℓ) := inferInstance
    have hle3 := (TauCeti.Matrix.ProjectiveSpecialLinearGroup.isSolvable_fin_two_iff
      (F := ZMod ℓ)).mp hsolv |>.2
    rw [Nat.card_zmod] at hle3
    omega
  obtain ⟨q, hq, -, hqN, ⟨e⟩⟩ :=
    exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL hN h hnotcomm hsec
  rwa [Matrix.ProjectiveSpecialLinearGroup.eq_of_fin_two_zmod_mulEquiv hℓ hq e]

/-! ### Alternating and symmetric monodromy noncongruence criteria -/

/-- **Alternating-section noncongruence theorem:** if `PSL₂(ℤ) ⧸ Γ.normalCore` admits
`alternatingGroup α` (`6 ≤ Nat.card α`) as a subnormal section, then `Γ.liftSL` is not a
congruence subgroup of `SL₂(ℤ)`. -/
theorem not_isCongruenceSubgroup_liftSL_of_hasSubnormalSection_alternatingGroup
    {Γ : Subgroup PSL(2, ℤ)} {α : Type*} [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α)
    (hsec : Subgroup.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) (alternatingGroup α)) :
    ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL := by
  rintro ⟨N, hN, hle⟩
  exact Matrix.SpecialLinearGroup.not_hasSubnormalSection_alternatingGroup hN hα
    ((hsec.of_surjective (signedQuotientToQuotientNormalCore_surjective hle)).of_surjective
      (QuotientGroup.mk'_surjective (negOneSubgroup (Fin 2) (ZMod N))))

/-- **Alternating monodromy noncongruence theorem (`A_n`, `n ≥ 6`):** if
`(PSL₂(ℤ) ⧸ Γ.normalCore) ≃* alternatingGroup α` with `6 ≤ Nat.card α`, then `Γ.liftSL` is not a
congruence subgroup. -/
theorem not_isCongruenceSubgroup_liftSL_of_quotient_normalCore_mulEquiv_alternatingGroup
    {Γ : Subgroup PSL(2, ℤ)} {α : Type*} [Fintype α] [DecidableEq α] (hα : 6 ≤ Nat.card α)
    (e : (PSL(2, ℤ) ⧸ Γ.normalCore) ≃* alternatingGroup α) :
    ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL :=
  not_isCongruenceSubgroup_liftSL_of_hasSubnormalSection_alternatingGroup hα
    ((Subgroup.HasSubnormalSection.refl (alternatingGroup α)).congr_left e.symm)

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
  have hsecA : Subgroup.HasSubnormalSection (Equiv.Perm α) (alternatingGroup α) :=
    (Subgroup.HasSubnormalSection.refl (alternatingGroup α)).of_isSubnormal
      (inferInstance : (alternatingGroup α).Normal).isSubnormal
  exact not_isCongruenceSubgroup_liftSL_of_hasSubnormalSection_alternatingGroup hα
    (hsecA.congr_left e.symm)

/-! ### Explicit principal projective indices and arithmetic obstruction checks -/

theorem GammaProjective_index_six : (GammaProjective 6).index = 72 := by
  have h := two_mul_index_map_Gamma (N := 6) (by omega)
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [← GammaProjective_def, h6, card_zmod_mul_of_coprime (Fin 2) (by decide),
    card_fin_two_zmod_prime Nat.prime_two, card_fin_two_zmod_prime Nat.prime_three] at h
  norm_num at h
  omega

theorem GammaProjective_index_eight : (GammaProjective 8).index = 192 := by
  rw [GammaProjective_index_eq_card, Matrix.SignedQuotient.card_fin_two_zmod_eight]

theorem GammaProjective_index_ten : (GammaProjective 10).index = 360 := by
  have h := two_mul_index_map_Gamma (N := 10) (by omega)
  have h10 : (10 : ℕ) = 2 * 5 := by norm_num
  rw [← GammaProjective_def, h10, card_zmod_mul_of_coprime (Fin 2) (by decide),
    card_fin_two_zmod_prime Nat.prime_two, card_fin_two_zmod_prime Nat.prime_five] at h
  norm_num at h
  omega

theorem GammaProjective_index_eleven : (GammaProjective 11).index = 660 := by
  have h := two_mul_index_map_Gamma (N := 11) (by omega)
  have h11 : Nat.Prime 11 := by decide
  rw [← GammaProjective_def, card_fin_two_zmod_prime h11] at h
  norm_num at h
  omega

theorem GammaProjective_index_twelve : (GammaProjective 12).index = 576 := by
  rw [GammaProjective_index_eq_card, Matrix.SignedQuotient.card_fin_two_zmod_twelve]

/-- `7` does not divide `(GammaProjective 6).index = 72`, ruling out `GammaProjective 6` inside any
index-`7` subgroup. -/
theorem not_seven_dvd_GammaProjective_index_six : ¬ 7 ∣ (GammaProjective 6).index := by
  rw [GammaProjective_index_six]
  omega

/-- `7` does not divide `(GammaProjective 10).index = 360`. -/
theorem not_seven_dvd_GammaProjective_index_ten : ¬ 7 ∣ (GammaProjective 10).index := by
  rw [GammaProjective_index_ten]
  omega

/-- `7` does not divide `(GammaProjective 12).index = 576`. -/
theorem not_seven_dvd_GammaProjective_index_twelve : ¬ 7 ∣ (GammaProjective 12).index := by
  rw [GammaProjective_index_twelve]
  omega

/-- `|PSL₂(𝔽₅)| = 60` divides `(GammaProjective 11).index = 660`, showing that the order
obstruction alone does not rule out `PSL₂(𝔽₅)` (`≃* A₅`) at level `11`. -/
theorem card_psl_zmod_five_dvd_GammaProjective_index_eleven :
    Nat.card PSL(2, ZMod 5) ∣ (GammaProjective 11).index := by
  have h5 : 2 * Nat.card PSL(2, ZMod 5) = 120 :=
    (Matrix.ProjectiveSpecialLinearGroup.two_mul_card_fin_two_zmod_prime
      Nat.prime_five (by decide)).trans (by norm_num)
  have hcard : Nat.card PSL(2, ZMod 5) = 60 := by omega
  rw [hcard, GammaProjective_index_eleven]
  norm_num

/-- **Separation of the composition-factor obstruction from the order obstruction (`N = 11`,
`ℓ = 5`):** although `|PSL₂(𝔽₅)| = 60 ∣ 660 = (GammaProjective 11).index`, `PSL₂(𝔽₅)` cannot occur
as a subnormal section of `PSL₂(ℤ) ⧸ Γ.normalCore` whenever `Γ(11) ≤ Γ.liftSL`, since `5 ∤ 11`. -/
theorem not_hasSubnormalSection_psl_zmod_five_of_Gamma_eleven_le_liftSL
    {Γ : Subgroup PSL(2, ℤ)} (h : CongruenceSubgroup.Gamma 11 ≤ Γ.liftSL) :
    ¬ Subgroup.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) PSL(2, ZMod 5) := fun hsec ↦ by
  have hdvd :=
    dvd_of_hasSubnormalSection_psl_zmod_of_Gamma_le_liftSL (N := 11) (ℓ := 5)
      (by decide) Nat.prime_five le_rfl h hsec
  omega

end TauCeti.CongruenceSubgroup
