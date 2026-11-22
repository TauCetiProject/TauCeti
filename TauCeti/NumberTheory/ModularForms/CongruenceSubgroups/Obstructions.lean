/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.Subgroup.IsSubnormal
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Principal
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective.Principal
import Mathlib.Algebra.Field.ZMod
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.ZMod
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.FinTwo.Solvable
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.CompositionFactors
import TauCeti.LinearAlgebra.Projectivization.PSL.Simple

/-!
# Composition-factor obstructions for principal modular quotients

This file establishes the Jordan–Hölder composition-factor obstructions that principal congruence
quotients place on congruence subgroups of `SL₂(ℤ)` and `PSL₂(ℤ)` (order obstructions live in
`TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Principal` and
`TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective.Principal`):

* **Composition-factor obstructions**: for `N ≠ 0`, every nonabelian simple subnormal section of
  `SL₂(ℤ) ⧸ Δ.normalCore` or `PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to `PSL₂(𝔽_ℓ)` for a prime
  `ℓ ≥ 5` dividing `N` (with level-free forms for arbitrary congruence subgroups, and prime-level
  divisibility `ℓ ∣ N` when `PSL₂(𝔽_ℓ)` occurs).
* **Alternating and symmetric noncongruence criteria**: if `PSL₂(ℤ) ⧸ Γ.normalCore` admits
  `alternatingGroup α` (`6 ≤ Nat.card α`) as a subnormal section — in particular if it is
  isomorphic to `A_n` or `S_n` for `n ≥ 6` — then `Γ.liftSL` is noncongruence.

Explicit fixed-level obstruction checks (e.g. at levels `6, 8, 10, 11, 12`) live in
`TauCeti.Examples.NumberTheory.ModularForms.CongruenceSubgroups.Obstructions`.

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

/-! ### Composition-factor obstructions in `SL₂(ℤ)` -/

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

/-! ### Composition-factor obstructions in `PSL₂(ℤ)` -/

/-- The quotient of `SL₂(ℤ)` by the normal core of `Γ.liftSL` is canonically isomorphic to the
quotient of `PSL₂(ℤ)` by the normal core of `Γ`, since `SL₂(ℤ) →* PSL₂(ℤ)` is surjective. -/
private noncomputable def quotientNormalCoreLiftSLEquiv (Γ : Subgroup PSL(2, ℤ)) :
    (SL(2, ℤ) ⧸ Γ.liftSL.normalCore) ≃* (PSL(2, ℤ) ⧸ Γ.normalCore) :=
  let π : SL(2, ℤ) →* PSL(2, ℤ) := QuotientGroup.mk' (Subgroup.center SL(2, ℤ))
  let φ : SL(2, ℤ) →* PSL(2, ℤ) ⧸ Γ.normalCore := (QuotientGroup.mk' Γ.normalCore).comp π
  have hker : Γ.liftSL.normalCore = φ.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.liftSL_def]
    exact Subgroup.normalCore_comap_of_forall_exists_mul_eq π fun g ↦
      let ⟨x, hx⟩ := QuotientGroup.mk'_surjective _ g; ⟨x, 1, one_mem _, by rw [mul_one]; exact hx⟩
  QuotientGroup.liftEquiv Γ.liftSL.normalCore
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) hker

/-- **Level-`N` composition-factor obstruction in `PSL₂(ℤ)`:** if `Γ(N) ≤ Γ.liftSL` with `N ≠ 0`,
then every nonabelian simple subnormal section `S` of `PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to
`PSL(2, ZMod ℓ)` for a prime `ℓ ≥ 5` dividing `N`. -/
theorem exists_prime_dvd_and_mulEquiv_of_Gamma_le_liftSL {N : ℕ} (hN : N ≠ 0)
    {Γ : Subgroup PSL(2, ℤ)} (h : CongruenceSubgroup.Gamma N ≤ Γ.liftSL)
    {S : Type*} [Group S] [IsSimpleGroup S] (hcomm : ¬ IsMulCommutative S)
    (hsec : TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ℓ ∣ N ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  CongruenceSubgroup.exists_prime_dvd_and_mulEquiv_of_Gamma_le hN h hcomm
    (hsec.congr_left (quotientNormalCoreLiftSLEquiv Γ).symm)

/-- **Composition-factor obstruction for projective congruence subgroups:** if `Γ.liftSL` is a
congruence subgroup of `SL₂(ℤ)`, then every nonabelian simple subnormal section `S` of
`PSL₂(ℤ) ⧸ Γ.normalCore` is isomorphic to `PSL(2, ZMod ℓ)` for some prime `ℓ ≥ 5`. -/
theorem compositionFactor_quotient_normalCore_of_isCongruenceSubgroup_liftSL
    {Γ : Subgroup PSL(2, ℤ)} (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL)
    {S : Type*} [Group S] [IsSimpleGroup S] (hcomm : ¬ IsMulCommutative S)
    (hsec : TauCeti.HasSubnormalSection (PSL(2, ℤ) ⧸ Γ.normalCore) S) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ Nonempty (S ≃* PSL(2, ZMod ℓ)) :=
  CongruenceSubgroup.compositionFactor_quotient_normalCore_of_isCongruenceSubgroup hΓ hcomm
    (hsec.congr_left (quotientNormalCoreLiftSLEquiv Γ).symm)

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
    ¬ CongruenceSubgroup.IsCongruenceSubgroup Γ.liftSL :=
  CongruenceSubgroup.not_isCongruenceSubgroup_of_hasSubnormalSection_alternatingGroup hα
    (hsec.congr_left (quotientNormalCoreLiftSLEquiv Γ).symm)

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

end TauCeti.CongruenceSubgroup
