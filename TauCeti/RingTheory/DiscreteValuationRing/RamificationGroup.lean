/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow
public import TauCeti.Algebra.Group.Action.Irreducible
public import TauCeti.RingTheory.DiscreteValuationRing.PrincipalUnitGroup
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded
import Mathlib.RingTheory.IntegralDomain
import TauCeti.RingTheory.Invariant.Basic

/-!
# Graded embeddings into principal unit groups of a discrete valuation ring

Let a group `G` act by ring automorphisms on a discrete valuation ring `S` with maximal ideal `𝔪`
and residue field `κ`. For a uniformizer `ϖ` and `σ ∈ G_i` (`i : ℕ`), the image `σ • ϖ` is again a
uniformizer, so `σ • ϖ = ϖ * u_σ` for a unique unit `u_σ : Sˣ` (`uniformizerChangeUnit`). Writing
`ϖ * (u_σ - 1) = σ • ϖ - ϖ ∈ 𝔪 ^ (i + 1)` and cancelling `ϖ` places `u_σ` in the `i`-th principal
unit group `U(S, i) = (𝔪 ^ i).principalUnitGroup` (with `U(S, 0) = Sˣ`).

Modulo `U(S, i + 1)`, the assignment `σ ↦ u_σ` is a group homomorphism
`G_i →* U(S, i) / U(S, i + 1)` that does not depend on the choice of uniformizer `ϖ` and kills
`G_{i+1}`, descending to `G_i / G_{i+1}`. Composing with
`TauCeti.IsLocalRing.principalUnitGradedZeroEquiv` at depth `0` recovers the canonical tame
character `TauCeti.IsLocalRing.tameCharacter`, while at depth `n + 1` composing with
`TauCeti.IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField` recovers the additive
coordinate of `TauCeti.IsLocalRing.ramificationGroupToResidueField`.

Under a separable residue extension over a local base ring `R` fixed by `G`, the kernel of
`G_i →* U(S, i) / U(S, i + 1)` is `G_{i+1}`, so `G_i / G_{i+1}` embeds into
`U(S, i) / U(S, i + 1)`. This file also records conjugation equivariance, cardinality formulas, and
characteristic-zero structure theorems for `G_0` and `G_1` on arbitrary discrete valuation rings:
* if the residue characteristic is prime `p`, the action is faithful, and `G_0` is finite, then
  `#G_1 = p ^ (v_p #G_0)` and `G_1 = ⊥ ↔ ¬ p ∣ #G_0`;
* if the residue characteristic is zero and `G_0` is finite (without any separability hypothesis),
  `ker tameCharacter = G_1` and `tameCharacterGraded` is injective, and when the action is also
  faithful, `tameCharacter` is injective and `G_0` is cyclic.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u_σ ∈ U(S, i)` satisfying
  `ϖ * u_σ = σ • ϖ`, for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded`: the
  uniformizer-independent homomorphisms `G_i →* U(S, i) / U(S, i + 1)` and
  `G_i / G_{i+1} →* U(S, i) / U(S, i + 1)`.

## Main results

* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGraded_eq_of_irreducible` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_eq_of_irreducible`:
  independence of the chosen uniformizer.
* `principalUnitGradedZeroEquiv_comp_ramificationGroupToPrincipalUnitGraded` and
  `principalUnitGradedSuccEquivResidueField_ofMul_ramificationGroupToPrincipalUnitGraded`
  (in `TauCeti.IsDiscreteValuationRing`): compatibility with `TauCeti.IsLocalRing.tameCharacter` and
  `TauCeti.IsLocalRing.ramificationGroupToResidueField`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_conj`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_conj`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_conj_of_smul_eq_pow`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_ramificationGroupGradedConj`, and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow`:
  conjugation equivariance of the tame character and positive-depth residue coordinate.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_injective`:
  exactness and injectivity of the principal-unit graded embedding under separable residue
  extension.
* `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_iff`,
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot`,
  `TauCeti.IsDiscreteValuationRing.natCard_ramificationGroup_one`, and
  `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero` (in
  `TauCeti.IsDiscreteValuationRing`): tame inertia and wild inertia structure on a discrete
  valuation ring with separable residue extension.
* `TauCeti.IsDiscreteValuationRing.ker_tameCharacter_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_of_charZero`, and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue
  characteristic zero without separability hypotheses, `ker tameCharacter = G_1` and
  `tameCharacterGraded` is injective when `G_0` is finite, and when the action is also faithful,
  `tameCharacter` is injective and `G_0` is cyclic.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–2, Propositions 1, 2, 5, 6, 7, 9.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, §3.1, Proposition 1.
* Adapted to arbitrary discrete valuation rings from two internal Tau Ceti precedents:
  * `TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`: the uniformizer
    ratio construction (`uniformizerRatio`), the graded principal-unit homomorphism and its
    descent (`ramificationGroupToPrincipalUnitGraded`,
    `ramificationGroupGradedToPrincipalUnitGraded`) with uniformizer-independence and
    separable-residue kernel/injectivity, and the wild-inertia order formula
    (`natCard_ramificationGroup_one`), adapted from `uniformizerRatio`,
    `ramificationGroupToUnitFiltrationGraded`, `ramificationGroupGradedToUnitFiltrationGraded`,
    and `natCard_ramificationGroup_one`.
  * `TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`: the tame and wild
    inertia structure results (`tameCharacter_injective_iff`,
    `isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot`, and
    `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`), adapted from the
    function-field place statements (`isCyclic_quotient_ramificationGroup_one` and
    `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`).
-/

public section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section UniformizerRatio

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

/-- For a uniformizer `ϖ` and `σ ∈ G_i`, the **uniformizer ratio** `u_σ ∈ U(S, i)` is the unique
unit satisfying `ϖ * u_σ = σ • ϖ`. -/
noncomputable def uniformizerRatio (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S i) : (maximalIdeal S ^ i).principalUnitGroup :=
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ (hϖ.smul (σ : G)), by
    rw [Ideal.mem_principalUnitGroup, ← hϖ.mul_mem_maximalIdeal_pow_succ_iff]
    have hmul :
        ϖ * ((uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
          (hϖ.smul (σ : G)) : S) - 1) = (σ : G) • ϖ - ϖ := by
      rw [mul_sub, mul_uniformizerChangeUnit, mul_one]
    rw [hmul]
    exact mem_ramificationGroup_natCast_iff.mp σ.property ϖ⟩

/-- As a unit of `S`, `uniformizerRatio i hϖ σ` is `uniformizerChangeUnit ϖ ((σ : G) • ϖ)`. -/
@[simp]
theorem coe_uniformizerRatio (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S i) :
    (uniformizerRatio i hϖ σ : Sˣ) =
      uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ (hϖ.smul (σ : G)) :=
  (rfl)

/-- The defining identity `ϖ * uniformizerRatio i hϖ σ = σ • ϖ` in `S`. -/
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S i) :
    ϖ * (((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S) =
      (σ : G) • ϖ :=
  mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

variable (G) in
@[simp]
theorem uniformizerRatio_one (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    uniformizerRatio i hϖ (1 : ramificationGroup G S i) = 1 := by
  ext
  apply mul_left_cancel₀ hϖ.ne_zero
  have h := mul_coe_uniformizerRatio i hϖ (1 : ramificationGroup G S i)
  simp only [Subgroup.coe_one, one_smul] at h
  simpa only [Subgroup.coe_one, Units.val_one, mul_one] using h

/-- Twisted multiplicativity (1-cocycle law) of `uniformizerRatio` in `Sˣ`:
`u_{σ * τ} = u_σ * σ(u_τ)`. -/
theorem coe_uniformizerRatio_mul (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G S i) :
    ((uniformizerRatio i hϖ (σ * τ) : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
      (uniformizerRatio i hϖ σ : Sˣ) *
        Units.map (MulDistribMulAction.toMonoidHom S (σ : G))
          (uniformizerRatio i hϖ τ : Sˣ) := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  calc
    ϖ * (((uniformizerRatio i hϖ (σ * τ) : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S)
      = (σ * τ : G) • ϖ := mul_coe_uniformizerRatio i hϖ (σ * τ)
    _ = (σ : G) • (ϖ * (((uniformizerRatio i hϖ τ :
          (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S)) := by
        rw [mul_smul, mul_coe_uniformizerRatio]
    _ = ϖ * ((((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) *
          Units.map (MulDistribMulAction.toMonoidHom S (σ : G))
            (uniformizerRatio i hϖ τ : Sˣ) : Sˣ) : S) := by
        rw [smul_mul', ← mul_coe_uniformizerRatio i hϖ σ, Units.val_mul, Units.coe_map,
          MulDistribMulAction.toMonoidHom_apply, mul_assoc]

/-- Replacing `ϖ` by `ϖ' = ϖ * a` multiplies `uniformizerRatio` by the coboundary `σ(a) * a⁻¹`:
`a * u'_σ = u_σ * σ(a)` in `Sˣ`. -/
theorem coe_uniformizerRatio_change (i : ℕ) {ϖ ϖ' : S} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (σ : ramificationGroup G S i) :
    uniformizerChangeUnit ϖ ϖ' hϖ hϖ' *
        ((uniformizerRatio i hϖ' σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
      ((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) *
        Units.map (MulDistribMulAction.toMonoidHom S (σ : G))
          (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  calc
    ϖ * ((uniformizerChangeUnit ϖ ϖ' hϖ hϖ' *
          ((uniformizerRatio i hϖ' σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : Sˣ) : S)
      = ϖ' * (((uniformizerRatio i hϖ' σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S) := by
        rw [Units.val_mul, ← mul_assoc, mul_uniformizerChangeUnit]
    _ = (σ : G) • (ϖ * (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : S)) := by
        rw [mul_coe_uniformizerRatio, mul_uniformizerChangeUnit]
    _ = ϖ * ((((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) *
          Units.map (MulDistribMulAction.toMonoidHom S (σ : G))
            (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') : Sˣ) : S) := by
        rw [smul_mul', ← mul_coe_uniformizerRatio i hϖ σ, Units.val_mul, Units.coe_map,
          MulDistribMulAction.toMonoidHom_apply, mul_assoc]

variable (G) in
/-- The homomorphism `G_i →* U(S, i) / U(S, i + 1)` sending `σ` to the class of `u_σ`, where
`ϖ * u_σ = σ • ϖ`. It does not depend on the choice of uniformizer `ϖ`
(`ramificationGroupToPrincipalUnitGraded_eq_of_irreducible`). -/
noncomputable def ramificationGroupToPrincipalUnitGraded (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) :
    ramificationGroup G S i →* PrincipalUnitGraded S i where
  toFun σ := QuotientGroup.mk (uniformizerRatio i hϖ σ)
  map_one' := by rw [uniformizerRatio_one, QuotientGroup.mk_one]
  map_mul' σ τ := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    let uτ : Sˣ := uniformizerRatio i hϖ τ
    let v : Sˣ := Units.map (MulDistribMulAction.toMonoidHom S (σ : G)) uτ
    have heq :
        (((uniformizerRatio i hϖ (σ * τ))⁻¹ *
          (uniformizerRatio i hϖ σ * uniformizerRatio i hϖ τ) :
          (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) = (v * uτ⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_uniformizerRatio_mul]
      rw [mul_comm v uτ⁻¹]
      dsimp only [uτ, v]
      group
    rw [heq]
    exact inv_mem (map_mul_inv_mem_principalUnitGroup σ.property uτ)

@[simp]
theorem ramificationGroupToPrincipalUnitGraded_apply (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S i) :
    ramificationGroupToPrincipalUnitGraded G i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

variable (G) in
/-- **Uniformizer-independence.** The homomorphism `G_i →* U(S, i) / U(S, i + 1)` is independent of
the chosen uniformizer `ϖ`: replacing `ϖ` by `ϖ' = ϖ * a` multiplies `u_σ` by `σ(a) * a⁻¹`, which
lies in `U(S, i + 1)` because `σ ∈ G_i`. -/
theorem ramificationGroupToPrincipalUnitGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToPrincipalUnitGraded G i hϖ =
      ramificationGroupToPrincipalUnitGraded G i hϖ' := by
  ext σ
  rw [ramificationGroupToPrincipalUnitGraded_apply,
    ramificationGroupToPrincipalUnitGraded_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  let a : Sˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  let b : Sˣ := Units.map (MulDistribMulAction.toMonoidHom S (σ : G)) a
  have hrel := coe_uniformizerRatio_change i hϖ hϖ' σ
  have heq :
      (((uniformizerRatio i hϖ σ)⁻¹ * uniformizerRatio i hϖ' σ :
        (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
      b * a⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, mul_comm _ a]
    exact hrel
  rw [heq]
  exact map_mul_inv_mem_principalUnitGroup σ.property a

/-- An element `σ ∈ G_i` lies in the kernel of `G_i →* U(S, i) / U(S, i + 1)` if and only if it
moves `ϖ` by an element of `𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGraded_iff (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) {σ : ramificationGroup G S i} :
    σ ∈ (ramificationGroupToPrincipalUnitGraded G i hϖ).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal S ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGraded_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Ideal.mem_principalUnitGroup,
    ← hϖ.mul_mem_maximalIdeal_pow_succ_iff]
  have hmul :
      ϖ * ((((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S) - 1) =
        (σ : G) • ϖ - ϖ := by
    rw [mul_sub, mul_coe_uniformizerRatio, mul_one]
  rw [hmul]

variable (G) in
/-- The subgroup `G_{i+1}` always lies in the kernel of `G_i →* U(S, i) / U(S, i + 1)`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    (ramificationGroup G S ((i : ℤ) + 1)).subgroupOf (ramificationGroup G S i) ≤
      (ramificationGroupToPrincipalUnitGraded G i hϖ).ker := by
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G S (i + 1 : ℕ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGraded_iff i hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

variable (G) in
/-- The descended homomorphism `G_i / G_{i+1} →* U(S, i) / U(S, i + 1)` induced by `σ ↦ u_σ`. -/
noncomputable def ramificationGroupGradedToPrincipalUnitGraded (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G S i →* PrincipalUnitGraded S i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGraded G i hϖ)
    fun _ hσ ↦ ramificationGroup_succ_subgroupOf_le_ker G i hϖ hσ

@[simp]
theorem ramificationGroupGradedToPrincipalUnitGraded_mk (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S i) :
    ramificationGroupGradedToPrincipalUnitGraded G i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupGradedToPrincipalUnitGraded, QuotientGroup.lift_mk,
    ramificationGroupToPrincipalUnitGraded_apply]

variable (G) in
/-- The descended homomorphism `G_i / G_{i+1} →* U(S, i) / U(S, i + 1)` does not depend on the
chosen uniformizer. -/
theorem ramificationGroupGradedToPrincipalUnitGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToPrincipalUnitGraded G i hϖ =
      ramificationGroupGradedToPrincipalUnitGraded G i hϖ' := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedToPrincipalUnitGraded_mk,
      ramificationGroupGradedToPrincipalUnitGraded_mk,
      ← ramificationGroupToPrincipalUnitGraded_apply,
      ← ramificationGroupToPrincipalUnitGraded_apply]
    exact DFunLike.congr_fun
      (ramificationGroupToPrincipalUnitGraded_eq_of_irreducible G i hϖ hϖ') σ

end UniformizerRatio

section Compatibility

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

variable (G) in
/-- Composing `ramificationGroupToPrincipalUnitGraded G 0 hϖ` with `principalUnitGradedZeroEquiv`
recovers the canonical tame character `TauCeti.IsLocalRing.tameCharacter G S`. -/
theorem principalUnitGradedZeroEquiv_comp_ramificationGroupToPrincipalUnitGraded
    {ϖ : S} (hϖ : Irreducible ϖ) :
    (principalUnitGradedZeroEquiv S).toMonoidHom.comp
        (ramificationGroupToPrincipalUnitGraded G 0 hϖ) =
      IsLocalRing.tameCharacter G S := by
  ext σ
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGraded_apply, coe_principalUnitGradedZeroEquiv_mk]
  exact (coe_tameCharacter_of_smul_eq_mul hϖ (mul_coe_uniformizerRatio 0 hϖ σ).symm).symm

variable (G) in
/-- Composing `ramificationGroupGradedToPrincipalUnitGraded G 0 hϖ` with
`principalUnitGradedZeroEquiv` recovers `TauCeti.IsLocalRing.tameCharacterGraded G S`. -/
theorem principalUnitGradedZeroEquiv_comp_ramificationGroupGradedToPrincipalUnitGraded
    {ϖ : S} (hϖ : Irreducible ϖ) :
    (principalUnitGradedZeroEquiv S).toMonoidHom.comp
        (ramificationGroupGradedToPrincipalUnitGraded G 0 hϖ) =
      IsLocalRing.tameCharacterGraded G S := by
  refine MonoidHom.ext fun x ↦ ?_
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.comp_apply, ramificationGroupGradedToPrincipalUnitGraded_mk,
    ← ramificationGroupToPrincipalUnitGraded_apply, ← MonoidHom.comp_apply,
    principalUnitGradedZeroEquiv_comp_ramificationGroupToPrincipalUnitGraded,
    ← QuotientGroup.coe_mk', QuotientGroup.mk'_apply, IsLocalRing.tameCharacterGraded_mk]

variable (G) in
/-- At positive depth `n + 1`, composing `ramificationGroupToPrincipalUnitGraded G (n + 1) hϖ`
with `principalUnitGradedSuccEquivResidueField n hϖ` agrees with the additive coordinate of
`TauCeti.IsLocalRing.ramificationGroupToResidueField hϖ n`. -/
theorem principalUnitGradedSuccEquivResidueField_ofMul_ramificationGroupToPrincipalUnitGraded
    (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    principalUnitGradedSuccEquivResidueField n hϖ
        (Additive.ofMul (ramificationGroupToPrincipalUnitGraded G (n + 1) hϖ
          ⟨(σ : G), by exact_mod_cast σ.property⟩)) =
      (IsLocalRing.ramificationGroupToResidueField hϖ n σ).toAdd := by
  let σ' : ramificationGroup G S (n + 1 : ℕ) := ⟨(σ : G), by exact_mod_cast σ.property⟩
  have hmove : (σ : G) • ϖ - ϖ ∈ maximalIdeal S ^ (n + 2) := by
    have h := mem_ramificationGroup_iff.mp σ.property ϖ
    rwa [(by omega : ((n : ℤ) + 1 + 1).toNat = n + 2)] at h
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
  obtain ⟨y, hy⟩ := hmove
  have hu :
      ((((uniformizerRatio (n + 1) hϖ σ' :
        (maximalIdeal S ^ (n + 1)).principalUnitGroup) : Sˣ) : S) - 1) =
        y * ϖ ^ (n + 1) := by
    apply mul_left_cancel₀ hϖ.ne_zero
    calc
      ϖ * ((((uniformizerRatio (n + 1) hϖ σ' :
            (maximalIdeal S ^ (n + 1)).principalUnitGroup) : Sˣ) : S) - 1)
        = (σ : G) • ϖ - ϖ := by rw [mul_sub, mul_coe_uniformizerRatio, mul_one]
      _ = y * ϖ ^ (n + 2) := hy.symm
      _ = ϖ * (y * ϖ ^ (n + 1)) := by rw [pow_succ']; ring
  rw [ramificationGroupToPrincipalUnitGraded_apply,
    principalUnitGradedSuccEquivResidueField_ofMul_mk_eq_residue n hϖ _ y hu,
    ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ (by rw [← hy, mul_comm]),
    toAdd_ofAdd]

variable (G) in
/-- At positive depth `n + 1`, the graded principal-unit map composed with
`principalUnitGradedSuccEquivResidueField` agrees with
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`. -/
theorem principalUnitGradedSuccEquivResidueField_ofMul_ramificationGroupGradedToPrincipalUnitGraded
    (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    principalUnitGradedSuccEquivResidueField n hϖ
        (Additive.ofMul (ramificationGroupGradedToPrincipalUnitGraded G (n + 1) hϖ
          (QuotientGroup.mk ⟨(σ : G), by exact_mod_cast σ.property⟩))) =
      (IsLocalRing.ramificationGroupGradedToResidueField hϖ n (QuotientGroup.mk σ)).toAdd := by
  rw [ramificationGroupGradedToPrincipalUnitGraded_mk,
    ← ramificationGroupToPrincipalUnitGraded_apply,
    ramificationGroupGradedToResidueField_mk]
  exact principalUnitGradedSuccEquivResidueField_ofMul_ramificationGroupToPrincipalUnitGraded
    G n hϖ σ

end Compatibility

section Conjugation

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

/-- The change from `ϖ` to `σ⁻¹ • ϖ` has residue equal to the inverse tame character of `σ`. -/
private theorem residue_uniformizerChangeUnit_inv_smul {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (σ : ramificationGroup G S 0)
    (hϖ'eq : ϖ' = (σ : G)⁻¹ • ϖ) :
    residue S (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : S) =
      ((IsLocalRing.tameCharacter G S σ : (ResidueField S)ˣ)⁻¹ : ResidueField S) := by
  have ha : ((σ⁻¹ : ramificationGroup G S 0) : G) • ϖ =
      ϖ * (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : S) := by
    rw [mul_uniformizerChangeUnit, hϖ'eq, Subgroup.coe_inv]
  rw [← Units.val_inv_eq_inv_val, ← map_inv, coe_tameCharacter_of_smul_eq_mul hϖ ha]

variable (G) in
/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` determined by `ϖ`,
conjugation by `σ ∈ G_0` acts on `G_{n+1} / G_{n+2}` as multiplication by `theta_0(σ) ^ (n + 1)`,
where `theta_0` is `TauCeti.IsLocalRing.tameCharacter`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S 0) (τ : RamificationGroupGraded G S ((n : ℤ) + 1)) :
    (IsLocalRing.ramificationGroupGradedToResidueField hϖ n
        (ramificationGroupGradedConj G S (σ : G) ((n : ℤ) + 1) τ)).toAdd =
      (IsLocalRing.tameCharacter G S σ : ResidueField S) ^ (n + 1) *
        (IsLocalRing.ramificationGroupGradedToResidueField hϖ n τ).toAdd := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let ϖ' : S := g⁻¹ • ϖ
    have hϖ' : Irreducible ϖ' := hϖ.smul g⁻¹
    have hmove : (τ : G) • ϖ' - ϖ' ∈ maximalIdeal S ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.property) ϖ'
    rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord :
        (IsLocalRing.ramificationGroupToResidueField hϖ' n τ).toAdd = residue S y := by
      rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ' (by rw [← hy, mul_comm]),
        toAdd_ofAdd]
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G S ((n : ℤ) + 1)) : G) • ϖ - ϖ =
          ϖ ^ (n + 2) * g • y := by
      calc
        _ = g • ((τ : G) • ϖ' - ϖ') := by simp [ϖ', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * ϖ' ^ (n + 2)) := by rw [hy]
        _ = ϖ ^ (n + 2) * g • y := by
          rw [smul_mul', smul_pow', show g • ϖ' = ϖ by simp [ϖ'], mul_comm]
    have hresidue : residue S (g • y) = residue S y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G S σ.property y
    have hchange := toAdd_ramificationGroupToResidueField_of_mul_eq hϖ hϖ'
      (mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ') τ
    rw [residue_uniformizerChangeUnit_inv_smul hϖ hϖ' σ rfl] at hchange
    simp only [ramificationGroupGradedConj_mk]
    rw [ramificationGroupGradedToResidueField_mk, ramificationGroupGradedToResidueField_mk,
      ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ hconjMove, toAdd_ofAdd, hresidue,
      ← hτcoord, hchange, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (Units.ne_zero _), one_pow,
      one_mul]

variable (G S) in
/-- **The tame character is equivariant.** For `g ∈ G` and `σ ∈ G_0`, the tame character of
`g σ g⁻¹` is the image of the tame character of `σ` under the automorphism of the residue field
induced by `g`: `theta_0(g σ g⁻¹) = g • theta_0(σ)`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G S 0) :
    (IsLocalRing.tameCharacter G S (MulAut.conjNormal g σ) : ResidueField S) =
      g • (IsLocalRing.tameCharacter G S σ : ResidueField S) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  have hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.smul (σ : G)
  have hgϖ : Irreducible (g • ϖ) := hϖ.smul g
  set u : S := (uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ : S)
  have hu : ϖ * u = (σ : G) • ϖ := mul_uniformizerChangeUnit ϖ _ hϖ hσϖ
  have hgu : (MulAut.conjNormal g σ : G) • (g • ϖ) = g • ϖ * g • u := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, ← hu, smul_mul']
  rw [coe_tameCharacter_of_smul_eq_mul hgϖ hgu, coe_tameCharacter_of_smul_eq_mul hϖ hu.symm,
    ResidueField.residue_smul]

variable (G S) in
/-- **The tame character twisted by a power map.** If `g ∈ G` acts on the residue field as the
`q`-th power map, then `theta_0(g σ g⁻¹) = theta_0(σ) ^ q` for every `σ ∈ G_0`. -/
theorem tameCharacter_conj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField S, g • x = x ^ q) (σ : ramificationGroup G S 0) :
    IsLocalRing.tameCharacter G S (MulAut.conjNormal g σ) =
      IsLocalRing.tameCharacter G S σ ^ q :=
  Units.ext (by rw [tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

variable (G S) in
/-- The equivariance of the tame character, read on the tame quotient `G_0 / G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (τ : RamificationGroupGraded G S 0) :
    (IsLocalRing.tameCharacterGraded G S (ramificationGroupGradedConj G S g 0 τ) :
        ResidueField S) =
      g • (IsLocalRing.tameCharacterGraded G S τ : ResidueField S) := by
  induction τ using QuotientGroup.induction_on with
  | _ σ => rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

variable (G S) in
/-- The power-map twist of the tame character, read on the tame quotient `G_0 / G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField S, g • x = x ^ q) (τ : RamificationGroupGraded G S 0) :
    IsLocalRing.tameCharacterGraded G S (ramificationGroupGradedConj G S g 0 τ) =
      IsLocalRing.tameCharacterGraded G S τ ^ q :=
  Units.ext (by rw [tameCharacterGraded_ramificationGroupGradedConj, hg,
    Units.val_pow_eq_pow_val])

end Conjugation

section SeparableResidue

variable {G : Type*} [Group G] (R : Type*) [CommRing R] [IsLocalRing R]
  {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
include R

variable (G) in
/-- Under separable residue extension, the kernel of `G_i →* U(S, i) / U(S, i + 1)` is `G_{i+1}`. -/
theorem ker_ramificationGroupToPrincipalUnitGraded (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    (ramificationGroupToPrincipalUnitGraded G i hϖ).ker =
      (ramificationGroup G S ((i : ℤ) + 1)).subgroupOf (ramificationGroup G S i) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker G i hϖ)
  rw [mem_ker_ramificationGroupToPrincipalUnitGraded_iff i hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G S 0 :=
    ramificationGroup_antitone G S (Int.natCast_nonneg i) σ.property
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ.maximalIdeal_eq hσ₀]
  exact hσ

variable (G) in
/-- **Graded unit-filtration embedding.** Under separable residue extension, the uniformizer-ratio
map embeds `G_i / G_{i+1}` into `U(S, i) / U(S, i + 1)`. -/
theorem ramificationGroupGradedToPrincipalUnitGraded_injective (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGraded G i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGraded G R i hϖ).symm

variable (G S) in
/-- Under separable residue extension, the tame character `G_0 →* (ResidueField S)ˣ` is injective
if and only if wild inertia `G_1` is trivial. -/
theorem tameCharacter_injective_iff :
    Function.Injective (IsLocalRing.tameCharacter G S) ↔ ramificationGroup G S 1 = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, IsLocalRing.ker_tameCharacter R, Subgroup.eq_bot_iff_forall]
  refine ⟨fun h ↦ eq_bot_iff.mpr fun σ hσ ↦ ?_, fun h ⟨σ, hσ₀⟩ hσ₁ ↦ ?_⟩
  · exact Subtype.ext_iff.mp (h ⟨σ, ramificationGroup_antitone G S zero_le_one hσ⟩
      (Subgroup.mem_subgroupOf.mpr hσ))
  · rw [Subgroup.mem_subgroupOf, h, Subgroup.mem_bot] at hσ₁
    exact Subtype.ext hσ₁

variable (G S) in
/-- When `G_0` is finite, the residue extension is separable, and wild inertia `G_1` is trivial,
inertia `G_0` is cyclic. -/
theorem isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot
    [Finite (ramificationGroup G S 0)] (h : ramificationGroup G S 1 = ⊥) :
    IsCyclic (ramificationGroup G S 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (IsLocalRing.tameCharacter G S))
    (Units.val_injective.comp ((tameCharacter_injective_iff G R S).mpr h))

variable (G S) in
/-- The order of wild inertia is the `p`-part of the order of inertia:
`#G_1 = p ^ (v_p #G_0)` (including `p = 0`). -/
theorem natCard_ramificationGroup_one (p : ℕ) [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    have hcard := Sylow.card_eq_multiplicity (IsLocalRing.ramificationGroupOneSylow G S R p)
    rw [IsLocalRing.ramificationGroupOneSylow_coe] at hcard
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm
  · have := CharP.charP_to_charZero (ResidueField S)
    have : Finite (ramificationGroup G S 1) :=
      finite_ramificationGroup_of_le G S zero_le_one
    simp [ramificationGroup_one_eq_bot_of_charZero G S]

variable (G S) in
/-- **Wild inertia vanishes iff `p ∤ #G_0`.** Under separable residue extension in residue
characteristic `p`, `G_1 = ⊥` if and only if `p` does not divide the order of `G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    ramificationGroup G S 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G S 0) := by
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hprime | rfl
  · rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one G R S p,
      pow_eq_one_iff_right hprime.ne_one, Nat.factorization_eq_zero_iff]
    simp only [hprime, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]
  · have := CharP.charP_to_charZero (ResidueField S)
    have : Finite (ramificationGroup G S 1) :=
      finite_ramificationGroup_of_le G S zero_le_one
    rw [ramificationGroup_one_eq_bot_of_charZero G S, zero_dvd_iff]
    exact iff_of_true rfl Nat.card_pos.ne'

end SeparableResidue

section CharZero

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S] [CharZero (ResidueField S)] [Finite (ramificationGroup G S 0)]

variable (G S) in
/-- In residue characteristic zero with finite inertia `G_0`, every element in the kernel of
`tameCharacter` lies in `G_1` (without any base ring `R`, separability, or faithfulness
hypothesis). -/
private theorem mem_ramificationGroup_one_of_mem_ker_tameCharacter_of_charZero
    {σ : ramificationGroup G S 0} (hσker : σ ∈ (IsLocalRing.tameCharacter G S).ker) :
    (σ : G) ∈ ramificationGroup G S 1 := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  let : Fintype (ramificationGroup G S 0) := Fintype.ofFinite _
  -- Because `ResidueField S` has characteristic zero, `#G_0` is a unit in `S`.
  have hunit : IsUnit ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  rw [← Nat.cast_one, mem_ramificationGroup_natCast_iff]
  intro x
  -- Average `x` over `G_0` to obtain a `G_0`-invariant element `s` congruent to `#G_0 * x`
  -- mod `𝔪`.
  let s : S := ∑ τ : ramificationGroup G S 0, (τ : G) • x
  have hs_inv : (σ : G) • s = s := TauCeti.smul_sum_smul σ x
  have hdiff_mem : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s ∈
      maximalIdeal S := by
    have heq : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s =
        ∑ τ : ramificationGroup G S 0, (x - (τ : G) • x) := by
      simp only [s, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [heq]
    exact Ideal.sum_mem _ fun τ _ ↦
      neg_mem_iff.mp (by simpa [neg_sub] using mem_ramificationGroup_zero_iff.mp τ.property x)
  -- Write `#G_0 * x - s = ϖ * c`; then `#G_0 * (σ x - x) = σ(ϖ * c) - ϖ * c ∈ 𝔪 ^ 2`.
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hdiff_mem
  obtain ⟨c, hc⟩ := hdiff_mem
  have hmul : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x - x) ∈
      maximalIdeal S ^ 2 := by
    have hsmul_nat :
        (σ : G) • ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) =
          (Fintype.card (ramificationGroup G S 0) : S) := by
      rw [← MulSemiringAction.toRingHom_apply, map_natCast]
    have hid : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x - x) =
        (σ : G) • (ϖ * c) - ϖ * c := by
      calc
        ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x - x)
          = ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x) - s -
              (((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s) := by ring
        _ = (σ : G) • (((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s) -
              (((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s) := by
            rw [smul_sub, smul_mul', hsmul_nat, hs_inv]
        _ = (σ : G) • (ϖ * c) - ϖ * c := by rw [hc]
    rw [hid]
    have hsplit : (σ : G) • (ϖ * c) - ϖ * c =
        ((σ : G) • ϖ - ϖ) * ((σ : G) • c) + ϖ * ((σ : G) • c - c) := by
      rw [smul_mul']
      ring
    rw [hsplit]
    refine add_mem ?_ ?_
    · exact Ideal.mul_mem_right _ _
        ((tameCharacter_eq_one_iff_smul_sub_mem hϖ).mp (MonoidHom.mem_ker.mp hσker))
    · have hϖm : ϖ ∈ maximalIdeal S := by rw [hϖ.maximalIdeal_eq]; exact Ideal.subset_span rfl
      rw [pow_two]
      exact Ideal.mul_mem_mul hϖm (mem_ramificationGroup_zero_iff.mp σ.property c)
  exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmul

variable (G S) in
/-- In residue characteristic zero with finite inertia `G_0`, the kernel of `tameCharacter` is
`G_1` (without any base ring `R`, separability, or faithfulness hypothesis). -/
theorem ker_tameCharacter_of_charZero :
    (IsLocalRing.tameCharacter G S).ker =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) := by
  refine le_antisymm (fun σ hσker ↦ ?_)
    ramificationGroup_one_subgroupOf_le_ker_tameCharacter
  exact mem_ramificationGroup_one_of_mem_ker_tameCharacter_of_charZero G S hσker

variable (G S) in
/-- **Tame character embedding in characteristic zero.** In residue characteristic zero with
finite inertia `G_0`, `G_0 / G_1` embeds into `(ResidueField S)ˣ` (without any base ring `R`,
separability, or faithfulness hypothesis). -/
theorem tameCharacterGraded_injective_of_charZero :
    Function.Injective (IsLocalRing.tameCharacterGraded G S) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  induction g using QuotientGroup.induction_on with
  | H σ =>
    rw [tameCharacterGraded_mk, ← MonoidHom.mem_ker, ker_tameCharacter_of_charZero G S] at hg
    rwa [QuotientGroup.eq_one_iff, zero_add]

variable (G S) in
/-- In residue characteristic zero with faithful action and finite inertia `G_0`, the tame
character `G_0 →* (ResidueField S)ˣ` is injective (without any base ring `R` or separability
hypothesis). -/
theorem tameCharacter_injective_of_charZero [FaithfulSMul G S] :
    Function.Injective (IsLocalRing.tameCharacter G S) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_tameCharacter_of_charZero G S, Subgroup.eq_bot_iff_forall]
  intro σ hσ₁
  have : Finite (ramificationGroup G S 1) :=
    finite_ramificationGroup_of_le G S zero_le_one
  rw [Subgroup.mem_subgroupOf, ramificationGroup_one_eq_bot_of_charZero G S,
    Subgroup.mem_bot] at hσ₁
  exact Subtype.ext hσ₁

variable (G S) in
/-- **Inertia is cyclic in residue characteristic zero.** When `ResidueField S` has characteristic
zero, the action is faithful, and `G_0` is finite, `G_0` itself is cyclic (without any base ring
`R` or separability hypothesis). -/
theorem isCyclic_ramificationGroup_zero_of_charZero [FaithfulSMul G S] :
    IsCyclic (ramificationGroup G S 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (IsLocalRing.tameCharacter G S))
    (Units.val_injective.comp (tameCharacter_injective_of_charZero G S))

end CharZero

end TauCeti.IsDiscreteValuationRing
