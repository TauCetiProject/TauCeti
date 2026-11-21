/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.Algebra.Group.Irreducible.Lemmas
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.RingTheory.IntegralDomain
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Graded embeddings of the ramification filtration of a discrete valuation ring

Let `G` act by ring automorphisms on a discrete valuation ring `B` with maximal ideal `𝔪` and
residue field `k`, and fix a uniformizer `ϖ` of `B`. Any `σ` in the `i`-th ramification group
`G_i = TauCeti.IsLocalRing.ramificationGroup G B i` carries `ϖ` to another uniformizer `σ • ϖ`,
so `ϖ * u_σ = σ • ϖ` for a unique unit `u_σ : Bˣ` congruent to `1` modulo `𝔪 ^ i`. Passing to the
`i`-th graded piece `U_B^i / U_B^{i+1} = (maximalIdeal B).PrincipalUnitGroupPowGraded i` of the
principal-unit filtration yields a group homomorphism

`ramificationGroupToPrincipalUnitGroupGraded : G_i →* U_B^i / U_B^{i+1}`

that does not depend on the choice of uniformizer `ϖ` and kills `G_{i+1}`, hence descends to
`θ_i : G_i / G_{i+1} →* U_B^i / U_B^{i+1}`.

Composing at depth zero with `U_B^0 / U_B^1 ≃* kˣ` gives the **tame character**
`tameCharacter : G_0 →* kˣ` and its quotient form `tameCharacterGraded : G_0 / G_1 →* kˣ`.
Composing at positive depth `i = n + 1` with the uniformizer coordinate `U_B^{n+1} / U_B^{n+2} ≃+ k`
of `TauCeti.maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer` gives an
additive homomorphism `G_{n+1} / G_{n+2} →+ k` whose dependence on `ϖ` is multiplication by the
`(n + 1)`-st power of the residue of the change unit.

When `B` is a local algebra over a local ring `A` whose elements `G` fixes and the residue
extension `ResidueField B / ResidueField A` is separable, membership of an element of `G_0` in
`G_i` is decided at `ϖ` alone (`mem_ramificationGroup_iff_smul_sub_mem`), so the kernel of the
`i`-th homomorphism is *equal* to `G_{i+1}` and all graded maps `θ_i`, `tameCharacterGraded`, and
`ramificationGroupGradedToResidueField` are injective. Together with the local-ring positive-depth
results from `TauCeti/RingTheory/LocalRing/RamificationGroup.lean`, this gives the tame/wild
decomposition of inertia without assuming that the residue field is finite or that `B` is
complete:

* whenever `G_0 / G_1` is finite, it is cyclic, and its cardinality is not divisible by the residue
  characteristic `p`;
* for a faithful action with finite `G_0` in prime residue characteristic `p`, the wild inertia
  group `G_1` is the unique normal Sylow `p`-subgroup of `G_0`, of cardinality `p ^ v_p(#G_0)`; in
  arbitrary residue characteristic `p`, `G_1 = ⊥` if and only if `p ∤ #G_0`;
* whenever `G_1 = ⊥` (in particular, for a faithful action with finite `G_0` in residue
  characteristic zero), the tame character embeds `G_0` itself into `kˣ`, and finite `G_0` is
  cyclic.

The parallel developments for nonarchimedean local fields (with finite residue field, phrased via
`TauCeti.unitFiltration` on the fraction field) and for places of function fields are in
`TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`,
`TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`, and
`TauCeti/FieldTheory/FunctionField/Place/Extension/WildInertia.lean`. Working directly in `Bˣ`
via `TauCeti.uniformizerChangeUnit` and `(maximalIdeal B ^ i).principalUnitGroup` avoids passing
through a fraction field or Teichmüller lifts.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: for `σ ∈ G_i` and uniformizer `ϖ`, the
  unique unit `u ∈ 1 + 𝔪 ^ i` with `ϖ * u = σ • ϖ`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded`: the
  uniformizer-independent homomorphisms `G_i →* U_B^i / U_B^{i+1}` and
  `G_i / G_{i+1} →* U_B^i / U_B^{i+1}`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter` and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded`: the tame character `G_0 →* kˣ` and its
  induced homomorphism on `G_0 / G_1`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField`: the positive-depth
  coordinate homomorphism `Additive (G_{n+1} / G_{n+2}) →+ k` attached to a uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: in prime residue characteristic `p`,
  `G_1` as the unique normal Sylow `p`-subgroup of a finite inertia group `G_0`.

## Main results

* `TauCeti.IsDiscreteValuationRing.coe_uniformizerRatio` and
  `TauCeti.IsDiscreteValuationRing.coe_uniformizerRatio_mul`: identification with
  `uniformizerChangeUnit` and the 1-cocycle multiplication law for `uniformizerRatio`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_eq_of_irreducible`: independence of the choice of
  uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_change`: changing the
  uniformizer scales the positive-depth residue coordinate by the `(n + 1)`-st power of the
  change-unit residue.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_iff_smul_sub_mem` and
  `TauCeti.IsDiscreteValuationRing.lowerIndex_eq_addVal_of_irreducible`: for a separable residue
  extension over a `G`-fixed local base `A`, membership in `G_i` and Serre's lower index on `G_0`
  are read at any uniformizer.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGroupGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_iff`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: exactness of
  the kernels and injectivity of the graded embeddings under separable residue extension.
* `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero`,
  `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`,
  `TauCeti.IsDiscreteValuationRing.eq_ramificationGroupOneSylow`,
  `TauCeti.IsDiscreteValuationRing.natCard_ramificationGroup_one`,
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot`,
  and `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: structure of
  `G_0 / G_1`, `G_1`, and `G_0`, including the tame criterion
  `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1 (Proposition 1) and §2 (Propositions 5–7
  and Corollaries).
-/

public section
noncomputable section

open IsLocalRing
open TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section UniformizerRatio

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [MulSemiringAction G B]
variable [IsDomain B] [_root_.IsDiscreteValuationRing B]

private theorem coe_unitsMap_ringHom {R₁ R₂ : Type*} [Ring R₁] [Ring R₂]
    (f : R₁ →+* R₂) (u : R₁ˣ) :
    ((Units.map f.toMonoidHom u : R₂ˣ) : R₂) = f (u : R₁) := by
  simp

private theorem unitsMap_mul_inv_mem_principalUnitGroup {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G B (i : ℤ)) (u : Bˣ) :
    Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom u * u⁻¹ ∈
      (maximalIdeal B ^ (i + 1)).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup]
  have hsub :
      ((Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom u * u⁻¹ : Bˣ) : B) - 1 =
        (σ • (u : B) - (u : B)) * ↑u⁻¹ := by
    rw [Units.val_mul, coe_unitsMap_ringHom, MulSemiringAction.toRingHom_apply, sub_mul,
      Units.mul_inv]
  rw [hsub]
  exact Ideal.mul_mem_right _ _ (mem_ramificationGroup_natCast_iff.mp hσ (u : B))

private theorem uniformizerChangeUnit_smul_mem_principalUnitGroup {ϖ : B} (hϖ : Irreducible ϖ)
    {i : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ (σ • ϖ) hϖ (hϖ.smul σ) ∈
      (maximalIdeal B ^ i).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup, ← mul_mem_maximalIdeal_pow_succ_iff hϖ]
  have hmul : ϖ * ((uniformizerChangeUnit ϖ (σ • ϖ) hϖ (hϖ.smul σ) : B) - 1) =
      σ • ϖ - ϖ := by
    rw [mul_sub, mul_one, mul_uniformizerChangeUnit]
  rw [hmul]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

/-- For `σ` in the `i`-th ramification group `G_i` of a discrete valuation ring `B` and a
uniformizer `ϖ`, the unique unit `u ∈ 1 + 𝔪 ^ i` satisfying `ϖ * u = σ • ϖ`. -/
def uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) : (maximalIdeal B ^ i).principalUnitGroup :=
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ (hϖ.smul (σ : G)),
    uniformizerChangeUnit_smul_mem_principalUnitGroup hϖ σ.property⟩

/-- As a unit of `B`, `uniformizerRatio i hϖ σ` is the uniformizer change unit from `ϖ` to
`σ • ϖ`. -/
theorem coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ σ : Bˣ) =
      uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ (hϖ.smul (σ : G)) :=
  -- `(rfl)`, not `rfl`, because the body of `uniformizerRatio` is not `@[expose]`d.
  (rfl)

/-- The unit `uniformizerRatio i hϖ σ` carries `ϖ` to `σ • ϖ` by right multiplication. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ := by
  rw [coe_uniformizerRatio, mul_uniformizerChangeUnit]

/-- Multiplication by `ϖ` relates `uniformizerRatio i hϖ σ - 1` directly to the displacement
`σ • ϖ - ϖ`. -/
theorem mul_coe_uniformizerRatio_sub_one (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * (((uniformizerRatio i hϖ σ : Bˣ) : B) - 1) = (σ : G) • ϖ - ϖ := by
  rw [mul_sub, mul_one, mul_coe_uniformizerRatio]

/-- At `σ = 1`, the uniformizer ratio is `1`. -/
@[simp]
theorem uniformizerRatio_one (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    uniformizerRatio (G := G) i hϖ 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  simp [mul_coe_uniformizerRatio]

/-- **1-cocycle law** in `Bˣ` for `uniformizerRatio`: multiplying by `σ * τ` multiplies the ratio
for `σ` by the `σ`-translate of the ratio for `τ`. -/
theorem coe_uniformizerRatio_mul (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  rw [mul_coe_uniformizerRatio, Subgroup.coe_mul, mul_smul, Units.val_mul, ← mul_assoc,
    mul_coe_uniformizerRatio, coe_unitsMap_ringHom, MulSemiringAction.toRingHom_apply,
    ← smul_mul', mul_coe_uniformizerRatio]

/-- **1-cocycle law** in `B` for `uniformizerRatio`. -/
theorem val_coe_uniformizerRatio_mul (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    ((uniformizerRatio i hϖ (σ * τ) : Bˣ) : B) =
      ((uniformizerRatio i hϖ σ : Bˣ) : B) *
        (σ : G) • ((uniformizerRatio i hϖ τ : Bˣ) : B) := by
  rw [coe_uniformizerRatio_mul, Units.val_mul, coe_unitsMap_ringHom,
    MulSemiringAction.toRingHom_apply]

/-! ### Homomorphisms into principal-unit graded pieces -/

/-- The homomorphism `G_i →* (1 + 𝔪 ^ i) / (1 + 𝔪 ^ (i + 1))` sending `σ` to the class of its
uniformizer ratio `u_σ` (`ϖ * u_σ = σ • ϖ`). It is independent of `ϖ`
(`ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible`) and kills `G_{i+1}`. -/
def ramificationGroupToPrincipalUnitGroupGraded (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (i : ℤ) →* (maximalIdeal B).PrincipalUnitGroupPowGraded i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) fun σ τ ↦ by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      ← Subgroup.inv_mem_iff, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      mul_inv_rev, inv_inv, coe_uniformizerRatio_mul]
    have hcomm :
        ((uniformizerRatio i hϖ σ : Bˣ) * (uniformizerRatio i hϖ τ : Bˣ))⁻¹ *
            ((uniformizerRatio i hϖ σ : Bˣ) *
              Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
                (uniformizerRatio i hϖ τ : Bˣ)) =
          Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
              (uniformizerRatio i hϖ τ : Bˣ) *
            (uniformizerRatio i hϖ τ : Bˣ)⁻¹ := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_comm]
    rw [hcomm]
    exact unitsMap_mul_inv_mem_principalUnitGroup σ.property _

/-- On `σ ∈ G_i`, the graded principal-unit homomorphism gives the class of `uniformizerRatio`. -/
@[simp]
theorem ramificationGroupToPrincipalUnitGroupGraded_apply (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToPrincipalUnitGroupGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

/-- The homomorphism `G_i →* (1 + 𝔪 ^ i) / (1 + 𝔪 ^ (i + 1))` does not depend on the choice of
uniformizer. -/
theorem ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ =
      ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ' := by
  -- Replacing `ϖ` by `ϖ * c` multiplies the ratio by `(σ • c) * c⁻¹ ∈ 1 + 𝔪 ^ (i + 1)`.
  set c : Bˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  refine MonoidHom.ext fun σ ↦ ?_
  rw [ramificationGroupToPrincipalUnitGroupGraded_apply,
    ramificationGroupToPrincipalUnitGroupGraded_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    Subgroup.coe_mul, Subgroup.coe_inv]
  have hrel : c * (uniformizerRatio i hϖ' σ : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom c := by
    apply Units.ext
    apply mul_left_cancel₀ hϖ.ne_zero
    calc
      ϖ * ((c * (uniformizerRatio i hϖ' σ : Bˣ) : Bˣ) : B)
          = (ϖ * (c : B)) * ((uniformizerRatio i hϖ' σ : Bˣ) : B) := by
            rw [Units.val_mul, mul_assoc]
      _ = ϖ' * ((uniformizerRatio i hϖ' σ : Bˣ) : B) := by
            rw [mul_uniformizerChangeUnit]
      _ = (σ : G) • (ϖ * (c : B)) := by
            rw [mul_coe_uniformizerRatio, ← mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ']
      _ = ϖ * (((uniformizerRatio i hϖ σ : Bˣ) *
            Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom c : Bˣ) : B) := by
            rw [smul_mul', ← mul_coe_uniformizerRatio i hϖ σ, Units.val_mul,
              coe_unitsMap_ringHom, MulSemiringAction.toRingHom_apply, mul_assoc]
  have hquot : (uniformizerRatio i hϖ σ : Bˣ)⁻¹ * (uniformizerRatio i hϖ' σ : Bˣ) =
      Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom c * c⁻¹ := by
    apply mul_left_cancel (a := (uniformizerRatio i hϖ σ : Bˣ))
    apply mul_right_cancel (b := c)
    rw [mul_inv_cancel_left, mul_assoc, inv_mul_cancel_right, mul_comm _ c, hrel]
  rw [hquot]
  exact unitsMap_mul_inv_mem_principalUnitGroup σ.property c

/-- An element `σ ∈ G_i` lies in the kernel of the `i`-th principal-unit homomorphism if and only
if `σ • ϖ - ϖ ∈ 𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToPrincipalUnitGroupGraded i hϖ).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGroupGraded_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Ideal.mem_principalUnitGroup,
    ← mul_mem_maximalIdeal_pow_succ_iff hϖ, mul_coe_uniformizerRatio_sub_one]

/-- The subgroup `G_{i+1}` of `G_i` lies in the kernel of
`ramificationGroupToPrincipalUnitGroupGraded`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToPrincipalUnitGroupGraded i hϖ).ker := by
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff i hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

/-- The induced homomorphism `θ_i : G_i / G_{i+1} →* (1 + 𝔪 ^ i) / (1 + 𝔪 ^ (i + 1))` on the
`i`-th successive quotient of the ramification filtration. -/
def ramificationGroupGradedToPrincipalUnitGroupGraded (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (i : ℤ) →* (maximalIdeal B).PrincipalUnitGroupPowGraded i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGroupGraded i hϖ)
    (ramificationGroup_succ_subgroupOf_le_ker i hϖ)

/-- On the class of `σ ∈ G_i`, the graded homomorphism `θ_i` gives the class of
`uniformizerRatio`. -/
@[simp]
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupGradedToPrincipalUnitGroupGraded, QuotientGroup.lift_mk,
    ramificationGroupToPrincipalUnitGroupGraded_apply]

/-- The graded homomorphism `θ_i : G_i / G_{i+1} →* (1 + 𝔪 ^ i) / (1 + 𝔪 ^ (i + 1))` does not
depend on the choice of uniformizer. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ =
      ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ' := by
  refine MonoidHom.ext fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedToPrincipalUnitGroupGraded_mk,
      ramificationGroupGradedToPrincipalUnitGroupGraded_mk]
    simpa only [ramificationGroupToPrincipalUnitGroupGraded_apply] using
      DFunLike.congr_fun
        (ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible i hϖ hϖ') σ

/-! ### The tame character and positive-depth residue coordinates -/

/-- The **tame character** `G_0 →* (ResidueField B)ˣ` sending an inertia element `σ` to the residue
of the unit `u_σ` with `ϖ * u_σ = σ • ϖ`. It is independent of `ϖ`
(`tameCharacter_eq_of_irreducible`) and kills `G_1`. -/
def tameCharacter {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupToPrincipalUnitGroupGraded 0 hϖ)

/-- Coerced to `ResidueField B`, the tame character at `σ` is the residue of `uniformizerRatio`. -/
@[simp]
theorem coe_tameCharacter_apply {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (0 : ℤ)) :
    (tameCharacter hϖ σ : ResidueField B) =
      residue B ((uniformizerRatio 0 hϖ σ : Bˣ) : B) := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGroupGraded_apply (i := 0),
    maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits_mk,
    coe_unitsMap_ringHom]

/-- If `ϖ * y = σ • ϖ` in `B`, then the tame character of `σ` has underlying value `residue B y`. -/
theorem coe_tameCharacter_of_mul_eq_smul {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (0 : ℤ)) {y : B} (hy : ϖ * y = (σ : G) • ϖ) :
    (tameCharacter hϖ σ : ResidueField B) = residue B y := by
  rw [coe_tameCharacter_apply hϖ]
  refine congrArg (residue B) ?_
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_coe_uniformizerRatio 0 hϖ σ).trans hy.symm)

/-- The tame character does not depend on the choice of uniformizer. -/
theorem tameCharacter_eq_of_irreducible {ϖ ϖ' : B} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    tameCharacter (G := G) hϖ = tameCharacter (G := G) hϖ' := by
  rw [tameCharacter, tameCharacter,
    ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible 0 hϖ hϖ']

/-- An inertia element `σ ∈ G_0` lies in the kernel of `tameCharacter` if and only if
`σ • ϖ - ϖ ∈ 𝔪 ^ 2`. -/
theorem mem_ker_tameCharacter_iff {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G B (0 : ℤ)} :
    σ ∈ (tameCharacter hϖ).ker ↔ (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ 2 := by
  rw [tameCharacter, MonoidHom.ker_comp_of_injective _ _
      (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).injective,
    mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff 0 hϖ, zero_add]

/-- The first ramification group `G_1`, viewed inside `G_0`, lies in the kernel of the tame
character. -/
theorem ramificationGroup_one_subgroupOf_le_ker_tameCharacter {ϖ : B} (hϖ : Irreducible ϖ) :
    (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) ≤
      (tameCharacter hϖ).ker := by
  rw [tameCharacter, MonoidHom.ker_comp_of_injective _ _
    (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).injective]
  simpa only [Int.natCast_zero, zero_add] using
    ramificationGroup_succ_subgroupOf_le_ker (G := G) 0 hϖ

/-- The **graded tame character** `G_0 / G_1 →* (ResidueField B)ˣ`. -/
def tameCharacterGraded {ϖ : B} (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded 0 hϖ)

/-- Evaluating `tameCharacterGraded` on the class of `σ ∈ G_0` gives `tameCharacter hϖ σ`. -/
@[simp]
theorem tameCharacterGraded_mk {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (0 : ℤ)) :
    tameCharacterGraded hϖ (QuotientGroup.mk σ) = tameCharacter hϖ σ := by
  rw [tameCharacterGraded, tameCharacter, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ramificationGroupGradedToPrincipalUnitGroupGraded_mk,
    ramificationGroupToPrincipalUnitGroupGraded_apply]

/-- The graded tame character does not depend on the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {ϖ ϖ' : B} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacterGraded (G := G) hϖ = tameCharacterGraded (G := G) hϖ' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible 0 hϖ hϖ']

private def ramificationGroupCastSuccEquiv (n : ℕ) :
    ramificationGroup G B ((n : ℤ) + 1) ≃* ramificationGroup G B ((n + 1 : ℕ) : ℤ) :=
  MulEquiv.subgroupCongr (congrArg (ramificationGroup G B) (Nat.cast_succ (R := ℤ) n).symm)

private def ramificationGroupGradedCastSuccEquiv (n : ℕ) :
    RamificationGroupGraded G B ((n : ℤ) + 1) ≃*
      RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ) :=
  QuotientGroup.congr _ _ (ramificationGroupCastSuccEquiv n) (by
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf,
      ramificationGroupCastSuccEquiv, Subtype.exists]
    constructor
    · rintro ⟨a, _, ha, rfl⟩
      simpa [Nat.cast_succ] using ha
    · intro hσ
      exact ⟨σ, Nat.cast_succ (R := ℤ) n ▸ σ.property,
        by simpa [Nat.cast_succ] using hσ, rfl⟩)

/-- At positive depth `n + 1`, composing `θ_{n+1}` with the uniformizer coordinate on
`(1 + 𝔪 ^ (n + 1)) / (1 + 𝔪 ^ (n + 2))` gives an additive homomorphism
`Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` sending `σ` to the residue of
`(σ • ϖ - ϖ) / ϖ ^ (n + 2)`. -/
def ramificationGroupGradedToResidueField (n : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    Additive (RamificationGroupGraded G B ((n : ℤ) + 1)) →+ ResidueField B :=
  (maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer
    n ϖ hϖ).toAddMonoidHom.comp
    ((ramificationGroupGradedToPrincipalUnitGroupGraded (n + 1) hϖ).comp
      (ramificationGroupGradedCastSuccEquiv n).toMonoidHom).toAdditive

private theorem ramificationGroupGradedToResidueField_apply (n : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) (q : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField n hϖ (Additive.ofMul q) =
      maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ
        (Additive.ofMul
          (ramificationGroupGradedToPrincipalUnitGroupGraded (n + 1) hϖ
            (ramificationGroupGradedCastSuccEquiv n q))) := by
  rw [ramificationGroupGradedToResidueField]
  rfl

/-- On the class of `τ ∈ G_{n+1}`, `ramificationGroupGradedToResidueField` evaluates the
principal-unit coordinate at `uniformizerRatio (n + 1) hϖ τ`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField n hϖ (Additive.ofMul (QuotientGroup.mk τ)) =
      maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ
        (Additive.ofMul (QuotientGroup.mk
          (uniformizerRatio (n + 1) hϖ
            ⟨(τ : G), (Nat.cast_succ (R := ℤ) n).symm ▸ τ.property⟩))) := by
  rw [ramificationGroupGradedToResidueField_apply, ramificationGroupGradedCastSuccEquiv,
    QuotientGroup.congr_mk, ramificationGroupGradedToPrincipalUnitGroupGraded_mk]
  rfl

/-- If `(τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)`, then the positive-depth residue coordinate of the
class of `τ` relative to `ϖ` is `residue B y`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) (τ : ramificationGroup G B ((n : ℤ) + 1)) (y : B)
    (hmove : (τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)) :
    ramificationGroupGradedToResidueField n hϖ (Additive.ofMul (QuotientGroup.mk τ)) =
      residue B y := by
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  refine
    maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
    n ϖ hϖ _ y ?_
  apply mul_left_cancel₀ hϖ.ne_zero
  rw [mul_coe_uniformizerRatio_sub_one, hmove, pow_succ', ← mul_assoc, mul_comm y ϖ, mul_assoc]

/-- Replacing `ϖ` by `ϖ'` scales the positive-depth residue coordinate on `G_{n+1} / G_{n+2}` by
the `(n + 1)`-st power of the residue of `uniformizerChangeUnit ϖ ϖ'`:
`coord_ϖ = residue(ϖ' / ϖ) ^ (n + 1) * coord_{ϖ'}`. -/
theorem ramificationGroupGradedToResidueField_change (n : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (q : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField n hϖ (Additive.ofMul q) =
      residue B (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : B) ^ (n + 1) *
        ramificationGroupGradedToResidueField n hϖ' (Additive.ofMul q) := by
  rw [ramificationGroupGradedToResidueField_apply, ramificationGroupGradedToResidueField_apply,
    DFunLike.congr_fun
      (ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) (n + 1)
        hϖ hϖ')]
  exact
    maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer_change n ϖ ϖ'
      hϖ hϖ' _

end UniformizerRatio

/-! ### Exactness and graded embeddings for separable residue extensions -/

section Separable

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

/-- When `B` is a local `A`-algebra on which `G` acts by `A`-algebra automorphisms with separable
residue extension `ResidueField B / ResidueField A`, membership of an inertia element `σ ∈ G_0` in
`G_i` is decided at any uniformizer `ϖ` of `B`. -/
theorem mem_ramificationGroup_iff_smul_sub_mem (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ)
    {i : ℤ} {σ : G} (hσ : σ ∈ ramificationGroup G B 0) :
    σ ∈ ramificationGroup G B i ↔ σ • ϖ - ϖ ∈ maximalIdeal B ^ (i + 1).toNat :=
  mem_ramificationGroup_iff_of_span_singleton_eq_maximalIdeal A hϖ.maximalIdeal_eq.symm hσ

/-- At a nonnegative index `n : ℕ`, when `B` is a local `A`-algebra on which `G` acts by
`A`-algebra automorphisms with separable residue extension, membership of `σ ∈ G_0` in `G_n` is
`σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ) {n : ℕ}
    {σ : G} (hσ : σ ∈ ramificationGroup G B 0) :
    σ ∈ ramificationGroup G B n ↔ σ • ϖ - ϖ ∈ maximalIdeal B ^ (n + 1) :=
  mem_ramificationGroup_natCast_iff_of_span_singleton_eq_maximalIdeal A hϖ.maximalIdeal_eq.symm hσ

/-- When `B` is a local `A`-algebra on which `G` acts by `A`-algebra automorphisms with separable
residue extension, Serre's lower index on the inertia group `G_0` is read at any uniformizer `ϖ`:
`i_G(σ) = v_B(σ • ϖ - ϖ)`, without assuming that `B` is monogenic over `A`. -/
theorem lowerIndex_eq_addVal_of_irreducible (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ) {σ : G}
    (hσ : σ ∈ ramificationGroup G B 0) :
    lowerIndex B σ = _root_.IsDiscreteValuationRing.addVal B (σ • ϖ - ϖ) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro m
  cases m with
  | zero => simp
  | succ n =>
    rw [natCast_le_lowerIndex_iff_mem_ramificationGroup, Nat.cast_succ, add_sub_cancel_right,
      mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ hσ, mem_maximalIdeal_pow_iff_le_addVal]

/-- **Exactness at depth `i`**: when `B` is a local `A`-algebra on which `G` acts by `A`-algebra
automorphisms with separable residue extension, the kernel of
`G_i →* (1 + 𝔪 ^ i) / (1 + 𝔪 ^ (i + 1))` is `G_{i+1}`. -/
theorem ker_ramificationGroupToPrincipalUnitGroupGraded (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    (ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker i hϖ)
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff i hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.property
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ hσ₀]
  exact hσ

/-- **Injectivity of `θ_i`**: when `B` is a local `A`-algebra on which `G` acts by `A`-algebra
automorphisms with separable residue extension, the graded map
`G_i / G_{i+1} →* (1 + 𝔪 ^ i) / (1 + 𝔪 ^ (i + 1))` is injective for every `i : ℕ`. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_injective (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra A B] [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGroupGraded A i hϖ).symm

/-- When `B` is a local `A`-algebra on which `G` acts by `A`-algebra automorphisms with separable
residue extension, the kernel of `tameCharacter` is `G_1`. -/
theorem ker_tameCharacter (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ) :
    (tameCharacter (G := G) hϖ).ker =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) := by
  rw [tameCharacter, MonoidHom.ker_comp_of_injective _ _
    (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).injective]
  simpa only [Int.natCast_zero, zero_add] using
    ker_ramificationGroupToPrincipalUnitGroupGraded A (G := G) 0 hϖ

/-- When `B` is a local `A`-algebra on which `G` acts by `A`-algebra automorphisms with separable
residue extension, `tameCharacter` is injective if and only if the wild inertia group `G_1` is
trivial. -/
theorem tameCharacter_injective_iff (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacter (G := G) hϖ) ↔ ramificationGroup G B 1 = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_tameCharacter A hϖ, Subgroup.subgroupOf_eq_bot,
    disjoint_iff, inf_eq_left.mpr (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))]

/-- **Injectivity of the graded tame character**: when `B` is a local `A`-algebra on which `G` acts
by `A`-algebra automorphisms with separable residue extension,
`tameCharacterGraded : G_0 / G_1 →* (ResidueField B)ˣ` is injective. -/
theorem tameCharacterGraded_injective (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacterGraded (G := G) hϖ) :=
  (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).injective.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded_injective A 0 hϖ)

/-- **Injectivity of the positive-depth residue coordinate**: when `B` is a local `A`-algebra on
which `G` acts by `A`-algebra automorphisms with separable residue extension,
`Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` is injective for every `n : ℕ`. -/
theorem ramificationGroupGradedToResidueField_injective (A : Type*) [CommRing A] [IsLocalRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (n : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToResidueField (G := G) n hϖ) := by
  rw [ramificationGroupGradedToResidueField]
  exact (maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer
    n ϖ hϖ).injective.comp
    (Additive.ofMul.injective.comp
      ((ramificationGroupGradedToPrincipalUnitGroupGraded_injective A (n + 1) hϖ).comp
        ((ramificationGroupGradedCastSuccEquiv n).injective.comp Additive.toMul.injective)))

end Separable

/-! ### Tame and wild structure of inertia -/

section Structure

/-- **The tame quotient `G_0 / G_1` is cyclic** whenever `G_0 / G_1` is finite and `B` is a local
`A`-algebra on which `G` acts by `A`-algebra automorphisms with separable residue extension. -/
theorem isCyclic_ramificationGroupGraded_zero (A G B : Type*) [CommRing A] [IsLocalRing A]
    [Group G] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    [Finite (RamificationGroupGraded G B 0)] :
    IsCyclic (RamificationGroupGraded G B 0) := by
  -- `tameCharacterGraded` embeds `G_0 / G_1` into `(ResidueField B)ˣ`, whose finite subgroups are
  -- cyclic.
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacterGraded hϖ))
    (Units.val_injective.comp (tameCharacterGraded_injective A hϖ))

/-- In residue characteristic `p`, `p` does not divide `#(G_0 / G_1)` whenever `G_0 / G_1` is
finite and `B` is a local `A`-algebra on which `G` acts by `A`-algebra automorphisms with separable
residue extension. -/
theorem not_dvd_natCard_ramificationGroupGraded_zero (A G B : Type*) [CommRing A] [IsLocalRing A]
    [Group G] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [CharP (ResidueField B) p]
    [Finite (RamificationGroupGraded G B 0)] :
    ¬ p ∣ Nat.card (RamificationGroupGraded G B 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  rcases CharP.char_is_prime_or_zero (ResidueField B) p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    exact TauCeti.not_dvd_natCard_of_injective_units p
      (tameCharacterGraded (G := G) hϖ) (tameCharacterGraded_injective A hϖ)
  · rw [zero_dvd_iff]
    exact Nat.card_pos.ne'

/-- In residue characteristic `p`, the index `[G_0 : G_1]` is not divisible by `p` whenever
`G_0 / G_1` is finite and `B` is a local `A`-algebra on which `G` acts by `A`-algebra automorphisms
with separable residue extension. -/
theorem not_dvd_index_ramificationGroup_one (A G B : Type*) [CommRing A] [IsLocalRing A]
    [Group G] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [CharP (ResidueField B) p]
    [Finite (RamificationGroupGraded G B 0)] :
    ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index := by
  have hidx : ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index =
      Nat.card (RamificationGroupGraded G B 0) := by
    rw [Subgroup.index_eq_card, RamificationGroupGraded, zero_add]
  rw [hidx]
  exact not_dvd_natCard_ramificationGroupGraded_zero A G B p

/-- **Wild inertia is the Sylow `p`-subgroup of inertia.** When `B` is a local `A`-algebra on which
`G` acts faithfully by `A`-algebra automorphisms with separable residue extension, prime residue
characteristic `p`, and finite `G_0`, the group `G_1` viewed inside `G_0` is a Sylow
`p`-subgroup. -/
def ramificationGroupOneSylow (A G B : Type*) [CommRing A] [IsLocalRing A] [Group G]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Sylow p (ramificationGroup G B 0) :=
  ((TauCeti.IsLocalRing.isPGroup_ramificationGroup G B p (i := 1) one_pos).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one A G B p)

/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (A G B : Type*) [CommRing A] [IsLocalRing A] [Group G]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow A G B p : Subgroup (ramificationGroup G B 0)) =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) :=
  (rfl)

/-- Membership in `ramificationGroupOneSylow` is membership in `G_1`. -/
@[simp]
theorem mem_ramificationGroupOneSylow (A G B : Type*) [CommRing A] [IsLocalRing A] [Group G]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (σ : ramificationGroup G B 0) :
    σ ∈ ramificationGroupOneSylow A G B p ↔ (σ : G) ∈ ramificationGroup G B 1 := by
  rw [← SetLike.mem_coe, ← Sylow.coe_coe, ramificationGroupOneSylow_coe, SetLike.mem_coe,
    Subgroup.mem_subgroupOf]

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
instance ramificationGroupOneSylow_normal (A G B : Type*) [CommRing A] [IsLocalRing A] [Group G]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow A G B p : Subgroup (ramificationGroup G B 0)).Normal := by
  rw [ramificationGroupOneSylow_coe]
  infer_instance

/-- **Uniqueness of the wild inertia Sylow subgroup**: when `B` is a local `A`-algebra on which `G`
acts faithfully by `A`-algebra automorphisms with separable residue extension, prime residue
characteristic `p`, and finite `G_0`, the group `G_1` is the unique Sylow `p`-subgroup of `G_0`. -/
theorem eq_ramificationGroupOneSylow (A G B : Type*) [CommRing A] [IsLocalRing A] [Group G]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (Q : Sylow p (ramificationGroup G B 0)) :
    Q = ramificationGroupOneSylow A G B p := by
  let _ : Unique (Sylow p (ramificationGroup G B 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow A G B p) inferInstance
  exact Subsingleton.elim _ _

/-- When `B` is a local `A`-algebra on which `G` acts faithfully by `A`-algebra automorphisms with
separable residue extension, prime residue characteristic `p`, and finite `G_0`, the cardinality of
`G_1` is the `p`-primary part `p ^ v_p(#G_0)` of the cardinality of `G_0`. -/
theorem natCard_ramificationGroup_one (A G B : Type*) [CommRing A] [IsLocalRing A] [Group G]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Nat.card (ramificationGroup G B 1) =
      p ^ (Nat.card (ramificationGroup G B 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow A G B p)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if `p ∤ #G_0`**, when `B` is a local `A`-algebra on which
`G` acts faithfully by `A`-algebra automorphisms with separable residue extension, residue
characteristic `p`, and finite `G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (A G B : Type*)
    [CommRing A] [IsLocalRing A] [Group G] [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (p : ℕ) [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  rcases CharP.char_is_prime_or_zero (ResidueField B) p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one A G B p,
      pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
    simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]
  · have : CharZero (ResidueField B) := CharP.charP_to_charZero (ResidueField B)
    rw [ramificationGroup_eq_bot_of_charZero G B one_pos, zero_dvd_iff]
    exact iff_of_true rfl Nat.card_pos.ne'

/-- When `B` is a local `A`-algebra on which `G` acts faithfully by `A`-algebra automorphisms with
separable residue extension, residue characteristic zero, and finite `G_0`, the tame character
`tameCharacter : G_0 →* (ResidueField B)ˣ` is injective. -/
theorem tameCharacter_injective_of_charZero (A : Type*) [CommRing A] [IsLocalRing A]
    {G B : Type*} [Group G] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [CharZero (ResidueField B)]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] {ϖ : B} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacter (G := G) hϖ) :=
  (tameCharacter_injective_iff A hϖ).mpr
    (ramificationGroup_eq_bot_of_charZero G B (i := 1) one_pos)

/-- When `B` is a local `A`-algebra on which `G` acts by `A`-algebra automorphisms with separable
residue extension, a finite inertia group `G_0` with trivial wild inertia `G_1 = ⊥` is cyclic. -/
theorem isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot (A G B : Type*)
    [CommRing A] [IsLocalRing A] [Group G] [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [Finite (ramificationGroup G B 0)]
    (h : ramificationGroup G B 1 = ⊥) :
    IsCyclic (ramificationGroup G B 0) := by
  have : IsCyclic (RamificationGroupGraded G B 0) :=
    isCyclic_ramificationGroupGraded_zero A G B
  refine isCyclic_of_injective
    (QuotientGroup.mk' ((ramificationGroup G B ((0 : ℤ) + 1)).subgroupOf
      (ramificationGroup G B 0))) ?_
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', zero_add, h, Subgroup.bot_subgroupOf]

/-- When `B` is a local `A`-algebra on which `G` acts faithfully by `A`-algebra automorphisms with
separable residue extension and residue characteristic zero, every finite inertia group `G_0` is
cyclic. -/
theorem isCyclic_ramificationGroup_zero_of_charZero (A G B : Type*) [CommRing A] [IsLocalRing A]
    [Group G] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] [CharZero (ResidueField B)]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    IsCyclic (ramificationGroup G B 0) :=
  isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot A G B
    (ramificationGroup_eq_bot_of_charZero G B one_pos)

end Structure

end TauCeti.IsDiscreteValuationRing
