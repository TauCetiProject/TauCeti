/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded
import Mathlib.RingTheory.IntegralDomain

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

Composing at depth zero with `U_B^0 / U_B^1 ≃* kˣ` recovers the tame character
`TauCeti.IsLocalRing.tameCharacter : G_0 →* kˣ` and its quotient form
`TauCeti.IsLocalRing.tameCharacterGraded : G_0 / G_1 →* kˣ`. Composing at positive depth
`i = n + 1` with the uniformizer coordinate `U_B^{n+1} / U_B^{n+2} ≃+ k` of
`TauCeti.maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer` recovers the
additive coordinate `TauCeti.IsLocalRing.ramificationGroupToResidueField` from
`TauCeti/RingTheory/LocalRing/RamificationGroup/Graded.lean`.

When `B` is a local algebra over a local ring `A` whose elements `G` fixes and the residue
extension `ResidueField B / ResidueField A` is separable, membership of an element of `G_0` in
`G_i` is decided at `ϖ` alone
(`TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`), so the kernel of
`ramificationGroupToPrincipalUnitGroupGraded` is *equal* to `G_{i+1}` and each graded map `θ_i` is
injective. Together with the local-ring structure results in
`TauCeti/RingTheory/LocalRing/RamificationGroup/Graded.lean` (such as
`TauCeti.IsLocalRing.tameCharacter_injective_iff`,
`TauCeti.IsLocalRing.natCard_ramificationGroup_one`, and
`TauCeti.IsLocalRing.isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot`), this gives
the graded decomposition of inertia without assuming completeness or finiteness of the residue
field.

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

## Main results

* `TauCeti.IsDiscreteValuationRing.coe_uniformizerRatio` and
  `TauCeti.IsDiscreteValuationRing.coe_uniformizerRatio_mul`: identification with
  `uniformizerChangeUnit` and the 1-cocycle multiplication law for `uniformizerRatio`.
* `ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible` and
  `ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible`: independence of the
  choice of uniformizer.
* `tameCharacter_eq_comp_ramificationGroupToPrincipalUnitGroupGraded`,
  `tameCharacterGraded_eq_comp_ramificationGroupGradedToPrincipalUnitGroupGraded`, and
  `toAdd_ramificationGroupToResidueField_eq`: compatibility with
  `TauCeti.IsLocalRing.tameCharacter`, `TauCeti.IsLocalRing.tameCharacterGraded`, and
  `TauCeti.IsLocalRing.ramificationGroupToResidueField`.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGroupGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective`:
  exactness of the kernels and injectivity of the graded principal-unit embeddings under separable
  residue extension.

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

private theorem uniformizerChangeUnit_smul_mem_principalUnitGroup {ϖ : B} (hϖ : Irreducible ϖ)
    {i : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ (σ • ϖ) hϖ
        (hϖ.map (MulDistribMulAction.toMulEquiv B σ) : Irreducible (σ • ϖ)) ∈
      (maximalIdeal B ^ i).principalUnitGroup := by
  have hσϖ : Irreducible (σ • ϖ) := hϖ.map (MulDistribMulAction.toMulEquiv B σ)
  rw [Ideal.mem_principalUnitGroup, ← mul_mem_maximalIdeal_pow_succ_iff hϖ]
  have hmul : ϖ * ((uniformizerChangeUnit ϖ (σ • ϖ) hϖ hσϖ : B) - 1) = σ • ϖ - ϖ := by
    rw [mul_sub, mul_one, mul_uniformizerChangeUnit]
  rw [hmul]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

/-- For `σ` in the `i`-th ramification group `G_i` of a discrete valuation ring `B` and a
uniformizer `ϖ`, the unique unit `u ∈ 1 + 𝔪 ^ i` satisfying `ϖ * u = σ • ϖ`. -/
def uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) : (maximalIdeal B ^ i).principalUnitGroup :=
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
      (hϖ.map (MulDistribMulAction.toMulEquiv B (σ : G)) : Irreducible ((σ : G) • ϖ)),
    uniformizerChangeUnit_smul_mem_principalUnitGroup hϖ σ.property⟩

/-- As a unit of `B`, `uniformizerRatio i hϖ σ` is the uniformizer change unit from `ϖ` to
`σ • ϖ`. -/
theorem coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ σ : Bˣ) =
      uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
        (hϖ.map (MulDistribMulAction.toMulEquiv B (σ : G)) : Irreducible ((σ : G) • ϖ)) :=
  -- `(rfl)`, not `rfl`, because the body of `uniformizerRatio` is not `@[expose]`d.
  (rfl)

/-- The unit `uniformizerRatio i hϖ σ` carries `ϖ` to `σ • ϖ` by right multiplication. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ := by
  have hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.map (MulDistribMulAction.toMulEquiv B (σ : G))
  rw [coe_uniformizerRatio, mul_uniformizerChangeUnit (hπ' := hσϖ)]

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
  rw [mul_coe_uniformizerRatio, Subgroup.coe_mul, mul_smul]
  simp [← mul_assoc, ← smul_mul']

/-- **1-cocycle law** in `B` for `uniformizerRatio`. -/
theorem val_coe_uniformizerRatio_mul (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    ((uniformizerRatio i hϖ (σ * τ) : Bˣ) : B) =
      ((uniformizerRatio i hϖ σ : Bˣ) : B) *
        (σ : G) • ((uniformizerRatio i hϖ τ : Bˣ) : B) := by
  rw [coe_uniformizerRatio_mul]
  simp

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
            simp [smul_mul', ← mul_assoc]
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

/-! ### Compatibility with the local-ring tame character and residue coordinate -/

/-- The tame character `TauCeti.IsLocalRing.tameCharacter` factors through the depth-zero
principal-unit homomorphism `ramificationGroupToPrincipalUnitGroupGraded 0 hϖ`, for any
uniformizer `ϖ`. -/
theorem tameCharacter_eq_comp_ramificationGroupToPrincipalUnitGroupGraded
    {ϖ : B} (hϖ : Irreducible ϖ) :
    IsLocalRing.tameCharacter G B =
      (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
        (ramificationGroupToPrincipalUnitGroupGraded 0 hϖ) := by
  refine MonoidHom.ext fun σ ↦ Units.ext ?_
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGroupGraded_apply (i := 0),
    maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits_mk]
  simpa using IsLocalRing.coe_tameCharacter_of_smul_eq_mul hϖ
    (mul_coe_uniformizerRatio 0 hϖ σ).symm

/-- The graded tame character `TauCeti.IsLocalRing.tameCharacterGraded` factors through
`ramificationGroupGradedToPrincipalUnitGroupGraded 0 hϖ`, for any uniformizer `ϖ`. -/
theorem tameCharacterGraded_eq_comp_ramificationGroupGradedToPrincipalUnitGroupGraded
    {ϖ : B} (hϖ : Irreducible ϖ) :
    IsLocalRing.tameCharacterGraded G B =
      (maximalIdealPrincipalUnitGroupPowGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
        (ramificationGroupGradedToPrincipalUnitGroupGraded 0 hϖ) := by
  refine MonoidHom.ext fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | H σ =>
    rw [IsLocalRing.tameCharacterGraded_mk,
      tameCharacter_eq_comp_ramificationGroupToPrincipalUnitGroupGraded hϖ,
      MonoidHom.comp_apply, ramificationGroupToPrincipalUnitGroupGraded_apply,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ramificationGroupGradedToPrincipalUnitGroupGraded_mk]

/-- For any uniformizer `ϖ`, the positive-depth residue coordinate
`TauCeti.IsLocalRing.ramificationGroupToResidueField hϖ n` agrees with
`ramificationGroupToPrincipalUnitGroupGraded (n + 1) hϖ` composed with the uniformizer
coordinate on `(1 + 𝔪 ^ (n + 1)) / (1 + 𝔪 ^ (n + 2))`. -/
theorem toAdd_ramificationGroupToResidueField_eq (n : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B ((n : ℤ) + 1)) :
    (IsLocalRing.ramificationGroupToResidueField (G := G) hϖ n σ).toAdd =
      maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ
        (Additive.ofMul
          (ramificationGroupToPrincipalUnitGroupGraded (n + 1) hϖ
            ⟨(σ : G), (Nat.cast_succ (R := ℤ) n).symm ▸ σ.property⟩)) := by
  set σ' : ramificationGroup G B ((n + 1 : ℕ) : ℤ) :=
    ⟨(σ : G), (Nat.cast_succ (R := ℤ) n).symm ▸ σ.property⟩
  have hmem : ((uniformizerRatio (n + 1) hϖ σ' : Bˣ) : B) - 1 ∈ Ideal.span {ϖ} ^ (n + 1) :=
    hϖ.maximalIdeal_eq ▸ Ideal.mem_principalUnitGroup.mp (uniformizerRatio (n + 1) hϖ σ').property
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hmove : (σ : G) • ϖ - ϖ = ϖ ^ (n + 2) * y := by
    change (σ' : G) • ϖ - ϖ = ϖ ^ (n + 2) * y
    rw [← mul_coe_uniformizerRatio_sub_one (n + 1) hϖ σ', hy, mul_comm (ϖ ^ (n + 1)) y]
    ring
  rw [IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ hmove,
    ramificationGroupToPrincipalUnitGroupGraded_apply, toAdd_ofAdd,
    maximalIdealPrincipalUnitGroupPowGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
      n ϖ hϖ _ y (hy.trans (mul_comm _ _))]

end UniformizerRatio

/-! ### Exactness and graded embeddings for separable residue extensions -/

section Separable

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

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
    IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ.maximalIdeal_eq hσ₀]
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

end Separable

end TauCeti.IsDiscreteValuationRing
