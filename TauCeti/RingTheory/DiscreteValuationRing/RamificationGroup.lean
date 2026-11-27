/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded

/-!
# Graded embeddings and tame/wild structure of ramification groups on a discrete valuation ring

Let a group `G` act by ring automorphisms on a discrete valuation ring `B` with maximal ideal `𝔪`
and residue field `k = ResidueField B`. Fixing a uniformizer `ϖ` of `B`, every `σ ∈ G_i` sends `ϖ`
to another uniformizer `σ • ϖ = ϖ * u_σ` with `u_σ ∈ (𝔪 ^ i).principalUnitGroup` (`Bˣ` for `i = 0`
and `1 + 𝔪 ^ i` for `i ≥ 1`). Passing to the successive quotient
`PrincipalUnitGroupGraded B i` yields a group homomorphism

`ramificationGroup G B i →* PrincipalUnitGroupGraded B i`

that is independent of the choice of uniformizer `ϖ` and kills `G_{i+1}`, hence descends to a
canonical homomorphism `RamificationGroupGraded G B i →* PrincipalUnitGroupGraded B i`. Composing
with the depth-`0` reduction isomorphism recovers `TauCeti.IsLocalRing.tameCharacter` and
`TauCeti.IsLocalRing.tameCharacterGraded`, while at positive depth `n + 1` composing with the
uniformizer coordinate recovers `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`.

Nothing in the construction of these homomorphisms, the conjugation equivariance of
`TauCeti.IsLocalRing.tameCharacter`, `TauCeti.IsLocalRing.tameCharacterGraded`, and
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`, or the characteristic-zero structure of
`G_0` requires a base ring, a fraction field, completeness, or residue-field finiteness. In residue
characteristic zero, any finite-order element of `G_0` that moves a uniformizer by `𝔪 ^ 2` lies in
`G_1`, so whenever `G` acts faithfully and `G_0` is finite, wild inertia vanishes
(`TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero`), the tame character is injective,
and `G_0` is cyclic.

When `G` acts by `R`-algebra automorphisms over a local ring `R` such that the residue extension
`ResidueField B / ResidueField R` is separable, the uniformizer criterion
(`TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`) shows that the kernel of
the `i`-th quotient homomorphism is `G_{i+1}` and all graded homomorphisms into
`PrincipalUnitGroupGraded B i` are injective, so `G_0 / G_1` is commutative and `G_0` acts
trivially on `G_0 / G_1` by conjugation (while at positive depth `i = n + 1`, commutativity holds
base-free via `TauCeti.IsLocalRing.instIsMulCommutativeRamificationGroupGradedNatCastSucc`).

The uniformizer-ratio homomorphism (`uniformizerRatio`,
`ramificationGroupToPrincipalUnitGroupGradedOf`) and its proof of independence of the uniformizer
(`ramificationGroupToPrincipalUnitGroupGradedOf_eq`) are adapted from
`TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`. The
conjugation-equivariance formulas (`TauCeti.IsLocalRing.tameCharacter_conj`,
`TauCeti.IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj`, and
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_conj`) are adapted from
`TauCeti/NumberTheory/LocalField/UnitFiltration/Conjugation.lean`.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u_σ ∈ (𝔪 ^ i).principalUnitGroup`
  satisfying `ϖ * u_σ = σ • ϖ`, for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded`: the
  uniformizer-independent homomorphisms `G_i →* PrincipalUnitGroupGraded B i` and
  `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i`.

## Main results

* `TauCeti.IsDiscreteValuationRing.coe_uniformizerRatio_mul`: the 1-cocycle law for
  `uniformizerRatio`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter_eq_principalUnitGroupGraded`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_eq_principalUnitGroupGraded`, and
  `TauCeti.IsDiscreteValuationRing.toAdd_ramificationGroupGradedToResidueField_eq`: bridges
  factoring `TauCeti.IsLocalRing.tameCharacter`, `TauCeti.IsLocalRing.tameCharacterGraded`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` through
  `PrincipalUnitGroupGraded B i`.
* `TauCeti.IsLocalRing.tameCharacter_conj`,
  `TauCeti.IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_conj`: conjugation-equivariance
  formulas on depth `0` and positive-depth graded pieces for any discrete valuation ring.
* `TauCeti.IsDiscreteValuationRing.smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer`:
  propagation of `σ • x - x ∈ 𝔪 ^ m` to `𝔪 ^ (m + 1)` on `𝔪` from a uniformizer.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_one_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.ker_tameCharacter_of_charZero`, and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue
  characteristic zero, without any base ring or separability assumption, a faithful action with
  finite `G_0` has injective tame character and cyclic inertia `G_0`.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGroupGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.isMulCommutative_ramificationGroupGraded_zero`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedConj_zero`: under separable residue
  extension over `R`, the graded maps into `PrincipalUnitGroupGraded B i` are injective,
  `G_0 / G_1` is commutative, and `G_0` acts trivially on `G_0 / G_1`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7 and 9.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 1 and Corollaries 1–2.
-/

public section
noncomputable section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti

namespace IsDiscreteValuationRing

section Homomorphisms

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]
variable {ϖ : B} {i : ℕ} {σ : G}

/-- Propagating congruence along a uniformizer `ϖ`: if `σ • ϖ - ϖ ∈ 𝔪 ^ (m + 1)` and
`σ • y - y ∈ 𝔪 ^ m` for every `y : B`, then `σ • w - w ∈ 𝔪 ^ (m + 1)` for every `w ∈ 𝔪`. -/
theorem smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer {m : ℕ} (hϖ : Irreducible ϖ)
    (hϖm : σ • ϖ - ϖ ∈ maximalIdeal B ^ (m + 1)) (hB : ∀ y : B, σ • y - y ∈ maximalIdeal B ^ m)
    {w : B} (hw : w ∈ maximalIdeal B) :
    σ • w - w ∈ maximalIdeal B ^ (m + 1) := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hw
  obtain ⟨y, rfl⟩ := hw
  rw [smul_mul_sub_mul]
  refine add_mem (Ideal.mul_mem_right _ _ hϖm) ?_
  rw [pow_succ']
  exact Ideal.mul_mem_mul ((mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) (hB y)

/-- For `σ ∈ G_i` and a uniformizer `ϖ`, the change unit sending `ϖ` to `σ • ϖ` lies in
`(𝔪 ^ i).principalUnitGroup`. -/
theorem uniformizerChangeUnit_smul_mem_principalUnitGroup (hϖ : Irreducible ϖ)
    (hσϖ : Irreducible (σ • ϖ)) (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ (σ • ϖ) hϖ hσϖ ∈ (maximalIdeal B ^ i).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup, ← hϖ.mul_mem_maximalIdeal_pow_succ_iff, mul_sub, mul_one,
    mul_uniformizerChangeUnit]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

variable (i) in
/-- The unit `u_σ ∈ (𝔪 ^ i).principalUnitGroup` characterized by `ϖ * u_σ = σ • ϖ`, for a
uniformizer `ϖ` and `σ ∈ G_i`. -/
def uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    (maximalIdeal B ^ i).principalUnitGroup :=
  have hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.map (MulSemiringAction.toRingAut G B (σ : G))
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ,
    uniformizerChangeUnit_smul_mem_principalUnitGroup hϖ hσϖ σ.property⟩

/-- Multiplying `ϖ` on the right by `uniformizerRatio i hϖ σ` yields `σ • ϖ`. -/
@[simp]
theorem mul_uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ :=
  mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

/-- The uniformizer ratio of the identity element is `1`. -/
@[simp]
theorem uniformizerRatio_one (hϖ : Irreducible ϖ) :
    uniformizerRatio i hϖ (1 : ramificationGroup G B (i : ℤ)) = 1 := by
  ext
  exact mul_left_cancel₀ hϖ.ne_zero (by simp)

/-- `uniformizerRatio i hϖ σ` lies one step deeper in the principal-unit filtration precisely when
`σ` moves `ϖ` by an element of `𝔪 ^ (i + 2)`. -/
theorem coe_uniformizerRatio_mem_principalUnitGroup_succ_iff (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ σ : Bˣ) ∈ (maximalIdeal B ^ (i + 1)).principalUnitGroup ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [Ideal.mem_principalUnitGroup, ← hϖ.mul_mem_maximalIdeal_pow_succ_iff, mul_sub,
    mul_one, mul_uniformizerRatio]

/-- Cocycle relation for `uniformizerRatio`: `u_{σ * τ} = u_σ * σ(u_τ)` in `Bˣ`. -/
theorem coe_uniformizerRatio_mul (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  calc ϖ * ((uniformizerRatio i hϖ (σ * τ) : Bˣ) : B)
      = (σ : G) • ((τ : G) • ϖ) := by simp [mul_smul]
    _ = (σ : G) • (ϖ * ((uniformizerRatio i hϖ τ : Bˣ) : B)) := by rw [mul_uniformizerRatio]
    _ = ((σ : G) • ϖ) * ((σ : G) • ((uniformizerRatio i hϖ τ : Bˣ) : B)) := smul_mul' _ _ _
    _ = ϖ * (((uniformizerRatio i hϖ σ : Bˣ) *
          Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
            (uniformizerRatio i hϖ τ : Bˣ) : Bˣ) : B) := by
        rw [← mul_uniformizerRatio hϖ σ, mul_assoc]
        simp

private def ramificationGroupToPrincipalUnitGroupGradedOf (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) fun σ τ ↦ by
    symm
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_mul, coe_uniformizerRatio_mul]
    have hcancel :
        ((uniformizerRatio i hϖ σ : Bˣ) * (uniformizerRatio i hϖ τ : Bˣ))⁻¹ *
          ((uniformizerRatio i hϖ σ : Bˣ) *
            Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
              (uniformizerRatio i hϖ τ : Bˣ)) =
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) * (uniformizerRatio i hϖ τ : Bˣ)⁻¹ := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_comm]
    rw [hcancel]
    exact unitsMap_mul_inv_mem_principalUnitGroup_natCast σ.property (uniformizerRatio i hϖ τ : Bˣ)

private theorem ramificationGroupToPrincipalUnitGroupGradedOf_eq {i : ℕ} {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToPrincipalUnitGroupGradedOf (G := G) i hϖ =
      ramificationGroupToPrincipalUnitGroupGradedOf (G := G) i hϖ' := by
  set a : Bˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have ha : ϖ * (a : B) = ϖ' := mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  refine MonoidHom.ext fun σ ↦ ?_
  simp only [ramificationGroupToPrincipalUnitGroupGradedOf, MonoidHom.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hrel : a * (uniformizerRatio i hϖ' σ : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
    apply Units.ext
    apply mul_left_cancel₀ hϖ.ne_zero
    calc ϖ * ((a * (uniformizerRatio i hϖ' σ : Bˣ) : Bˣ) : B)
        = ϖ' * ((uniformizerRatio i hϖ' σ : Bˣ) : B) := by rw [Units.val_mul, ← mul_assoc, ha]
      _ = (σ : G) • (ϖ * (a : B)) := by rw [mul_uniformizerRatio, ha]
      _ = ((σ : G) • ϖ) * ((σ : G) • (a : B)) := smul_mul' _ _ _
      _ = ϖ * (((uniformizerRatio i hϖ σ : Bˣ) *
            Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a : Bˣ) : B) := by
          rw [← mul_uniformizerRatio hϖ σ, mul_assoc]
          simp
  have hratio : (uniformizerRatio i hϖ σ : Bˣ)⁻¹ * (uniformizerRatio i hϖ' σ : Bˣ) =
      Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul]
    apply mul_right_cancel (b := a)
    rw [mul_comm _ a, hrel, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  rw [hratio]
  exact unitsMap_mul_inv_mem_principalUnitGroup_natCast σ.property a

variable (G B i) in
/-- The **quotient homomorphism** `G_i →* PrincipalUnitGroupGraded B i` sending `σ` to the class of
the unit `u_σ` with `ϖ * u_σ = σ • ϖ` for any uniformizer `ϖ`. It is independent of `ϖ` and kills
`G_{i+1}`. -/
def ramificationGroupToPrincipalUnitGroupGraded :
    ramificationGroup G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  ramificationGroupToPrincipalUnitGroupGradedOf i
    (_root_.IsDiscreteValuationRing.exists_irreducible B).choose_spec

/-- Evaluating `ramificationGroupToPrincipalUnitGroupGraded` at `σ` using any uniformizer `ϖ`
yields the class of `uniformizerRatio i hϖ σ`. -/
theorem ramificationGroupToPrincipalUnitGroupGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToPrincipalUnitGroupGraded G B i σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupToPrincipalUnitGroupGraded,
    ramificationGroupToPrincipalUnitGroupGradedOf_eq (G := G) _ hϖ]
  rfl

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToPrincipalUnitGroupGraded G B i`
precisely when `σ • ϖ - ϖ ∈ 𝔪 ^ (i + 2)` for a uniformizer `ϖ`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToPrincipalUnitGroupGraded G B i).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGroupGraded_apply hϖ,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    coe_uniformizerRatio_mem_principalUnitGroup_succ_iff]

variable (G B i) in
/-- The next ramification subgroup `G_{i+1}` lies in the kernel of
`ramificationGroupToPrincipalUnitGroupGraded G B i`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToPrincipalUnitGroupGraded G B i).ker := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

variable (G B i) in
/-- The induced homomorphism `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i` on successive
quotients. It is injective whenever the residue extension over a `G`-invariant local subring is
separable (`ramificationGroupGradedToPrincipalUnitGroupGraded_injective`). -/
def ramificationGroupGradedToPrincipalUnitGroupGraded :
    RamificationGroupGraded G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGroupGraded G B i)
    (ramificationGroup_succ_subgroupOf_le_ker G B i)

variable (G B i) in
/-- `ramificationGroupGradedToPrincipalUnitGroupGraded` is the quotient lift of
`ramificationGroupToPrincipalUnitGroupGraded`. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_def :
    ramificationGroupGradedToPrincipalUnitGroupGraded G B i =
      QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGroupGraded G B i)
        (ramificationGroup_succ_subgroupOf_le_ker G B i) :=
  (rfl)

/-- Evaluating `ramificationGroupGradedToPrincipalUnitGroupGraded` on the class of `σ` agrees with
`ramificationGroupToPrincipalUnitGroupGraded`. -/
@[simp]
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded G B i (QuotientGroup.mk σ) =
      ramificationGroupToPrincipalUnitGroupGraded G B i σ :=
  QuotientGroup.lift_mk _ _ _

/-- Evaluating `ramificationGroupGradedToPrincipalUnitGroupGraded` on the class of `σ` using any
uniformizer `ϖ` yields the class of `uniformizerRatio i hϖ σ`. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk_eq_uniformizerRatio
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded G B i (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupGradedToPrincipalUnitGroupGraded_mk,
    ramificationGroupToPrincipalUnitGroupGraded_apply hϖ]

/-! ### Bridges to `TauCeti.IsLocalRing` maps and conjugation equivariance -/

variable (G B) in
/-- `TauCeti.IsLocalRing.tameCharacter` factors `ramificationGroupToPrincipalUnitGroupGraded`
at depth `0` through `TauCeti.IsLocalRing.principalUnitGroupGradedZeroEquivResidueFieldUnits`. -/
theorem tameCharacter_eq_principalUnitGroupGraded :
    IsLocalRing.tameCharacter G B =
      (principalUnitGroupGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
        (ramificationGroupToPrincipalUnitGroupGraded G B 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  refine MonoidHom.ext fun σ ↦ Units.ext ?_
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGroupGraded_apply (i := 0) hϖ,
    principalUnitGroupGradedZeroEquivResidueFieldUnits_mk]
  exact IsLocalRing.coe_tameCharacter_of_smul_eq_mul hϖ (mul_uniformizerRatio hϖ σ).symm

variable (G B) in
/-- `TauCeti.IsLocalRing.tameCharacterGraded` factors
`ramificationGroupGradedToPrincipalUnitGroupGraded` at depth `0` through
`TauCeti.IsLocalRing.principalUnitGroupGradedZeroEquivResidueFieldUnits`. -/
theorem tameCharacterGraded_eq_principalUnitGroupGraded :
    IsLocalRing.tameCharacterGraded G B =
      (principalUnitGroupGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
        (ramificationGroupGradedToPrincipalUnitGroupGraded G B 0) := by
  refine MonoidHom.ext fun x ↦ QuotientGroup.induction_on x fun σ ↦ ?_
  rw [IsLocalRing.tameCharacterGraded_mk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupGradedToPrincipalUnitGroupGraded_mk,
    ← MulEquiv.coe_toMonoidHom, ← MonoidHom.comp_apply,
    ← tameCharacter_eq_principalUnitGroupGraded]

/-- `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` factors
`ramificationGroupGradedToPrincipalUnitGroupGraded` at depth `n + 1` through
`TauCeti.principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer`. -/
theorem toAdd_ramificationGroupGradedToResidueField_eq (n : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    (IsLocalRing.ramificationGroupGradedToResidueField hϖ n τ).toAdd =
      principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ
        (Additive.ofMul
          (ramificationGroupGradedToPrincipalUnitGroupGraded G B (n + 1)
            (ramificationGroupGradedCongr G B (Nat.cast_succ n).symm τ))) := by
  induction τ using QuotientGroup.induction_on with
  | H σ =>
    let σ' : ramificationGroup G B ((n + 1 : ℕ) : ℤ) :=
      ⟨(σ : G), (Nat.cast_succ (R := ℤ) n).symm ▸ σ.property⟩
    have hmove : (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (n + 2) := by
      have h := mem_ramificationGroup_iff.mp σ.property ϖ
      rwa [(by omega : ((n : ℤ) + 1 + 1).toNat = n + 2)] at h
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hdiff : ((uniformizerRatio (n + 1) hϖ σ' : Bˣ) : B) - 1 = y * ϖ ^ (n + 1) := by
      apply mul_left_cancel₀ hϖ.ne_zero
      calc ϖ * (((uniformizerRatio (n + 1) hϖ σ' : Bˣ) : B) - 1)
          = (σ' : G) • ϖ - ϖ := by rw [mul_sub, mul_uniformizerRatio, mul_one]
        _ = y * ϖ ^ (n + 2) := hy.symm
        _ = ϖ * (y * ϖ ^ (n + 1)) := by rw [pow_succ']; ring
    rw [IsLocalRing.ramificationGroupGradedToResidueField_mk,
      IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ
        (by rw [← hy, mul_comm]),
      toAdd_ofAdd, ramificationGroupGradedCongr_mk,
      ramificationGroupGradedToPrincipalUnitGroupGraded_mk_eq_uniformizerRatio (i := n + 1) hϖ]
    exact (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
      n ϖ hϖ _ y hdiff).symm

end Homomorphisms

end IsDiscreteValuationRing

namespace IsLocalRing

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

/-- **Conjugation equivariance of the tame character** (Serre, *Local Fields*, IV §2,
Proposition 9): conjugating `σ ∈ G_0` by `g ∈ G` acts on `tameCharacter G B σ` via the induced
action of `g` on `ResidueField B`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G B (0 : ℤ)) :
    (tameCharacter G B (MulAut.conjNormal g σ) : ResidueField B) =
      g • (tameCharacter G B σ : ResidueField B) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hgϖ : Irreducible (g⁻¹ • ϖ) := hϖ.map (MulSemiringAction.toRingAut G B g⁻¹)
  rw [coe_tameCharacter_of_smul_eq_mul hgϖ
      (IsDiscreteValuationRing.mul_uniformizerRatio hgϖ σ).symm,
    ← ResidueField.residue_smul]
  refine coe_tameCharacter_of_smul_eq_mul hϖ ?_
  calc (MulAut.conjNormal g σ : G) • ϖ
      = g • ((σ : G) • (g⁻¹ • ϖ)) := by
        rw [MulAut.conjNormal_apply, mul_smul, mul_smul]
    _ = g • (g⁻¹ • ϖ * ((IsDiscreteValuationRing.uniformizerRatio 0 hgϖ σ : Bˣ) : B)) := by
        rw [IsDiscreteValuationRing.mul_uniformizerRatio]
    _ = g • (g⁻¹ • ϖ) * g • ((IsDiscreteValuationRing.uniformizerRatio 0 hgϖ σ : Bˣ) : B) :=
        smul_mul' g _ _
    _ = ϖ * g • ((IsDiscreteValuationRing.uniformizerRatio 0 hgϖ σ : Bˣ) : B) := by
        rw [smul_inv_smul]

/-- Conjugation by `g ∈ G` on `G_0 / G_1` corresponds under `tameCharacterGraded` to the induced
action of `g` on `ResidueField B`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (x : RamificationGroupGraded G B (0 : ℤ)) :
    (tameCharacterGraded G B (ramificationGroupGradedConj G B g 0 x) : ResidueField B) =
      g • (tameCharacterGraded G B x : ResidueField B) := by
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-- **Conjugation action formula on positive ramification quotients** (Serre, *Local Fields*,
IV §2, Proposition 9): in the residue coordinate determined by `ϖ`, conjugation by `σ ∈ G_0` acts
on `G_{n+1} / G_{n+2}` as multiplication by `(tameCharacter G B σ) ^ (n + 1)`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B 0) (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    (ramificationGroupGradedToResidueField hϖ n
        (ramificationGroupGradedConj G B (σ : G) ((n : ℤ) + 1) τ)).toAdd =
      (tameCharacter G B σ : ResidueField B) ^ (n + 1) *
        (ramificationGroupGradedToResidueField hϖ n τ).toAdd := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let ϖ' : B := g⁻¹ • ϖ
    have hϖ' : Irreducible ϖ' := hϖ.map (MulSemiringAction.toRingAut G B g⁻¹)
    have hmove : (τ : G) • ϖ' - ϖ' ∈ maximalIdeal B ^ (n + 2) :=
      mem_ramificationGroup_add_one_iff.mp τ.property ϖ'
    rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord :
        (ramificationGroupToResidueField hϖ' n τ).toAdd = residue B y := by
      rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ' (by rw [← hy, mul_comm]),
        toAdd_ofAdd]
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G B ((n : ℤ) + 1)) : G) • ϖ - ϖ =
          ϖ ^ (n + 2) * (g • y) := by
      calc
        _ = g • ((τ : G) • ϖ' - ϖ') := by
          simp [ϖ', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * ϖ' ^ (n + 2)) := by rw [hy]
        _ = ϖ ^ (n + 2) * (g • y) := by simp [ϖ', smul_mul', smul_pow', mul_comm]
    have hconjCoord :
        (ramificationGroupToResidueField hϖ n (MulAut.conjNormal g τ)).toAdd =
          residue B (g • y) := by
      rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ hconjMove, toAdd_ofAdd]
    have hresidue : residue B (g • y) = residue B y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G B σ.property y
    set a : Bˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
    have hprodB : ((IsDiscreteValuationRing.uniformizerRatio 0 hϖ σ : Bˣ) : B) * (g • (a : B)) =
        1 := by
      apply mul_left_cancel₀ hϖ.ne_zero
      calc ϖ * (((IsDiscreteValuationRing.uniformizerRatio 0 hϖ σ : Bˣ) : B) * (g • (a : B)))
          = (g • ϖ) * (g • (a : B)) := by
            rw [← mul_assoc, IsDiscreteValuationRing.mul_uniformizerRatio]
        _ = g • (ϖ * (a : B)) := (smul_mul' g _ _).symm
        _ = g • ϖ' := by rw [mul_uniformizerChangeUnit]
        _ = ϖ * 1 := by simp [ϖ']
    have hprod : (tameCharacter G B σ : ResidueField B) * residue B (a : B) = 1 := by
      rw [coe_tameCharacter_of_smul_eq_mul hϖ
          (IsDiscreteValuationRing.mul_uniformizerRatio hϖ σ).symm,
        ← residue_smul_eq_of_mem_ramificationGroup_zero G B σ.property (a : B),
        ← map_mul, hprodB, map_one]
    have hchange := toAdd_ramificationGroupToResidueField_of_mul_eq hϖ hϖ'
      (mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ') τ
    rw [ramificationGroupGradedConj_mk, ramificationGroupGradedToResidueField_mk,
      ramificationGroupGradedToResidueField_mk, hconjCoord, hresidue, ← hτcoord, hchange,
      ← mul_assoc, ← mul_pow, hprod, one_pow, one_mul]

end IsLocalRing

namespace IsDiscreteValuationRing

section CharZero

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

/-- In residue characteristic zero, a finite-order inertia element `σ ∈ G_0` that moves a
uniformizer `ϖ` by an element of `𝔪 ^ 2` lies in wild inertia `G_1`, with no base ring or
separability assumption. -/
theorem mem_ramificationGroup_one_of_charZero [CharZero (ResidueField B)]
    {ϖ : B} (hϖ : Irreducible ϖ) {σ : G} (hσ : σ ∈ ramificationGroup G B 0)
    (hfin : IsOfFinOrder σ) (hϖ2 : σ • ϖ - ϖ ∈ maximalIdeal B ^ 2) :
    σ ∈ ramificationGroup G B 1 := by
  have h1 : σ ∈ (maximalIdeal B ^ 2).inertia G :=
    mem_inertia_of_forall_mem_of_pow_mem
      (Ideal.mem_inertia.mpr (mem_ramificationGroup_zero_iff.mp hσ))
      (fun w hw ↦ smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer hϖ hϖ2
        (fun y ↦ by simpa only [pow_one] using mem_ramificationGroup_zero_iff.mp hσ y) hw)
      (Nat.cast_ne_zero.mpr hfin.orderOf_pos.ne')
      (by rw [pow_orderOf_eq_one]; exact one_mem _)
  simpa [ramificationGroup_def] using h1

variable (G B) in
/-- **In residue characteristic zero, the tame character is injective** whenever `G` acts faithfully
on `B` and `G_0` is finite, with no base ring or separability assumption. -/
theorem ker_tameCharacter_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    (IsLocalRing.tameCharacter G B).ker = ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  rw [eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker, tameCharacter_eq_one_iff_smul_sub_mem hϖ] at hσ
  have h1 : (σ : G) ∈ ramificationGroup G B 1 :=
    mem_ramificationGroup_one_of_charZero hϖ σ.property
      ((ramificationGroup G B 0).subtype.isOfFinOrder (isOfFinOrder_of_finite σ)) hσ
  have : Finite (ramificationGroup G B 1) :=
    Finite.of_injective
      (Subgroup.inclusion (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)))
      (Subgroup.inclusion_injective _)
  rw [ramificationGroup_eq_bot_of_charZero one_pos (iInf_ramificationGroup_eq_bot G B)] at h1
  exact Subtype.ext h1

/-- **Inertia `G_0` is cyclic in residue characteristic zero**, whenever `G` acts faithfully on `B`
and `G_0` is finite, with no base ring or separability assumption. -/
theorem isCyclic_ramificationGroup_zero_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    IsCyclic (ramificationGroup G B 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (IsLocalRing.tameCharacter G B))
    (Units.val_injective.comp
      ((MonoidHom.ker_eq_bot_iff _).mp (ker_tameCharacter_of_charZero G B)))

end CharZero

section Separable

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]
variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R B] [IsLocalHom (algebraMap R B)]
  [SMulCommClass G R B] [Algebra.IsSeparable (ResidueField R) (ResidueField B)]
variable {i : ℕ}

include R

variable (G B i) in
/-- **The kernel of the `i`-th quotient homomorphism is `G_{i+1}`**, when the residue extension
over `R` is separable. -/
theorem ker_ramificationGroupToPrincipalUnitGroupGraded :
    (ramificationGroupToPrincipalUnitGroupGraded G B i).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker G B i)
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff hϖ] at hσ
  have hσ0 : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.property
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ.maximalIdeal_eq hσ0]
  exact hσ

variable (G B i) in
/-- **The graded homomorphism `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i` is injective**, when
the residue extension over `R` is separable. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_injective :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGroupGraded G B i) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGroupGraded G B R i).symm

/-! ### Tame and wild structure of `G_0` and `G_1` -/

variable (G B) in
/-- The tame quotient `G_0 / G_1` is commutative when the residue extension over `R` is
separable: it embeds into `PrincipalUnitGroupGraded B 0`, a quotient of `Bˣ`. (At positive depth
`i = n + 1`, commutativity holds without `R` or DVR hypotheses via
`TauCeti.IsLocalRing.instIsMulCommutativeRamificationGroupGradedNatCastSucc`.) -/
theorem isMulCommutative_ramificationGroupGraded_zero :
    IsMulCommutative (RamificationGroupGraded G B (0 : ℤ)) :=
  let hinj := ramificationGroupGradedToPrincipalUnitGroupGraded_injective G B R 0
  IsMulCommutative.of_comm fun _ _ ↦
    hinj (by rw [map_mul, map_mul]; exact mul_comm (G := PrincipalUnitGroupGraded B 0) _ _)

/-- Conjugation by an inertia element `σ ∈ G_0` acts trivially on the tame quotient `G_0 / G_1`,
when the residue extension over `R` is separable. (Not marked `@[simp]` because `R` does not
appear in the left-hand side; once `isMulCommutative_ramificationGroupGraded_zero G B R` is in
scope, `TauCeti.IsLocalRing.ramificationGroupGradedConj_self` simplifies this automatically.) -/
theorem ramificationGroupGradedConj_zero (σ : ramificationGroup G B 0)
    (τ : RamificationGroupGraded G B (0 : ℤ)) :
    ramificationGroupGradedConj G B (σ : G) 0 τ = τ := by
  have := isMulCommutative_ramificationGroupGraded_zero G B R
  exact ramificationGroupGradedConj_self G B 0 σ τ

end Separable

end IsDiscreteValuationRing

end TauCeti
