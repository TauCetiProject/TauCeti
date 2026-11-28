/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

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
with the depth-`0` reduction isomorphism defines `TauCeti.IsLocalRing.tameCharacter` and
`TauCeti.IsLocalRing.tameCharacterGraded`, while at positive depth `n + 1` composing with the
uniformizer coordinate defines `TauCeti.IsLocalRing.ramificationGroupToResidueField` and
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`.

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
* `TauCeti.IsLocalRing.tameCharacter` and `TauCeti.IsLocalRing.tameCharacterGraded`: the tame
  character `G_0 →* kˣ` and its factorization through `G_0 / G_1`.
* `TauCeti.IsLocalRing.ramificationGroupToResidueField` and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`: the positive-depth residue
  coordinates `G_{n+1} →* Multiplicative k` and `G_{n+1} / G_{n+2} →* Multiplicative k`.

## Main results

* `TauCeti.IsDiscreteValuationRing.coe_uniformizerRatio_mul`: the 1-cocycle law for
  `uniformizerRatio`.
* `TauCeti.IsLocalRing.coe_tameCharacter_of_smul_eq_mul`,
  `TauCeti.IsLocalRing.ker_tameCharacter`, `TauCeti.IsLocalRing.tameCharacterGraded_injective`,
  `TauCeti.IsLocalRing.isCyclic_ramificationGroupGraded_zero`, and
  `TauCeti.IsLocalRing.not_dvd_index_ramificationGroup_one`: evaluation, kernel, injectivity,
  cyclicity, and coprime index of the tame quotient.
* `TauCeti.IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq`,
  `TauCeti.IsLocalRing.toAdd_ramificationGroupToResidueField_of_mul_eq`,
  `TauCeti.IsLocalRing.ker_ramificationGroupToResidueField`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_injective`: evaluation, uniformizer
  change, kernel, and injectivity of the positive-depth residue coordinates.
* `TauCeti.IsLocalRing.tameCharacter_conj`,
  `TauCeti.IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_conj`: conjugation-equivariance
  formulas on depth `0` and positive-depth graded pieces for any discrete valuation ring.
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
    ramificationGroupToPrincipalUnitGroupGradedOf_eq (G := G) _ hϖ,
    ramificationGroupToPrincipalUnitGroupGradedOf, MonoidHom.mk'_apply]

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

end Homomorphisms

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

namespace IsLocalRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S]
  [_root_.IsDiscreteValuationRing S] [MulSemiringAction G S]

/-! ### The tame character -/

variable (G S) in
/-- The **tame character** `G_0 →* kˣ` of a group acting on a discrete valuation ring: it sends
`σ` to the residue of the unit `c` with `σ π = π * c`, for any uniformizer `π`
(`TauCeti.IsLocalRing.coe_tameCharacter_of_smul_eq_mul`). Its kernel contains `G_1`, with
equality for a separable residue extension (`TauCeti.IsLocalRing.ker_tameCharacter`). -/
noncomputable def tameCharacter : ramificationGroup G S 0 →* (ResidueField S)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits S).toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded G S 0)

/-- **The tame character at a uniformizer**: if `σ π = π * c` for a uniformizer `π`, then the tame
character of `σ` is the residue of `c`. In particular it does not depend on the uniformizer. -/
theorem coe_tameCharacter_of_smul_eq_mul {π c : S} (hπ : Irreducible π)
    {σ : ramificationGroup G S 0} (hc : (σ : G) • π = π * c) :
    (tameCharacter G S σ : ResidueField S) = residue S c := by
  have hceq : c = ((IsDiscreteValuationRing.uniformizerRatio 0 hπ σ : Sˣ) : S) :=
    mul_left_cancel₀ hπ.ne_zero
      (hc.symm.trans (IsDiscreteValuationRing.mul_uniformizerRatio hπ σ).symm)
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded_apply (i := 0) hπ,
    principalUnitGroupGradedZeroEquivResidueFieldUnits_mk, Units.coe_map, hceq]
  rfl

/-- The tame character of `σ` is trivial exactly when `σ π ≡ π` modulo `𝔪 ^ 2`, for any
uniformizer `π`. -/
theorem tameCharacter_eq_one_iff_smul_sub_mem {π : S} (hπ : Irreducible π)
    {σ : ramificationGroup G S 0} :
    tameCharacter G S σ = 1 ↔ (σ : G) • π - π ∈ maximalIdeal S ^ 2 := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGroupGradedZeroEquivResidueFieldUnits S).injective,
    ← MonoidHom.mem_ker,
    IsDiscreteValuationRing.mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (i := 0) hπ,
    zero_add]

/-- The tame character is trivial on the first ramification group. -/
theorem ramificationGroup_one_subgroupOf_le_ker_tameCharacter :
    (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) ≤ (tameCharacter G S).ker := by
  intro σ hσ
  rw [tameCharacter, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGroupGradedZeroEquivResidueFieldUnits S).injective,
    ← MonoidHom.mem_ker]
  exact IsDiscreteValuationRing.ramificationGroup_succ_subgroupOf_le_ker G S 0 (by simpa using hσ)

/-- **The kernel of the tame character is `G_1`**, viewed inside `G_0`, when the residue extension
over a local ring `R` fixed by `G` is separable. -/
theorem ker_tameCharacter (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    (tameCharacter G S).ker = (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) := by
  refine le_antisymm (fun σ hσ ↦ ?_) ramificationGroup_one_subgroupOf_le_ker_tameCharacter
  rw [tameCharacter, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGroupGradedZeroEquivResidueFieldUnits S).injective,
    ← MonoidHom.mem_ker,
    IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGroupGraded G S R 0] at hσ
  simpa using hσ

variable (G S) in
/-- The tame character on the tame quotient `G_0 / G_1`. -/
noncomputable def tameCharacterGraded : RamificationGroupGraded G S 0 →* (ResidueField S)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits S).toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded G S 0)

@[simp]
theorem tameCharacterGraded_mk (σ : ramificationGroup G S 0) :
    tameCharacterGraded G S (σ : RamificationGroupGraded G S 0) = tameCharacter G S σ :=
  (rfl)

/-- For a separable residue extension, the tame character embeds `G_0 / G_1` into `kˣ`. -/
theorem tameCharacterGraded_injective (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    Function.Injective (tameCharacterGraded G S) :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits S).injective.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective G S R 0)

/-- **The tame quotient is cyclic**: a finite `G_0 / G_1` embeds into the multiplicative group of
the residue field, when the residue extension is separable. -/
theorem isCyclic_ramificationGroupGraded_zero (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Finite (RamificationGroupGraded G S 0)] :
    IsCyclic (RamificationGroupGraded G S 0) :=
  isCyclic_of_injective_ringHom ((Units.coeHom _).comp (tameCharacterGraded G S))
    (Units.val_injective.comp (tameCharacterGraded_injective R))

/-- **The order of the tame quotient is prime to the residue characteristic**: the index of
`G_1` in `G_0` is not divisible by `p` when `G_0 / G_1` is finite and the residue extension is
separable. The quotient embeds into `kˣ`, which has no element of order `p` when `k` has
characteristic `p`, and for `p = 0` the statement is the nonvanishing of the index. -/
theorem not_dvd_index_ramificationGroup_one (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Finite (RamificationGroupGraded G S 0)] (p : ℕ) [CharP (ResidueField S) p] :
    ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index := by
  rw [Subgroup.index, ← zero_add (1 : ℤ)]
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := RamificationGroupGraded G S 0) p hdvd
    -- The image of `x` would be a primitive `p`-th root of unity in characteristic `p`.
    have hord : orderOf ((tameCharacterGraded G S x : (ResidueField S)ˣ) : ResidueField S) = p := by
      rw [orderOf_units, orderOf_injective _ (tameCharacterGraded_injective R) x, hx]
    have : NeZero p := ⟨hp.ne_zero⟩
    exact (hord ▸ IsPrimitiveRoot.orderOf _).neZero'.out (CharP.cast_eq_zero _ p)
  · rw [zero_dvd_iff]
    exact Nat.card_pos.ne'

/-! ### The positive-depth graded embeddings -/

/-- The homomorphism `G_{n+1} →* Multiplicative k` in the coordinate of the uniformizer `π`: it
sends `σ` to the residue of the `c` with `σ π - π = π ^ (n + 2) c`
(`TauCeti.IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq`). Its kernel contains
`G_{n+2}`, with equality for a separable residue extension
(`TauCeti.IsLocalRing.ker_ramificationGroupToResidueField`). -/
noncomputable def ramificationGroupToResidueField {π : S} (hπ : Irreducible π) (n : ℕ) :
    ramificationGroup G S ((n : ℤ) + 1) →* Multiplicative (ResidueField S) :=
  ((principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ).toMultiplicativeRight
      |>.toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded G S (n + 1))).comp
    (MulEquiv.cast (M := fun k : ℤ ↦ ↥(ramificationGroup G S k))
      (Nat.cast_succ n).symm).toMonoidHom

/-- The positive-depth homomorphism at an element `σ` with `σ π - π = π ^ (n + 2) c` is the residue
of `c`. -/
theorem ramificationGroupToResidueField_apply_of_smul_sub_eq {π : S} (hπ : Irreducible π) {n : ℕ}
    {σ : ramificationGroup G S ((n : ℤ) + 1)} {c : S} (hc : (σ : G) • π - π = π ^ (n + 2) * c) :
    ramificationGroupToResidueField hπ n σ = Multiplicative.ofAdd (residue S c) := by
  let σ' : ramificationGroup G S ((n + 1 : ℕ) : ℤ) :=
    MulEquiv.cast (M := fun k : ℤ ↦ ↥(ramificationGroup G S k)) (Nat.cast_succ n).symm σ
  have hcoe : (σ' : G) = (σ : G) := by
    have : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := (Nat.cast_succ n).symm
    cases this
    rfl
  have hdiff :
      ((IsDiscreteValuationRing.uniformizerRatio (n + 1) hπ σ' : Sˣ) : S) - 1 =
        c * π ^ (n + 1) := by
    apply mul_left_cancel₀ hπ.ne_zero
    calc π * (((IsDiscreteValuationRing.uniformizerRatio (n + 1) hπ σ' : Sˣ) : S) - 1)
        = (σ' : G) • π - π := by
          rw [mul_sub, IsDiscreteValuationRing.mul_uniformizerRatio, mul_one]
      _ = (σ : G) • π - π := by rw [hcoe]
      _ = π ^ (n + 2) * c := hc
      _ = π * (c * π ^ (n + 1)) := by rw [pow_succ']; ring
  rw [ramificationGroupToResidueField, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded_apply hπ,
    AddEquiv.toMultiplicativeRight_apply_apply]
  exact congrArg Multiplicative.ofAdd
    (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
      n π hπ _ c hdiff)

/-- The positive-depth homomorphism at `σ` is trivial exactly when `σ π ≡ π` modulo
`𝔪 ^ (n + 3)`. -/
theorem ramificationGroupToResidueField_eq_one_iff {π : S} (hπ : Irreducible π) {n : ℕ}
    {σ : ramificationGroup G S ((n : ℤ) + 1)} :
    ramificationGroupToResidueField hπ n σ = 1 ↔ (σ : G) • π - π ∈ maximalIdeal S ^ (n + 3) := by
  have hmem :=
    IsDiscreteValuationRing.mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (i := n + 1) hπ
      (σ := MulEquiv.cast (M := fun k : ℤ ↦ ↥(ramificationGroup G S k))
        (Nat.cast_succ n).symm σ)
  have hcoe :
      ((MulEquiv.cast (M := fun k : ℤ ↦ ↥(ramificationGroup G S k))
          (Nat.cast_succ n).symm σ : ramificationGroup G S ((n + 1 : ℕ) : ℤ)) : G) = (σ : G) := by
    have : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := (Nat.cast_succ n).symm
    cases this
    rfl
  rw [ramificationGroupToResidueField, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _
      ((principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ).toMultiplicativeRight
        |>.injective),
    ← MonoidHom.mem_ker]
  simpa [hcoe, Nat.add_assoc] using hmem

/-- **Changing the uniformizer** in the positive-depth homomorphism: if `π' = π a`, then the
coordinate of `σ` at `π` is `a ^ (n + 1)` times its coordinate at `π'`, modulo `𝔪`. -/
theorem toAdd_ramificationGroupToResidueField_of_mul_eq {π π' a : S} (hπ : Irreducible π)
    (hπ' : Irreducible π') (ha : π * a = π') {n : ℕ} (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    (ramificationGroupToResidueField hπ n σ).toAdd =
      residue S a ^ (n + 1) * (ramificationGroupToResidueField hπ' n σ).toAdd := by
  have haeq : (uniformizerChangeUnit π π' hπ hπ' : S) = a :=
    mul_left_cancel₀ hπ.ne_zero ((mul_uniformizerChangeUnit π π' hπ hπ').trans ha.symm)
  simpa [ramificationGroupToResidueField, haeq] using
    principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_change n π π' hπ hπ' _

/-- The positive-depth homomorphism is trivial on `G_{n+2}`. -/
theorem ramificationGroup_add_one_subgroupOf_le_ker_ramificationGroupToResidueField {π : S}
    (hπ : Irreducible π) (n : ℕ) :
    (ramificationGroup G S ((n : ℤ) + 1 + 1)).subgroupOf (ramificationGroup G S ((n : ℤ) + 1)) ≤
      (ramificationGroupToResidueField hπ n).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker, ramificationGroupToResidueField_eq_one_iff hπ]
  have h := mem_ramificationGroup_iff.mp hσ π
  rwa [(by omega : ((n : ℤ) + 1 + 1 + 1).toNat = n + 3)] at h

/-- **The kernel of the positive-depth homomorphism is `G_{n+2}`**, viewed inside `G_{n+1}`, when
the residue extension over a local ring `R` fixed by `G` is separable. -/
theorem ker_ramificationGroupToResidueField (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S} (hπ : Irreducible π)
    (n : ℕ) :
    (ramificationGroupToResidueField hπ n).ker =
      (ramificationGroup G S ((n : ℤ) + 1 + 1)).subgroupOf
        (ramificationGroup G S ((n : ℤ) + 1)) := by
  refine le_antisymm (fun σ hσ ↦ ?_)
    (ramificationGroup_add_one_subgroupOf_le_ker_ramificationGroupToResidueField hπ n)
  rw [MonoidHom.mem_ker, ramificationGroupToResidueField_eq_one_iff hπ] at hσ
  rw [Subgroup.mem_subgroupOf, (by push_cast; ring : (n : ℤ) + 1 + 1 = (n + 2 : ℕ)),
    mem_ramificationGroup_natCast_iff_smul_sub_mem R hπ.maximalIdeal_eq
      (ramificationGroup_antitone G S (by omega) σ.property)]
  exact hσ

/-- The positive-depth homomorphism on the graded piece `G_{n+1} / G_{n+2}`. -/
noncomputable def ramificationGroupGradedToResidueField {π : S} (hπ : Irreducible π) (n : ℕ) :
    RamificationGroupGraded G S ((n : ℤ) + 1) →* Multiplicative (ResidueField S) :=
  ((principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ).toMultiplicativeRight
      |>.toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded G S (n + 1))).comp
    (MulEquiv.cast (M := RamificationGroupGraded G S) (Nat.cast_succ n).symm).toMonoidHom

@[simp]
theorem ramificationGroupGradedToResidueField_mk {π : S} (hπ : Irreducible π) (n : ℕ)
    (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField hπ n (σ : RamificationGroupGraded G S ((n : ℤ) + 1)) =
      ramificationGroupToResidueField hπ n σ := by
  simp only [ramificationGroupGradedToResidueField, ramificationGroupToResidueField,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, cast_ramificationGroupGraded_mk,
    IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_mk]

/-- For a separable residue extension, the positive-depth graded piece `G_{n+1} / G_{n+2}` embeds
into the additive group of the residue field. -/
theorem ramificationGroupGradedToResidueField_injective (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S} (hπ : Irreducible π)
    (n : ℕ) : Function.Injective (ramificationGroupGradedToResidueField (G := G) hπ n) :=
  ((principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ).toMultiplicativeRight
      |>.injective.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective
      G S R (n + 1))).comp
    (MulEquiv.cast (M := RamificationGroupGraded G S) (Nat.cast_succ n).symm).injective

/-! ### Conjugation equivariance -/

/-- **Conjugation equivariance of the tame character** (Serre, *Local Fields*, IV §2,
Proposition 9): conjugating `σ ∈ G_0` by `g ∈ G` acts on `tameCharacter G S σ` via the induced
action of `g` on `ResidueField S`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G S (0 : ℤ)) :
    (tameCharacter G S (MulAut.conjNormal g σ) : ResidueField S) =
      g • (tameCharacter G S σ : ResidueField S) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  have hgϖ : Irreducible (g⁻¹ • ϖ) := hϖ.map (MulSemiringAction.toRingAut G S g⁻¹)
  rw [coe_tameCharacter_of_smul_eq_mul hgϖ
      (IsDiscreteValuationRing.mul_uniformizerRatio hgϖ σ).symm,
    ← ResidueField.residue_smul]
  refine coe_tameCharacter_of_smul_eq_mul hϖ ?_
  calc (MulAut.conjNormal g σ : G) • ϖ
      = g • ((σ : G) • (g⁻¹ • ϖ)) := by
        rw [MulAut.conjNormal_apply, mul_smul, mul_smul]
    _ = g • (g⁻¹ • ϖ * ((IsDiscreteValuationRing.uniformizerRatio 0 hgϖ σ : Sˣ) : S)) := by
        rw [IsDiscreteValuationRing.mul_uniformizerRatio]
    _ = g • (g⁻¹ • ϖ) * g • ((IsDiscreteValuationRing.uniformizerRatio 0 hgϖ σ : Sˣ) : S) :=
        smul_mul' g _ _
    _ = ϖ * g • ((IsDiscreteValuationRing.uniformizerRatio 0 hgϖ σ : Sˣ) : S) := by
        rw [smul_inv_smul]

/-- Conjugation by `g ∈ G` on `G_0 / G_1` corresponds under `tameCharacterGraded` to the induced
action of `g` on `ResidueField S`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (x : RamificationGroupGraded G S (0 : ℤ)) :
    (tameCharacterGraded G S (ramificationGroupGradedConj G S g 0 x) : ResidueField S) =
      g • (tameCharacterGraded G S x : ResidueField S) := by
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-- **Conjugation action formula on positive ramification quotients** (Serre, *Local Fields*,
IV §2, Proposition 9): in the residue coordinate determined by `ϖ`, conjugation by `σ ∈ G_0` acts
on `G_{n+1} / G_{n+2}` as multiplication by `(tameCharacter G S σ) ^ (n + 1)`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S 0) (τ : RamificationGroupGraded G S ((n : ℤ) + 1)) :
    (ramificationGroupGradedToResidueField hϖ n
        (ramificationGroupGradedConj G S (σ : G) ((n : ℤ) + 1) τ)).toAdd =
      (tameCharacter G S σ : ResidueField S) ^ (n + 1) *
        (ramificationGroupGradedToResidueField hϖ n τ).toAdd := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let ϖ' : S := g⁻¹ • ϖ
    have hϖ' : Irreducible ϖ' := hϖ.map (MulSemiringAction.toRingAut G S g⁻¹)
    have hmove : (τ : G) • ϖ' - ϖ' ∈ maximalIdeal S ^ (n + 2) :=
      mem_ramificationGroup_add_one_iff.mp τ.property ϖ'
    rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord :
        (ramificationGroupToResidueField hϖ' n τ).toAdd = residue S y := by
      rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ' (by rw [← hy, mul_comm]),
        toAdd_ofAdd]
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G S ((n : ℤ) + 1)) : G) • ϖ - ϖ =
          ϖ ^ (n + 2) * (g • y) := by
      calc
        _ = g • ((τ : G) • ϖ' - ϖ') := by
          simp [ϖ', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * ϖ' ^ (n + 2)) := by rw [hy]
        _ = ϖ ^ (n + 2) * (g • y) := by simp [ϖ', smul_mul', smul_pow', mul_comm]
    have hconjCoord :
        (ramificationGroupToResidueField hϖ n (MulAut.conjNormal g τ)).toAdd =
          residue S (g • y) := by
      rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ hconjMove, toAdd_ofAdd]
    have hresidue : residue S (g • y) = residue S y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G S σ.property y
    set a : Sˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
    have hprodB : ((IsDiscreteValuationRing.uniformizerRatio 0 hϖ σ : Sˣ) : S) * (g • (a : S)) =
        1 := by
      apply mul_left_cancel₀ hϖ.ne_zero
      calc ϖ * (((IsDiscreteValuationRing.uniformizerRatio 0 hϖ σ : Sˣ) : S) * (g • (a : S)))
          = (g • ϖ) * (g • (a : S)) := by
            rw [← mul_assoc, IsDiscreteValuationRing.mul_uniformizerRatio]
        _ = g • (ϖ * (a : S)) := (smul_mul' g _ _).symm
        _ = g • ϖ' := by rw [mul_uniformizerChangeUnit]
        _ = ϖ * 1 := by simp [ϖ']
    have hprod : (tameCharacter G S σ : ResidueField S) * residue S (a : S) = 1 := by
      rw [coe_tameCharacter_of_smul_eq_mul hϖ
          (IsDiscreteValuationRing.mul_uniformizerRatio hϖ σ).symm,
        ← residue_smul_eq_of_mem_ramificationGroup_zero G S σ.property (a : S),
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
      (fun w hw ↦ smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer hϖ.maximalIdeal_eq hϖ2
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
    finite_ramificationGroup_of_le (by omega : (0 : ℤ) ≤ 1)
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

end IsDiscreteValuationRing

end TauCeti
