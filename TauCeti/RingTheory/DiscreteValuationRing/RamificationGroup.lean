/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.RingTheory.DiscreteValuationRing.UnitFiltration
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded
import TauCeti.Algebra.Group.Action.MulDistribMulAction
import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.LocalRing.RamificationGroup.UnitFiltration

/-!
# Graded embeddings of the ramification filtration into the unit filtration of a DVR

Let a group `G` act by ring automorphisms on a discrete valuation ring `B` with maximal ideal `𝔪`
and residue field `k`. Fixing a uniformizer `ϖ` of `B`, every automorphism `σ` carries `ϖ` to
another uniformizer `σ • ϖ`, so there is a unique unit `u_σ : Bˣ` with `ϖ * u_σ = σ • ϖ`. When `σ`
lies in the `i`-th lower ramification group `G_i = TauCeti.IsLocalRing.ramificationGroup G B i`,
`u_σ` lies in the `i`-th step `U_i = TauCeti.IsLocalRing.unitFiltration B i` of the unit
filtration, and its class modulo `U_{i+1}` is independent of `ϖ`, multiplicative in `σ`, and
trivial on `G_{i+1}`. It therefore descends to a canonical homomorphism

`θ_i : G_i / G_{i+1} →* U_i / U_{i+1}`.

At depth zero, composing with `U_0 / U_1 ≃* kˣ` recovers `TauCeti.IsLocalRing.tameCharacter` and
`TauCeti.IsLocalRing.tameCharacterGraded`. At positive depth `i = n + 1`, composing with the
uniformizer coordinate `Additive (U_{n+1} / U_{n+2}) ≃+ k` recovers
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`.

When `B` is a local algebra over a local ring `A` fixed by `G` with separable residue extension
`ResidueField B / ResidueField A`,
`TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem` implies that the kernel of
`G_i →* U_i / U_{i+1}` is `G_{i+1}` and every `θ_i` is injective. This file also records
conjugation equivariance on `G_0 / G_1` and `G_{n+1} / G_{n+2}`, tame inertia cyclicity when
`G_1 = ⊥`, and characteristic-zero structure theorems for `G_0` and `G_1` without separability.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u_σ ∈ U_i` with
  `ϖ * u_σ = σ • ϖ`, for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded`: the quotient
  homomorphisms `G_i →* U_i / U_{i+1}` and `θ_i : G_i / G_{i+1} →* U_i / U_{i+1}`.

## Main results

* `TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible`:
  independence of the choice of uniformizer.
* `unitFiltrationGradedZeroEquivResidueFieldUnits_ramificationGroupToUnitFiltrationGraded`,
  `unitFiltrationGradedZeroEquivResidueFieldUnits_ramificationGroupGradedToUnitFiltrationGraded`,
  and
unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ramificationGroupGradedToUnitFiltrationGraded
  (in `TauCeti.IsDiscreteValuationRing`): compatibility of `θ_i` with
  `TauCeti.IsLocalRing.tameCharacter`, `TauCeti.IsLocalRing.tameCharacterGraded`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_conj`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_conj`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_conj_of_smul_eq_pow`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_ramificationGroupGradedConj`, and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow`:
  conjugation equivariance of the tame character and positive-depth residue coordinate.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToUnitFiltrationGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedConj_zero`:
  exactness of the kernels, injectivity of `θ_i`, and triviality of inertia conjugation on
  `G_0 / G_1` under separable residue extension.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_one_of_pow_sub_one_mem_maximalIdeal`: in
  prime residue characteristic `p`, an element of `G_0` lies in `G_1` once a `p`-power of its
  uniformizer ratio is congruent to `1` modulo `𝔪`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_iff` and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot`:
  injectivity of `tameCharacter` and cyclicity of `G_0` when `G_1 = ⊥`.
* `TauCeti.IsDiscreteValuationRing.ker_tameCharacter_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_of_charZero`, and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue
  characteristic zero without separability hypotheses, `ker tameCharacter = G_1` and
  `tameCharacterGraded` is injective when `G_0` is finite, and when the action is also faithful,
  `tameCharacter` is injective and `G_0` is cyclic.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7, 9, and Corollaries.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, §3.1, Proposition 1.
-/

public section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

/-! ### Uniformizer ratios and graded homomorphisms -/

section Homomorphisms

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

private theorem uniformizerChangeUnit_smul_mem_unitFiltration {ϖ : B} (hϖ : Irreducible ϖ)
    {i : ℕ} {σ : G} (hσϖ : Irreducible (σ • ϖ))
    (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ (σ • ϖ) hϖ hσϖ ∈ unitFiltration B i := by
  rw [mem_unitFiltration_iff_mul_irreducible_mem hϖ, sub_mul, one_mul, mul_comm,
    mul_uniformizerChangeUnit]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

/-- The unit `u_σ ∈ U_i` carrying a uniformizer `ϖ` to `(σ : G) • ϖ`, for `σ` in the `i`-th
ramification group `G_i`. -/
noncomputable def uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) : unitFiltration B i :=
  have hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.smul (σ : G)
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ,
    uniformizerChangeUnit_smul_mem_unitFiltration hϖ hσϖ σ.property⟩

/-- Multiplying `ϖ` on the right by `uniformizerRatio i hϖ σ` gives `(σ : G) • ϖ`. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ :=
  mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

private theorem coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ))
    (hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.smul (σ : G)) :
    (uniformizerRatio i hϖ σ : Bˣ) = uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ :=
  rfl

/-- The 1-cocycle identity `u_{στ} = u_σ * σ(u_τ)` in `Bˣ` for the uniformizer ratio. -/
theorem coe_uniformizerRatio_mul (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  rw [coe_uniformizerRatio i hϖ (σ * τ), coe_uniformizerRatio i hϖ σ,
    coe_uniformizerRatio i hϖ τ,
    (MulSemiringAction.toRingHom G B (σ : G)).unitsMap_uniformizerChangeUnit ϖ ((τ : G) • ϖ)
      hϖ (hϖ.smul (τ : G)) (hϖ.smul (σ : G)) ((hϖ.smul (τ : G)).smul (σ : G))]
  have hmul : ((σ * τ : ramificationGroup G B (i : ℤ)) : G) • ϖ = (σ : G) • (τ : G) • ϖ := by
    rw [Subgroup.coe_mul, mul_smul]
  simp_rw [MulSemiringAction.toRingHom_apply, hmul]
  exact (uniformizerChangeUnit_mul ϖ ((σ : G) • ϖ) ((σ : G) • (τ : G) • ϖ) hϖ
    (hϖ.smul (σ : G)) _).symm

/-- The **quotient homomorphism** `G_i →* U_i / U_{i+1}` sending `σ` to the class of its
uniformizer ratio `u_σ`. It does not depend on `ϖ`
(`ramificationGroupToUnitFiltrationGraded_eq_of_irreducible`) and kills `G_{i+1}`. -/
noncomputable def ramificationGroupToUnitFiltrationGraded (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (i : ℤ) →* UnitFiltrationGraded B i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) <| by
    intro σ τ
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf, ← Subgroup.inv_mem_iff]
    have hcocycle :
        ((↑((uniformizerRatio i hϖ (σ * τ))⁻¹ *
            (uniformizerRatio i hϖ σ * uniformizerRatio i hϖ τ)))⁻¹ : Bˣ) =
          Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
            (uniformizerRatio i hϖ τ : Bˣ) / (uniformizerRatio i hϖ τ : Bˣ) := by
      push_cast
      rw [coe_uniformizerRatio_mul]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    rw [hcocycle]
    exact unitsMap_div_mem_unitFiltration_succ σ.property _

/-- Evaluates `ramificationGroupToUnitFiltrationGraded i hϖ` at `σ` as the quotient class of
`uniformizerRatio i hϖ σ`. -/
@[simp]
theorem ramificationGroupToUnitFiltrationGraded_apply (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

private theorem coe_uniformizerRatio_change (i : ℕ) {ϖ ϖ' : B} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (σ : ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ ϖ' hϖ hϖ' * (uniformizerRatio i hϖ' σ : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') := by
  rw [coe_uniformizerRatio i hϖ' σ, coe_uniformizerRatio i hϖ σ,
    (MulSemiringAction.toRingHom G B (σ : G)).unitsMap_uniformizerChangeUnit ϖ ϖ'
      hϖ hϖ' (hϖ.smul (σ : G)) (hϖ'.smul (σ : G)),
    uniformizerChangeUnit_mul]
  simp_rw [MulSemiringAction.toRingHom_apply]
  exact (uniformizerChangeUnit_mul ϖ ((σ : G) • ϖ) ((σ : G) • ϖ') hϖ (hϖ.smul (σ : G))
    (hϖ'.smul (σ : G))).symm

/-- The quotient homomorphism `G_i →* U_i / U_{i+1}` does not depend on the choice of
uniformizer. -/
theorem ramificationGroupToUnitFiltrationGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupToUnitFiltrationGraded (G := G) i hϖ' := by
  refine MonoidHom.ext fun σ ↦ ?_
  rw [ramificationGroupToUnitFiltrationGraded_apply, ramificationGroupToUnitFiltrationGraded_apply]
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf]
  set a := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have hrel :
      ((uniformizerRatio i hϖ σ)⁻¹ * uniformizerRatio i hϖ' σ : unitFiltration B i).val =
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a / a := by
    rw [Subgroup.coe_mul, InvMemClass.coe_inv, inv_mul_eq_div, div_eq_div_iff_mul_eq_mul]
    simpa [mul_comm] using coe_uniformizerRatio_change i hϖ hϖ' σ
  rw [hrel]
  exact unitsMap_div_mem_unitFiltration_succ σ.property a

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToUnitFiltrationGraded i hϖ`
if and only if `(σ : G) • ϖ - ϖ ∈ 𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToUnitFiltrationGraded_iff {i : ℕ} {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToUnitFiltrationGraded i hϖ).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToUnitFiltrationGraded_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, mem_unitFiltration_iff_mul_irreducible_mem hϖ, sub_mul, one_mul,
    mul_comm, mul_coe_uniformizerRatio]

/-- The next ramification group `G_{i+1}` lies in the kernel of the `i`-th quotient
homomorphism. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded i hϖ).ker := by
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

/-- The **graded ramification homomorphism** `θ_i : G_i / G_{i+1} →* U_i / U_{i+1}`, induced by
sending `σ ∈ G_i` to the class of its uniformizer ratio `u_σ`. -/
noncomputable def ramificationGroupGradedToUnitFiltrationGraded (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (i : ℤ) →* UnitFiltrationGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToUnitFiltrationGraded i hϖ)
    (ramificationGroup_succ_subgroupOf_le_ker i hϖ)

/-- Evaluates `ramificationGroupGradedToUnitFiltrationGraded` on the class of `σ`. -/
@[simp]
theorem ramificationGroupGradedToUnitFiltrationGraded_mk (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

/-- The graded ramification homomorphism `θ_i` does not depend on the choice of uniformizer. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ' := by
  apply QuotientGroup.monoidHom_ext
  simp only [ramificationGroupGradedToUnitFiltrationGraded, QuotientGroup.lift_comp_mk']
  exact ramificationGroupToUnitFiltrationGraded_eq_of_irreducible i hϖ hϖ'

/-! ### Compatibility with the local-ring tame character and residue coordinates -/

/-- Composing `ramificationGroupToUnitFiltrationGraded 0 hϖ` with
`unitFiltrationGradedZeroEquivResidueFieldUnits` recovers `TauCeti.IsLocalRing.tameCharacter`. -/
theorem unitFiltrationGradedZeroEquivResidueFieldUnits_ramificationGroupToUnitFiltrationGraded
    {ϖ : B} (hϖ : Irreducible ϖ) (σ : ramificationGroup G B 0) :
    unitFiltrationGradedZeroEquivResidueFieldUnits B
        (ramificationGroupToUnitFiltrationGraded 0 hϖ σ) =
      TauCeti.IsLocalRing.tameCharacter G B σ := by
  ext
  rw [ramificationGroupToUnitFiltrationGraded_apply (i := 0),
    coe_unitFiltrationGradedZeroEquivResidueFieldUnits_mk]
  exact (coe_tameCharacter_of_smul_eq_mul hϖ
    (mul_coe_uniformizerRatio 0 hϖ σ).symm).symm

/-- Composing `ramificationGroupGradedToUnitFiltrationGraded 0 hϖ` with
`unitFiltrationGradedZeroEquivResidueFieldUnits` recovers
`TauCeti.IsLocalRing.tameCharacterGraded`. -/
theorem
    unitFiltrationGradedZeroEquivResidueFieldUnits_ramificationGroupGradedToUnitFiltrationGraded
    {ϖ : B} (hϖ : Irreducible ϖ) (τ : RamificationGroupGraded G B 0) :
    unitFiltrationGradedZeroEquivResidueFieldUnits B
        (ramificationGroupGradedToUnitFiltrationGraded 0 hϖ τ) =
      TauCeti.IsLocalRing.tameCharacterGraded G B τ := by
  induction τ using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedToUnitFiltrationGraded_mk,
      ← ramificationGroupToUnitFiltrationGraded_apply,
      unitFiltrationGradedZeroEquivResidueFieldUnits_ramificationGroupToUnitFiltrationGraded,
      TauCeti.IsLocalRing.tameCharacterGraded_mk]

/-- Composing `ramificationGroupGradedToUnitFiltrationGraded (n + 1) hπ` with the uniformizer
coordinate `unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ` recovers
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField hπ n`. -/
theorem
unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ramificationGroupGradedToUnitFiltrationGraded
    (n : ℕ) {π : B} (hπ : Irreducible π)
    (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul (ramificationGroupGradedToUnitFiltrationGraded (n + 1) hπ τ)) =
      (TauCeti.IsLocalRing.ramificationGroupGradedToResidueField hπ n τ).toAdd := by
  induction τ using QuotientGroup.induction_on with
  | _ σ =>
    have hdiv : π ^ (n + 2) ∣ (σ : G) • π - π := by
      have h := mem_ramificationGroup_iff.mp σ.property π
      rwa [(by omega : ((n : ℤ) + 1 + 1).toNat = n + 2), hπ.maximalIdeal_eq,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨y, hy⟩ := hdiv
    have h1 : ((uniformizerRatio (n + 1) hπ σ : Bˣ) : B) - 1 = y * π ^ (n + 1) := by
      apply mul_right_cancel₀ hπ.ne_zero
      rw [sub_mul, one_mul, mul_comm _ π, mul_coe_uniformizerRatio, hy]
      ring
    rw [ramificationGroupGradedToUnitFiltrationGraded_mk,
      unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_eq_residue n π hπ _ y h1,
      TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_mk,
      TauCeti.IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq hπ hy,
      toAdd_ofAdd]

end Homomorphisms

/-! ### Separable residue extensions: kernel exactness and injectivity -/

section Separable

variable {G : Type*} [Group G] (A : Type*) [CommRing A] [IsLocalRing A]
variable {B : Type*} [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [MulSemiringAction G B] [SMulCommClass G A B]

include A in
/-- For a separable residue extension, **the kernel of the `i`-th quotient homomorphism is
`G_{i+1}`**. -/
theorem ker_ramificationGroupToUnitFiltrationGraded
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    (ramificationGroupToUnitFiltrationGraded (G := G) i hϖ).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker i hϖ)
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.property
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ.maximalIdeal_eq hσ₀]
  exact hσ

include A in
/-- **The graded ramification homomorphisms `θ_i : G_i / G_{i+1} →* U_i / U_{i+1}` are injective**
when the residue extension is separable. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToUnitFiltrationGraded A i hϖ).symm

include A in
/-- In prime residue characteristic `p`, an element `σ ∈ G_0` lies in `G_1` as soon as a `p`-power
of its uniformizer ratio is congruent to `1` modulo `𝔪`. -/
theorem mem_ramificationGroup_one_of_pow_sub_one_mem_maximalIdeal
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : G} (hσ : σ ∈ ramificationGroup G B 0) (p k : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p]
    (h : ((uniformizerRatio 0 hϖ ⟨σ, hσ⟩ : Bˣ) : B) ^ p ^ k - 1 ∈ maximalIdeal B) :
    σ ∈ ramificationGroup G B 1 := by
  set u : Bˣ := (uniformizerRatio 0 hϖ ⟨σ, hσ⟩ : Bˣ)
  have hu1 : u ∈ unitFiltration B 1 := by
    rw [← residue_eq_zero_iff, map_sub, map_pow, map_one, sub_eq_zero,
      ← mul_one (p ^ k), ExpChar.pow_prime_pow_mul_eq_one_iff p k 1, pow_one] at h
    exact mem_unitFiltration_one_iff_residue_eq_one.mpr h
  have h2 : σ • ϖ - ϖ ∈ maximalIdeal B ^ 2 := by
    rw [mem_unitFiltration_iff_mul_irreducible_mem hϖ, sub_mul, one_mul,
      mul_comm _ ϖ, mul_coe_uniformizerRatio 0 hϖ ⟨σ, hσ⟩] at hu1
    exact hu1
  exact (TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem A
    hϖ.maximalIdeal_eq hσ (n := 1)).mpr h2

/-- Conjugation by inertia acts trivially on the tame quotient `G_0 / G_1` under a separable
residue extension. -/
theorem ramificationGroupGradedConj_zero [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (σ : ramificationGroup G B 0) (τ : RamificationGroupGraded G B 0) :
    ramificationGroupGradedConj G B (σ : G) 0 τ = τ := by
  apply TauCeti.IsLocalRing.tameCharacterGraded_injective (G := G) A
  induction τ using QuotientGroup.induction_on with
  | H τ =>
    simp only [ramificationGroupGradedConj_mk]
    rw [TauCeti.IsLocalRing.tameCharacterGraded_mk, TauCeti.IsLocalRing.tameCharacterGraded_mk,
      MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      mul_comm (TauCeti.IsLocalRing.tameCharacter G B σ)
        (TauCeti.IsLocalRing.tameCharacter G B τ),
      mul_assoc, mul_inv_cancel, mul_one]

variable (G B) in
include A in
/-- Under separable residue extension, the tame character `G_0 →* (ResidueField B)ˣ` is injective
if and only if wild inertia `G_1` is trivial. -/
theorem tameCharacter_injective_iff [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Function.Injective (TauCeti.IsLocalRing.tameCharacter G B) ↔ ramificationGroup G B 1 = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, TauCeti.IsLocalRing.ker_tameCharacter A,
    Subgroup.eq_bot_iff_forall]
  refine ⟨fun h ↦ eq_bot_iff.mpr fun σ hσ ↦ ?_, fun h ⟨σ, hσ₀⟩ hσ₁ ↦ ?_⟩
  · exact Subtype.ext_iff.mp (h ⟨σ, ramificationGroup_antitone G B zero_le_one hσ⟩
      (Subgroup.mem_subgroupOf.mpr hσ))
  · rw [Subgroup.mem_subgroupOf, h, Subgroup.mem_bot] at hσ₁
    exact Subtype.ext hσ₁

variable (G B) in
include A in
/-- When `G_0` is finite, the residue extension is separable, and wild inertia `G_1` is trivial,
inertia `G_0` is cyclic. -/
theorem isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    [Finite (ramificationGroup G B 0)] (h : ramificationGroup G B 1 = ⊥) :
    IsCyclic (ramificationGroup G B 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (TauCeti.IsLocalRing.tameCharacter G B))
    (Units.val_injective.comp ((tameCharacter_injective_iff G A B).mpr h))

end Separable

/-! ### Conjugation action on graded quotients and the tame character -/

section Conjugation

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

/-- The change from `ϖ` to `σ⁻¹ • ϖ` has residue equal to the inverse tame character of `σ`. -/
private theorem residue_uniformizerChangeUnit_inv_smul {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (σ : ramificationGroup G B 0)
    (hϖ'eq : ϖ' = (σ : G)⁻¹ • ϖ) :
    residue B (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : B) =
      ((TauCeti.IsLocalRing.tameCharacter G B σ : (ResidueField B)ˣ)⁻¹ : ResidueField B) := by
  have ha : ((σ⁻¹ : ramificationGroup G B 0) : G) • ϖ =
      ϖ * (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : B) := by
    rw [mul_uniformizerChangeUnit, hϖ'eq, Subgroup.coe_inv]
  rw [← Units.val_inv_eq_inv_val, ← map_inv, coe_tameCharacter_of_smul_eq_mul hϖ ha]

variable (G) in
/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` determined by `ϖ`,
conjugation by `σ ∈ G_0` acts on `G_{n+1} / G_{n+2}` as multiplication by `theta_0(σ) ^ (n + 1)`,
where `theta_0` is `TauCeti.IsLocalRing.tameCharacter`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B 0) (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    (TauCeti.IsLocalRing.ramificationGroupGradedToResidueField hϖ n
        (ramificationGroupGradedConj G B (σ : G) ((n : ℤ) + 1) τ)).toAdd =
      (TauCeti.IsLocalRing.tameCharacter G B σ : ResidueField B) ^ (n + 1) *
        (TauCeti.IsLocalRing.ramificationGroupGradedToResidueField hϖ n τ).toAdd := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let ϖ' : B := g⁻¹ • ϖ
    have hϖ' : Irreducible ϖ' := hϖ.smul g⁻¹
    have hmove : (τ : G) • ϖ' - ϖ' ∈ maximalIdeal B ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.property) ϖ'
    rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord :
        (TauCeti.IsLocalRing.ramificationGroupToResidueField hϖ' n τ).toAdd = residue B y := by
      rw [TauCeti.IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ'
        (by rw [← hy, mul_comm]), toAdd_ofAdd]
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G B ((n : ℤ) + 1)) : G) • ϖ - ϖ =
          ϖ ^ (n + 2) * g • y := by
      calc
        _ = g • ((τ : G) • ϖ' - ϖ') := by simp [ϖ', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * ϖ' ^ (n + 2)) := by rw [hy]
        _ = ϖ ^ (n + 2) * g • y := by
          rw [smul_mul', smul_pow', show g • ϖ' = ϖ by simp [ϖ'], mul_comm]
    have hresidue : residue B (g • y) = residue B y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G B σ.property y
    have hchange := TauCeti.IsLocalRing.toAdd_ramificationGroupToResidueField_of_mul_eq hϖ hϖ'
      (mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ') τ
    rw [residue_uniformizerChangeUnit_inv_smul hϖ hϖ' σ rfl] at hchange
    simp only [ramificationGroupGradedConj_mk]
    rw [TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_mk,
      TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_mk,
      TauCeti.IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ hconjMove,
      toAdd_ofAdd, hresidue, ← hτcoord, hchange, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (Units.ne_zero _), one_pow, one_mul]

variable (G B) in
/-- **The tame character is equivariant.** For `g ∈ G` and `σ ∈ G_0`, the tame character of
`g σ g⁻¹` is the image of the tame character of `σ` under the automorphism of the residue field
induced by `g`: `theta_0(g σ g⁻¹) = g • theta_0(σ)`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G B 0) :
    (TauCeti.IsLocalRing.tameCharacter G B (MulAut.conjNormal g σ) : ResidueField B) =
      g • (TauCeti.IsLocalRing.tameCharacter G B σ : ResidueField B) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.smul (σ : G)
  have hgϖ : Irreducible (g • ϖ) := hϖ.smul g
  set u : B := (uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ : B)
  have hu : ϖ * u = (σ : G) • ϖ := mul_uniformizerChangeUnit ϖ _ hϖ hσϖ
  have hgu : (MulAut.conjNormal g σ : G) • (g • ϖ) = g • ϖ * g • u := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, ← hu, smul_mul']
  rw [coe_tameCharacter_of_smul_eq_mul hgϖ hgu, coe_tameCharacter_of_smul_eq_mul hϖ hu.symm,
    ResidueField.residue_smul]

variable (G B) in
/-- **The tame character twisted by a power map.** If `g ∈ G` acts on the residue field as the
`q`-th power map, then `theta_0(g σ g⁻¹) = theta_0(σ) ^ q` for every `σ ∈ G_0`. -/
theorem tameCharacter_conj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField B, g • x = x ^ q) (σ : ramificationGroup G B 0) :
    TauCeti.IsLocalRing.tameCharacter G B (MulAut.conjNormal g σ) =
      TauCeti.IsLocalRing.tameCharacter G B σ ^ q :=
  Units.ext (by rw [tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

variable (G B) in
/-- The equivariance of the tame character, read on the tame quotient `G_0 / G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (τ : RamificationGroupGraded G B 0) :
    (TauCeti.IsLocalRing.tameCharacterGraded G B (ramificationGroupGradedConj G B g 0 τ) :
        ResidueField B) =
      g • (TauCeti.IsLocalRing.tameCharacterGraded G B τ : ResidueField B) := by
  induction τ using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedConj_mk, TauCeti.IsLocalRing.tameCharacterGraded_mk,
      TauCeti.IsLocalRing.tameCharacterGraded_mk, tameCharacter_conj]

variable (G B) in
/-- The power-map twist of the tame character, read on the tame quotient `G_0 / G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField B, g • x = x ^ q) (τ : RamificationGroupGraded G B 0) :
    TauCeti.IsLocalRing.tameCharacterGraded G B (ramificationGroupGradedConj G B g 0 τ) =
      TauCeti.IsLocalRing.tameCharacterGraded G B τ ^ q :=
  Units.ext (by rw [tameCharacterGraded_ramificationGroupGradedConj, hg,
    Units.val_pow_eq_pow_val])

end Conjugation

/-! ### Residue characteristic zero -/

section CharZero

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]
  [CharZero (ResidueField B)] [Finite (ramificationGroup G B 0)]

variable (G B) in
/-- In residue characteristic zero with finite inertia `G_0`, every element in the kernel of
`tameCharacter` lies in `G_1` (without any base ring `A`, separability, or faithfulness
hypothesis). -/
private theorem mem_ramificationGroup_one_of_mem_ker_tameCharacter_of_charZero
    {σ : ramificationGroup G B 0} (hσker : σ ∈ (TauCeti.IsLocalRing.tameCharacter G B).ker) :
    (σ : G) ∈ ramificationGroup G B 1 := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  let : Fintype (ramificationGroup G B 0) := Fintype.ofFinite _
  -- Because `ResidueField B` has characteristic zero, `#G_0` is a unit in `B`.
  have hunit : IsUnit ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  rw [← Nat.cast_one, mem_ramificationGroup_natCast_iff]
  intro x
  -- Average `x` over `G_0` to obtain a `G_0`-invariant element `s` congruent to `#G_0 * x`
  -- mod `𝔪`.
  let s : B := ∑ τ : ramificationGroup G B 0, (τ : G) • x
  have hs_inv : (σ : G) • s = s := TauCeti.smul_sum_smul σ x
  have hdiff_mem : ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * x - s ∈
      maximalIdeal B := by
    have heq : ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * x - s =
        ∑ τ : ramificationGroup G B 0, (x - (τ : G) • x) := by
      simp only [s, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [heq]
    exact Ideal.sum_mem _ fun τ _ ↦
      neg_mem_iff.mp (by simpa [neg_sub] using mem_ramificationGroup_zero_iff.mp τ.property x)
  -- Write `#G_0 * x - s = ϖ * c`; then `#G_0 * (σ x - x) = σ(ϖ * c) - ϖ * c ∈ 𝔪 ^ 2`.
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hdiff_mem
  obtain ⟨c, hc⟩ := hdiff_mem
  have hmul : ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * ((σ : G) • x - x) ∈
      maximalIdeal B ^ 2 := by
    have hsmul_nat :
        (σ : G) • ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) =
          (Fintype.card (ramificationGroup G B 0) : B) := by
      rw [← MulSemiringAction.toRingHom_apply, map_natCast]
    have hid : ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * ((σ : G) • x - x) =
        (σ : G) • (ϖ * c) - ϖ * c := by
      calc
        ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * ((σ : G) • x - x)
          = ((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * ((σ : G) • x) - s -
              (((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * x - s) := by ring
        _ = (σ : G) • (((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * x - s) -
              (((Fintype.card (ramificationGroup G B 0) : ℕ) : B) * x - s) := by
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
        ((TauCeti.IsLocalRing.tameCharacter_eq_one_iff_smul_sub_mem hϖ).mp
          (MonoidHom.mem_ker.mp hσker))
    · have hϖm : ϖ ∈ maximalIdeal B := by rw [hϖ.maximalIdeal_eq]; exact Ideal.subset_span rfl
      rw [pow_two]
      exact Ideal.mul_mem_mul hϖm (mem_ramificationGroup_zero_iff.mp σ.property c)
  exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmul

variable (G B) in
/-- In residue characteristic zero with finite inertia `G_0`, the kernel of `tameCharacter` is
`G_1` (without any base ring `A`, separability, or faithfulness hypothesis). -/
theorem ker_tameCharacter_of_charZero :
    (TauCeti.IsLocalRing.tameCharacter G B).ker =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) := by
  refine le_antisymm (fun σ hσker ↦ ?_)
    TauCeti.IsLocalRing.ramificationGroup_one_subgroupOf_le_ker_tameCharacter
  exact mem_ramificationGroup_one_of_mem_ker_tameCharacter_of_charZero G B hσker

variable (G B) in
/-- **Tame character embedding in characteristic zero.** In residue characteristic zero with
finite inertia `G_0`, `G_0 / G_1` embeds into `(ResidueField B)ˣ` (without any base ring `A`,
separability, or faithfulness hypothesis). -/
theorem tameCharacterGraded_injective_of_charZero :
    Function.Injective (TauCeti.IsLocalRing.tameCharacterGraded G B) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  induction g using QuotientGroup.induction_on with
  | H σ =>
    rw [TauCeti.IsLocalRing.tameCharacterGraded_mk, ← MonoidHom.mem_ker,
      ker_tameCharacter_of_charZero G B] at hg
    rwa [QuotientGroup.eq_one_iff, zero_add]

variable (G B) in
/-- In residue characteristic zero with faithful action and finite inertia `G_0`, the tame
character `G_0 →* (ResidueField B)ˣ` is injective (without any base ring `A` or separability
hypothesis). -/
theorem tameCharacter_injective_of_charZero [FaithfulSMul G B] :
    Function.Injective (TauCeti.IsLocalRing.tameCharacter G B) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_tameCharacter_of_charZero G B, Subgroup.eq_bot_iff_forall]
  intro σ hσ₁
  have : Finite (ramificationGroup G B 1) :=
    finite_ramificationGroup_of_le G B zero_le_one
  rw [Subgroup.mem_subgroupOf, ramificationGroup_one_eq_bot_of_charZero G B,
    Subgroup.mem_bot] at hσ₁
  exact Subtype.ext hσ₁

variable (G B) in
/-- **Inertia is cyclic in residue characteristic zero.** When `ResidueField B` has characteristic
zero, the action is faithful, and `G_0` is finite, `G_0` itself is cyclic (without any base ring
`A` or separability hypothesis). -/
theorem isCyclic_ramificationGroup_zero_of_charZero [FaithfulSMul G B] :
    IsCyclic (ramificationGroup G B 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (TauCeti.IsLocalRing.tameCharacter G B))
    (Units.val_injective.comp (tameCharacter_injective_of_charZero G B))

end CharZero

end TauCeti.IsDiscreteValuationRing
