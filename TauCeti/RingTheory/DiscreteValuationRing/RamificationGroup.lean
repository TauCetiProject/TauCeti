/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.UnitFiltration
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded
import TauCeti.Algebra.Group.Action.MulDistribMulAction
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
`G_i →* U_i / U_{i+1}` is `G_{i+1}` and every `θ_i` is injective; in particular, `G_0 / G_1` is
commutative and `G_0` acts trivially on `G_0 / G_1` by conjugation.

Without any base ring or separability assumption, conjugation equivariance holds for
`TauCeti.IsLocalRing.tameCharacter`, `TauCeti.IsLocalRing.tameCharacterGraded`, and
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`, and in residue characteristic zero a
faithful action with finite `G_0` has injective tame character and cyclic inertia `G_0`. The
conjugation formulas (`ramificationGroupGradedConj_zero`, `tameCharacter_conj`,
`tameCharacterGraded_ramificationGroupGradedConj`, and `ramificationGroupGradedToResidueField_conj`)
generalize the local-field formalization in
`TauCeti/NumberTheory/LocalField/UnitFiltration/Conjugation.lean`.

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
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToUnitFiltrationGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.isMulCommutative_ramificationGroupGraded_zero`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedConj_zero`:
  exactness of the kernels, injectivity of `θ_i`, commutativity of `G_0 / G_1`, and triviality of
  inertia conjugation on `G_0 / G_1` under separable residue extension.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_one_of_pow_sub_one_mem_maximalIdeal`: in
  prime residue characteristic `p`, an element of `G_0` lies in `G_1` once a `p`-power of its
  uniformizer ratio is congruent to `1` modulo `𝔪`.
* `TauCeti.IsLocalRing.tameCharacter_conj`,
  `TauCeti.IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_conj`: conjugation-equivariance
  formulas on depth `0` and positive-depth graded pieces for any discrete valuation ring.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_one_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.ker_tameCharacter_of_charZero`, and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue
  characteristic zero, without any base ring or separability assumption, a faithful action with
  finite `G_0` has injective tame character and cyclic inertia `G_0`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7, 9, and Corollaries.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 1 and Corollaries 1–2.
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

/-- The uniformizer ratio of the identity element is `1`. -/
@[simp]
theorem uniformizerRatio_one (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    uniformizerRatio (G := G) i hϖ 1 = 1 := by
  exact Subtype.ext (Units.ext (mul_left_cancel₀ hϖ.ne_zero (by simp)))

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

/-- **Change-of-uniformizer coboundary law** for the uniformizer ratio: if `ϖ' = ϖ * a`, then
`a * u_σ(ϖ') = u_σ(ϖ) * σ(a)` in `Bˣ`. -/
theorem coe_uniformizerRatio_change (i : ℕ) {ϖ ϖ' : B} (hϖ : Irreducible ϖ)
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

section
variable (G B)
include A

/-- The tame quotient `G_0 / G_1` is commutative when the residue extension over `A` is
separable: it embeds into `UnitFiltrationGraded B 0`, a quotient of `Bˣ`. (At positive depth
`i = n + 1`, commutativity holds without `A` or DVR hypotheses via
`TauCeti.IsLocalRing.instIsMulCommutativeRamificationGroupGradedNatCastSucc`.) -/
theorem isMulCommutative_ramificationGroupGraded_zero
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    IsMulCommutative (RamificationGroupGraded G B (0 : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hinj := ramificationGroupGradedToUnitFiltrationGraded_injective (G := G) A 0 hϖ
  exact IsMulCommutative.of_comm fun _ _ ↦
    hinj (by rw [map_mul, map_mul]; exact mul_comm (G := UnitFiltrationGraded B 0) _ _)

end

include A in
/-- Conjugation by an inertia element `σ ∈ G_0` acts trivially on the tame quotient `G_0 / G_1`,
when the residue extension over `A` is separable. (Not marked `@[simp]` because `A` does not
appear in the left-hand side; once `isMulCommutative_ramificationGroupGraded_zero G A B` is in
scope, `TauCeti.IsLocalRing.ramificationGroupGradedConj_self` simplifies this automatically.) -/
theorem ramificationGroupGradedConj_zero
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (σ : ramificationGroup G B 0)
    (τ : RamificationGroupGraded G B (0 : ℤ)) :
    ramificationGroupGradedConj G B (σ : G) 0 τ = τ := by
  have := isMulCommutative_ramificationGroupGraded_zero G A B
  exact ramificationGroupGradedConj_self G B 0 σ τ

end Separable

end TauCeti.IsDiscreteValuationRing

namespace TauCeti.IsLocalRing

/-! ### Conjugation equivariance -/

section Conjugation

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S]
  [_root_.IsDiscreteValuationRing S] [MulSemiringAction G S]

/-- **Conjugation equivariance of the tame character** (Serre, *Local Fields*, IV §2,
Proposition 9): conjugating `σ ∈ G_0` by `g ∈ G` acts on `tameCharacter G S σ` via the induced
action of `g` on `ResidueField S`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G S (0 : ℤ)) :
    (tameCharacter G S (MulAut.conjNormal g σ) : ResidueField S) =
      g • (tameCharacter G S σ : ResidueField S) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  have hgϖ : Irreducible (g⁻¹ • ϖ) := hϖ.smul g⁻¹
  rw [coe_tameCharacter_of_smul_eq_mul hgϖ
      (IsDiscreteValuationRing.mul_coe_uniformizerRatio 0 hgϖ σ).symm,
    ← ResidueField.residue_smul]
  refine coe_tameCharacter_of_smul_eq_mul hϖ ?_
  calc (MulAut.conjNormal g σ : G) • ϖ
      = g • ((σ : G) • (g⁻¹ • ϖ)) := by
        rw [MulAut.conjNormal_apply, mul_smul, mul_smul]
    _ = g • (g⁻¹ • ϖ * ((IsDiscreteValuationRing.uniformizerRatio 0 hgϖ σ : Sˣ) : S)) := by
        rw [IsDiscreteValuationRing.mul_coe_uniformizerRatio]
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

private theorem residue_uniformizerChangeUnit_inv_smul {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S 0) (hσϖ : Irreducible ((σ : G)⁻¹ • ϖ) := hϖ.smul _) :
    residue S (uniformizerChangeUnit ϖ ((σ : G)⁻¹ • ϖ) hϖ hσϖ : S) =
      (tameCharacter G S σ : ResidueField S)⁻¹ := by
  have h1 : (tameCharacter G S σ⁻¹ : ResidueField S) =
      residue S (uniformizerChangeUnit ϖ ((σ : G)⁻¹ • ϖ) hϖ hσϖ : S) :=
    coe_tameCharacter_of_smul_eq_mul hϖ
      (by simp)
  rw [← h1, map_inv, Units.val_inv_eq_inv_val]

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
    have hϖ' : Irreducible ϖ' := hϖ.smul g⁻¹
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
    have hchange := toAdd_ramificationGroupToResidueField_of_mul_eq hϖ hϖ'
      (mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ') τ
    rw [ramificationGroupGradedConj_mk, ramificationGroupGradedToResidueField_mk,
      ramificationGroupGradedToResidueField_mk, hconjCoord, hresidue, ← hτcoord, hchange,
      residue_uniformizerChangeUnit_inv_smul hϖ σ hϖ', inv_pow, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), one_mul]

end Conjugation

end TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

/-! ### Residue characteristic zero -/

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

end TauCeti.IsDiscreteValuationRing
