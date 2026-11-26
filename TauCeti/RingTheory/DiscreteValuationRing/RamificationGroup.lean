/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.UnitFiltration
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded
import TauCeti.Algebra.Group.Action.MulDistribMulAction

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
`G_i →* U_i / U_{i+1}` is `G_{i+1}` and every `θ_i` is injective.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u_σ ∈ U_i` with
  `ϖ * u_σ = σ • ϖ`, for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded`: the quotient
  homomorphisms `G_i →* U_i / U_{i+1}` and `θ_i : G_i / G_{i+1} →* U_i / U_{i+1}`.

## Main results

* `TauCeti.IsLocalRing.unitsMap_div_mem_unitFiltration_succ`: an element of the `i`-th
  ramification group moves every unit of a local ring by a factor in `U_{i+1}`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible`:
  independence of the choice of uniformizer.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_injective`:
  exactness of the kernels and injectivity of `θ_i` under separable residue extension.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7 and Corollaries.
-/

public section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsLocalRing

section Action

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- For an element `σ` in the `i`-th ramification group of a local ring `S` and any unit `u : Sˣ`,
the ratio `(σ • u) / u` lies one step deeper in the unit filtration, in `unitFiltration S (i + 1)`.
-/
theorem unitsMap_div_mem_unitFiltration_succ {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S (i : ℤ)) (u : Sˣ) :
    Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom u / u ∈
      unitFiltration S (i + 1) := by
  rw [mem_unitFiltration_iff, div_eq_mul_inv]
  have hsub :
      ((Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom u * u⁻¹ : Sˣ) : S) - 1 =
        (σ • (u : S) - (u : S)) * (u⁻¹ : Sˣ) := by
    simp [sub_mul]
  rw [hsub]
  exact Ideal.mul_mem_right _ _ (mem_ramificationGroup_natCast_iff.mp hσ (u : S))

end Action

end TauCeti.IsLocalRing

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
theorem coe_uniformizerRatio_mul_apply (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  rw [coe_uniformizerRatio i hϖ (σ * τ), coe_uniformizerRatio i hϖ σ,
    coe_uniformizerRatio i hϖ τ,
    unitsMap_uniformizerChangeUnit (MulSemiringAction.toRingHom G B (σ : G)) ϖ ((τ : G) • ϖ)
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
      rw [coe_uniformizerRatio_mul_apply]
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
    unitsMap_uniformizerChangeUnit (MulSemiringAction.toRingHom G B (σ : G)) ϖ ϖ'
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
coordinate `unitFiltrationGradedSuccEquivResidueField n π hπ` recovers
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField hπ n`. -/
theorem unitFiltrationGradedSuccEquivResidueField_ramificationGroupGradedToUnitFiltrationGraded
    (n : ℕ) {π : B} (hπ : Irreducible π)
    (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    unitFiltrationGradedSuccEquivResidueField n π hπ
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
      unitFiltrationGradedSuccEquivResidueField_eq_residue n π hπ _ y h1,
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

end Separable

end TauCeti.IsDiscreteValuationRing
