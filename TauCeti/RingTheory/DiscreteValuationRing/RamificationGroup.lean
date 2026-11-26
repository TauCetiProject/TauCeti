/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.UnitFiltration
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded

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
`G_i →* U_i / U_{i+1}` is `G_{i+1}` and every `θ_i` is injective. This file also records the
`Nat.card` and divisibility corollaries for `G_0 / G_1` and `G_1` from the local-ring graded
embeddings in `TauCeti.RingTheory.LocalRing.RamificationGroup.Graded`.

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
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_injective`:
  exactness of the kernels and injectivity of `θ_i` under separable residue extension.
* `TauCeti.IsDiscreteValuationRing.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`,
  `TauCeti.IsDiscreteValuationRing.natCard_ramificationGroup_one`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroup_one_eq_bot_iff_not_dvd_card`: cardinality and
  divisibility corollaries for `G_0 / G_1` and `G_1`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7 and Corollaries.
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
  have hσϖ : Irreducible ((σ : G) • ϖ) :=
    hϖ.map (MulSemiringAction.toRingEquiv G B (σ : G)).toMulEquiv
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ,
    uniformizerChangeUnit_smul_mem_unitFiltration hϖ hσϖ σ.property⟩

/-- Multiplying `ϖ` on the right by `uniformizerRatio i hϖ σ` gives `(σ : G) • ϖ`. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ :=
  mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

omit [IsDomain B] [_root_.IsDiscreteValuationRing B] in
private theorem irreducible_smul (σ : G) {ϖ : B} (hϖ : Irreducible ϖ) :
    Irreducible (σ • ϖ) :=
  hϖ.map (MulSemiringAction.toRingEquiv G B σ).toMulEquiv

private theorem coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ))
    (hσϖ : Irreducible ((σ : G) • ϖ) := irreducible_smul (σ : G) hϖ) :
    (uniformizerRatio i hϖ σ : Bˣ) = uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ :=
  rfl

private theorem uniformizerChangeUnit_eq_right {ϖ ϖ₁ ϖ₂ : B} (hϖ : Irreducible ϖ)
    (h₁ : Irreducible ϖ₁) (h₂ : Irreducible ϖ₂) (h : ϖ₁ = ϖ₂) :
    uniformizerChangeUnit ϖ ϖ₁ hϖ h₁ = uniformizerChangeUnit ϖ ϖ₂ hϖ h₂ := by
  subst h; rfl

private theorem unitsMap_uniformizerChangeUnit (σ : G) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (hσϖ : Irreducible (σ • ϖ) := irreducible_smul σ hϖ)
    (hσϖ' : Irreducible (σ • ϖ') := irreducible_smul σ hϖ') :
    Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom
        (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') =
      uniformizerChangeUnit (σ • ϖ) (σ • ϖ') hσϖ hσϖ' := by
  apply Units.ext
  apply mul_left_cancel₀ hσϖ.ne_zero
  simp only [mul_uniformizerChangeUnit, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, MulSemiringAction.toRingHom_apply, ← smul_mul']

/-- The 1-cocycle identity `u_{στ} = u_σ * σ(u_τ)` in `Bˣ` for the uniformizer ratio. -/
theorem coe_uniformizerRatio_mul_apply (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  rw [coe_uniformizerRatio i hϖ (σ * τ), coe_uniformizerRatio i hϖ σ,
    coe_uniformizerRatio i hϖ τ, unitsMap_uniformizerChangeUnit, uniformizerChangeUnit_mul]
  exact uniformizerChangeUnit_eq_right _ _ _ (by rw [Subgroup.coe_mul, mul_smul])

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
    unitsMap_uniformizerChangeUnit, uniformizerChangeUnit_mul, uniformizerChangeUnit_mul]

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

/-! ### Cardinality and divisibility corollaries for `G_0 / G_1` and `G_1` -/

section Consequences

variable (G : Type*) [Group G] (A : Type*) [CommRing A] [IsLocalRing A]
variable (B : Type*) [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [MulSemiringAction G B] [SMulCommClass G A B]
variable [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

include A

/-- When the residue extension is separable, the order of the tame quotient `G_0 / G_1` divides
`#(ResidueField B) - 1`. -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G B 0) ∣ Nat.card (ResidueField B) - 1 := by
  rw [← Nat.card_units]
  exact Subgroup.card_dvd_of_injective _
    (TauCeti.IsLocalRing.tameCharacterGraded_injective A (G := G) (S := B))

/-- The order of `G_1` is the `p`-part of the order of `G_0`: `#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Nat.card (ramificationGroup G B 1) =
      p ^ (Nat.card (ramificationGroup G B 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (TauCeti.IsLocalRing.ramificationGroupOneSylow G B A p),
    TauCeti.IsLocalRing.ramificationGroupOneSylow_coe]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe
      (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`** (the tamely ramified
case). -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one G A B p,
    pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`** when `ResidueField B` is
finite (the tamely ramified case), without assuming `G_0` is finite. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_of_finite_residueField (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ResidueField B)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  by_cases hfin : Finite (ramificationGroup G B 0)
  · exact ramificationGroup_one_eq_bot_iff_not_dvd_card G A B p
  · have hinf := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    simp only [dvd_zero, not_true_eq_false, iff_false]
    intro h
    have hker := TauCeti.IsLocalRing.ker_tameCharacter A (G := G) (S := B)
    rw [h, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff] at hker
    exact hfin (Finite.of_injective _ hker)

/-- When `p` does not divide `#G_0`, every positive-depth ramification group `G_i` (`i > 0`) is
trivial. -/
theorem ramificationGroup_eq_bot_of_not_dvd_card (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    {i : ℤ} (hi : 0 < i) (hp : ¬ p ∣ Nat.card (ramificationGroup G B 0)) :
    ramificationGroup G B i = ⊥ :=
  eq_bot_mono (ramificationGroup_antitone G B (by omega : (1 : ℤ) ≤ i))
    ((ramificationGroup_one_eq_bot_iff_not_dvd_card G A B p).mpr hp)

end Consequences

end TauCeti.IsDiscreteValuationRing
