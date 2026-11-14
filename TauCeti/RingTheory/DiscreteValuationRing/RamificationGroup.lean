/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Graded embeddings of the ramification filtration on a discrete valuation ring

Let a group `G` act by ring automorphisms on a discrete valuation ring `S` with maximal ideal `𝔪`
and residue field `κ`. For a uniformizer `ϖ` and `σ ∈ G_i` (`i : ℕ`), the image `σ • ϖ` is again a
uniformizer, so `σ • ϖ = ϖ * u_σ` for a unique unit `u_σ : Sˣ` (`uniformizerChangeUnit`). Writing
`ϖ * (u_σ - 1) = σ • ϖ - ϖ ∈ 𝔪 ^ (i + 1)` and cancelling `ϖ` places `u_σ` in the `i`-th principal
unit group `U(S, i) = (𝔪 ^ i).principalUnitGroup` (with `U(S, 0) = Sˣ`).

Modulo `U(S, i + 1)`, the assignment `σ ↦ u_σ` is a group homomorphism
`G_i →* U(S, i) / U(S, i + 1)` that does not depend on the choice of uniformizer `ϖ` and kills
`G_{i+1}`, descending to `G_i / G_{i+1}`. Composing with the canonical isomorphism
`U(S, 0) / U(S, 1) ≃* κˣ` gives the **tame character** `G_0 / G_1 →* κˣ`, still independent of `ϖ`,
while for `i = n + 1 ≥ 1` a choice of uniformizer `ϖ` identifies `U(S, n + 1) / U(S, n + 2)` with
the additive group of `κ` via `1 + y * ϖ ^ (n + 1) ↦ residue S y`, producing an additive
homomorphism `Additive (G_{n+1} / G_{n+2}) →+ κ` that scales by `(residue S a) ^ (n + 1)` when `ϖ`
is replaced by `ϖ' = ϖ * a`. None of these constructions require a fraction field or a separability
hypothesis.

When `S` is a local algebra over a local ring `R` fixed by `G` and the residue field extension
`ResidueField S / ResidueField R` is separable, membership of `σ ∈ G_0` in `G_n` is decided at `ϖ`
alone (`mem_ramificationGroup_natCast_iff_smul_sub_mem`), so the kernel of
`G_i →* U(S, i) / U(S, i + 1)` is `G_{i+1}` and all three graded maps are embeddings. Combined
with the positive-depth `p`-group and characteristic-zero vanishing theorems from
`TauCeti/RingTheory/LocalRing/RamificationGroup.lean`, this yields Serre's structure theorems for
inertia and wild inertia:
* `G_0 / G_1` is cyclic whenever it is finite, of order prime to the residue characteristic `p`;
* if the residue characteristic is a prime `p`, the action is faithful, and `G_0` is finite, then
  `G_1` is the unique Sylow `p`-subgroup of `G_0`, and `G_1 = ⊥ ↔ ¬ p ∣ #G_0`;
* if the residue characteristic is zero, the action is faithful, and `G_0` is finite, then `G_1 = ⊥`
  and `G_0` itself embeds into `κˣ` and is cyclic.

The graded homomorphisms, uniformizer-change formulas, and Sylow consequences adapt the local-field
development in `TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean` and
`TauCeti/NumberTheory/LocalField/UnitFiltration/Uniformizer.lean`, together with the Cauchy-root
coprimality argument of `TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`, to
arbitrary discrete valuation rings without finiteness of the residue field or reference to an
ambient valued field.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.PrincipalUnitGraded S i`: the `i`-th successive quotient
  `U(S, i) / U(S, i + 1)` of the filtration of `Sˣ` by `(𝔪 ^ i).principalUnitGroup`.
* `TauCeti.IsDiscreteValuationRing.principalUnitGradedZeroEquiv S`: the depth-zero identification
  `U(S, 0) / U(S, 1) ≃* (ResidueField S)ˣ`.
* `TauCeti.IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField`: the uniformizer
  coordinate `Additive (U(S, n + 1) / U(S, n + 2)) ≃+ ResidueField S`.
* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u_σ ∈ U(S, i)` satisfying
  `ϖ * u_σ = σ • ϖ`, for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded`: the
  uniformizer-independent homomorphisms `G_i →* U(S, i) / U(S, i + 1)` and
  `G_i / G_{i+1} →* U(S, i) / U(S, i + 1)`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter` and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded`: the tame character `G_0 →* κˣ` and its
  descent `G_0 / G_1 →* κˣ`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToResidueField` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField`: the positive-depth
  additive coordinate `Additive (G_{n+1} / G_{n+2}) →+ κ` attached to a uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: `G_1` as the unique normal Sylow
  `p`-subgroup of `G_0` under separable residue extension in prime residue characteristic `p`.

## Main results

* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_eq_of_irreducible`
  and `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_eq_of_irreducible`: independence of the
  chosen uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_change`:
  uniformizer-change scaling at positive depth.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: injectivity of
  the graded maps when the residue extension is separable.
* `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`: `G_0 / G_1` is cyclic of
  order prime to the residue characteristic.
* `TauCeti.IsDiscreteValuationRing.eq_ramificationGroupOneSylow`,
  `TauCeti.IsDiscreteValuationRing.natCard_ramificationGroup_one`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroup_one_eq_bot_iff_not_dvd_card`:
  characterization and order of wild inertia in prime residue characteristic.
* `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_of_charZero` and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue
  characteristic zero, `G_0` embeds into `κˣ` and is cyclic.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–2, Propositions 1, 2, 5, 6, 7.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, §3.1, Proposition 1.
-/

public section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section PrincipalUnitGraded

/-- The `i`-th successive quotient `U(S, i) / U(S, i + 1)` of the filtration of `Sˣ` by the
principal unit groups `(𝔪 ^ i).principalUnitGroup` of powers of the maximal ideal. At `i = 0`,
`(𝔪 ^ 0).principalUnitGroup = ⊤` is the full unit group `Sˣ`. -/
abbrev PrincipalUnitGraded (S : Type*) [CommRing S] [IsLocalRing S] (i : ℕ) :=
  (maximalIdeal S ^ i).principalUnitGroup ⧸
    (maximalIdeal S ^ (i + 1)).principalUnitGroup.subgroupOf
      (maximalIdeal S ^ i).principalUnitGroup

section Zero

variable {S : Type*} [CommRing S] [IsLocalRing S]

private noncomputable def principalUnitZeroToResidueUnits (S : Type*) [CommRing S] [IsLocalRing S] :
    (maximalIdeal S ^ 0).principalUnitGroup →* (ResidueField S)ˣ :=
  (Units.map (residue S).toMonoidHom).comp (maximalIdeal S ^ 0).principalUnitGroup.subtype

private theorem ker_principalUnitZeroToResidueUnits :
    (principalUnitZeroToResidueUnits S).ker =
      (maximalIdeal S ^ 1).principalUnitGroup.subgroupOf
        (maximalIdeal S ^ 0).principalUnitGroup := by
  ext u
  rw [principalUnitZeroToResidueUnits, MonoidHom.mem_ker, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← MonoidHom.mem_ker, ← Ideal.principalUnitGroup_ker,
    IsLocalRing.ker_residue, Subgroup.mem_subgroupOf, pow_one]

private theorem principalUnitZeroToResidueUnits_surjective :
    Function.Surjective (principalUnitZeroToResidueUnits S) := by
  have hres : Function.Surjective (Units.map (residue S).toMonoidHom) :=
    IsLocalRing.surjective_units_map_of_local_ringHom _ residue_surjective inferInstance
  intro v
  obtain ⟨u, rfl⟩ := hres v
  exact ⟨⟨u, by simp⟩, rfl⟩

variable (S) in
/-- At depth `0`, reduction of units modulo the maximal ideal identifies
`U(S, 0) / U(S, 1) = Sˣ / (1 + 𝔪)` with `(ResidueField S)ˣ`. -/
noncomputable def principalUnitGradedZeroEquiv :
    PrincipalUnitGraded S 0 ≃* (ResidueField S)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_principalUnitZeroToResidueUnits (S := S)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ principalUnitZeroToResidueUnits_surjective)

@[simp]
theorem principalUnitGradedZeroEquiv_mk (u : (maximalIdeal S ^ 0).principalUnitGroup) :
    principalUnitGradedZeroEquiv S (QuotientGroup.mk u) =
      Units.map (residue S).toMonoidHom (u : Sˣ) :=
  (MulEquiv.trans_apply ..).trans <|
    (congrArg _ (QuotientGroup.quotientMulEquivOfEq_mk ..)).trans
      (TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk ..)

theorem coe_principalUnitGradedZeroEquiv_mk (u : (maximalIdeal S ^ 0).principalUnitGroup) :
    (principalUnitGradedZeroEquiv S (QuotientGroup.mk u) : ResidueField S) =
      residue S ((u : Sˣ) : S) := by
  rw [principalUnitGradedZeroEquiv_mk]
  rfl

end Zero

section Succ

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

private theorem comap_maximalIdeal_pow_succ_eq_smul_top (n : ℕ) :
    Submodule.comap (maximalIdeal S ^ (n + 1)).subtype (maximalIdeal S ^ (n + 2)) =
      (maximalIdeal S • ⊤ : Submodule S (maximalIdeal S ^ (n + 1) : Ideal S)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_smul_top_iff, smul_eq_mul,
    pow_succ']

/-- At positive depth `n + 1`, fixing a uniformizer `ϖ` identifies the additive group of
`U(S, n + 1) / U(S, n + 2)` with `ResidueField S` by sending the class of `1 + y * ϖ ^ (n + 1)` to
`residue S y`. -/
noncomputable def principalUnitGradedSuccEquivResidueField (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    Additive (PrincipalUnitGraded S (n + 1)) ≃+ ResidueField S :=
  (Ideal.principalUnitGroupPowQuotientEquiv
      (Ideal.jacobson_bot.trans (ringJacobson_eq_maximalIdeal S)).ge n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative _).trans <|
      (Submodule.quotEquivOfEq _ _ (comap_maximalIdeal_pow_succ_eq_smul_top (S := S) n)).toAddEquiv
        |>.trans (residueFieldEquivMaximalIdealGradedOfUniformizer ϖ hϖ (n + 1)).symm.toAddEquiv

/-- Applying `residueFieldEquivMaximalIdealGradedOfUniformizer` to the uniformizer coordinate of
`u ∈ U(S, n + 1)` recovers the class of `u - 1` in `𝔪 ^ (n + 1) ⧸ 𝔪 ^ (n + 2)`. -/
@[simp]
theorem apply_principalUnitGradedSuccEquivResidueField_ofMul_mk (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (u : (maximalIdeal S ^ (n + 1)).principalUnitGroup) :
    residueFieldEquivMaximalIdealGradedOfUniformizer ϖ hϖ (n + 1)
        (principalUnitGradedSuccEquivResidueField n hϖ
          (Additive.ofMul (QuotientGroup.mk u))) =
      Submodule.Quotient.mk ⟨((u : Sˣ) : S) - 1, Ideal.mem_principalUnitGroup.mp u.2⟩ := by
  rw [principalUnitGradedSuccEquivResidueField]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    Ideal.principalUnitGroupPowQuotientEquiv_mk, AddEquiv.additiveMultiplicative_apply,
    toAdd_ofAdd, LinearEquiv.coe_toAddEquiv]
  exact LinearEquiv.apply_symm_apply _ _

/-- If `u - 1 = y * ϖ ^ (n + 1)` for `u ∈ U(S, n + 1)`, then the uniformizer coordinate of the
class of `u` in `U(S, n + 1) / U(S, n + 2)` is `residue S y`. -/
theorem principalUnitGradedSuccEquivResidueField_ofMul_mk_eq_residue (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (u : (maximalIdeal S ^ (n + 1)).principalUnitGroup) (y : S)
    (hu : ((u : Sˣ) : S) - 1 = y * ϖ ^ (n + 1)) :
    principalUnitGradedSuccEquivResidueField n hϖ
        (Additive.ofMul (QuotientGroup.mk u)) = residue S y := by
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer ϖ hϖ (n + 1)).injective
  rw [apply_principalUnitGradedSuccEquivResidueField_ofMul_mk,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hu)

/-- Replacing the uniformizer `ϖ` by `ϖ' = ϖ * a` scales the positive-depth principal-unit
coordinate by `(residue S a) ^ (n + 1)`. -/
theorem principalUnitGradedSuccEquivResidueField_change (n : ℕ) {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (x : Additive (PrincipalUnitGraded S (n + 1))) :
    principalUnitGradedSuccEquivResidueField n hϖ x =
      residue S (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : S) ^ (n + 1) *
        principalUnitGradedSuccEquivResidueField n hϖ' x :=
  residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change ϖ ϖ' hϖ hϖ' (n + 1) _

end Succ

end PrincipalUnitGraded

section UniformizerRatio

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

/-- Cancelling a uniformizer from membership in a positive power of the maximal ideal. -/
private theorem mul_mem_maximalIdeal_pow_succ_iff {ϖ : S} (hϖ : Irreducible ϖ) (k : ℕ) (z : S) :
    ϖ * z ∈ maximalIdeal S ^ (k + 1) ↔ z ∈ maximalIdeal S ^ k := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow, pow_succ',
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, mul_dvd_mul_iff_left hϖ.ne_zero]

/-- The induced action of `G` on `Sˣ`. -/
private def smulUnits (σ : G) (u : Sˣ) : Sˣ :=
  Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom u

omit [IsDomain S] [IsDiscreteValuationRing S] in
@[simp]
private theorem coe_smulUnits (σ : G) (u : Sˣ) : ((smulUnits σ u : Sˣ) : S) = σ • (u : S) :=
  rfl

omit [IsDomain S] [IsDiscreteValuationRing S] in
private theorem irreducible_smul (σ : G) {ϖ : S} (hϖ : Irreducible ϖ) :
    Irreducible (σ • ϖ) := by
  simpa only [MulSemiringAction.toRingEquiv_apply_apply] using
    hϖ.map (MulSemiringAction.toRingEquiv G S σ)

/-- An element `σ ∈ G_i` moves every unit `u : Sˣ` by a factor in `U(S, i + 1)`. -/
private theorem smulUnits_mul_inv_mem_principalUnitGroup {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S i) (u : Sˣ) :
    smulUnits σ u * u⁻¹ ∈ (maximalIdeal S ^ (i + 1)).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup]
  have hsub : ((smulUnits σ u * u⁻¹ : Sˣ) : S) - 1 = (σ • (u : S) - (u : S)) * (↑u⁻¹ : S) := by
    rw [Units.val_mul, coe_smulUnits, sub_mul, Units.mul_inv]
  rw [hsub]
  exact Ideal.mul_mem_right _ _ (mem_ramificationGroup_natCast_iff.mp hσ (u : S))

/-- For a uniformizer `ϖ` and `σ ∈ G_i`, the **uniformizer ratio** `u_σ ∈ U(S, i)` is the unique
unit satisfying `ϖ * u_σ = σ • ϖ`. -/
noncomputable def uniformizerRatio (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S i) : (maximalIdeal S ^ i).principalUnitGroup :=
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ (irreducible_smul (σ : G) hϖ), by
    rw [Ideal.mem_principalUnitGroup, ← mul_mem_maximalIdeal_pow_succ_iff hϖ i]
    have hmul :
        ϖ * ((uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
          (irreducible_smul (σ : G) hϖ) : S) - 1) = (σ : G) • ϖ - ϖ := by
      rw [mul_sub, mul_uniformizerChangeUnit, mul_one]
    rw [hmul]
    exact mem_ramificationGroup_natCast_iff.mp σ.2 ϖ⟩

/-- The defining identity `ϖ * uniformizerRatio i hϖ σ = σ • ϖ` in `S`. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S i) :
    ϖ * (((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S) =
      (σ : G) • ϖ :=
  mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

@[simp]
theorem uniformizerRatio_one (G : Type*) [Group G] [MulSemiringAction G S] (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) :
    uniformizerRatio i hϖ (1 : ramificationGroup G S i) = 1 := by
  ext
  apply mul_left_cancel₀ hϖ.ne_zero
  have h := mul_coe_uniformizerRatio i hϖ (1 : ramificationGroup G S i)
  simp only [Subgroup.coe_one, one_smul] at h
  simpa only [Subgroup.coe_one, Units.val_one, mul_one] using h

/-- Twisted multiplicativity (1-cocycle law) of `uniformizerRatio` in `Sˣ`:
`u_{σ * τ} = u_σ * σ(u_τ)`. -/
private theorem coe_uniformizerRatio_mul (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G S i) :
    ((uniformizerRatio i hϖ (σ * τ) : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
      (uniformizerRatio i hϖ σ : Sˣ) * smulUnits (σ : G) (uniformizerRatio i hϖ τ : Sˣ) := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  calc
    ϖ * (((uniformizerRatio i hϖ (σ * τ) : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S)
      = (σ * τ : G) • ϖ := mul_coe_uniformizerRatio i hϖ (σ * τ)
    _ = (σ : G) • (ϖ * (((uniformizerRatio i hϖ τ :
          (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) : S)) := by
        rw [mul_smul, mul_coe_uniformizerRatio]
    _ = ϖ * ((((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) *
          smulUnits (σ : G) (uniformizerRatio i hϖ τ : Sˣ) : Sˣ) : S) := by
        rw [smul_mul', ← mul_coe_uniformizerRatio i hϖ σ, Units.val_mul, coe_smulUnits, mul_assoc]

/-- Replacing `ϖ` by `ϖ' = ϖ * a` multiplies `uniformizerRatio` by the coboundary `σ(a) * a⁻¹`. -/
private theorem coe_uniformizerRatio_change (i : ℕ) {ϖ ϖ' : S} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (σ : ramificationGroup G S i) :
    uniformizerChangeUnit ϖ ϖ' hϖ hϖ' *
        ((uniformizerRatio i hϖ' σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
      ((uniformizerRatio i hϖ σ : (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) *
        smulUnits (σ : G) (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') := by
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
          smulUnits (σ : G) (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') : Sˣ) : S) := by
        rw [smul_mul', ← mul_coe_uniformizerRatio i hϖ σ, Units.val_mul, coe_smulUnits, mul_assoc]

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
    let uσ : Sˣ := uniformizerRatio i hϖ σ
    let uτ : Sˣ := uniformizerRatio i hϖ τ
    let v : Sˣ := smulUnits (σ : G) uτ
    have heq :
        (((uniformizerRatio i hϖ (σ * τ))⁻¹ *
          (uniformizerRatio i hϖ σ * uniformizerRatio i hϖ τ) :
          (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) = (v * uτ⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_uniformizerRatio_mul, uτ, v]
      apply mul_left_cancel (a := uσ * v)
      apply mul_right_cancel (b := v)
      have h1 : (uσ * v) * ((uσ * v)⁻¹ * (uσ * uτ)) * v = (uσ * uτ) * v := by group
      have h2 : (uσ * v) * (v * uτ⁻¹)⁻¹ * v = (uσ * v) * uτ := by group
      rw [h1, h2]
      ext
      simp only [Units.val_mul]
      ring
    rw [heq]
    exact inv_mem (smulUnits_mul_inv_mem_principalUnitGroup σ.2 uτ)

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
  have hrel := coe_uniformizerRatio_change i hϖ hϖ' σ
  have heq :
      (((uniformizerRatio i hϖ σ)⁻¹ * uniformizerRatio i hϖ' σ :
        (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
      smulUnits (σ : G) a * a⁻¹ := by
    apply mul_left_cancel (a := a * (uniformizerRatio i hϖ σ : Sˣ))
    apply mul_right_cancel (b := a)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, a]
    calc
      a * (uniformizerRatio i hϖ σ : Sˣ) *
          ((uniformizerRatio i hϖ σ : Sˣ)⁻¹ * (uniformizerRatio i hϖ' σ : Sˣ)) * a
        = (a * (uniformizerRatio i hϖ' σ : Sˣ)) * a := by group
      _ = ((uniformizerRatio i hϖ σ : Sˣ) * smulUnits (σ : G) a) * a := by rw [hrel]
      _ = a * (uniformizerRatio i hϖ σ : Sˣ) * (smulUnits (σ : G) a * a⁻¹) * a := by
          have hr :
              a * (uniformizerRatio i hϖ σ : Sˣ) * (smulUnits (σ : G) a * a⁻¹) * a =
                a * (uniformizerRatio i hϖ σ : Sˣ) * smulUnits (σ : G) a := by group
          rw [hr]
          ext
          simp only [Units.val_mul]
          ring
  rw [heq]
  exact smulUnits_mul_inv_mem_principalUnitGroup σ.2 a

/-- An element `σ ∈ G_i` lies in the kernel of `G_i →* U(S, i) / U(S, i + 1)` if and only if it
moves `ϖ` into `𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGraded_iff (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) {σ : ramificationGroup G S i} :
    σ ∈ (ramificationGroupToPrincipalUnitGraded G i hϖ).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal S ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGraded_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Ideal.mem_principalUnitGroup,
    ← mul_mem_maximalIdeal_pow_succ_iff hϖ (i + 1)]
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
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

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
    exact DFunLike.congr_fun
      (ramificationGroupToPrincipalUnitGraded_eq_of_irreducible G i hϖ hϖ') σ

end UniformizerRatio

section Coordinates

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

/-! ### Depth zero: the tame character -/

variable (G) in
/-- The **tame character** `G_0 →* (ResidueField S)ˣ`, sending `σ ∈ G_0` to the residue of the unit
`u_σ` satisfying `ϖ * u_σ = σ • ϖ`. It is independent of `ϖ` (`tameCharacter_eq_of_irreducible`)
and kills `G_1`. -/
noncomputable def tameCharacter {ϖ : S} (hϖ : Irreducible ϖ) :
    ramificationGroup G S 0 →* (ResidueField S)ˣ :=
  (principalUnitGradedZeroEquiv S).toMonoidHom.comp
    (ramificationGroupToPrincipalUnitGraded G 0 hϖ)

/-- Evaluating `tameCharacter` reduces `uniformizerRatio 0 hϖ σ` modulo the maximal ideal. -/
theorem tameCharacter_apply {ϖ : S} (hϖ : Irreducible ϖ) (σ : ramificationGroup G S 0) :
    tameCharacter G hϖ σ = Units.map (residue S).toMonoidHom (uniformizerRatio 0 hϖ σ : Sˣ) :=
  principalUnitGradedZeroEquiv_mk (uniformizerRatio 0 hϖ σ)

/-- If `ϖ * y = σ • ϖ` in `S`, then `(tameCharacter G hϖ σ : ResidueField S)` is `residue S y`. -/
theorem coe_tameCharacter_of_mul_eq {ϖ : S} (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G S 0} {y : S} (hy : ϖ * y = (σ : G) • ϖ) :
    (tameCharacter G hϖ σ : ResidueField S) = residue S y := by
  have hy_eq :
      (((uniformizerRatio 0 hϖ σ : (maximalIdeal S ^ 0).principalUnitGroup) : Sˣ) : S) = y :=
    mul_left_cancel₀ hϖ.ne_zero ((mul_coe_uniformizerRatio 0 hϖ σ).trans hy.symm)
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGraded_apply, coe_principalUnitGradedZeroEquiv_mk, hy_eq]

variable (G) in
/-- The tame character is independent of the chosen uniformizer. -/
theorem tameCharacter_eq_of_irreducible {ϖ ϖ' : S} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    tameCharacter G hϖ = tameCharacter G hϖ' := by
  rw [tameCharacter, tameCharacter,
    ramificationGroupToPrincipalUnitGraded_eq_of_irreducible G 0 hϖ hϖ']

/-- An element `σ ∈ G_0` lies in the kernel of `tameCharacter` iff `σ • ϖ - ϖ ∈ 𝔪 ^ 2`. -/
theorem mem_ker_tameCharacter_iff {ϖ : S} (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G S 0} :
    σ ∈ (tameCharacter G hϖ).ker ↔ (σ : G) • ϖ - ϖ ∈ maximalIdeal S ^ 2 := by
  rw [tameCharacter, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGradedZeroEquiv S).injective, ← MonoidHom.mem_ker]
  exact mem_ker_ramificationGroupToPrincipalUnitGraded_iff 0 hϖ

variable (G) in
/-- The descended **tame character** `G_0 / G_1 →* (ResidueField S)ˣ`. -/
noncomputable def tameCharacterGraded {ϖ : S} (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G S 0 →* (ResidueField S)ˣ :=
  (principalUnitGradedZeroEquiv S).toMonoidHom.comp
    (ramificationGroupGradedToPrincipalUnitGraded G 0 hϖ)

@[simp]
theorem tameCharacterGraded_mk {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S 0) :
    tameCharacterGraded G hϖ (QuotientGroup.mk σ) = tameCharacter G hϖ σ :=
  (rfl)

variable (G) in
/-- The descended tame character is independent of the chosen uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {ϖ ϖ' : S} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacterGraded G hϖ = tameCharacterGraded G hϖ' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    ramificationGroupGradedToPrincipalUnitGraded_eq_of_irreducible G 0 hϖ hϖ']

/-! ### Positive depth: additive residue coordinates -/

variable (G) in
private def ramificationGroupSuccEquiv (n : ℕ) :
    ramificationGroup G S ((n : ℤ) + 1) ≃* ramificationGroup G S (n + 1 : ℕ) :=
  MulEquiv.subgroupCongr (by push_cast; rfl)

variable (G) in
private noncomputable def ramificationGroupGradedSuccEquiv (n : ℕ) :
    RamificationGroupGraded G S ((n : ℤ) + 1) ≃* RamificationGroupGraded G S (n + 1 : ℕ) :=
  QuotientGroup.congr _ _ (ramificationGroupSuccEquiv G n) <| by
    ext ⟨σ, hσ⟩
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    refine ⟨?_, fun h ↦ ⟨⟨σ, by exact_mod_cast hσ⟩, ?_, rfl⟩⟩
    · rintro ⟨⟨_, _⟩, h, hστ⟩
      cases Subtype.mk.inj hστ
      exact_mod_cast h
    · rw [Subgroup.mem_subgroupOf]
      exact_mod_cast h

variable (G) in
/-- The positive-depth additive homomorphism `Additive G_{n+1} →+ ResidueField S` attached to a
uniformizer `ϖ`, sending `σ` with `σ • ϖ - ϖ = y * ϖ ^ (n + 2)` to `residue S y`. -/
noncomputable def ramificationGroupToResidueField (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    Additive (ramificationGroup G S ((n : ℤ) + 1)) →+ ResidueField S :=
  (principalUnitGradedSuccEquivResidueField n hϖ).toAddMonoidHom.comp
    ((ramificationGroupToPrincipalUnitGraded G (n + 1) hϖ).comp
      (ramificationGroupSuccEquiv G n).toMonoidHom).toAdditive

variable (G) in
/-- The positive-depth additive homomorphism `Additive (G_{n+1} / G_{n+2}) →+ ResidueField S` in
the coordinate determined by a uniformizer `ϖ`. -/
noncomputable def ramificationGroupGradedToResidueField (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    Additive (RamificationGroupGraded G S ((n : ℤ) + 1)) →+ ResidueField S :=
  (principalUnitGradedSuccEquivResidueField n hϖ).toAddMonoidHom.comp
    ((ramificationGroupGradedToPrincipalUnitGraded G (n + 1) hϖ).comp
      (ramificationGroupGradedSuccEquiv G n).toMonoidHom).toAdditive

@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (τ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G n hϖ (Additive.ofMul (QuotientGroup.mk τ)) =
      ramificationGroupToResidueField G n hϖ (Additive.ofMul τ) :=
  (rfl)

/-- If `τ ∈ G_{n+1}` satisfies `(τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)`, then
`ramificationGroupToResidueField` sends `τ` to `residue S y`. -/
theorem ramificationGroupToResidueField_of_smul_sub_eq (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (τ : ramificationGroup G S ((n : ℤ) + 1)) (y : S)
    (hmove : (τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)) :
    ramificationGroupToResidueField G n hϖ (Additive.ofMul τ) = residue S y := by
  let τ' : ramificationGroup G S (n + 1 : ℕ) := ramificationGroupSuccEquiv G n τ
  have hu :
      ((((uniformizerRatio (n + 1) hϖ τ' :
        (maximalIdeal S ^ (n + 1)).principalUnitGroup) : Sˣ) : S) - 1) =
        y * ϖ ^ (n + 1) := by
    apply mul_left_cancel₀ hϖ.ne_zero
    calc
      ϖ * ((((uniformizerRatio (n + 1) hϖ τ' :
            (maximalIdeal S ^ (n + 1)).principalUnitGroup) : Sˣ) : S) - 1)
        = (τ : G) • ϖ - ϖ := by
            rw [mul_sub, mul_coe_uniformizerRatio, mul_one]
            rfl
      _ = y * ϖ ^ (n + 2) := hmove
      _ = ϖ * (y * ϖ ^ (n + 1)) := by rw [pow_succ']; ring
  exact principalUnitGradedSuccEquivResidueField_ofMul_mk_eq_residue n hϖ
    (uniformizerRatio (n + 1) hϖ τ') y hu

/-- If `τ ∈ G_{n+1}` satisfies `(τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)`, then its positive-depth
residue coordinate with respect to `ϖ` is `residue S y`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (τ : ramificationGroup G S ((n : ℤ) + 1)) (y : S)
    (hmove : (τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)) :
    ramificationGroupGradedToResidueField G n hϖ
        (Additive.ofMul (QuotientGroup.mk τ)) = residue S y :=
  ramificationGroupToResidueField_of_smul_sub_eq n hϖ τ y hmove

/-- An element `τ ∈ G_{n+1}` lies in the kernel of `ramificationGroupToResidueField` iff
`τ • ϖ - ϖ ∈ 𝔪 ^ (n + 3)`. -/
theorem mem_ker_ramificationGroupToResidueField_iff (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    {τ : ramificationGroup G S ((n : ℤ) + 1)} :
    Additive.ofMul τ ∈ (ramificationGroupToResidueField G n hϖ).ker ↔
      (τ : G) • ϖ - ϖ ∈ maximalIdeal S ^ (n + 3) := by
  rw [ramificationGroupToResidueField, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom,
    map_eq_zero_iff _ (principalUnitGradedSuccEquivResidueField n hϖ).injective,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, ofMul_eq_zero, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
    mem_ker_ramificationGroupToPrincipalUnitGraded_iff (n + 1) hϖ]
  rfl

/-- Replacing `ϖ` by `ϖ' = ϖ * a` scales `ramificationGroupGradedToResidueField` by
`(residue S a) ^ (n + 1)`. -/
theorem ramificationGroupGradedToResidueField_change (n : ℕ) {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (τ : RamificationGroupGraded G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G n hϖ (Additive.ofMul τ) =
      residue S (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : S) ^ (n + 1) *
        ramificationGroupGradedToResidueField G n hϖ' (Additive.ofMul τ) := by
  have htheta := DFunLike.congr_fun
    (ramificationGroupGradedToPrincipalUnitGraded_eq_of_irreducible G (n + 1) hϖ hϖ')
    (ramificationGroupGradedSuccEquiv G n τ)
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [principalUnitGradedSuccEquivResidueField_change n hϖ hϖ', htheta]

end Coordinates

section SeparableResidue

variable {G : Type*} [Group G] (R : Type*) [CommRing R] [IsLocalRing R]
  {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
include R

/-- **Testing `G_n` at a uniformizer.** When `S` is a discrete valuation ring over a local ring `R`
fixed by `G` with separable residue extension, an element `σ ∈ G_0` lies in `G_n` if and only if
`σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem {ϖ : S} (hϖ : Irreducible ϖ)
    {n : ℕ} {σ : G} (hσ₀ : σ ∈ ramificationGroup G S 0) :
    σ ∈ ramificationGroup G S n ↔ σ • ϖ - ϖ ∈ maximalIdeal S ^ (n + 1) :=
  mem_ramificationGroup_natCast_iff_smul_sub_mem_of_span_eq_maximalIdeal R
    hϖ.maximalIdeal_eq.symm hσ₀

/-! ### Exactness and injectivity of the graded maps -/

variable (G) in
/-- Under separable residue extension, the kernel of `G_i →* U(S, i) / U(S, i + 1)` is `G_{i+1}`. -/
theorem ker_ramificationGroupToPrincipalUnitGraded (i : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    (ramificationGroupToPrincipalUnitGraded G i hϖ).ker =
      (ramificationGroup G S ((i : ℤ) + 1)).subgroupOf (ramificationGroup G S i) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker G i hϖ)
  rw [mem_ker_ramificationGroupToPrincipalUnitGraded_iff i hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G S 0 :=
    ramificationGroup_antitone G S (Int.natCast_nonneg i) σ.2
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ hσ₀]
  exact hσ

variable (G) in
/-- **Graded unit-filtration embedding.** Under separable residue extension, the uniformizer-ratio
map embeds `G_i / G_{i+1}` into `U(S, i) / U(S, i + 1)`. -/
theorem ramificationGroupGradedToPrincipalUnitGraded_injective (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGraded G i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGraded G R i hϖ).symm

variable (G) in
/-- Under separable residue extension, the kernel of the tame character `G_0 →* κˣ` is `G_1`. -/
theorem ker_tameCharacter {ϖ : S} (hϖ : Irreducible ϖ) :
    (tameCharacter G hϖ).ker =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) := by
  ext σ
  rw [mem_ker_tameCharacter_iff hϖ, Subgroup.mem_subgroupOf]
  have h1 : (1 : ℤ) = ((1 : ℕ) : ℤ) := rfl
  rw [h1, mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ σ.2]

variable (G) in
/-- **Tame character embedding.** Under separable residue extension, `G_0 / G_1` embeds into
`(ResidueField S)ˣ`. -/
theorem tameCharacterGraded_injective {ϖ : S} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacterGraded G hϖ) :=
  (principalUnitGradedZeroEquiv S).injective.comp
    (ramificationGroupGradedToPrincipalUnitGraded_injective G R 0 hϖ)

variable (G) in
/-- **Positive-depth additive embedding.** Under separable residue extension, each positive graded
piece `G_{n+1} / G_{n+2}` embeds into the additive group of `ResidueField S`. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToResidueField G n hϖ) :=
  (principalUnitGradedSuccEquivResidueField n hϖ).injective.comp <|
    (ramificationGroupGradedToPrincipalUnitGraded_injective G R (n + 1) hϖ).comp
      (ramificationGroupGradedSuccEquiv G n).injective

/-! ### Consequences for tame inertia `G_0 / G_1` and wild inertia `G_1` -/

variable (G S) in
/-- **Tame inertia is cyclic.** When `G_0 / G_1` is finite and the residue extension is separable,
`G_0 / G_1` is cyclic, because it embeds into the multiplicative group of the field
`ResidueField S`. -/
theorem isCyclic_ramificationGroupGraded_zero [Finite (RamificationGroupGraded G S 0)] :
    IsCyclic (RamificationGroupGraded G S 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacterGraded G hϖ))
    (Units.val_injective.comp (tameCharacterGraded_injective G R hϖ))

variable (G S) in
/-- **The order of `G_0 / G_1` is prime to the residue characteristic `p`.** A field of
characteristic `p` has no nontrivial `p`-th roots of unity, while `G_0 / G_1` embeds into
`(ResidueField S)ˣ`. -/
theorem not_dvd_card_ramificationGroupGraded_zero (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [Finite (RamificationGroupGraded G S 0)] :
    ¬ p ∣ Nat.card (RamificationGroupGraded G S 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  let φ := tameCharacterGraded G hϖ
  have hφ := tameCharacterGraded_injective G R hϖ
  intro hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
  have hord : orderOf ((φ x : (ResidueField S)ˣ) : ResidueField S) = p := by
    rw [orderOf_units, orderOf_injective φ hφ x, hx]
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hroot := hord ▸ IsPrimitiveRoot.orderOf ((φ x : (ResidueField S)ˣ) : ResidueField S)
  exact hroot.neZero'.out (CharP.cast_eq_zero _ p)

variable (G S) in
/-- **The index `[G_0 : G_1]` is prime to the residue characteristic `p`.** -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [Finite (RamificationGroupGraded G S 0)] :
    ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index := by
  rw [Subgroup.index_eq_card]
  exact not_dvd_card_ramificationGroupGraded_zero G R S p

section PrimeChar

variable (G S) (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
  [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]

/-- **Wild inertia is a Sylow `p`-subgroup of inertia.** When the residue extension is separable,
the residue characteristic `p` is prime, the action is faithful, and `G_0` is finite, `G_1` viewed
inside `G_0` is a Sylow `p`-subgroup of `G_0`: it is a `p`-group (`isPGroup_ramificationGroup`) of
index prime to `p` (`not_dvd_index_ramificationGroup_one`). -/
noncomputable def ramificationGroupOneSylow : Sylow p (ramificationGroup G S 0) :=
  ((isPGroup_ramificationGroup G S p zero_lt_one).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one G R S p)

/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe :
    (ramificationGroupOneSylow G R S p : Subgroup (ramificationGroup G S 0)) =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal :
    (ramificationGroupOneSylow G R S p : Subgroup (ramificationGroup G S 0)).Normal := by
  rw [ramificationGroupOneSylow_coe, Subgroup.normal_subgroupOf_iff_le_normalizer
    (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))]
  rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

variable {G S p} in
/-- **Wild inertia is the unique Sylow `p`-subgroup of inertia.** -/
theorem eq_ramificationGroupOneSylow (Q : Sylow p (ramificationGroup G S 0)) :
    Q = ramificationGroupOneSylow G R S p := by
  let _ : Unique (Sylow p (ramificationGroup G S 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow G R S p)
      (ramificationGroupOneSylow_normal G R S p)
  exact Subsingleton.elim _ _

/-- The order of wild inertia is the `p`-part of the order of inertia:
`#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow G R S p)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia vanishes iff `p ∤ #G_0`.** Under separable residue extension in prime residue
characteristic `p`, `G_1 = ⊥` if and only if `p` does not divide the order of `G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card :
    ramificationGroup G S 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G S 0) := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one G R S p, pow_eq_one_iff_right hp.ne_one,
    Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

/-- When `p ∤ #G_0`, every positive-depth ramification group `G_i` (`0 < i`) is trivial. -/
theorem ramificationGroup_eq_bot_of_not_dvd_card {i : ℤ} (hi : 0 < i)
    (hp : ¬ p ∣ Nat.card (ramificationGroup G S 0)) :
    ramificationGroup G S i = ⊥ :=
  eq_bot_iff.mpr <| (ramificationGroup_antitone G S (by omega : 1 ≤ i)).trans <|
    ((ramificationGroup_one_eq_bot_iff_not_dvd_card G R S p).mpr hp).le

end PrimeChar

section CharZero

variable [CharZero (ResidueField S)] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]

variable (G) in
/-- In residue characteristic zero with separable residue extension, `G_1 = ⊥`, so the tame
character `G_0 →* (ResidueField S)ˣ` is itself injective. -/
theorem tameCharacter_injective_of_charZero {ϖ : S} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacter G hϖ) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_tameCharacter G R hϖ,
    ramificationGroup_one_eq_bot_of_charZero G S, Subgroup.bot_subgroupOf]

variable (G S) in
/-- **Inertia is cyclic in residue characteristic zero.** When `ResidueField S` has characteristic
zero, the residue extension is separable, the action is faithful, and `G_0` is finite, `G_0` itself
is cyclic. -/
theorem isCyclic_ramificationGroup_zero_of_charZero :
    IsCyclic (ramificationGroup G S 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacter G hϖ))
    (Units.val_injective.comp (tameCharacter_injective_of_charZero G R hϖ))

end CharZero

end SeparableResidue

end TauCeti.IsDiscreteValuationRing
