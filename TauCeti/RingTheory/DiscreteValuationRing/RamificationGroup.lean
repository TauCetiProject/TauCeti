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
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.RingTheory.IntegralDomain
import TauCeti.RingTheory.RootsOfUnity.Basic

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
`U(S, 0) / U(S, 1) ≃* κˣ` (`TauCeti.IsLocalRing.principalUnitGradedZeroEquiv`) gives the
**tame character** `G_0 / G_1 →* κˣ`, still independent of `ϖ`, while for `i = n + 1 ≥ 1` a choice
of uniformizer `ϖ` identifies `U(S, n + 1) / U(S, n + 2)` with the additive group of `κ` via
`1 + y * ϖ ^ (n + 1) ↦ residue S y` (`principalUnitGradedSuccEquivResidueField`), producing an
additive homomorphism `Additive (G_{n+1} / G_{n+2}) →+ κ` whose coordinate relative to `ϖ` equals
`(residue S a) ^ (n + 1)` times the coordinate relative to `ϖ' = ϖ * a` (equivalently, replacing
`ϖ` by `ϖ * a` multiplies the coordinate by `((residue S a) ^ (n + 1))⁻¹`). None of these
constructions require a fraction field or a separability hypothesis.

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
* if the residue characteristic is zero and the action is faithful, then `G_1 = ⊥` and `G_0` embeds
  into `κˣ` whenever `G_1` is finite (under separable residue extension) or `G_0` is finite
  (without any separability hypothesis), and `G_0` is cyclic whenever `G_0` is finite.

The graded homomorphisms, uniformizer-change formulas, and Sylow consequences adapt the local-field
development in `TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean` and
`TauCeti/NumberTheory/LocalField/UnitFiltration/Uniformizer.lean`, together with the Cauchy-root
coprimality argument of `TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`, to
arbitrary discrete valuation rings without finiteness of the residue field or reference to an
ambient valued field.

## Main definitions

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
  additive homomorphism `Additive G_{n+1} →+ κ` and its descent
  `Additive (G_{n+1} / G_{n+2}) →+ κ` attached to a uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: `G_1` as the unique normal Sylow
  `p`-subgroup of `G_0` under separable residue extension in prime residue characteristic `p`.

## Main results

* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_eq_of_irreducible`
  and `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_eq_of_irreducible`: independence of the
  chosen uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToResidueField_change` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_change`: uniformizer-change
  scaling at positive depth.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: injectivity of
  the graded maps when the residue extension is separable.
* `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_iff` and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot`:
  under separable residue extension, injectivity of the tame character and cyclicity of finite
  inertia when wild inertia is trivial.
* `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`: `G_0 / G_1` is cyclic of
  order prime to the residue characteristic.
* `TauCeti.IsDiscreteValuationRing.eq_ramificationGroupOneSylow`,
  `TauCeti.IsDiscreteValuationRing.natCard_ramificationGroup_one`, and
  `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`:
  characterization and order of wild inertia.
* `TauCeti.IsDiscreteValuationRing.tameCharacter_injective_of_charZero` and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue
  characteristic zero without separability hypotheses, finite `G_0` embeds into `κˣ` and is
  cyclic.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–2, Propositions 1, 2, 5, 6, 7.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, §3.1, Proposition 1.
-/

public section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section UniformizerRatio

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

/-- An element `σ ∈ G_i` moves every unit `u : Sˣ` by a factor in `U(S, i + 1)`. -/
private theorem map_mul_inv_mem_principalUnitGroup {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S i) (u : Sˣ) :
    Units.map (MulDistribMulAction.toMonoidHom S σ) u * u⁻¹ ∈
      (maximalIdeal S ^ (i + 1)).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup]
  have hsub :
      ((Units.map (MulDistribMulAction.toMonoidHom S σ) u * u⁻¹ : Sˣ) : S) - 1 =
        (σ • (u : S) - (u : S)) * (↑u⁻¹ : S) := by
    rw [Units.val_mul, Units.coe_map, MulDistribMulAction.toMonoidHom_apply, sub_mul, Units.mul_inv]
  rw [hsub]
  exact Ideal.mul_mem_right _ _ (mem_ramificationGroup_natCast_iff.mp hσ (u : S))

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
    exact mem_ramificationGroup_natCast_iff.mp σ.2 ϖ⟩

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
    let uσ : Sˣ := uniformizerRatio i hϖ σ
    let uτ : Sˣ := uniformizerRatio i hϖ τ
    let v : Sˣ := Units.map (MulDistribMulAction.toMonoidHom S (σ : G)) uτ
    have heq :
        (((uniformizerRatio i hϖ (σ * τ))⁻¹ *
          (uniformizerRatio i hϖ σ * uniformizerRatio i hϖ τ) :
          (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) = (v * uτ⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_uniformizerRatio_mul]
      rw [mul_comm v uτ⁻¹]
      dsimp only [uσ, uτ, v]
      group
    rw [heq]
    exact inv_mem (map_mul_inv_mem_principalUnitGroup σ.2 uτ)

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
  exact map_mul_inv_mem_principalUnitGroup σ.2 a

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
    tameCharacter G hϖ σ = Units.map (residue S).toMonoidHom (uniformizerRatio 0 hϖ σ : Sˣ) := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGraded_apply, principalUnitGradedZeroEquiv_mk]

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
    tameCharacterGraded G hϖ (QuotientGroup.mk σ) = tameCharacter G hϖ σ := by
  rw [tameCharacterGraded, tameCharacter, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ramificationGroupGradedToPrincipalUnitGraded_mk,
    ramificationGroupToPrincipalUnitGraded_apply]

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
    · rintro ⟨τ, h, hστ⟩
      have hval : (τ : G) = σ :=
        (MulEquiv.subgroupCongr_apply _ τ).symm.trans (congrArg Subtype.val hστ)
      have h' : (τ : G) ∈ ramificationGroup G S ((n : ℤ) + 1 + 1) := Subgroup.mem_subgroupOf.mp h
      simpa only [← hval, Nat.cast_add, Nat.cast_one] using h'
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

/-- Evaluating `ramificationGroupToResidueField` sends `τ ∈ G_{n+1}` to the uniformizer
coordinate of the class of `uniformizerRatio (n + 1) hϖ τ`. -/
theorem ramificationGroupToResidueField_ofMul (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (τ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupToResidueField G n hϖ (Additive.ofMul τ) =
      principalUnitGradedSuccEquivResidueField n hϖ
        (Additive.ofMul (QuotientGroup.mk
          (uniformizerRatio (n + 1) hϖ ⟨(τ : G), by exact_mod_cast τ.2⟩))) := by
  rw [ramificationGroupToResidueField, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ramificationGroupToPrincipalUnitGraded_apply]
  have hτ : ramificationGroupSuccEquiv G n τ = ⟨(τ : G), by exact_mod_cast τ.2⟩ :=
    Subtype.ext (MulEquiv.subgroupCongr_apply _ τ)
  rw [hτ]

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
      ramificationGroupToResidueField G n hϖ (Additive.ofMul τ) := by
  rw [ramificationGroupGradedToResidueField, ramificationGroupToResidueField]
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ramificationGroupGradedSuccEquiv, QuotientGroup.congr_mk,
    ramificationGroupGradedToPrincipalUnitGraded_mk,
    ramificationGroupToPrincipalUnitGraded_apply]

/-- If `τ ∈ G_{n+1}` satisfies `(τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)`, then
`ramificationGroupToResidueField` sends `τ` to `residue S y`. -/
theorem ramificationGroupToResidueField_of_smul_sub_eq (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (τ : ramificationGroup G S ((n : ℤ) + 1)) (y : S)
    (hmove : (τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)) :
    ramificationGroupToResidueField G n hϖ (Additive.ofMul τ) = residue S y := by
  let τ' : ramificationGroup G S (n + 1 : ℕ) := ⟨(τ : G), by exact_mod_cast τ.2⟩
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
      _ = y * ϖ ^ (n + 2) := hmove
      _ = ϖ * (y * ϖ ^ (n + 1)) := by rw [pow_succ']; ring
  rw [ramificationGroupToResidueField_ofMul]
  exact principalUnitGradedSuccEquivResidueField_ofMul_mk_eq_residue n hϖ
    (uniformizerRatio (n + 1) hϖ τ') y hu

/-- If `τ ∈ G_{n+1}` satisfies `(τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)`, then its positive-depth
residue coordinate with respect to `ϖ` is `residue S y`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (τ : ramificationGroup G S ((n : ℤ) + 1)) (y : S)
    (hmove : (τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)) :
    ramificationGroupGradedToResidueField G n hϖ
        (Additive.ofMul (QuotientGroup.mk τ)) = residue S y := by
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  exact ramificationGroupToResidueField_of_smul_sub_eq n hϖ τ y hmove

/-- An element `τ ∈ G_{n+1}` lies in the kernel of `ramificationGroupToResidueField` iff
`τ • ϖ - ϖ ∈ 𝔪 ^ (n + 3)`. -/
theorem mem_ker_ramificationGroupToResidueField_iff (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    {τ : ramificationGroup G S ((n : ℤ) + 1)} :
    Additive.ofMul τ ∈ (ramificationGroupToResidueField G n hϖ).ker ↔
      (τ : G) • ϖ - ϖ ∈ maximalIdeal S ^ (n + 3) := by
  rw [AddMonoidHom.mem_ker, ramificationGroupToResidueField_ofMul,
    map_eq_zero_iff _ (principalUnitGradedSuccEquivResidueField n hϖ).injective, ofMul_eq_zero,
    ← ramificationGroupToPrincipalUnitGraded_apply, ← MonoidHom.mem_ker,
    mem_ker_ramificationGroupToPrincipalUnitGraded_iff (n + 1) hϖ]

/-- When `ϖ' = ϖ * a` with `a = uniformizerChangeUnit ϖ ϖ' hϖ hϖ'`, the positive-depth
coordinate `ramificationGroupGradedToResidueField` relative to `ϖ` equals
`(residue S a) ^ (n + 1)` times the coordinate relative to `ϖ'` (equivalently, replacing `ϖ` by
`ϖ * a` multiplies the coordinate by `((residue S a) ^ (n + 1))⁻¹`). -/
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

/-- When `ϖ' = ϖ * a` with `a = uniformizerChangeUnit ϖ ϖ' hϖ hϖ'`, the ungraded positive-depth
coordinate `ramificationGroupToResidueField` relative to `ϖ` equals `(residue S a) ^ (n + 1)`
times the coordinate relative to `ϖ'` (equivalently, replacing `ϖ` by `ϖ * a` multiplies the
coordinate by `((residue S a) ^ (n + 1))⁻¹`). -/
theorem ramificationGroupToResidueField_change (n : ℕ) {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (τ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupToResidueField G n hϖ (Additive.ofMul τ) =
      residue S (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : S) ^ (n + 1) *
        ramificationGroupToResidueField G n hϖ' (Additive.ofMul τ) := by
  rw [← ramificationGroupGradedToResidueField_ofMul_mk,
    ← ramificationGroupGradedToResidueField_ofMul_mk]
  exact ramificationGroupGradedToResidueField_change n hϖ hϖ' (QuotientGroup.mk τ)

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
  rw [MonoidHom.mem_ker, tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGradedZeroEquiv S).injective, ← MonoidHom.mem_ker,
    ker_ramificationGroupToPrincipalUnitGraded G R 0 hϖ]
  simp only [Subgroup.mem_subgroupOf, Nat.cast_zero, zero_add]

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
    Function.Injective (ramificationGroupGradedToResidueField G n hϖ) := by
  rw [ramificationGroupGradedToResidueField, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    MonoidHom.coe_toAdditive, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (principalUnitGradedSuccEquivResidueField n hϖ).injective.comp <|
    Additive.ofMul.injective.comp <|
      (ramificationGroupGradedToPrincipalUnitGraded_injective G R (n + 1) hϖ).comp <|
        (ramificationGroupGradedSuccEquiv G n).injective.comp Additive.toMul.injective

variable (G) in
/-- Under separable residue extension, the kernel of `ramificationGroupToResidueField` is
`G_{n+2}` inside `G_{n+1}`. -/
theorem ker_ramificationGroupToResidueField (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ) :
    (ramificationGroupToResidueField G n hϖ).ker =
      ((ramificationGroup G S ((n : ℤ) + 2)).subgroupOf
        (ramificationGroup G S ((n : ℤ) + 1))).toAddSubgroup := by
  ext x
  obtain ⟨τ, rfl⟩ := Additive.ofMul.surjective x
  have hτ₀ : (τ : G) ∈ ramificationGroup G S 0 :=
    ramificationGroup_antitone G S (by omega : 0 ≤ (n : ℤ) + 1) τ.2
  rw [mem_ker_ramificationGroupToResidueField_iff n hϖ]
  change _ ↔ τ ∈ (ramificationGroup G S ((n : ℤ) + 2)).subgroupOf
    (ramificationGroup G S ((n : ℤ) + 1))
  rw [Subgroup.mem_subgroupOf, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by push_cast; ring,
    mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ hτ₀]

/-! ### Consequences for tame inertia `G_0 / G_1` and wild inertia `G_1` -/

variable (G) in
/-- Under separable residue extension, the tame character `G_0 →* (ResidueField S)ˣ` is injective
if and only if wild inertia `G_1` is trivial. -/
theorem tameCharacter_injective_iff {ϖ : S} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacter G hϖ) ↔ ramificationGroup G S 1 = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_tameCharacter G R hϖ, Subgroup.eq_bot_iff_forall]
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
    IsCyclic (ramificationGroup G S 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacter G hϖ))
    (Units.val_injective.comp ((tameCharacter_injective_iff G R hϖ).mpr h))

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
theorem not_dvd_card_ramificationGroupGraded_zero (p : ℕ)
    [CharP (ResidueField S) p] [Finite (RamificationGroupGraded G S 0)] :
    ¬ p ∣ Nat.card (RamificationGroupGraded G S 0) := by
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
    exact TauCeti.not_dvd_card_of_injective_units p (tameCharacterGraded G hϖ)
      (tameCharacterGraded_injective G R hϖ)
  · simpa using Nat.card_pos.ne'

variable (G S) in
/-- **The index `[G_0 : G_1]` is prime to the residue characteristic `p`.** -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ)
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
  letI : Finite (ramificationGroup G S 1) :=
    Finite.of_injective _
      (Subgroup.inclusion_injective (ramificationGroup_antitone G S zero_le_one))
  ((isPGroup_ramificationGroup G S p zero_lt_one).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one G R S p)

/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe :
    (ramificationGroupOneSylow G R S p : Subgroup (ramificationGroup G S 0)) =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) :=
  IsPGroup.toSylow_coe _ _

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal :
    (ramificationGroupOneSylow G R S p : Subgroup (ramificationGroup G S 0)).Normal := by
  rw [ramificationGroupOneSylow_coe]
  infer_instance

variable {G S p} in
/-- **Wild inertia is the unique Sylow `p`-subgroup of inertia.** -/
theorem eq_ramificationGroupOneSylow (Q : Sylow p (ramificationGroup G S 0)) :
    Q = ramificationGroupOneSylow G R S p := by
  let _ : Unique (Sylow p (ramificationGroup G S 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow G R S p)
      (ramificationGroupOneSylow_normal G R S p)
  exact Subsingleton.elim _ _

end PrimeChar

variable (G S) in
/-- The order of wild inertia is the `p`-part of the order of inertia:
`#G_1 = p ^ (v_p #G_0)` (including `p = 0`). -/
theorem natCard_ramificationGroup_one (p : ℕ) [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    have hcard := Sylow.card_eq_multiplicity (ramificationGroupOneSylow G R S p)
    rw [ramificationGroupOneSylow_coe] at hcard
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm
  · have := CharP.charP_to_charZero (ResidueField S)
    have : Finite (ramificationGroup G S 1) :=
      Finite.of_injective _
        (Subgroup.inclusion_injective (ramificationGroup_antitone G S zero_le_one))
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
      Finite.of_injective _
        (Subgroup.inclusion_injective (ramificationGroup_antitone G S zero_le_one))
    rw [ramificationGroup_one_eq_bot_of_charZero G S, zero_dvd_iff]
    exact iff_of_true rfl Nat.card_pos.ne'

end SeparableResidue

section CharZero

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S] [CharZero (ResidueField S)] [FaithfulSMul G S]
  [Finite (ramificationGroup G S 0)]

variable (G) in
/-- In residue characteristic zero with faithful action and finite inertia `G_0`, the tame
character `G_0 →* (ResidueField S)ˣ` is injective (without any base ring `R` or separability
hypothesis). -/
theorem tameCharacter_injective_of_charZero {ϖ : S} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacter G hϖ) := by
  let : Fintype (ramificationGroup G S 0) := Fintype.ofFinite _
  have hunit : IsUnit ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro σ hσker
  have hσ₁ : (σ : G) ∈ ramificationGroup G S 1 := by
    rw [← Nat.cast_one, mem_ramificationGroup_natCast_iff]
    intro x
    let s : S := ∑ τ : ramificationGroup G S 0, (τ : G) • x
    have hs_inv : (σ : G) • s = s := by
      simp only [s, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ ↦ ?_
      simp [Subgroup.coe_mul, mul_smul]
    have hdiff_mem : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s ∈
        maximalIdeal S := by
      have heq : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s =
          ∑ τ : ramificationGroup G S 0, (x - (τ : G) • x) := by
        simp only [s, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [heq]
      exact Ideal.sum_mem _ fun τ _ ↦
        neg_mem_iff.mp (by simpa [neg_sub] using mem_ramificationGroup_zero_iff.mp τ.2 x)
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
      · exact Ideal.mul_mem_right _ _ ((mem_ker_tameCharacter_iff hϖ).mp hσker)
      · have hϖm : ϖ ∈ maximalIdeal S := by rw [hϖ.maximalIdeal_eq]; exact Ideal.subset_span rfl
        rw [pow_two]
        exact Ideal.mul_mem_mul hϖm (mem_ramificationGroup_zero_iff.mp σ.2 c)
    exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmul
  have : Finite (ramificationGroup G S 1) :=
    Finite.of_injective _
      (Subgroup.inclusion_injective (ramificationGroup_antitone G S zero_le_one))
  rw [ramificationGroup_one_eq_bot_of_charZero G S, Subgroup.mem_bot] at hσ₁
  exact Subtype.ext hσ₁

variable (G S) in
/-- **Inertia is cyclic in residue characteristic zero.** When `ResidueField S` has characteristic
zero, the action is faithful, and `G_0` is finite, `G_0` itself is cyclic (without any base ring
`R` or separability hypothesis). -/
theorem isCyclic_ramificationGroup_zero_of_charZero :
    IsCyclic (ramificationGroup G S 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacter G hϖ))
    (Units.val_injective.comp (tameCharacter_injective_of_charZero G hϖ))

end CharZero

end TauCeti.IsDiscreteValuationRing
