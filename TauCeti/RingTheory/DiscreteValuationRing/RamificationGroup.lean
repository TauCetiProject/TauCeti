/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.PrincipalUnitGroup
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded

/-!
# Principal-unit graded embeddings of DVR ramification groups

Let a group `G` act by ring automorphisms on a discrete valuation ring `B` with maximal ideal `𝔪`
and residue field `κ`. Fixing a uniformizer `ϖ` of `B`, every `σ` in the `i`-th ramification group
`G_i = TauCeti.IsLocalRing.ramificationGroup G B (i : ℤ)` (`i : ℕ`) sends `ϖ` to the uniformizer
`σ • ϖ = ϖ * u`, where the unique unit `u : Bˣ` lies in `U(B, i) = (𝔪 ^ i).principalUnitGroup`.

Without any base ring or separability assumption, the assignment `σ ↦ u` modulo `U(B, i + 1)` is a
uniformizer-independent group homomorphism `G_i →* U(B, i) / U(B, i + 1)` that kills `G_{i+1}` and
therefore descends to a canonical graded homomorphism
`θ_i : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`:

* at depth zero, composing with `U(B, 0) / U(B, 1) ≃* κˣ`
  (`TauCeti.IsLocalRing.principalUnitGroupGradedZeroEquivResidueFieldUnits`) recovers the tame
  character `TauCeti.IsLocalRing.tameCharacter` and its graded descent
  `TauCeti.IsLocalRing.tameCharacterGraded`;
* at positive depth `n + 1`, composing with the uniformizer coordinate
  `Additive (U(B, n + 1) / U(B, n + 2)) ≃+ κ`
  (`TauCeti.IsDiscreteValuationRing.principalUnitGroupGradedSuccEquivResidueField`) recovers the
  positive-depth residue-field homomorphism `TauCeti.IsLocalRing.ramificationGroupToResidueField`
  and its graded descent `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`.

When `B` is an algebra over a local ring `A` fixed by `G` with separable residue extension
`ResidueField B / ResidueField A`, the kernel of `G_i →* U(B, i) / U(B, i + 1)` is `G_{i+1}`, so
`θ_i : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)` is injective at every depth `i : ℕ`. On a
nonarchimedean local field `L`, the fraction-field counterpart into `UnitFiltrationGraded L i` is
`TauCeti.ramificationGroupGradedToUnitFiltrationGraded` in
`TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u ∈ U(B, i)` with `ϖ * u = σ • ϖ`
  for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded`: the canonical
  uniformizer-independent homomorphism `G_i →* U(B, i) / U(B, i + 1)`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded`: the canonical
  uniformizer-independent graded homomorphism `G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`.

## Main results

* `ramificationGroupToPrincipalUnitGroupGraded_apply_of_irreducible` and
  `ramificationGroupGradedToPrincipalUnitGroupGraded_mk_of_irreducible`: evaluation of the canonical
  maps using any uniformizer `ϖ`.
* `principalUnitGroupGradedZeroEquiv_ramificationGroupToPrincipalUnitGroupGraded` and
  `principalUnitGroupGradedSuccEquiv_ramificationGroupToPrincipalUnitGroupGraded`: compatibility
  with `TauCeti.IsLocalRing.tameCharacter` and
  `TauCeti.IsLocalRing.ramificationGroupToResidueField`.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGroupGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective`:
  under a separable residue extension, the kernel is `G_{i+1}` and the graded map is injective.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5 and 7.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math. France
  89 (1961), n° 3.1, Proposition 1, p. 126, and n° 3.4, Proposition 6, p. 132.
-/

public section
noncomputable section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section GradedMaps

variable {G : Type*} [Group G]
variable {B : Type*} [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [MulSemiringAction G B]

/-- An element `σ ∈ G_i` moves any unit `u : Bˣ` by a factor `u⁻¹ * σ(u)` in `U(B, i + 1)`. -/
private theorem inv_mul_unitsMap_mem_principalUnitGroup_succ {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G B (i : ℤ)) (u : Bˣ) :
    u⁻¹ * Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom u ∈
      (maximalIdeal B ^ (i + 1)).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup]
  have hsplit : ((u⁻¹ * Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom u : Bˣ) : B) -
      1 = ↑u⁻¹ * (σ • (u : B) - (u : B)) := by
    rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulSemiringAction.toRingHom_apply, mul_sub, Units.inv_mul]
  rw [hsplit]
  exact Ideal.mul_mem_left _ _ (mem_ramificationGroup_natCast_iff.mp hσ (u : B))

/-- For `σ ∈ G_i` and a uniformizer `ϖ`, the unique unit carrying `ϖ` to `σ • ϖ` lies in
`U(B, i) = (𝔪 ^ i).principalUnitGroup`. -/
theorem uniformizerChangeUnit_smul_mem_principalUnitGroup (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : G} (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    TauCeti.uniformizerChangeUnit ϖ (σ • ϖ) hϖ
        (by simpa using hϖ.map (MulSemiringAction.toRingAut G B σ)) ∈
      (maximalIdeal B ^ i).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup, ← hϖ.mul_mem_maximalIdeal_pow_succ_iff, mul_sub, mul_one,
    TauCeti.mul_uniformizerChangeUnit]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

/-- The unit `u ∈ U(B, i)` satisfying `ϖ * u = σ • ϖ`, attached to a uniformizer `ϖ` and an
element `σ` of the `i`-th ramification group `G_i`. -/
def uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (maximalIdeal B ^ i).principalUnitGroup :=
  ⟨TauCeti.uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
      (by simpa using hϖ.map (MulSemiringAction.toRingAut G B (σ : G))),
    uniformizerChangeUnit_smul_mem_principalUnitGroup i hϖ σ.property⟩

/-- In `Bˣ`, `uniformizerRatio i hϖ σ` is `uniformizerChangeUnit ϖ (σ • ϖ)`. -/
theorem coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ σ : Bˣ) =
      TauCeti.uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
        (by simpa using hϖ.map (MulSemiringAction.toRingAut G B (σ : G))) :=
  (rfl)

/-- Multiplying `ϖ` on the right by `uniformizerRatio i hϖ σ` recovers `σ • ϖ`. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ :=
  TauCeti.mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

/-- Auxiliary homomorphism `G_i →* U(B, i) / U(B, i + 1)` defined using a chosen uniformizer `ϖ`. -/
private def ramificationGroupToPrincipalUnitGroupGradedAux (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) fun σ τ ↦ by
    rw [← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    set uσ : Bˣ := (uniformizerRatio i hϖ σ : Bˣ)
    set uτ : Bˣ := (uniformizerRatio i hϖ τ : Bˣ)
    set uστ : Bˣ := (uniformizerRatio i hϖ (σ * τ) : Bˣ)
    have hcocycle :
        uστ = uσ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom uτ := by
      apply Units.ext
      apply mul_left_cancel₀ hϖ.ne_zero
      rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        MulSemiringAction.toRingHom_apply, ← mul_assoc, mul_coe_uniformizerRatio,
        mul_coe_uniformizerRatio, Subgroup.coe_mul, mul_smul,
        ← mul_coe_uniformizerRatio i hϖ τ, smul_mul']
    rw [hcocycle, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact inv_mul_unitsMap_mem_principalUnitGroup_succ σ.property uτ

/-- Two uniformizers define the same class
`(uniformizerRatio i hϖ σ : PrincipalUnitGroupGraded B i)`. -/
private theorem uniformizerRatio_mk_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (σ : ramificationGroup G B (i : ℤ)) :
    (QuotientGroup.mk (uniformizerRatio i hϖ σ) : PrincipalUnitGroupGraded B i) =
      QuotientGroup.mk (uniformizerRatio i hϖ' σ) := by
  set a : Bˣ := TauCeti.uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have ha : ϖ * (a : B) = ϖ' := TauCeti.mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  set u : Bˣ := (uniformizerRatio i hϖ σ : Bˣ)
  set u' : Bˣ := (uniformizerRatio i hϖ' σ : Bˣ)
  have hrel :
      a * u' = u * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
    apply Units.ext
    apply mul_left_cancel₀ hϖ.ne_zero
    rw [Units.val_mul, ← mul_assoc, ha, mul_coe_uniformizerRatio, ← ha, smul_mul',
      Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulSemiringAction.toRingHom_apply, ← mul_assoc, mul_coe_uniformizerRatio]
  have hrel' :
      u⁻¹ * u' = a⁻¹ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
    calc u⁻¹ * u' = u⁻¹ * (a⁻¹ * (a * u')) := by rw [inv_mul_cancel_left]
      _ = u⁻¹ * (a⁻¹ *
            (u * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a)) := by
        rw [hrel]
      _ = a⁻¹ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
        rw [← mul_assoc, mul_comm u⁻¹ a⁻¹, mul_assoc, inv_mul_cancel_left]
  rw [hrel']
  exact inv_mul_unitsMap_mem_principalUnitGroup_succ σ.property a

variable (G B) in
/-- The canonical **uniformizer-independent homomorphism** `G_i →* U(B, i) / U(B, i + 1)` sending
`σ` to the class of the unit `u` with `ϖ * u = σ • ϖ` for any uniformizer `ϖ`
(`ramificationGroupToPrincipalUnitGroupGraded_apply_of_irreducible`). -/
def ramificationGroupToPrincipalUnitGroupGraded (i : ℕ) :
    ramificationGroup G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  ramificationGroupToPrincipalUnitGroupGradedAux i
    (_root_.IsDiscreteValuationRing.exists_irreducible B).choose_spec

/-- At any uniformizer `ϖ`, `ramificationGroupToPrincipalUnitGroupGraded G B i` evaluates `σ` to the
class of `uniformizerRatio i hϖ σ`. -/
theorem ramificationGroupToPrincipalUnitGroupGraded_apply_of_irreducible (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToPrincipalUnitGroupGraded G B i σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  uniformizerRatio_mk_eq_of_irreducible i
    (_root_.IsDiscreteValuationRing.exists_irreducible B).choose_spec hϖ σ

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToPrincipalUnitGroupGraded G B i`
if and only if `σ • ϖ - ϖ ∈ 𝔪 ^ (i + 2)` for a uniformizer `ϖ`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToPrincipalUnitGroupGraded G B i).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGroupGraded_apply_of_irreducible i hϖ,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Ideal.mem_principalUnitGroup,
    ← hϖ.mul_mem_maximalIdeal_pow_succ_iff, mul_sub, mul_one, mul_coe_uniformizerRatio]

/-- The subgroup `G_{i+1}` is contained in the kernel of
`ramificationGroupToPrincipalUnitGroupGraded G B i`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (i : ℕ) :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToPrincipalUnitGroupGraded G B i).ker := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff i hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

variable (G B) in
/-- The canonical **uniformizer-independent graded homomorphism**
`θ_i : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`. Under a separable residue extension it is injective
(`ramificationGroupGradedToPrincipalUnitGroupGraded_injective`). -/
def ramificationGroupGradedToPrincipalUnitGroupGraded (i : ℕ) :
    RamificationGroupGraded G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGroupGraded G B i)
    (ramificationGroup_succ_subgroupOf_le_ker i)

@[simp]
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk (i : ℕ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded G B i
        (σ : RamificationGroupGraded G B (i : ℤ)) =
      ramificationGroupToPrincipalUnitGroupGraded G B i σ :=
  (rfl)

/-- On the class of `σ ∈ G_i`, `ramificationGroupGradedToPrincipalUnitGroupGraded G B i` evaluates
to the class of `uniformizerRatio i hϖ σ` for any uniformizer `ϖ`. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk_of_irreducible (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded G B i
        (σ : RamificationGroupGraded G B (i : ℤ)) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  ramificationGroupToPrincipalUnitGroupGraded_apply_of_irreducible i hϖ σ

/-! ### Factorization of the residue-field graded maps -/

/-- At depth zero, composing `ramificationGroupToPrincipalUnitGroupGraded` with
`principalUnitGroupGradedZeroEquivResidueFieldUnits` recovers `tameCharacter`. -/
theorem principalUnitGroupGradedZeroEquiv_ramificationGroupToPrincipalUnitGroupGraded
    (σ : ramificationGroup G B 0) :
    principalUnitGroupGradedZeroEquivResidueFieldUnits
        (ramificationGroupToPrincipalUnitGroupGraded G B 0 σ) =
      tameCharacter G B σ := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  apply Units.ext
  rw [ramificationGroupToPrincipalUnitGroupGraded_apply_of_irreducible 0 hϖ,
    principalUnitGroupGradedZeroEquivResidueFieldUnits_mk, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    coe_tameCharacter_of_smul_eq_mul hϖ (mul_coe_uniformizerRatio 0 hϖ σ).symm]

/-- At depth zero, composing `ramificationGroupGradedToPrincipalUnitGroupGraded` with
`principalUnitGroupGradedZeroEquivResidueFieldUnits` recovers `tameCharacterGraded`. -/
theorem principalUnitGroupGradedZeroEquiv_ramificationGroupGradedToPrincipalUnitGroupGraded
    (τ : RamificationGroupGraded G B 0) :
    principalUnitGroupGradedZeroEquivResidueFieldUnits
        (ramificationGroupGradedToPrincipalUnitGroupGraded G B 0 τ) =
      tameCharacterGraded G B τ := by
  induction τ using QuotientGroup.induction_on with
  | H σ =>
    exact ((congrArg _ (ramificationGroupGradedToPrincipalUnitGroupGraded_mk 0 σ)).trans
      (principalUnitGroupGradedZeroEquiv_ramificationGroupToPrincipalUnitGroupGraded σ)).trans
      (tameCharacterGraded_mk σ).symm

/-- At positive depth `n + 1`, composing `ramificationGroupToPrincipalUnitGroupGraded` with the
uniformizer coordinate `principalUnitGroupGradedSuccEquivResidueField` recovers
`ramificationGroupToResidueField`. -/
theorem principalUnitGroupGradedSuccEquiv_ramificationGroupToPrincipalUnitGroupGraded
    (n : ℕ) (π : B) (hπ : Irreducible π) (σ : ramificationGroup G B ((n + 1 : ℕ) : ℤ)) :
    principalUnitGroupGradedSuccEquivResidueField n π hπ
        (Additive.ofMul (ramificationGroupToPrincipalUnitGroupGraded G B (n + 1) σ)) =
      (ramificationGroupToResidueField hπ n
        ⟨(σ : G), by simpa only [Nat.cast_add, Nat.cast_one] using σ.property⟩).toAdd := by
  have hmem := mem_ramificationGroup_natCast_iff.mp σ.property π
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [ramificationGroupToPrincipalUnitGroupGraded_apply_of_irreducible (n + 1) hπ,
    ramificationGroupToResidueField_apply_of_smul_sub_eq hπ
      (σ := ⟨(σ : G), by simpa only [Nat.cast_add, Nat.cast_one] using σ.property⟩) hc,
    toAdd_ofAdd]
  refine principalUnitGroupGradedSuccEquivResidueField_of_sub_eq n π hπ _ c ?_
  apply mul_left_cancel₀ hπ.ne_zero
  calc π * (((uniformizerRatio (n + 1) hπ σ : Bˣ) : B) - 1)
      = (σ : G) • π - π := by rw [mul_sub, mul_one, mul_coe_uniformizerRatio]
    _ = π ^ (n + 2) * c := hc
    _ = π * (c * π ^ (n + 1)) := by rw [pow_succ', mul_assoc, mul_comm (π ^ (n + 1)) c]

/-- At positive depth `n + 1`, composing `ramificationGroupGradedToPrincipalUnitGroupGraded` with
`principalUnitGroupGradedSuccEquivResidueField` on the class of `σ` recovers
`ramificationGroupGradedToResidueField`. -/
theorem principalUnitGroupGradedSuccEquiv_ramificationGroupGradedToPrincipalUnitGroupGraded_mk
    (n : ℕ) (π : B) (hπ : Irreducible π) (σ : ramificationGroup G B ((n + 1 : ℕ) : ℤ)) :
    principalUnitGroupGradedSuccEquivResidueField n π hπ
        (Additive.ofMul (ramificationGroupGradedToPrincipalUnitGroupGraded G B (n + 1)
          (σ : RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)))) =
      (ramificationGroupGradedToResidueField hπ n
        ((⟨(σ : G), by simpa only [Nat.cast_add, Nat.cast_one] using σ.property⟩ :
          ramificationGroup G B ((n : ℤ) + 1)) :
          RamificationGroupGraded G B ((n : ℤ) + 1))).toAdd := by
  rw [ramificationGroupGradedToPrincipalUnitGroupGraded_mk,
    ramificationGroupGradedToResidueField_mk,
    principalUnitGroupGradedSuccEquiv_ramificationGroupToPrincipalUnitGroupGraded]

end GradedMaps

/-! ### Kernel and injectivity for a separable residue extension -/

section SeparableResidue

variable (A : Type*) [CommRing A] [IsLocalRing A]
variable {G : Type*} [Group G]
variable {B : Type*} [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
variable [MulSemiringAction G B] [SMulCommClass G A B]
include A

/-- **The kernel of `G_i →* U(B, i) / U(B, i + 1)` is `G_{i+1}`** under a separable residue
extension. -/
theorem ker_ramificationGroupToPrincipalUnitGroupGraded (i : ℕ) :
    (ramificationGroupToPrincipalUnitGroupGraded G B i).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker i)
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff i hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.property
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ.maximalIdeal_eq hσ₀]
  exact hσ

/-- **The graded homomorphism `G_i / G_{i+1} →* U(B, i) / U(B, i + 1)` is injective** under a
separable residue extension. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_injective (i : ℕ) :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGroupGraded G B i) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGroupGraded A i).symm

end SeparableResidue

end TauCeti.IsDiscreteValuationRing
