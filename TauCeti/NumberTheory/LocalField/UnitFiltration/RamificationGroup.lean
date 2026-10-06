/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.NumberTheory.LocalField.Teichmuller
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import TauCeti.GroupTheory.PGroup
import TauCeti.NumberTheory.LocalField.UnitFiltration.ProP
import TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# The quotient embeddings of the ramification filtration

Let `L` be a nonarchimedean local field and let a group `G` act on `L` by ring automorphisms
preserving the ring of integers, so that both the ramification filtration
`G_i = TauCeti.IsLocalRing.ramificationGroup G 𝒪[L] i` and the unit filtration
`U(L,i) = TauCeti.unitFiltration L i` are defined. The motivating case is the Galois group
`L ≃ₐ[K] L` of a finite extension of local fields, for which
`TauCeti.integerRingIsInvariantSubring` supplies the invariance hypothesis.

Fixing a uniformizer `ϖ`, that is an irreducible element of `𝒪[L]`, this file compares the two
filtrations through the ratio `σ ϖ / ϖ`. An element of `G_i` moves `ϖ` by a factor lying in
`U(L,i)`, and the class of that factor modulo `U(L,i+1)`

* does not depend on the choice of `ϖ`,
* is multiplicative in `σ`, and
* is trivial on `G_{i+1}`,

so it defines `θ_i : G_i / G_{i+1} → U(L,i) / U(L,i+1)`. The map `θ_i` is injective: an element
of `G_0` fixes every Teichmüller representative, and every integer of `L` is a Teichmüller
representative plus `ϖ` times an integer, so membership of an element of `G_0` in `G_{i+1}` is
decided at `ϖ` alone.

At depth zero, composing with the reduction isomorphism `U(L,0) / U(L,1) ≃ 𝓀[L]ˣ`
gives the **tame character** `G_0 → 𝓀[L]ˣ`, which kills `G_1`; the induced map on `G_0 / G_1` is
injective, so the tame quotient is cyclic of order dividing `q - 1`, where `q` is the cardinality
of the residue field. At positive depth `U(L,i) / U(L,i+1)` has `q` elements, so every
`G_i / G_{i+1}` with `i ≥ 1` is a `p`-group for the residue characteristic `p`; when the action is
faithful and `G_0` is finite, the filtration reaches `1`, and every `G_i` with `i ≥ 1`, in
particular the wild inertia group `G_1`, is a `p`-group.

## Main definitions

* `TauCeti.uniformizerRatio`: the ratio `σ ϖ / ϖ`, as an element of `U(L,i)`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded`: the homomorphism
  `G_i → U(L,i) / U(L,i+1)`, and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded`: the induced `θ_i` on `G_i / G_{i+1}`.
* `TauCeti.ramificationGroupGradedToResidueField`: the positive-depth quotient embedding
  composed with the additive residue-field coordinate determined by a uniformizer.
* `TauCeti.tameCharacter`: the depth-zero homomorphism `G_0 → 𝓀[L]ˣ`, and
  `TauCeti.tameCharacterGraded`: the map it induces on `G_0 / G_1`.

## Main results

* `TauCeti.mem_ramificationGroup_natCast_iff_valuation_le`: the valuation form of the
  ramification filtration, `v(σ x - x) ≤ v(ϖ)^(i+1)` for every integer `x`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible`,
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible`,
  `TauCeti.tameCharacter_eq_of_irreducible` and
  `TauCeti.tameCharacterGraded_eq_of_irreducible`: independence of the choice of uniformizer.
* `TauCeti.smul_teichmullerLift_of_mem_ramificationGroup_zero`: `G_0` fixes every Teichmüller
  representative.
* `TauCeti.mem_ramificationGroup_natCast_iff_smul_sub_mem`: an element of `G_0` lies in `G_n`
  exactly when it moves a uniformizer by an element of `𝓂[L] ^ (n + 1)`.
* `TauCeti.smul_div_mem_unitFiltration`: for `σ ∈ G_i`, every ratio `σ y / y` lies in `U(L,i)`.
* `TauCeti.mem_ramificationGroup_one_of_valuation_pow_sub_one_lt_one`: an element of `G_0` lies in
  `G_1` once a `p`-power of `σ ϖ / ϖ` is congruent to `1`.
* `TauCeti.valuation_smul_div_pow_sub_one_lt_one`: if `σ ∈ G_0` fixes an element of valuation
  `v(a) ^ n`, then `(σ a / a) ^ n` is congruent to `1`.
* `TauCeti.ker_ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded_injective`: the kernel is exactly
  `G_{i+1}`, and `θ_i` is injective.
* `TauCeti.ramificationGroupGradedToResidueField_change`: changing the uniformizer in the
  positive-depth residue coordinate multiplies it by the corresponding residue-field unit.
* `TauCeti.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`: the tame quotient
  is cyclic, of order dividing `q - 1`.
* `TauCeti.isPGroup_ramificationGroupGraded_natCast_succ` and
  `TauCeti.isPGroup_ramificationGroup`: the positive-depth graded pieces, and, for a faithful
  action with finite `G_0`, the positive-depth ramification groups, are `p`-groups.
* `TauCeti.ramificationGroupOneSylow` and `TauCeti.eq_ramificationGroupOneSylow`: the wild inertia
  group `G_1`, viewed inside `G_0`, is its unique normal Sylow `p`-subgroup.
* `TauCeti.natCard_ramificationGroup_one`: the order of `G_1` is the `p`-part of the order of `G_0`.
* `TauCeti.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: `G_1` is
  trivial exactly when `p` does not divide the order of `G_0`, the tame case.

## Implementation notes

The ramification groups are indexed by `ℤ` and the unit filtration by `ℕ`. Every general statement
below therefore fixes a natural index `i` and reads the ramification group at `(i : ℤ)`, whereas
the depth-zero declarations fix the index `(0 : ℤ)`, the spelling in which a statement about
`G_0 / G_1` is met.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Proposition 5.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti.IsLocalRing

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]
variable {ϖ : 𝒪[L]} {i : ℕ} {σ : G}

/-! ### The valuation form of the ramification filtration -/

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The image of an integer of `L` under the action, read in `L`. This is `map_smul` for the
equivariant inclusion `IsInvariantSubring.subtypeHom`. -/
private theorem coe_smul_integer (σ : G) (y : 𝒪[L]) : ((σ • y : 𝒪[L]) : L) = σ • (y : L) :=
  map_smul (IsInvariantSubring.subtypeHom G 𝒪[L]) σ y

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The displacement `σ y - y` of an integer of `L`, read in `L`. -/
private theorem coe_smul_sub_integer (σ : G) (y : 𝒪[L]) :
    ((σ • y - y : 𝒪[L]) : L) = σ • (y : L) - (y : L) := by
  rw [AddSubgroupClass.coe_sub, coe_smul_integer]

/-- Lying in a power of the maximal ideal, for a difference `σ y - y`, is a valuation inequality
measured against a uniformizer. -/
private theorem sub_mem_maximalIdeal_pow_iff (hϖ : Irreducible ϖ) (σ : G) (y : 𝒪[L]) (n : ℕ) :
    σ • y - y ∈ 𝓂[L] ^ n ↔ valuation L (σ • (y : L) - (y : L)) ≤ valuation L (ϖ : L) ^ n := by
  rw [← coe_smul_sub_integer]
  exact Set.ext_iff.mp
    (hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation L) n) (σ • y - y)

/-- **Serre's valuation form** of the ramification filtration: `σ` lies in `G_i` exactly when it
moves every integer of `L` by an element of valuation at most `v(ϖ) ^ (i + 1)`, for `ϖ` a
uniformizer. The left-hand side does not mention `ϖ`, so neither side depends on the choice.
The same condition read through the additive valuation of the discrete valuation ring `𝒪[L]` is
`TauCeti.IsLocalRing.mem_ramificationGroup_iff_le_addVal`; the multiplicative form below is the
one in which the unit filtration is stated. -/
theorem mem_ramificationGroup_natCast_iff_valuation_le (hϖ : Irreducible ϖ) :
    σ ∈ ramificationGroup G 𝒪[L] (i : ℤ) ↔
      ∀ y : 𝒪[L], valuation L (σ • (y : L) - (y : L)) ≤ valuation L (ϖ : L) ^ (i + 1) := by
  rw [mem_ramificationGroup_natCast_iff]
  exact forall_congr' fun y ↦ sub_mem_maximalIdeal_pow_iff hϖ σ y (i + 1)

/-- The action preserves the valuation of a uniformizer: the image of an irreducible element of
`𝒪[L]` is irreducible, hence associated to it. -/
theorem valuation_smul_of_irreducible (hϖ : Irreducible ϖ) (σ : G) :
    valuation L (σ • (ϖ : L)) = valuation L (ϖ : L) := by
  have hσϖ : Irreducible (σ • ϖ) := hϖ.map (MulSemiringAction.toRingAut G 𝒪[L] σ)
  obtain ⟨u, hu⟩ : ∃ u : 𝒪[L]ˣ, σ • ϖ * (u : 𝒪[L]) = ϖ :=
    ⟨uniformizerChangeUnit (σ • ϖ) ϖ hσϖ hϖ, mul_uniformizerChangeUnit (σ • ϖ) ϖ hσϖ hϖ⟩
  have h := congrArg (fun y : 𝒪[L] ↦ valuation L (y : L)) hu
  have hu1 : valuation L ((u : 𝒪[L]) : L) = 1 :=
    (Valuation.integer.integers (valuation L)).valuation_unit u
  simpa [hu1, coe_smul_integer] using h

/-! ### The ratio of a uniformizer -/

/-- For `σ` in the `i`-th ramification group and `x` a unit of `𝒪[L]`, the ratio `σ x / x` lies
one step deeper in the unit filtration, in `U(L, i+1)`. -/
theorem mem_unitFiltration_succ_of_val_eq_smul_div
    (hσ : σ ∈ ramificationGroup G 𝒪[L] (i : ℤ)) {x y : Lˣ} (hx : x ∈ unitFiltration L 0)
    (hy : (y : L) = σ • (x : L) / (x : L)) : y ∈ unitFiltration L (i + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
  obtain ⟨u, -, hux⟩ := mem_unitFiltration_iff_exists.mp hx
  have hx1 : valuation L (x : L) = 1 := (mem_unitFiltration_zero x).mp hx
  have hval : valuation L (σ • (x : L) - (x : L)) ≤ valuation L (ϖ : L) ^ (i + 1) := by
    rw [← hux]
    exact (mem_ramificationGroup_natCast_iff_valuation_le hϖ).mp hσ u
  rw [mem_unitFiltration_succ_valuation i y ϖ hϖ, hy, div_sub_one x.ne_zero, map_div₀, hx1,
    div_one, map_pow]
  exact hval

/-- For `σ` in the `i`-th ramification group and `ϖ` a uniformizer, the ratio `σ ϖ / ϖ` lies in
the `i`-th step `U(L,i)` of the unit filtration. -/
theorem mem_unitFiltration_of_val_eq_smul_div (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] (i : ℤ)) {y : Lˣ}
    (hy : (y : L) = σ • (ϖ : L) / (ϖ : L)) : y ∈ unitFiltration L i := by
  have hϖpos : 0 < valuation L (ϖ : L) := by
    simpa using Valuation.integer.v_irreducible_pos (v := valuation L) hϖ
  have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  refine (mem_unitFiltration_iff_valuation_le hϖ).mpr ⟨?_, ?_⟩
  · rw [hy, map_div₀, valuation_smul_of_irreducible hϖ σ, div_self hϖpos.ne']
  · rw [hy, div_sub_one hϖne, map_div₀, div_le_iff₀ hϖpos, ← pow_succ]
    exact (mem_ramificationGroup_natCast_iff_valuation_le hϖ).mp hσ ϖ

variable (i) in
/-- The ratio `σ ϖ / ϖ` of a uniformizer `ϖ` and its image under an element `σ` of the `i`-th
ramification group, as an element of the `i`-th step `U(L,i)` of the unit filtration. -/
def uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    unitFiltration L i :=
  ⟨Units.mk0 ((σ : G) • (ϖ : L) / (ϖ : L)) (by
      have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
      exact div_ne_zero ((smul_ne_zero_iff_ne _).mpr hϖne) hϖne),
    mem_unitFiltration_of_val_eq_smul_div hϖ σ.2 rfl⟩

@[simp]
theorem coe_uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ((uniformizerRatio i hϖ σ : Lˣ) : L) = (σ : G) • (ϖ : L) / (ϖ : L) := (rfl)

/-- For `σ` in the `i`-th ramification group, the ratio `σ y / y` of any nonzero `y` lies in the
`i`-th step `U(L,i)` of the unit filtration. For a uniformizer this is
`TauCeti.mem_unitFiltration_of_val_eq_smul_div`, and for a unit it is one step deeper, by
`TauCeti.mem_unitFiltration_succ_of_val_eq_smul_div`. -/
theorem smul_div_mem_unitFiltration (hσ : σ ∈ ramificationGroup G 𝒪[L] (i : ℤ)) {y z : Lˣ}
    (hz : (z : L) = σ • (y : L) / (y : L)) : z ∈ unitFiltration L i := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hϖ0 : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  -- The ratio `y ↦ σ y / y` is a homomorphism `Lˣ →* Lˣ`.
  let f : Lˣ →* Lˣ := Units.map (MulSemiringAction.toRingHom G L σ).toMonoidHom / MonoidHom.id Lˣ
  have hf (y : Lˣ) : ((f y : Lˣ) : L) = σ • (y : L) / (y : L) := by
    simp [f, div_eq_mul_inv]
  -- Write `y = ϖ ^ k u` with `u` a unit of `𝒪[L]`.
  obtain ⟨⟨k, u⟩, rfl, -⟩ := existsUnique_eq_zpow_mul (normalizedValuation_irreducible hϖ) y
  have h₁ : f (Units.mk0 _ hϖ0) ∈ unitFiltration L i :=
    mem_unitFiltration_of_val_eq_smul_div hϖ hσ (hf _)
  have h₂ : f u ∈ unitFiltration L i := unitFiltration_antitone (Nat.le_succ i)
    (mem_unitFiltration_succ_of_val_eq_smul_div hσ u.2 (hf _))
  rw [show z = f (Units.mk0 _ hϖ0 ^ k * u) from Units.ext (by rw [hz, hf]), map_mul, map_zpow]
  exact mul_mem (zpow_mem h₁ k) h₂

/-! ### The quotient homomorphism -/

variable (i) in
/-- The **quotient homomorphism** attached to a uniformizer `ϖ`: the homomorphism
`G_i → U(L,i) / U(L,i+1)` carrying `σ` to the class of `σ ϖ / ϖ`. It kills `G_{i+1}`, so it may
fail to be injective; the map it induces on `G_i / G_{i+1}` is the embedding `θ_i` of
`TauCeti.ramificationGroupGradedToUnitFiltrationGraded`. -/
def ramificationGroupToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    ramificationGroup G 𝒪[L] (i : ℤ) →* UnitFiltrationGraded L i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) <| by
    intro σ τ
    have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
    have hσϖ : (σ : G) • (ϖ : L) ≠ 0 := (smul_ne_zero_iff_ne _).mpr hϖne
    have hτϖ : (τ : G) • (ϖ : L) ≠ 0 := (smul_ne_zero_iff_ne _).mpr hϖne
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf, ← Subgroup.inv_mem_iff]
    refine mem_unitFiltration_succ_of_val_eq_smul_div (σ := (σ : G)) σ.2
      (unitFiltration_antitone (Nat.zero_le i) (uniformizerRatio i hϖ τ).2) ?_
    have hsmul : (σ : G) • ((τ : G) • (ϖ : L) / (ϖ : L))
        = ((σ : G) * (τ : G)) • (ϖ : L) / (σ : G) • (ϖ : L) := by
      rw [div_eq_mul_inv, smul_mul', smul_inv'', ← div_eq_mul_inv, ← mul_smul]
    push_cast [coe_uniformizerRatio, hsmul]
    field_simp

@[simp]
theorem ramificationGroupToUnitFiltrationGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := (rfl)

/-- The quotient homomorphism does not depend on the choice of uniformizer: two uniformizers
differ by a unit of `𝒪[L]`, and `σ` moves that unit inside `U(L,i+1)`. -/
theorem ramificationGroupToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupToUnitFiltrationGraded (G := G) i hϖ' := by
  obtain ⟨u, hu⟩ : ∃ u : 𝒪[L]ˣ, ϖ * (u : 𝒪[L]) = ϖ' :=
    ⟨uniformizerChangeUnit ϖ ϖ' hϖ hϖ', mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ'⟩
  have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  refine MonoidHom.ext fun σ ↦ ?_
  have hσϖ : (σ : G) • (ϖ : L) ≠ 0 := (smul_ne_zero_iff_ne _).mpr hϖne
  have hune : ((u : 𝒪[L]) : L) ≠ 0 := (u.isUnit.map (Subring.subtype 𝒪[L])).ne_zero
  rw [ramificationGroupToUnitFiltrationGraded_apply, ramificationGroupToUnitFiltrationGraded_apply]
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf]
  refine mem_unitFiltration_succ_of_val_eq_smul_div (σ := (σ : G)) σ.2
    (x := Units.map (Subring.subtype 𝒪[L]).toMonoidHom u) (mem_unitFiltration_iff_exists.mpr
      ⟨u, by simp, rfl⟩) ?_
  have hϖ'L : (ϖ' : L) = (ϖ : L) * ((u : 𝒪[L]) : L) := by
    rw [← hu]
    simp
  have hsmul : (σ : G) • (ϖ' : L) = (σ : G) • (ϖ : L) * (σ : G) • ((u : 𝒪[L]) : L) := by
    rw [hϖ'L, smul_mul']
  have hxval : ((Units.map (Subring.subtype 𝒪[L]).toMonoidHom u : Lˣ) : L) = ((u : 𝒪[L]) : L) :=
    rfl
  push_cast [coe_uniformizerRatio, hϖ'L, hsmul, hxval, smul_mul']
  field_simp

/-! ### Membership decided at a uniformizer -/

/-- An element of the inertia group `G_0` fixes every Teichmüller representative: its image is
again fixed by the `q`-th power map and has the same residue. -/
@[simp]
theorem smul_teichmullerLift_of_mem_ramificationGroup_zero
    (hσ : σ ∈ ramificationGroup G 𝒪[L] 0) (a : 𝓀[L]) :
    σ • teichmullerLift L a = teichmullerLift L a := by
  refine (eq_teichmullerLift_iff L).2 ⟨?_, ?_⟩
  · have h := mem_ramificationGroup_zero_iff.mp hσ (teichmullerLift L a)
    rwa [← residue_eq_zero_iff, map_sub, sub_eq_zero, residue_teichmullerLift] at h
  · rw [← smul_pow', teichmullerLift_pow_natCard]

/-- **Membership in the ramification filtration is decided at a uniformizer**: an element `σ` of
the inertia group `G_0` lies in `G_n` exactly when `σ ϖ ≡ ϖ` modulo `𝓂[L] ^ (n + 1)`. Writing an
integer as a Teichmüller representative, which `σ` fixes, plus `ϖ` times an integer, the
congruence propagates from `ϖ` to every integer one power of `𝓂[L]` at a time. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] 0) {n : ℕ} :
    σ ∈ ramificationGroup G 𝒪[L] (n : ℤ) ↔ σ • ϖ - ϖ ∈ 𝓂[L] ^ (n + 1) := by
  rw [mem_ramificationGroup_natCast_iff]
  refine ⟨fun h ↦ h ϖ, fun h ↦ ?_⟩
  have hσϖ : σ • ϖ ∈ 𝓂[L] := by
    have h₁ := mem_ramificationGroup_zero_iff.mp hσ ϖ
    have h₂ : ϖ ∈ 𝓂[L] := (mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    simpa using Ideal.add_mem _ h₁ h₂
  suffices ∀ m ≤ n + 1, ∀ x : 𝒪[L], σ • x - x ∈ 𝓂[L] ^ m from this _ le_rfl
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm x
    obtain ⟨y, hy⟩ : ∃ y, x = teichmullerLift L (residue 𝒪[L] x) + ϖ * y := by
      have hx : x - teichmullerLift L (residue 𝒪[L] x) ∈ 𝓂[L] := by
        rw [← residue_eq_zero_iff, map_sub, residue_teichmullerLift, sub_self]
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.mem_span_singleton'] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, by rw [mul_comm, hy]; ring⟩
    have hsplit : σ • x - x = σ • ϖ * (σ • y - y) + (σ • ϖ - ϖ) * y := by
      rw [hy, smul_add, smul_mul', smul_teichmullerLift_of_mem_ramificationGroup_zero hσ]
      ring
    have h₁ : σ • ϖ * (σ • y - y) ∈ 𝓂[L] ^ (m + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul hσϖ (ih (by omega) y)
    have h₂ : (σ • ϖ - ϖ) * y ∈ 𝓂[L] ^ (m + 1) :=
      Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hm h)
    rw [hsplit]
    exact Ideal.add_mem _ h₁ h₂

/-- An element of the inertia group `G_0` lies in `G_1` as soon as the ratio `σ ϖ / ϖ` of a
uniformizer `ϖ` has a `p`-power congruent to `1` modulo the maximal ideal, for `p` the residue
characteristic. -/
theorem mem_ramificationGroup_one_of_valuation_pow_sub_one_lt_one (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] 0) (p k : ℕ) [CharP 𝓀[L] p]
    (h : valuation L ((σ • (ϖ : L) / (ϖ : L)) ^ p ^ k - 1) < 1) :
    σ ∈ ramificationGroup G 𝒪[L] 1 := by
  have hp : p.Prime := CharP.char_is_prime 𝓀[L] p
  have := Fact.mk hp
  have hϖ0 : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  -- The ratio `c = σ ϖ / ϖ` is an integer of `L`, and `σ ϖ = ϖ c`.
  have hcv : valuation L (σ • (ϖ : L) / (ϖ : L)) ≤ 1 := by
    rw [map_div₀, valuation_smul_of_irreducible hϖ σ, div_self ((map_ne_zero _).2 hϖ0)]
  set c : 𝒪[L] := ⟨σ • (ϖ : L) / (ϖ : L), hcv⟩
  have hc : σ • ϖ = ϖ * c := Subtype.ext (by
    rw [coe_smul_integer, MulMemClass.coe_mul, mul_div_cancel₀ _ hϖ0])
  -- In the residue field, the residue `x` of `c` satisfies `x ^ p ^ k = 1`, forcing `x = 1`.
  have hcp : c ^ p ^ k - 1 ∈ 𝓂[L] := by
    rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    simpa [c] using h
  have hc1 : c - 1 ∈ 𝓂[L] := by
    rw [← residue_eq_zero_iff] at hcp ⊢
    rw [map_sub, map_pow, map_one] at hcp
    rw [map_sub, map_one, ← pow_eq_zero_iff (pow_ne_zero k hp.ne_zero), sub_pow_char_pow,
      one_pow, hcp]
  refine (mem_ramificationGroup_natCast_iff_smul_sub_mem hϖ hσ (n := 1)).2 ?_
  rw [hc, pow_two, show ϖ * c - ϖ = ϖ * (c - 1) by ring]
  exact Ideal.mul_mem_mul ((mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) hc1

/-- For `σ` in the inertia group `G_0` fixing an element `b` of valuation `v(a) ^ n`, the `n`-th
power of the ratio `σ a / a` is congruent to `1` modulo the maximal ideal. -/
theorem valuation_smul_div_pow_sub_one_lt_one (hσ : σ ∈ ramificationGroup G 𝒪[L] 0)
    {a b : L} {n : ℕ} (ha : a ≠ 0) (hab : valuation L b = valuation L a ^ n) (hσb : σ • b = b) :
    valuation L ((σ • a / a) ^ n - 1) < 1 := by
  set d := σ • a / a
  have hd : valuation L d = 1 := by
    have hσa : σ • a ≠ 0 := (smul_ne_zero_iff_ne _).2 ha
    exact (mem_unitFiltration_zero _).1 (smul_div_mem_unitFiltration (i := 0)
      (y := Units.mk0 a ha) (z := Units.mk0 d (div_ne_zero hσa ha)) (by exact_mod_cast hσ) rfl)
  have hd0 : d ≠ 0 := by
    rintro h
    simp [h] at hd
  -- `w = b / a ^ n` is a unit of `𝒪[L]`, and `σ w = w / d ^ n`.
  set w := b / a ^ n with hw_def
  have hw : valuation L w = 1 := by
    rw [hw_def, map_div₀, hab, map_pow, div_self (pow_ne_zero _ ((map_ne_zero _).2 ha))]
  have hw0 : w ≠ 0 := by
    rintro h
    simp [h] at hw
  have hσw : σ • w = w / d ^ n := by
    rw [hw_def, smul_div₀', smul_pow', hσb, div_pow, div_div, mul_div_cancel₀ _ (pow_ne_zero _ ha)]
  have hmem := mem_ramificationGroup_zero_iff.mp hσ ⟨w, hw.le⟩
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    coe_smul_sub_integer] at hmem
  -- `d ^ n - 1 = (σ w - w) · (-d ^ n / w)`, whose valuation is that of `σ w - w`.
  have : d ^ n - 1 = (σ • w - w) * (-d ^ n / w) := by
    rw [hσw]
    field_simp
    ring
  rw [this, map_mul, map_div₀, Valuation.map_neg, map_pow, hd, hw, one_pow, div_one, mul_one]
  exact hmem

/-! ### The kernel -/

/-- The kernel of the quotient homomorphism, as a valuation condition at the chosen uniformizer:
`σ` is killed exactly when it moves `ϖ` one step deeper than membership in `G_i` requires. -/
theorem mem_ker_ramificationGroupToUnitFiltrationGraded_iff (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G 𝒪[L] (i : ℤ)} :
    σ ∈ (ramificationGroupToUnitFiltrationGraded i hϖ).ker ↔
      valuation L ((σ : G) • (ϖ : L) - (ϖ : L)) ≤ valuation L (ϖ : L) ^ (i + 2) := by
  have hϖpos : 0 < valuation L (ϖ : L) := by
    simpa using Valuation.integer.v_irreducible_pos (v := valuation L) hϖ
  have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  rw [MonoidHom.mem_ker, ramificationGroupToUnitFiltrationGraded_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    mem_unitFiltration_succ_valuation i _ ϖ hϖ, coe_uniformizerRatio, div_sub_one hϖne,
    map_div₀, map_pow, div_le_iff₀ hϖpos, ← pow_succ]

/-- The next step `G_{i+1}` of the ramification filtration is killed by the quotient
homomorphism. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (hϖ : Irreducible ϖ) :
    (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded i hϖ).ker := by
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G 𝒪[L] ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ]
  exact (mem_ramificationGroup_natCast_iff_valuation_le hϖ).mp hσ' ϖ

/-- **The kernel of the quotient homomorphism is exactly `G_{i+1}`**, which is what makes the
induced `θ_i` on `G_i / G_{i+1}` an embedding: membership of an element of `G_0` in `G_{i+1}` is
decided at `ϖ` (`TauCeti.mem_ramificationGroup_natCast_iff_smul_sub_mem`). -/
theorem ker_ramificationGroupToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    (ramificationGroupToUnitFiltrationGraded i hϖ).ker =
      (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker hϖ)
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G 𝒪[L] 0 :=
    ramificationGroup_antitone G 𝒪[L] (Int.natCast_nonneg i) σ.2
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem hϖ hσ₀, sub_mem_maximalIdeal_pow_iff hϖ]
  exact hσ

/-! ### The embedding of the graded pieces -/

variable (i) in
/-- The **quotient map** `θ_i : G_i / G_{i+1} →* U(L,i) / U(L,i+1)`, induced by
`σ ↦ σ ϖ / ϖ` for a uniformizer `ϖ`. It is an embedding
(`TauCeti.ramificationGroupGradedToUnitFiltrationGraded_injective`). -/
def ramificationGroupGradedToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G 𝒪[L] (i : ℤ) →* UnitFiltrationGraded L i :=
  QuotientGroup.lift _ (ramificationGroupToUnitFiltrationGraded i hϖ)
    fun _ hσ ↦ ramificationGroup_succ_subgroupOf_le_ker hϖ hσ

@[simp]
theorem ramificationGroupGradedToUnitFiltrationGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := (rfl)

/-- **The quotient embeddings are injective.** -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToUnitFiltrationGraded hϖ).symm

/-- The descended quotient map does not depend on the choice of uniformizer. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ' := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    exact DFunLike.congr_fun
      (ramificationGroupToUnitFiltrationGraded_eq_of_irreducible (G := G) (i := i) hϖ hϖ') σ

/-! ### Positive-depth residue-field coordinates -/

variable (G L) in
/-- The positive-depth embedding of `G_{n+1}/G_{n+2}` into the additive residue field, in the
coordinate determined by a uniformizer `π`. -/
noncomputable def ramificationGroupGradedToResidueField (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Additive (RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) →+
      IsLocalRing.ResidueField 𝒪[L] :=
  by
    simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
      (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).toAddMonoidHom.comp
        (ramificationGroupGradedToUnitFiltrationGraded (G := G) (n + 1) hπ).toAdditive

@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π)
    (τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (QuotientGroup.mk τ)) =
      unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul (QuotientGroup.mk (uniformizerRatio (n + 1) hπ τ))) :=
  by
    rw [ramificationGroupGradedToResidueField]
    simp only [AddMonoidHom.comp_apply]
    apply congrArg _
    exact congrArg Additive.ofMul
      (ramificationGroupGradedToUnitFiltrationGraded_mk (i := n + 1) hπ τ)

/-- The positive-depth ramification quotient embeds in the additive residue field. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ) :=
  (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).injective.comp
    (ramificationGroupGradedToUnitFiltrationGraded_injective (G := G)
      (i := n + 1) hπ)

/-- Compute a positive-depth residue coordinate from the displacement of a representative. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq
    (n : ℕ) (π : 𝒪[L]) (hπ : Irreducible π)
    (τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) (y : 𝒪[L])
    (hmove : (τ : G) • π - π = y * π ^ (n + 2)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (QuotientGroup.mk τ)) = residue 𝒪[L] y := by
  have hπ0 : (π : L) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hmoveL := congrArg (fun z : 𝒪[L] ↦ (z : L)) hmove
  have hmoveL' : (τ : G) • (π : L) - (π : L) =
      (y : L) * (π : L) ^ (n + 2) := by
    calc
      _ = (((τ : G) • π - π : 𝒪[L]) : L) := (coe_smul_sub_integer (τ : G) π).symm
      _ = ((y * π ^ (n + 2) : 𝒪[L]) : L) := hmoveL
      _ = _ := by rfl
  have hdiff :
      (unitFiltrationDifference n (uniformizerRatio (n + 1) hπ τ) : 𝒪[L]) =
        y * π ^ (n + 1) := by
    apply Subtype.ext
    rw [coe_coe_unitFiltrationDifference, coe_uniformizerRatio, div_sub_one hπ0, hmoveL']
    field_simp
    push_cast
    ring
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  exact unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
    n π hπ _ y hdiff

/-- Change the uniformizer used for a positive-depth ramification coordinate. -/
theorem ramificationGroupGradedToResidueField_change
    (n : ℕ) (π π' : 𝒪[L]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ (Additive.ofMul τ) =
      residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) ^ (n + 1) *
        ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
          (Additive.ofMul τ) := by
  have hchange :=
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change n π π' hπ hπ'
      (Additive.ofMul
        (ramificationGroupGradedToUnitFiltrationGraded (G := G) (n + 1) hπ τ))
  rw [uniformizerChangeResidueAddEquiv_apply] at hchange
  have htheta := DFunLike.congr_fun
    (ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible
      (G := G) (i := n + 1) hπ hπ') τ
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply]
  simpa [htheta] using hchange

/-! ### The tame character -/

/-- The **tame character** `θ_0 : G_0 →* 𝓀[L]ˣ`: the depth-zero quotient homomorphism composed
with the identification of `U(L,0) / U(L,1)` with the multiplicative group of the residue
field. It carries `σ` to the residue of `σ ϖ / ϖ`. It kills `G_1`, hence factors through
`TauCeti.tameCharacterGraded`. -/
def tameCharacter (hϖ : Irreducible ϖ) : ramificationGroup G 𝒪[L] (0 : ℤ) →* 𝓀[L]ˣ :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits (K := L)).toMonoidHom.comp
    (ramificationGroupToUnitFiltrationGraded 0 hϖ)

theorem coe_tameCharacter_of_val_eq_smul_div (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (0 : ℤ)) {y : 𝒪[L]}
    (hy : (y : L) = (σ : G) • (ϖ : L) / (ϖ : L)) :
    (tameCharacter hϖ σ : 𝓀[L]) = IsLocalRing.residue 𝒪[L] y := by
  -- `ramificationGroupToUnitFiltrationGraded_apply` is keyed on the cast index `(i : ℤ)`, which
  -- does not match the `simp`-normal `(0 : ℤ)` of the statement, so instantiate it at `i = 0`.
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToUnitFiltrationGraded_apply (i := 0)]
  simp only [unitFiltrationGradedZeroEquivResidueFieldUnits_mk,
    ValuationSubring.coe_unitGroupToResidueFieldUnits_apply]
  refine congrArg _ (Subtype.ext ?_)
  rw [ValuationSubring.coe_unitGroupMulEquiv_apply, coe_uniformizerRatio, hy]

/-- The tame character does not depend on the choice of uniformizer. -/
theorem tameCharacter_eq_of_irreducible {ϖ' : 𝒪[L]} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacter (G := G) hϖ = tameCharacter (G := G) hϖ' := by
  rw [tameCharacter, tameCharacter,
    ramificationGroupToUnitFiltrationGraded_eq_of_irreducible (G := G) (i := 0) hϖ hϖ']

/-- The tame character read on the quotient `G_0 / G_1` it factors through. It is injective
(`TauCeti.tameCharacterGraded_injective`). -/
def tameCharacterGraded (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G 𝒪[L] (0 : ℤ) →* 𝓀[L]ˣ :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits (K := L)).toMonoidHom.comp
    (ramificationGroupGradedToUnitFiltrationGraded 0 hϖ)

-- The `(0 : ℤ)` index of the depth-zero declarations is `simp`-normal, unlike the cast `(i : ℤ)`
-- of the general ones, so this application lemma can carry `@[simp]`.
@[simp]
theorem tameCharacterGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (0 : ℤ)) :
    tameCharacterGraded hϖ (QuotientGroup.mk σ) = tameCharacter hϖ σ := (rfl)

/-- The graded tame character does not depend on the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {ϖ' : 𝒪[L]} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacterGraded (G := G) hϖ = tameCharacterGraded (G := G) hϖ' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible (G := G) (i := 0) hϖ hϖ']

/-- **The tame character is injective on `G_0 / G_1`.** -/
theorem tameCharacterGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacterGraded (G := G) hϖ) :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits (K := L)).injective.comp
    (ramificationGroupGradedToUnitFiltrationGraded_injective (i := 0) hϖ)

variable (G L) in
/-- **The tame quotient is cyclic**: `G_0 / G_1` embeds into the multiplicative group of the
residue field, which is cyclic because the residue field is finite. -/
theorem isCyclic_ramificationGroupGraded_zero :
    IsCyclic (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) :=
  have ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  isCyclic_of_injective _ (tameCharacterGraded_injective hϖ)

variable (G L) in
/-- The order of the tame quotient `G_0 / G_1` divides `q - 1`, for `q` the cardinality of the
residue field. -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) ∣ Nat.card 𝓀[L] - 1 := by
  obtain ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Nat.card_units]
  exact Subgroup.card_dvd_of_injective _ (tameCharacterGraded_injective hϖ)

/-! ### Wild inertia is a `p`-group -/

variable (G) in
/-- At positive depth `i`, the graded piece `G_i / G_{i+1}` is a `p`-group for the residue
characteristic `p`: it embeds into `U(L,i) / U(L,i+1)`, which has `q` elements. -/
theorem isPGroup_ramificationGroupGraded_natCast_succ (p : ℕ) [CharP 𝓀[L] p] (i : ℕ) :
    IsPGroup p (RamificationGroupGraded G 𝒪[L] ((i + 1 : ℕ) : ℤ)) :=
  have ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  (isPGroup_unitFiltration_succ_quotient_add_succ p i 1).of_injective _
    (ramificationGroupGradedToUnitFiltrationGraded_injective (i := i + 1) hϖ)

variable (G) in
/-- **The positive-depth ramification groups are `p`-groups**, for `p` the residue
characteristic, whenever the action is faithful and `G_0` is finite; in particular the wild
inertia group `G_1` is a `p`-group. The filtration reaches `1`, and each positive-depth step
`G_i / G_{i+1}` is a `p`-group (`TauCeti.isPGroup_ramificationGroupGraded_natCast_succ`). -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP 𝓀[L] p] [FaithfulSMul G 𝒪[L]]
    [Finite (ramificationGroup G 𝒪[L] 0)] {i : ℤ} (hi : 0 < i) :
    IsPGroup p (ramificationGroup G 𝒪[L] i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G 𝒪[L]
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = ((j + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
  -- Descending induction on the distance `d` from the index `j + 1` to a vanishing index.
  suffices ∀ d j : ℕ, N ≤ j + 1 + d → IsPGroup p (ramificationGroup G 𝒪[L] ((j + 1 : ℕ) : ℤ)) from
    this N.toNat j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [hN _ (by omega)]
    exact IsPGroup.of_bot
  | succ d ih =>
    intro j hj
    have hsucc := ih (j + 1) (by omega)
    push_cast at hsucc
    -- `G_{j+1}` is an extension of the `p`-group `G_{j+1} / G_{j+2}` by the `p`-group `G_{j+2}`.
    refine IsPGroup.of_subgroup_of_quotient ?_ (isPGroup_ramificationGroupGraded_natCast_succ G p j)
    push_cast
    exact hsucc.comap_subtype

/-! ### Wild inertia as the Sylow subgroup of inertia -/

variable (G) in
/-- The index of `G_1` in `G_0` is prime to the residue characteristic `p`. This is the
order-theoretic consequence of the tame-character embedding `G_0/G_1 → 𝓀[L]ˣ`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [CharP 𝓀[L] p] :
    ¬p ∣ ((ramificationGroup G 𝒪[L] 1).subgroupOf
      (ramificationGroup G 𝒪[L] 0)).index := by
  let _ := Fintype.ofFinite 𝓀[L]
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  intro hpIndex
  have hpCard : p ∣ Nat.card (RamificationGroupGraded G 𝒪[L] 0) := by
    rwa [RamificationGroupGraded, zero_add, ← Subgroup.index_eq_card]
  have hpResidueCard : p ∣ Nat.card 𝓀[L] := by
    obtain ⟨d, -, hd⟩ := FiniteField.card 𝓀[L] p
    rw [Nat.card_eq_fintype_card, hd]
    exact dvd_pow_self p d.ne_zero
  have hcoprime : Nat.Coprime p (Nat.card 𝓀[L] - 1) :=
    Nat.Coprime.of_dvd_left hpResidueCard <|
      (Nat.coprime_self_sub_right
        (show 1 ≤ Nat.card 𝓀[L] from Nat.card_pos)).2 (by simp)
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime <|
    hpCard.trans
      (card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one (L := L) G)

variable (G) in
/-- **Wild inertia is the Sylow `p`-subgroup of inertia.** For the residue characteristic `p`,
the first ramification group `G_1`, viewed as a subgroup of `G_0`, is a Sylow `p`-subgroup.

The two inputs are the positive-depth `p`-group theorem and the tame-character embedding, which
shows that the index `#(G_0/G_1)` divides `#𝓀[L] - 1` and is therefore prime to `p`. -/
noncomputable def ramificationGroupOneSylow (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    Sylow p (ramificationGroup G 𝒪[L] 0) :=
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  ((isPGroup_ramificationGroup G p (i := 1) (by omega)).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one G p)

variable (G) in
/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    (ramificationGroupOneSylow (G := G) (L := L) p :
      Subgroup (ramificationGroup G 𝒪[L] 0)) =
      (ramificationGroup G 𝒪[L] 1).subgroupOf (ramificationGroup G 𝒪[L] 0) :=
  (rfl)

variable (G) in
/-- The wild inertia Sylow subgroup is normal in inertia. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    (ramificationGroupOneSylow (G := G) (L := L) p :
      Subgroup (ramificationGroup G 𝒪[L] 0)).Normal := by
  rw [ramificationGroupOneSylow_coe, Subgroup.normal_subgroupOf_iff_le_normalizer
    (ramificationGroup_antitone (G := G) (𝒪[L]) (by omega : (0 : ℤ) ≤ 1))]
  rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

variable (G) in
/-- The wild inertia Sylow subgroup is the unique Sylow `p`-subgroup of inertia. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)]
    (Q : Sylow p (ramificationGroup G 𝒪[L] 0)) :
    Q = ramificationGroupOneSylow (G := G) (L := L) p := by
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  let _ : Unique (Sylow p (ramificationGroup G 𝒪[L] 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow (G := G) (L := L) p)
      (ramificationGroupOneSylow_normal (G := G) (L := L) p)
  exact Subsingleton.elim _ _

variable (G) in
/-- The order of wild inertia is the residue-characteristic part of the order of inertia:
`#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    Nat.card (ramificationGroup G 𝒪[L] 1) =
      p ^ (Nat.card (ramificationGroup G 𝒪[L] 0)).factorization p := by
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow G p)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G 𝒪[L] (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

variable (G) in
/-- **Wild inertia is trivial exactly in the tame case.** For the residue characteristic `p`, the
first ramification group `G_1` is trivial if and only if `p` does not divide the order of the
inertia group `G_0`: `G_1` is the Sylow `p`-subgroup of `G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [CharP 𝓀[L] p] [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    ramificationGroup G 𝒪[L] 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G 𝒪[L] 0) := by
  have hp : p.Prime := CharP.char_is_prime 𝓀[L] p
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one G p, pow_eq_one_iff_right hp.ne_one,
    Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

end TauCeti
