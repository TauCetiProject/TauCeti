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
public import TauCeti.RingTheory.DiscreteValuationRing.RamificationGroup
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded
import TauCeti.NumberTheory.LocalField.Units.Decomposition
import TauCeti.RingTheory.Valuation.ValuativeRel.Action

/-!
# The quotient embeddings of the ramification filtration

Let `L` be a nonarchimedean local field and let a group `G` act on `L` by ring automorphisms
preserving the ring of integers, so that both the ramification filtration
`G_i = TauCeti.IsLocalRing.ramificationGroup G 𝒪[L] i` and the unit filtration
`U(L,i) = TauCeti.unitFiltration L i` are defined. The motivating case is the Galois group
`L ≃ₐ[K] L` of a finite extension of local fields, for which
`TauCeti.integerRingIsInvariantSubring` supplies the invariance hypothesis.

Identifying `U(L,i)` with `(maximalIdeal 𝒪[L] ^ i).principalUnitGroup`
(`TauCeti.unitFiltrationEquivPrincipalUnitGroup`) and `U(L,i) / U(L,i+1)` with
`(maximalIdeal 𝒪[L]).PrincipalUnitGroupPowGraded i`
(`TauCeti.unitFiltrationGradedEquivPrincipalUnitGroupPowGraded`), this file transports the
general discrete-valuation-ring constructions from
`TauCeti/RingTheory/DiscreteValuationRing/RamificationGroup.lean` to the unit filtration,
yielding `θ_i : G_i / G_{i+1} →* U(L,i) / U(L,i+1)`. The map `θ_i` is injective, because
membership of an element of `G_0` in `G_{i+1}` is decided at `ϖ` alone: this is the uniformizer
criterion `TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem` over the invariant
subring of `𝒪[L]`, whose residue extension is separable because `𝓀[L]` is finite.

At depth zero the general tame character `TauCeti.IsLocalRing.tameCharacter G 𝒪[L]` embeds
`G_0 / G_1` into `𝓀[L]ˣ`, so the tame quotient is cyclic of order dividing `q - 1`, where `q` is
the cardinality of the residue field, and the index of `G_1` in `G_0` is prime to the residue
characteristic `p`. At positive depth every `G_i / G_{i+1}` is a `p`-group; when the action is
faithful and `G_0` is finite, every `G_i` with `i ≥ 1`, in particular the wild inertia group `G_1`,
is a `p`-group, and `G_1` is the Sylow `p`-subgroup `TauCeti.IsLocalRing.ramificationGroupOneSylow`
of `G_0`. These are the local-field cases of the general local-ring statements in
`TauCeti.RingTheory.LocalRing.RamificationGroup.Graded`.

## Main definitions

* `TauCeti.uniformizerRatio`: the ratio `σ ϖ / ϖ` in `U(L,i)`, transported from
  `TauCeti.IsDiscreteValuationRing.uniformizerRatio`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded`: the homomorphism
  `G_i → U(L,i) / U(L,i+1)`, and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded`: the induced `θ_i` on `G_i / G_{i+1}`.

## Main results

* `TauCeti.mem_ramificationGroup_natCast_iff_valuation_le`: the valuation form of the
  ramification filtration, `v(σ x - x) ≤ v(ϖ)^(i+1)` for every integer `x`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible` and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible`: independence of the
  choice of uniformizer.
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
* `TauCeti.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`: the tame quotient
  is cyclic, of order dividing `q - 1`.
* `TauCeti.isPGroup_ramificationGroupGraded_natCast_succ` and
  `TauCeti.isPGroup_ramificationGroup`: the positive-depth graded pieces, and, for a faithful
  action with finite `G_0`, the positive-depth ramification groups, are `p`-groups.
* `TauCeti.not_dvd_index_ramificationGroup_one`: the index of `G_1` in `G_0` is prime to `p`.
* `TauCeti.natCard_ramificationGroup_one`: the order of `G_1` is the `p`-part of the order of `G_0`.
* `TauCeti.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: `G_1` is
  trivial exactly when `p` does not divide `Nat.card G_0`, that is when `G_0` is finite of order
  prime to `p` (the tame case), since `Nat.card G_0 = 0` when `G_0` is infinite.

## Implementation notes

The ramification groups are indexed by `ℤ` and the unit filtration by `ℕ`. Every general statement
below therefore fixes a natural index `i` and reads the ramification group at `(i : ℤ)`, whereas
the depth-zero declarations fix the index `(0 : ℤ)`, the spelling in which a statement about
`G_0 / G_1` is met.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5 to 7.
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
  · rw [hy, map_div₀, valuation_smul σ (ϖ : L), div_self hϖpos.ne']
  · rw [hy, div_sub_one hϖne, map_div₀, div_le_iff₀ hϖpos, ← pow_succ]
    exact (mem_ramificationGroup_natCast_iff_valuation_le hϖ).mp hσ ϖ

variable (i) in
/-- The ratio `σ ϖ / ϖ` of a uniformizer `ϖ` and its image under an element `σ` of the `i`-th
ramification group, as an element of the `i`-th step `U(L,i)` of the unit filtration. -/
def uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    unitFiltration L i :=
  (unitFiltrationEquivPrincipalUnitGroup i).symm
    (IsDiscreteValuationRing.uniformizerRatio i hϖ σ)

private theorem uniformizerRatio_eq_symm (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    uniformizerRatio i hϖ σ =
      (unitFiltrationEquivPrincipalUnitGroup i).symm
        (IsDiscreteValuationRing.uniformizerRatio i hϖ σ) :=
  (rfl)

/-- Coerced to `L`, `uniformizerRatio i hϖ σ` is `σ • ϖ / ϖ`. -/
@[simp]
theorem coe_uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ((uniformizerRatio i hϖ σ : Lˣ) : L) = (σ : G) • (ϖ : L) / (ϖ : L) := by
  have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hcoe : ((uniformizerRatio i hϖ σ : Lˣ) : L) =
      (((IsDiscreteValuationRing.uniformizerRatio i hϖ σ : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
    rw [uniformizerRatio_eq_symm, coe_unitFiltrationEquivPrincipalUnitGroup_symm_apply,
      Units.coe_map, MonoidHom.coe_ofClass, Subring.coe_subtype]
  rw [hcoe, eq_div_iff hϖne, mul_comm, ← coe_smul_integer, ← MulMemClass.coe_mul,
    IsDiscreteValuationRing.mul_coe_uniformizerRatio]

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
    (mem_unitFiltration_succ_of_val_eq_smul_div hσ u.property (hf _))
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
  (unitFiltrationGradedEquivPrincipalUnitGroupPowGraded i).symm.toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded i hϖ)

/-- Evaluating `ramificationGroupToUnitFiltrationGraded` on `σ ∈ G_i` gives the class of
`uniformizerRatio`. -/
@[simp]
theorem ramificationGroupToUnitFiltrationGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded_apply,
    unitFiltrationGradedEquivPrincipalUnitGroupPowGraded_symm_mk, ← uniformizerRatio_eq_symm]

/-- The quotient homomorphism does not depend on the choice of uniformizer: two uniformizers
differ by a unit of `𝒪[L]`, and `σ` moves that unit inside `U(L,i+1)`. -/
theorem ramificationGroupToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupToUnitFiltrationGraded (G := G) i hϖ' := by
  rw [ramificationGroupToUnitFiltrationGraded, ramificationGroupToUnitFiltrationGraded,
    IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible
      i hϖ hϖ']

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

/-- The residue field of `L` is separable over the residue field of the invariant subring of
`𝒪[L]`, because it is finite, hence perfect. So the invariant subring, which is local by
`TauCeti.FixedPoints.isLocalRing_subalgebra`, is a base ring for the uniformizer criterion
`TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem` and the graded embeddings of
`TauCeti.RingTheory.LocalRing.RamificationGroup.Graded`. -/
instance isSeparable_residueField_fixedPoints_subalgebra :
    Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra ℤ 𝒪[L] G)) 𝓀[L] := by
  have : Finite (ResidueField (FixedPoints.subalgebra ℤ 𝒪[L] G)) :=
    Finite.of_injective _ (algebraMap _ 𝓀[L]).injective
  infer_instance

/-- **Membership in the ramification filtration is decided at a uniformizer**: an element `σ` of
the inertia group `G_0` lies in `G_n` exactly when `σ ϖ ≡ ϖ` modulo `𝓂[L] ^ (n + 1)`. This is the
local-field case of `TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`, over the
invariant subring of `𝒪[L]`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] 0) {n : ℕ} :
    σ ∈ ramificationGroup G 𝒪[L] (n : ℤ) ↔ σ • ϖ - ϖ ∈ 𝓂[L] ^ (n + 1) :=
  IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem (FixedPoints.subalgebra ℤ 𝒪[L] G)
    hϖ.maximalIdeal_eq hσ

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
    rw [map_div₀, valuation_smul σ (ϖ : L), div_self ((map_ne_zero _).2 hϖ0)]
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
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.ker_comp_of_injective _ _
      (unitFiltrationGradedEquivPrincipalUnitGroupPowGraded i).symm.injective,
    IsDiscreteValuationRing.mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff i hϖ,
    sub_mem_maximalIdeal_pow_iff hϖ]

/-- The next step `G_{i+1}` of the ramification filtration is killed by the quotient
homomorphism. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (hϖ : Irreducible ϖ) :
    (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded i hϖ).ker := by
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.ker_comp_of_injective _ _
    (unitFiltrationGradedEquivPrincipalUnitGroupPowGraded i).symm.injective]
  exact IsDiscreteValuationRing.ramificationGroup_succ_subgroupOf_le_ker i hϖ

/-- **The kernel of the quotient homomorphism is exactly `G_{i+1}`**, which is what makes the
induced `θ_i` on `G_i / G_{i+1}` an embedding: membership of an element of `G_0` in `G_{i+1}` is
decided at `ϖ` (`TauCeti.mem_ramificationGroup_natCast_iff_smul_sub_mem`). -/
theorem ker_ramificationGroupToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    (ramificationGroupToUnitFiltrationGraded i hϖ).ker =
      (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker hϖ)
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G 𝒪[L] 0 :=
    ramificationGroup_antitone G 𝒪[L] (Int.natCast_nonneg i) σ.property
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
  (unitFiltrationGradedEquivPrincipalUnitGroupPowGraded i).symm.toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded i hϖ)

/-- Evaluating `ramificationGroupGradedToUnitFiltrationGraded` on a quotient class gives the class
of `uniformizerRatio`. -/
@[simp]
theorem ramificationGroupGradedToUnitFiltrationGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  simp only [ramificationGroupGradedToUnitFiltrationGraded, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_mk,
    unitFiltrationGradedEquivPrincipalUnitGroupPowGraded_symm_mk, uniformizerRatio_eq_symm]

/-- **The quotient embeddings are injective.** -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ) := by
  have hlift :
      ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ =
        QuotientGroup.lift _ (ramificationGroupToUnitFiltrationGraded i hϖ)
          (ramificationGroup_succ_subgroupOf_le_ker hϖ) := by
    refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun σ ↦ ?_)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk, ramificationGroupGradedToUnitFiltrationGraded_mk,
      ramificationGroupToUnitFiltrationGraded_apply]
  rw [hlift, QuotientGroup.injective_lift_iff]
  exact (ker_ramificationGroupToUnitFiltrationGraded hϖ).symm

/-- The descended quotient map does not depend on the choice of uniformizer. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ' := by
  rw [ramificationGroupGradedToUnitFiltrationGraded, ramificationGroupGradedToUnitFiltrationGraded,
    IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible
      i hϖ hϖ']

/-! ### The tame quotient -/

variable (G L) in
/-- **The tame quotient is cyclic**: the tame character `TauCeti.IsLocalRing.tameCharacterGraded`
embeds `G_0 / G_1` into the multiplicative group of the residue field, which is cyclic because the
residue field is finite. Unlike `TauCeti.IsLocalRing.isCyclic_ramificationGroupGraded_zero`, no
finiteness of `G_0 / G_1` is assumed. -/
theorem isCyclic_ramificationGroupGraded_zero :
    IsCyclic (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) :=
  isCyclic_of_injective _
    (IsLocalRing.tameCharacterGraded_injective (G := G) (FixedPoints.subalgebra ℤ 𝒪[L] G))

variable (G L) in
/-- The order of the tame quotient `G_0 / G_1` divides `q - 1`, for `q` the cardinality of the
residue field. -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) ∣ Nat.card 𝓀[L] - 1 := by
  rw [← Nat.card_units]
  exact Subgroup.card_dvd_of_injective _
    (IsLocalRing.tameCharacterGraded_injective (G := G) (FixedPoints.subalgebra ℤ 𝒪[L] G))

/-! ### Wild inertia is a `p`-group -/

variable (G) in
/-- At positive depth `i`, the graded piece `G_i / G_{i+1}` is a `p`-group for the residue
characteristic `p`. This is the local-field case of
`TauCeti.IsLocalRing.isPGroup_ramificationGroupGraded`. -/
theorem isPGroup_ramificationGroupGraded_natCast_succ (p : ℕ) [CharP 𝓀[L] p] (i : ℕ) :
    IsPGroup p (RamificationGroupGraded G 𝒪[L] ((i + 1 : ℕ) : ℤ)) :=
  IsLocalRing.isPGroup_ramificationGroupGraded p (by omega)

variable (G) in
/-- **The positive-depth ramification groups are `p`-groups**, for `p` the residue
characteristic, whenever the action is faithful and `G_0` is finite; in particular the wild
inertia group `G_1` is a `p`-group. This is the local-field case of
`TauCeti.IsLocalRing.isPGroup_ramificationGroup`. -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP 𝓀[L] p] [FaithfulSMul G 𝒪[L]]
    [Finite (ramificationGroup G 𝒪[L] 0)] {i : ℤ} (hi : 0 < i) :
    IsPGroup p (ramificationGroup G 𝒪[L] i) :=
  IsLocalRing.isPGroup_ramificationGroup G 𝒪[L] p hi

/-! ### Wild inertia as the Sylow subgroup of inertia -/

variable (G) in
/-- The index of `G_1` in `G_0` is prime to the residue characteristic `p`. This is the local-field
case of `TauCeti.IsLocalRing.not_dvd_index_ramificationGroup_one`, where `G_0 / G_1` is finite
because it embeds in `𝓀[L]ˣ`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [CharP 𝓀[L] p] :
    ¬p ∣ ((ramificationGroup G 𝒪[L] 1).subgroupOf
      (ramificationGroup G 𝒪[L] 0)).index := by
  have : Finite (RamificationGroupGraded G 𝒪[L] 0) := Finite.of_injective _
    (IsLocalRing.tameCharacterGraded_injective (G := G) (FixedPoints.subalgebra ℤ 𝒪[L] G))
  exact IsLocalRing.not_dvd_index_ramificationGroup_one (FixedPoints.subalgebra ℤ 𝒪[L] G) p

variable (G) in
/-- The order of wild inertia is the residue-characteristic part of the order of inertia:
`#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    Nat.card (ramificationGroup G 𝒪[L] 1) =
      p ^ (Nat.card (ramificationGroup G 𝒪[L] 0)).factorization p := by
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  exact IsLocalRing.natCard_ramificationGroup_one_of_not_dvd_index G 𝒪[L] p
    (not_dvd_index_ramificationGroup_one G p)

variable (G) in
/-- **Wild inertia is trivial exactly in the tame case.** For the residue characteristic `p`, the
first ramification group `G_1` is trivial if and only if `p` does not divide `Nat.card G_0`, that
is, if and only if the inertia group `G_0` is finite of order prime to `p`: when `G_0` is infinite,
`Nat.card G_0 = 0`, and `G_1` is nontrivial because `G_0 / G_1` embeds in the finite group
`𝓀[L]ˣ`. When `G_0` is finite, `G_1` is its Sylow `p`-subgroup. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [CharP 𝓀[L] p] [FaithfulSMul G 𝒪[L]] :
    ramificationGroup G 𝒪[L] 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G 𝒪[L] 0) := by
  have hp : p.Prime := CharP.char_is_prime 𝓀[L] p
  by_cases hfin : Finite (ramificationGroup G 𝒪[L] 0)
  · rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one G p, pow_eq_one_iff_right hp.ne_one,
      Nat.factorization_eq_zero_iff]
    simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]
  · -- if `G_0` is infinite, `G_1 ≠ ⊥`, since `G_0 / G_1` embeds in the finite group `𝓀[L]ˣ`
    have hinf := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    simp only [dvd_zero, not_true_eq_false, iff_false]
    intro h
    have hker :=
      IsLocalRing.ker_tameCharacter (G := G) (S := 𝒪[L]) (FixedPoints.subalgebra ℤ 𝒪[L] G)
    rw [h, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff] at hker
    exact hfin (Finite.of_injective _ hker)

end TauCeti
