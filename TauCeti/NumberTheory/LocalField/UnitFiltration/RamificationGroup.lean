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
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.Valuation.ValuativeRel.Action

/-!
# The quotient embeddings of the ramification filtration

Let `L` be a nonarchimedean local field and let a group `G` act on `L` by ring automorphisms
preserving the ring of integers, so that both the ramification filtration
`G_i = TauCeti.IsLocalRing.ramificationGroup G 𝒪[L] i` and the unit filtration
`U(L,i) = TauCeti.unitFiltration L i` are defined. The motivating case is the Galois group
`L ≃ₐ[K] L` of a finite extension of local fields, for which
`TauCeti.integerRingIsInvariantSubring` supplies the invariance hypothesis.

Transporting the discrete-valuation-ring quotient homomorphisms of
`TauCeti/RingTheory/DiscreteValuationRing/RamificationGroup.lean` into `UnitFiltrationGraded L i`
gives the choice-free quotient maps `θ_i : G_i / G_{i+1} → U(L,i) / U(L,i+1)`, and without any
specified base ring `R`, Teichmüller lifting (`TauCeti.teichmullerLift`) shows that every `θ_i` is
injective: an element of `G_0` fixes every Teichmüller representative, and every integer of `L` is
a Teichmüller representative plus `ϖ` times an integer, so membership of an element of `G_0` in
`G_{i+1}` is decided at `ϖ` alone.

At depth zero, the DVR tame character `TauCeti.IsDiscreteValuationRing.tameCharacter G 𝒪[L]` and
its graded form `TauCeti.IsDiscreteValuationRing.tameCharacterGraded G 𝒪[L]` embed `G_0 / G_1`
into `𝓀[L]ˣ`, so the tame quotient is cyclic of order dividing `q - 1`, where `q` is the
cardinality of the residue field. Combining this prime-to-`p` index bound with the local-ring
positive-depth `p`-group theorem `TauCeti.IsLocalRing.isPGroup_ramificationGroup` shows that, when
the action is faithful and `G_0` is finite, wild inertia `G_1` is the unique normal Sylow
`p`-subgroup of `G_0`.

## Main definitions

* `TauCeti.uniformizerRatio`: the ratio `σ ϖ / ϖ`, as an element of `U(L,i)`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded`: the choice-free homomorphism
  `G_i → U(L,i) / U(L,i+1)`, and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded`: the induced `θ_i` on `G_i / G_{i+1}`.
* `TauCeti.ramificationGroupOneSylow`: the wild inertia group `G_1`, viewed inside `G_0`, as its
  unique normal Sylow `p`-subgroup.

## Main results

* `TauCeti.mem_ramificationGroup_natCast_iff_valuation_le`: the valuation form of the
  ramification filtration, `v(σ x - x) ≤ v(ϖ)^(i+1)` for every integer `x`.
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
  `G_{i+1}`, and `θ_i` is injective without specifying a base ring.
* `TauCeti.ramificationGroupGradedToResidueField_injective`,
  `TauCeti.coe_tameCharacter_of_val_eq_smul_div`, and `TauCeti.tameCharacterGraded_injective`:
  fraction-field evaluation and base-free injectivity of the DVR tame character and positive-depth
  residue coordinate.
* `TauCeti.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`: the tame quotient
  is cyclic, of order dividing `q - 1`.
* `TauCeti.eq_ramificationGroupOneSylow`, `TauCeti.natCard_ramificationGroup_one`, and
  `TauCeti.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: `G_1` is the
  unique normal Sylow `p`-subgroup of `G_0`, its order is the `p`-part of `#G_0`, and `G_1` is
  trivial exactly when `p ∤ #G_0`.

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
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
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
ramification group, as an element of the `i`-th step `U(L,i)` of the unit filtration, transported
from `TauCeti.IsDiscreteValuationRing.uniformizerRatio`. -/
def uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    unitFiltration L i :=
  principalUnitGroupEquivUnitFiltration L i (IsDiscreteValuationRing.uniformizerRatio i hϖ σ)

@[simp]
theorem coe_uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ((uniformizerRatio i hϖ σ : Lˣ) : L) = (σ : G) • (ϖ : L) / (ϖ : L) := by
  have hϖ0 : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  rw [uniformizerRatio, coe_principalUnitGroupEquivUnitFiltration, Units.coe_map]
  refine eq_div_of_mul_eq hϖ0 ?_
  rw [mul_comm]
  change (ϖ : L) * (((IsDiscreteValuationRing.uniformizerRatio i hϖ σ : 𝒪[L]ˣ) : 𝒪[L]) : L) =
    (σ : G) • (ϖ : L)
  rw [← MulMemClass.coe_mul, IsDiscreteValuationRing.mul_uniformizerRatio]
  rfl

/-- For `σ` in the `i`-th ramification group, the ratio `σ y / y` of any nonzero `y` lies in the
`i`-th step `U(L,i)` of the unit filtration. For a uniformizer this is
`TauCeti.mem_unitFiltration_of_val_eq_smul_div`, and for a unit it is one step deeper, by
`TauCeti.mem_unitFiltration_succ_of_val_eq_smul_div`. -/
theorem smul_div_mem_unitFiltration (hσ : σ ∈ ramificationGroup G 𝒪[L] (i : ℤ)) {y z : Lˣ}
    (hz : (z : L) = σ • (y : L) / (y : L)) : z ∈ unitFiltration L i := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible 𝒪[L]
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

variable (L G i) in
/-- The **quotient homomorphism** `G_i → U(L,i) / U(L,i+1)` carrying `σ` to the class of `σ ϖ / ϖ`
for any uniformizer `ϖ`, transported from
`TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded`. It is independent of
`ϖ` and kills `G_{i+1}`, inducing `TauCeti.ramificationGroupGradedToUnitFiltrationGraded`. -/
def ramificationGroupToUnitFiltrationGraded :
    ramificationGroup G 𝒪[L] (i : ℤ) →* UnitFiltrationGraded L i :=
  (principalUnitGroupGradedEquivUnitFiltrationGraded L i).toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded G 𝒪[L] i)

theorem ramificationGroupToUnitFiltrationGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded L G i σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded_apply hϖ,
    principalUnitGroupGradedEquivUnitFiltrationGraded_mk]
  rfl

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
  suffices ∀ m ≤ n + 1, ∀ x : 𝒪[L], σ • x - x ∈ 𝓂[L] ^ m from this _ le_rfl
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm x
    have hx : x - teichmullerLift L (residue 𝒪[L] x) ∈ 𝓂[L] := by
      rw [← residue_eq_zero_iff, map_sub, residue_teichmullerLift, sub_self]
    have hstep := IsDiscreteValuationRing.smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer hϖ
      (Ideal.pow_le_pow_right hm h) (ih (by omega)) hx
    simpa [smul_sub, smul_teichmullerLift_of_mem_ramificationGroup_zero hσ] using hstep

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

/-- The kernel of the quotient homomorphism, as a valuation condition at a uniformizer:
`σ` is killed exactly when it moves `ϖ` one step deeper than membership in `G_i` requires. -/
theorem mem_ker_ramificationGroupToUnitFiltrationGraded_iff (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G 𝒪[L] (i : ℤ)} :
    σ ∈ (ramificationGroupToUnitFiltrationGraded L G i).ker ↔
      valuation L ((σ : G) • (ϖ : L) - (ϖ : L)) ≤ valuation L (ϖ : L) ^ (i + 2) := by
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.mem_ker, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGroupGradedEquivUnitFiltrationGraded L i).injective,
    ← MonoidHom.mem_ker,
    IsDiscreteValuationRing.mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff hϖ,
    sub_mem_maximalIdeal_pow_iff hϖ]

variable (L G i) in
/-- The next step `G_{i+1}` of the ramification filtration is killed by the quotient
homomorphism. -/
theorem ramificationGroup_succ_subgroupOf_le_ker :
    (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded L G i).ker := by
  intro σ hσ
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.mem_ker, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGroupGradedEquivUnitFiltrationGraded L i).injective]
  exact IsDiscreteValuationRing.ramificationGroup_succ_subgroupOf_le_ker G 𝒪[L] i hσ

variable (L G i) in
/-- **The kernel of the quotient homomorphism is exactly `G_{i+1}`**, which is what makes the
induced `θ_i` on `G_i / G_{i+1}` an embedding: membership of an element of `G_0` in `G_{i+1}` is
decided at `ϖ` (`TauCeti.mem_ramificationGroup_natCast_iff_smul_sub_mem`), without needing a base
ring. -/
theorem ker_ramificationGroupToUnitFiltrationGraded :
    (ramificationGroupToUnitFiltrationGraded L G i).ker =
      (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker L G i)
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G 𝒪[L] 0 :=
    ramificationGroup_antitone G 𝒪[L] (Int.natCast_nonneg i) σ.2
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem hϖ hσ₀, sub_mem_maximalIdeal_pow_iff hϖ]
  exact hσ

/-! ### The embedding of the graded pieces -/

variable (L G i) in
/-- The choice-free **quotient map** `θ_i : G_i / G_{i+1} →* U(L,i) / U(L,i+1)`, transported from
`TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded`. It is an
embedding (`TauCeti.ramificationGroupGradedToUnitFiltrationGraded_injective`). -/
def ramificationGroupGradedToUnitFiltrationGraded :
    RamificationGroupGraded G 𝒪[L] (i : ℤ) →* UnitFiltrationGraded L i :=
  (principalUnitGroupGradedEquivUnitFiltrationGraded L i).toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded G 𝒪[L] i)

theorem ramificationGroupGradedToUnitFiltrationGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded L G i (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupGradedToUnitFiltrationGraded, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_mk hϖ,
    principalUnitGroupGradedEquivUnitFiltrationGraded_mk]
  rfl

variable (L G i) in
/-- **The quotient embeddings are injective**, without specifying a base ring. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded L G i) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with | _ σ =>
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [ramificationGroupGradedToUnitFiltrationGraded_mk hϖ] at hx
  have hσ : σ ∈ (ramificationGroupToUnitFiltrationGraded L G i).ker := by
    rw [MonoidHom.mem_ker, ramificationGroupToUnitFiltrationGraded_apply hϖ, hx]
  rw [ker_ramificationGroupToUnitFiltrationGraded] at hσ
  exact (QuotientGroup.eq_one_iff _).2 hσ

/-! ### Fraction-field formulas and base-free injectivity for DVR coordinates -/

variable (G) in
/-- **The positive-depth residue coordinate is injective**, without specifying a base ring. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Function.Injective
      (IsDiscreteValuationRing.ramificationGroupGradedToResidueField G 𝒪[L] n π hπ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Additive.rec with | ofMul x =>
  induction x using QuotientGroup.induction_on with | _ τ =>
  rw [IsDiscreteValuationRing.ramificationGroupGradedToResidueField_ofMul_mk,
    map_eq_zero_iff _ (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ).injective,
    ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    IsDiscreteValuationRing.coe_uniformizerRatio_mem_principalUnitGroup_succ_iff] at hx
  have hτ0 : (τ : G) ∈ ramificationGroup G 𝒪[L] 0 :=
    ramificationGroup_antitone G 𝒪[L] (by omega : (0 : ℤ) ≤ (n : ℤ) + 1) τ.2
  have hτmem : (τ : G) ∈ ramificationGroup G 𝒪[L] ((n + 2 : ℕ) : ℤ) :=
    (mem_ramificationGroup_natCast_iff_smul_sub_mem hπ hτ0 (n := n + 2)).2 hx
  rw [ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact_mod_cast hτmem

/-- Computing the DVR tame character in fraction-field coordinates: if `(y : L) = σ • ϖ / ϖ`, then
`tameCharacter G 𝒪[L] σ = residue 𝒪[L] y`. -/
theorem coe_tameCharacter_of_val_eq_smul_div (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (0 : ℤ)) {y : 𝒪[L]}
    (hy : (y : L) = (σ : G) • (ϖ : L) / (ϖ : L)) :
    (IsDiscreteValuationRing.tameCharacter G 𝒪[L] σ : 𝓀[L]) = IsLocalRing.residue 𝒪[L] y := by
  have hϖ0 : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  refine IsDiscreteValuationRing.coe_tameCharacter_of_mul_eq hϖ σ (Subtype.ext ?_)
  rw [MulMemClass.coe_mul, coe_smul_integer, hy, mul_div_cancel₀ _ hϖ0]

variable (L G) in
/-- **The graded tame character is injective on `G_0 / G_1`**, without specifying a base ring. -/
theorem tameCharacterGraded_injective :
    Function.Injective (IsDiscreteValuationRing.tameCharacterGraded G 𝒪[L]) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with | _ σ =>
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [IsDiscreteValuationRing.tameCharacterGraded_mk, ← MonoidHom.mem_ker,
    IsDiscreteValuationRing.mem_ker_tameCharacter_iff hϖ] at hx
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, zero_add,
    ← Nat.cast_one, mem_ramificationGroup_natCast_iff_smul_sub_mem hϖ σ.2]
  exact hx

variable (L G) in
/-- **The tame quotient is cyclic**: `G_0 / G_1` embeds into the multiplicative group of the
residue field, which is cyclic because the residue field is finite. -/
theorem isCyclic_ramificationGroupGraded_zero :
    IsCyclic (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) :=
  isCyclic_of_injective _ (tameCharacterGraded_injective L G)

variable (L G) in
/-- The order of the tame quotient `G_0 / G_1` divides `q - 1`, for `q` the cardinality of the
residue field. -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) ∣ Nat.card 𝓀[L] - 1 := by
  rw [← Nat.card_units]
  exact Subgroup.card_dvd_of_injective _ (tameCharacterGraded_injective L G)

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
the first ramification group `G_1`, viewed as a subgroup of `G_0`, is a Sylow `p`-subgroup,
delegated to `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`. -/
noncomputable def ramificationGroupOneSylow (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    Sylow p (ramificationGroup G 𝒪[L] 0) :=
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  IsDiscreteValuationRing.ramificationGroupOneSylow G 𝒪[L] p
    (not_dvd_index_ramificationGroup_one G p)

variable (G) in
/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    (ramificationGroupOneSylow (G := G) (L := L) p :
      Subgroup (ramificationGroup G 𝒪[L] 0)) =
      (ramificationGroup G 𝒪[L] 1).subgroupOf (ramificationGroup G 𝒪[L] 0) :=
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  IsDiscreteValuationRing.ramificationGroupOneSylow_coe p
    (not_dvd_index_ramificationGroup_one G p)

variable (G) in
/-- The wild inertia Sylow subgroup is normal in inertia. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    (ramificationGroupOneSylow (G := G) (L := L) p :
      Subgroup (ramificationGroup G 𝒪[L] 0)).Normal := by
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  exact IsDiscreteValuationRing.ramificationGroupOneSylow_normal p
    (not_dvd_index_ramificationGroup_one G p)

variable (G) in
/-- The wild inertia Sylow subgroup is the unique Sylow `p`-subgroup of inertia. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)]
    (Q : Sylow p (ramificationGroup G 𝒪[L] 0)) :
    Q = ramificationGroupOneSylow (G := G) (L := L) p := by
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  exact IsDiscreteValuationRing.eq_ramificationGroupOneSylow p
    (not_dvd_index_ramificationGroup_one G p) Q

variable (G) in
/-- The order of wild inertia is the residue-characteristic part of the order of inertia:
`#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    Nat.card (ramificationGroup G 𝒪[L] 1) =
      p ^ (Nat.card (ramificationGroup G 𝒪[L] 0)).factorization p := by
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  exact IsDiscreteValuationRing.natCard_ramificationGroup_one p
    (not_dvd_index_ramificationGroup_one G p)

variable (G) in
/-- **Wild inertia is trivial exactly in the tame case.** For the residue characteristic `p`, the
first ramification group `G_1` is trivial if and only if `p` does not divide the order of the
inertia group `G_0`: `G_1` is the Sylow `p`-subgroup of `G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [CharP 𝓀[L] p] [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    ramificationGroup G 𝒪[L] 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G 𝒪[L] 0) := by
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  exact IsDiscreteValuationRing.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero
    p (not_dvd_index_ramificationGroup_one G p)

end TauCeti
