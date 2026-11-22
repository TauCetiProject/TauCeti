/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import TauCeti.NumberTheory.LocalField.Teichmuller
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.RamificationGroup
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.LocalRing.Pullback
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.Valuation.ValuativeRel.Action

/-!
# The quotient embeddings of the ramification filtration of a local field

Let `L` be a nonarchimedean local field and let a group `G` act on `L` by ring automorphisms
preserving the ring of integers, so that both the ramification filtration
`G_i = TauCeti.IsLocalRing.ramificationGroup G 𝒪[L] i` and the ambient-field unit filtration
`U(L,i) = TauCeti.unitFiltration L i` are defined. The motivating case is the Galois group
`L ≃ₐ[K] L` of a finite extension of local fields, for which
`TauCeti.integerRingIsInvariantSubring` supplies the invariance hypothesis.

The general discrete-valuation-ring theory — uniformizer ratios in `𝒪[L]ˣ`, graded embeddings into
`TauCeti.IsLocalRing.UnitFiltrationGraded 𝒪[L] i`, the tame character `G_0 →* 𝓀[L]ˣ`, positive-depth
residue coordinates, cyclicity of `G_0 / G_1`, and the `p`-group / Sylow structure of wild inertia
— lives in `TauCeti.RingTheory.DiscreteValuationRing.RamificationGroup`. This file transports the
unit-filtration maps to the ambient-field unit filtration `U(L,i)` via
`TauCeti.unitFiltrationEquivInteger` and `TauCeti.unitFiltrationGradedEquivInteger`, and records
the valuation and Teichmüller-lift statements specific to local fields.

## Main definitions

* `TauCeti.uniformizerRatio`: the ratio `σ ϖ / ϖ`, as an element of `U(L,i)`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded`: the homomorphism
  `G_i → U(L,i) / U(L,i+1)`, and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded`: the induced embedding `θ_i` on
  `G_i / G_{i+1}`.

## Main results

* `TauCeti.mem_ramificationGroup_natCast_iff_valuation_le`: the valuation form of the
  ramification filtration, `v(σ x - x) ≤ v(ϖ)^(i+1)` for every integer `x`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible` and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible`: independence of the
  choice of uniformizer.
* `TauCeti.smul_teichmullerLift_of_mem_ramificationGroup_zero`: `G_0` fixes every Teichmüller
  representative.
* `TauCeti.smul_div_mem_unitFiltration`: for `σ ∈ G_i`, every ratio `σ y / y` lies in `U(L,i)`.
* `TauCeti.mem_ramificationGroup_one_of_valuation_pow_sub_one_lt_one`: an element of `G_0` lies in
  `G_1` once a `p`-power of `σ ϖ / ϖ` is congruent to `1`.
* `TauCeti.valuation_smul_div_pow_sub_one_lt_one`: if `σ ∈ G_0` fixes an element of valuation
  `v(a) ^ n`, then `(σ a / a) ^ n` is congruent to `1`.
* `TauCeti.ker_ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded_injective`: the kernel is exactly
  `G_{i+1}`, and `θ_i` is injective.

## Implementation notes

The ramification groups are indexed by `ℤ` and the unit filtration by `ℕ`. Every general statement
below therefore fixes a natural index `i` and reads the ramification group at `(i : ℤ)`. Since the
residue field `𝓀[L]` of a local field is finite, any group action on `𝒪[L]` has a separable residue
extension over its fixed subring, so the DVR injectivity results apply without specifying a base
field.

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

/-- The `G`-fixed subring of `𝒪[L]` is a local subring over which `𝓀[L]` is a separable residue
field extension (because `𝓀[L]` is finite). -/
private theorem exists_separableBaseRing.{u, v} (G : Type v) [Group G] (L : Type u) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : Algebra A 𝒪[L])
      (_ : IsLocalHom (algebraMap A 𝒪[L])) (_ : SMulCommClass G A 𝒪[L]),
      Algebra.IsSeparable (ResidueField A) 𝓀[L] := by
  let A : Subring 𝒪[L] := FixedPoints.subring 𝒪[L] G
  let E : Subring 𝒪[L] :=
    (RingHom.pi (MulSemiringAction.toRingHom G 𝒪[L])).eqLocus (RingHom.pi fun _ ↦ RingHom.id 𝒪[L])
  have hAE : A = E := Subring.ext fun _ ↦ funext_iff.symm
  have : IsLocalHom (algebraMap A 𝒪[L]) := hAE ▸ inferInstanceAs (IsLocalHom E.subtype)
  have : IsLocalRing A := hAE ▸ RingHom.isLocalRing_eqLocus _ _
  have : Finite (ResidueField A) :=
    Finite.of_injective _ (algebraMap (ResidueField A) 𝓀[L]).injective
  have : PerfectField (ResidueField A) := PerfectField.ofFinite
  have : Module.Finite (ResidueField A) 𝓀[L] := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (ResidueField A) 𝓀[L] := Algebra.IsAlgebraic.of_finite _ _
  exact ⟨↥A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

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
  set u : 𝒪[L]ˣ := unitFiltrationToIntegerUnits 0 ⟨x, hx⟩
  set w : 𝒪[L]ˣ := Units.map (MulSemiringAction.toRingHom G 𝒪[L] σ).toMonoidHom u / u
  have hw : Units.map (Subring.subtype 𝒪[L]).toMonoidHom w = y := by
    apply Units.ext
    have hu : ((u : 𝒪[L]) : L) = (x : L) := coe_unitFiltrationToIntegerUnits 0 ⟨x, hx⟩
    simp [w, hy, div_eq_mul_inv, coe_smul_integer, hu]
  simpa [← hw] using ((unitFiltrationEquivInteger (K := L) (i + 1)).symm
    ⟨w, unitsMap_div_mem_unitFiltration_succ hσ u⟩).property

variable (i) in
/-- The ratio `σ ϖ / ϖ` of a uniformizer `ϖ` and its image under an element `σ` of the `i`-th
ramification group, as an element of the `i`-th step `U(L,i)` of the unit filtration. -/
def uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    unitFiltration L i :=
  (unitFiltrationEquivInteger i).symm
    (TauCeti.IsDiscreteValuationRing.uniformizerRatio i hϖ σ)

@[simp]
theorem coe_uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ((uniformizerRatio i hϖ σ : Lˣ) : L) = (σ : G) • (ϖ : L) / (ϖ : L) := by
  have hϖ0 : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  apply mul_left_cancel₀ hϖ0
  rw [mul_div_cancel₀ _ hϖ0, uniformizerRatio, coe_unitFiltrationEquivInteger_symm,
    Units.coe_map, MonoidHom.coe_ofClass, Subring.coe_subtype, ← Subring.coe_mul,
    TauCeti.IsDiscreteValuationRing.mul_coe_uniformizerRatio, coe_smul_integer]

/-- For `σ` in the `i`-th ramification group and `ϖ` a uniformizer, the ratio `σ ϖ / ϖ` lies in
the `i`-th step `U(L,i)` of the unit filtration. -/
theorem mem_unitFiltration_of_val_eq_smul_div (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] (i : ℤ)) {y : Lˣ}
    (hy : (y : L) = σ • (ϖ : L) / (ϖ : L)) : y ∈ unitFiltration L i := by
  have hy' : y = uniformizerRatio i hϖ ⟨σ, hσ⟩ :=
    Units.ext (by rw [hy, coe_uniformizerRatio])
  exact hy' ▸ (uniformizerRatio i hϖ ⟨σ, hσ⟩).property

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
  (unitFiltrationGradedEquivInteger (K := L) i).symm.toMonoidHom.comp
    (TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded i hϖ)

@[simp]
theorem ramificationGroupToUnitFiltrationGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  simp [ramificationGroupToUnitFiltrationGraded, uniformizerRatio]

/-- The quotient homomorphism does not depend on the choice of uniformizer: two uniformizers
differ by a unit of `𝒪[L]`, and `σ` moves that unit inside `U(L,i+1)`. -/
theorem ramificationGroupToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupToUnitFiltrationGraded (G := G) i hϖ' := by
  rw [ramificationGroupToUnitFiltrationGraded, ramificationGroupToUnitFiltrationGraded,
    TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible
      i hϖ hϖ']

/-! ### Teichmüller lifts and valuation criteria -/

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

/-- An element of the inertia group `G_0` lies in `G_1` as soon as the ratio `σ ϖ / ϖ` of a
uniformizer `ϖ` has a `p`-power congruent to `1` modulo the maximal ideal, for `p` the residue
characteristic. -/
theorem mem_ramificationGroup_one_of_valuation_pow_sub_one_lt_one (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] 0) (p k : ℕ) [CharP 𝓀[L] p]
    (h : valuation L ((σ • (ϖ : L) / (ϖ : L)) ^ p ^ k - 1) < 1) :
    σ ∈ ramificationGroup G 𝒪[L] 1 := by
  obtain ⟨A, _, _, _, _, _, _⟩ := exists_separableBaseRing G L
  have : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  refine TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_one_of_pow_sub_one_mem_maximalIdeal
    A hϖ hσ p k ?_
  rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hcoe :
      (((TauCeti.IsDiscreteValuationRing.uniformizerRatio 0 hϖ ⟨σ, hσ⟩ : 𝒪[L]ˣ) : 𝒪[L]) : L) =
        σ • (ϖ : L) / (ϖ : L) := by
    simpa [uniformizerRatio] using coe_uniformizerRatio (i := 0) hϖ ⟨σ, hσ⟩
  simpa [hcoe] using h

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

/-! ### The kernel and the embedding of the graded pieces -/

/-- The kernel of the quotient homomorphism, as a valuation condition at the chosen uniformizer:
`σ` is killed exactly when it moves `ϖ` one step deeper than membership in `G_i` requires. -/
theorem mem_ker_ramificationGroupToUnitFiltrationGraded_iff (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G 𝒪[L] (i : ℤ)} :
    σ ∈ (ramificationGroupToUnitFiltrationGraded i hϖ).ker ↔
      valuation L ((σ : G) • (ϖ : L) - (ϖ : L)) ≤ valuation L (ϖ : L) ^ (i + 2) := by
  rw [ramificationGroupToUnitFiltrationGraded, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.ker_mulEquiv_comp,
    TauCeti.IsDiscreteValuationRing.mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ,
    sub_mem_maximalIdeal_pow_iff hϖ]

/-- The next step `G_{i+1}` of the ramification filtration is killed by the quotient
homomorphism. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (hϖ : Irreducible ϖ) :
    (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded i hϖ).ker := by
  rw [ramificationGroupToUnitFiltrationGraded, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.ker_mulEquiv_comp]
  exact TauCeti.IsDiscreteValuationRing.ramificationGroup_succ_subgroupOf_le_ker i hϖ

/-- **The kernel of the quotient homomorphism is exactly `G_{i+1}`**, which is what makes the
induced `θ_i` on `G_i / G_{i+1}` an embedding. -/
theorem ker_ramificationGroupToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    (ramificationGroupToUnitFiltrationGraded i hϖ).ker =
      (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) := by
  obtain ⟨A, _, _, _, _, _, _⟩ := exists_separableBaseRing G L
  rw [ramificationGroupToUnitFiltrationGraded, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.ker_mulEquiv_comp]
  exact TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToUnitFiltrationGraded A i hϖ

variable (i) in
/-- The **quotient map** `θ_i : G_i / G_{i+1} →* U(L,i) / U(L,i+1)`, induced by
`σ ↦ σ ϖ / ϖ` for a uniformizer `ϖ`. It is an embedding
(`TauCeti.ramificationGroupGradedToUnitFiltrationGraded_injective`). -/
def ramificationGroupGradedToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G 𝒪[L] (i : ℤ) →* UnitFiltrationGraded L i :=
  (unitFiltrationGradedEquivInteger (K := L) i).symm.toMonoidHom.comp
    (TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded i hϖ)

@[simp]
theorem ramificationGroupGradedToUnitFiltrationGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  simp [ramificationGroupGradedToUnitFiltrationGraded, uniformizerRatio]

/-- **The quotient embeddings are injective.** -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ) := by
  obtain ⟨A, _, _, _, _, _, _⟩ := exists_separableBaseRing G L
  exact (unitFiltrationGradedEquivInteger i).symm.injective.comp
    (TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_injective A i hϖ)

/-- The descended quotient map does not depend on the choice of uniformizer. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ' := by
  rw [ramificationGroupGradedToUnitFiltrationGraded, ramificationGroupGradedToUnitFiltrationGraded,
    TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible
      i hϖ hϖ']

end TauCeti
