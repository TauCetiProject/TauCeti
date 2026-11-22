/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.GroupTheory.Sylow
public import TauCeti.NumberTheory.LocalField.Teichmuller
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.DiscreteValuationRing.RamificationGroup
import TauCeti.RingTheory.Valuation.ValuativeRel.Action

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

so it defines `θ_i : G_i / G_{i+1} → U(L,i) / U(L,i+1)`. The map `θ_i` is injective: membership of
an element of `G_0` in `G_{i+1}` is decided at `ϖ` alone (supplied by the general
discrete-valuation-ring theory in `TauCeti.IsDiscreteValuationRing`).

At depth zero, composing with the reduction isomorphism `U(L,0) / U(L,1) ≃ 𝓀[L]ˣ`
gives the **tame character** `G_0 → 𝓀[L]ˣ`, which kills `G_1`; the induced map on `G_0 / G_1` is
injective, so the tame quotient is cyclic of order dividing `q - 1`, where `q` is the cardinality
of the residue field. At positive depth, `TauCeti.IsLocalRing.isPGroup_ramificationGroup` shows
that `G_1` is a `p`-group for the residue characteristic `p` when the action is faithful and `G_0`
is finite.

## Main definitions

* `TauCeti.uniformizerRatio`: the ratio `σ ϖ / ϖ`, as an element of `U(L,i)`.
* `TauCeti.ramificationGroupToUnitFiltrationGraded`: the homomorphism
  `G_i → U(L,i) / U(L,i+1)`, and
  `TauCeti.ramificationGroupGradedToUnitFiltrationGraded`: the induced `θ_i` on `G_i / G_{i+1}`.
* `TauCeti.ramificationGroupGradedToResidueField`: the positive-depth quotient embedding
  composed with the additive residue-field coordinate determined by a uniformizer.
* `TauCeti.tameCharacter`: the depth-zero homomorphism `G_0 → 𝓀[L]ˣ`, and
  `TauCeti.tameCharacterGraded`: the map it induces on `G_0 / G_1`.
* `TauCeti.ramificationGroupOneSylow`: the wild inertia group `G_1`, viewed inside `G_0`, as its
  unique normal Sylow `p`-subgroup.

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
* `TauCeti.eq_ramificationGroupOneSylow`: `G_1` is the unique Sylow `p`-subgroup of `G_0`.
* `TauCeti.natCard_ramificationGroup_one`: the order of `G_1` is the `p`-part of the order of `G_0`.
* `TauCeti.ker_tameCharacter`: the kernel of the tame character is `G_1`.
* `TauCeti.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: `G_1` is
  trivial exactly when `p` does not divide `Nat.card G_0`, that is when `G_0` is finite of order
  prime to `p` (the tame case), since `Nat.card G_0 = 0` when `G_0` is infinite.

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

/-! ### Identification with the DVR principal-unit filtration and separable base ring -/

omit [IsNonarchimedeanLocalField L] in
private def unitFiltrationEquivPrincipalUnitGroup (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (i : ℕ) :
    unitFiltration L i ≃* (maximalIdeal 𝒪[L] ^ i).principalUnitGroup where
  toFun x := ⟨unitFiltrationToIntegerUnits i x, by
    rw [Ideal.mem_principalUnitGroup]
    obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.mp x.prop
    have heq : unitFiltrationToIntegerUnits i x = u :=
      Units.ext (Subtype.ext (by rw [coe_unitFiltrationToIntegerUnits, ← hux]))
    rwa [heq]⟩
  invFun u := ⟨Units.map (Subring.subtype 𝒪[L]).toMonoidHom (u : 𝒪[L]ˣ),
    mem_unitFiltration_iff_exists.mpr ⟨u, Ideal.mem_principalUnitGroup.mp u.prop, rfl⟩⟩
  left_inv x := Subtype.ext (unitsMap_subtype_unitFiltrationToIntegerUnits i x)
  right_inv u := Subtype.ext (Units.ext (Subtype.ext (coe_unitFiltrationToIntegerUnits i _)))
  map_mul' x y := Subtype.ext (map_mul (unitFiltrationToIntegerUnits i) x y)

@[simp]
private theorem coe_unitFiltrationEquivPrincipalUnitGroup (i : ℕ) (x : unitFiltration L i) :
    (((unitFiltrationEquivPrincipalUnitGroup L i x : 𝒪[L]ˣ) : 𝒪[L]) : L) = ((x : Lˣ) : L) :=
  coe_unitFiltrationToIntegerUnits i x

@[simp]
private theorem coe_unitFiltrationEquivPrincipalUnitGroup_symm (i : ℕ)
    (u : (maximalIdeal 𝒪[L] ^ i).principalUnitGroup) :
    (((unitFiltrationEquivPrincipalUnitGroup L i).symm u : Lˣ) : L) = ((u : 𝒪[L]ˣ) : L) := by
  simp [unitFiltrationEquivPrincipalUnitGroup]

private def unitFiltrationGradedEquivPrincipalUnitGraded (L : Type*) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] (i : ℕ) :
    UnitFiltrationGraded L i ≃* PrincipalUnitGraded 𝒪[L] i :=
  QuotientGroup.congr _ _ (unitFiltrationEquivPrincipalUnitGroup L i) <| by
    ext u
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    refine ⟨?_, fun hu ↦ ?_⟩
    · rintro ⟨x, hx, rfl⟩
      rw [Ideal.mem_principalUnitGroup]
      obtain ⟨v, hv, hvx⟩ :=
        mem_unitFiltration_iff_exists.mp (hx : (x : Lˣ) ∈ unitFiltration L (i + 1))
      have hv_eq : ((unitFiltrationEquivPrincipalUnitGroup L i x : 𝒪[L]ˣ) : 𝒪[L]) = (v : 𝒪[L]) :=
        Subtype.ext (by rw [coe_unitFiltrationEquivPrincipalUnitGroup, ← hvx])
      change ((unitFiltrationEquivPrincipalUnitGroup L i x : 𝒪[L]ˣ) : 𝒪[L]) - 1 ∈ 𝓂[L] ^ (i + 1)
      rwa [hv_eq]
    · obtain ⟨x, hxu⟩ := (unitFiltrationEquivPrincipalUnitGroup L i).surjective u
      refine ⟨x, ?_, hxu⟩
      rw [mem_unitFiltration_iff_exists]
      refine ⟨(unitFiltrationEquivPrincipalUnitGroup L i x : 𝒪[L]ˣ), ?_,
        coe_unitFiltrationEquivPrincipalUnitGroup i x⟩
      rwa [hxu, ← Ideal.mem_principalUnitGroup]

@[simp]
private theorem unitFiltrationGradedEquivPrincipalUnitGraded_symm_mk (i : ℕ)
    (u : (maximalIdeal 𝒪[L] ^ i).principalUnitGroup) :
    (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm (QuotientGroup.mk u) =
      QuotientGroup.mk ((unitFiltrationEquivPrincipalUnitGroup L i).symm u) := by
  rw [MulEquiv.symm_apply_eq, unitFiltrationGradedEquivPrincipalUnitGraded,
    QuotientGroup.congr_mk, MulEquiv.apply_symm_apply]

private theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_symm (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) (x : Additive (PrincipalUnitGraded 𝒪[L] (n + 1))) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := L) n π hπ
        (Additive.ofMul
          ((unitFiltrationGradedEquivPrincipalUnitGraded L (n + 1)).symm x.toMul)) =
      IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField n hπ x := by
  obtain ⟨q, rfl⟩ := Additive.ofMul.surjective x
  induction q using QuotientGroup.induction_on with | H u =>
  rw [toMul_ofMul, unitFiltrationGradedEquivPrincipalUnitGraded_symm_mk]
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).injective
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk,
    IsDiscreteValuationRing.principalUnitGradedSuccEquivResidueField_ofMul_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  apply Subtype.ext
  rw [coe_coe_unitFiltrationDifference, coe_unitFiltrationEquivPrincipalUnitGroup_symm]
  rfl

private def basePrimeIdeal (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Ideal ℤ :=
  (maximalIdeal 𝒪[L]).under ℤ

private local instance instBasePrimeIdealPrime (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : (basePrimeIdeal L).IsPrime :=
  (maximalIdeal.isMaximal 𝒪[L]).isPrime.comap _

private theorem isUnit_algebraMap_of_mem_basePrimeIdeal_primeCompl (L : Type*) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (s : (basePrimeIdeal L).primeCompl) : IsUnit (algebraMap ℤ 𝒪[L] s) :=
  IsLocalRing.notMem_maximalIdeal.mp s.prop

private local instance instBaseRingAlgebra (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    Algebra (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] :=
  (IsLocalization.lift (M := (basePrimeIdeal L).primeCompl)
    (S := Localization.AtPrime (basePrimeIdeal L))
    (isUnit_algebraMap_of_mem_basePrimeIdeal_primeCompl L)).toAlgebra

private local instance instBaseRingIsLocalHom (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    IsLocalHom (algebraMap (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L]) := ⟨fun r hr ↦ by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (basePrimeIdeal L).primeCompl r
  dsimp only at hr ⊢
  have hspec :
      algebraMap (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L]
          (IsLocalization.mk' (Localization.AtPrime (basePrimeIdeal L)) z s) *
        algebraMap ℤ 𝒪[L] (s : ℤ) = algebraMap ℤ 𝒪[L] z := by
    rw [mul_comm]
    exact ((IsLocalization.lift_mk'_spec (isUnit_algebraMap_of_mem_basePrimeIdeal_primeCompl L)
      z _ s).mp rfl).symm
  have hz : z ∈ (basePrimeIdeal L).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    intro hzp
    have hunit : IsUnit (algebraMap ℤ 𝒪[L] z) := by
      rw [← hspec]
      exact hr.mul (isUnit_algebraMap_of_mem_basePrimeIdeal_primeCompl L s)
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) hzp
  have hmul :
      IsLocalization.mk' (Localization.AtPrime (basePrimeIdeal L)) z s *
        algebraMap ℤ (Localization.AtPrime (basePrimeIdeal L)) (s : ℤ) =
        algebraMap ℤ (Localization.AtPrime (basePrimeIdeal L)) z :=
    IsLocalization.mk'_spec (Localization.AtPrime (basePrimeIdeal L)) z s
  exact isUnit_of_mul_isUnit_left
    (hmul.symm ▸ IsLocalization.map_units (Localization.AtPrime (basePrimeIdeal L)) ⟨z, hz⟩)⟩

private local instance instBaseRingSMulCommClass (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (G : Type*) [Group G]
    [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]] :
    SMulCommClass G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] := ⟨fun σ r x ↦ by
  have hfix : σ • algebraMap (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] r =
      algebraMap (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] r := by
    change ((MulSemiringAction.toRingHom G 𝒪[L] σ).comp
      (algebraMap (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L])) r =
      algebraMap (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] r
    congr 1
    exact IsLocalization.ringHom_ext (basePrimeIdeal L).primeCompl (Subsingleton.elim _ _)
  rw [Algebra.smul_def, smul_mul', hfix, ← Algebra.smul_def]⟩

private local instance instBaseRingFiniteQuotient (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Finite (ℤ ⧸ basePrimeIdeal L) := by
  let f : ℤ →+* 𝓀[L] := (residue 𝒪[L]).comp (algebraMap ℤ 𝒪[L])
  have hker : RingHom.ker f = basePrimeIdeal L := by
    ext z
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    rfl
  have hinj : Function.Injective
      ((RingHom.kerLift f).comp (Ideal.quotEquivOfEq hker.symm).toRingHom) :=
    (RingHom.kerLift_injective f).comp (Ideal.quotEquivOfEq hker.symm).injective
  exact Finite.of_injective _ hinj

private local instance instBaseRingIsSeparableResidueField (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    Algebra.IsSeparable (ResidueField (Localization.AtPrime (basePrimeIdeal L))) 𝓀[L] := by
  have : Finite (ResidueField (Localization.AtPrime (basePrimeIdeal L))) :=
    (inferInstance : Finite (basePrimeIdeal L).ResidueField)
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

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
  (unitFiltrationEquivPrincipalUnitGroup L i).symm
    (IsDiscreteValuationRing.uniformizerRatio i hϖ σ)

@[simp]
theorem coe_uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ((uniformizerRatio i hϖ σ : Lˣ) : L) = (σ : G) • (ϖ : L) / (ϖ : L) := by
  have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  rw [uniformizerRatio, coe_unitFiltrationEquivPrincipalUnitGroup_symm]
  have hmul := congrArg (fun z : 𝒪[L] ↦ (z : L))
    (IsDiscreteValuationRing.mul_coe_uniformizerRatio i hϖ σ)
  rw [Subring.coe_mul, coe_smul_integer] at hmul
  exact (eq_div_iff_mul_eq hϖne).mpr (by rw [mul_comm, hmul])

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
  (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGraded G i hϖ)

@[simp]
theorem ramificationGroupToUnitFiltrationGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGraded_apply,
    unitFiltrationGradedEquivPrincipalUnitGraded_symm_mk]
  rfl

/-- The quotient homomorphism does not depend on the choice of uniformizer: two uniformizers
differ by a unit of `𝒪[L]`, and `σ` moves that unit inside `U(L,i+1)`. -/
theorem ramificationGroupToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupToUnitFiltrationGraded (G := G) i hϖ' := by
  rw [ramificationGroupToUnitFiltrationGraded, ramificationGroupToUnitFiltrationGraded,
    IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGraded_eq_of_irreducible G i hϖ hϖ']

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
the inertia group `G_0` lies in `G_n` exactly when `σ ϖ ≡ ϖ` modulo `𝓂[L] ^ (n + 1)`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G 𝒪[L] 0) {n : ℕ} :
    σ ∈ ramificationGroup G 𝒪[L] (n : ℤ) ↔ σ • ϖ - ϖ ∈ 𝓂[L] ^ (n + 1) :=
  IsDiscreteValuationRing.mem_ramificationGroup_natCast_iff_smul_sub_mem
    (Localization.AtPrime (basePrimeIdeal L)) hϖ hσ

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
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.ker_comp_of_injective _
    (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.toMonoidHom
    (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.injective,
    ← sub_mem_maximalIdeal_pow_iff hϖ]
  exact IsDiscreteValuationRing.mem_ker_ramificationGroupToPrincipalUnitGraded_iff i hϖ

/-- The next step `G_{i+1}` of the ramification filtration is killed by the quotient
homomorphism. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (hϖ : Irreducible ϖ) :
    (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded i hϖ).ker := by
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.ker_comp_of_injective _
    (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.toMonoidHom
    (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.injective]
  exact IsDiscreteValuationRing.ramificationGroup_succ_subgroupOf_le_ker G i hϖ

/-- **The kernel of the quotient homomorphism is exactly `G_{i+1}`**, which is what makes the
induced `θ_i` on `G_i / G_{i+1}` an embedding: membership of an element of `G_0` in `G_{i+1}` is
decided at `ϖ` (`TauCeti.mem_ramificationGroup_natCast_iff_smul_sub_mem`). -/
theorem ker_ramificationGroupToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    (ramificationGroupToUnitFiltrationGraded i hϖ).ker =
      (ramificationGroup G 𝒪[L] ((i : ℤ) + 1)).subgroupOf (ramificationGroup G 𝒪[L] (i : ℤ)) := by
  rw [ramificationGroupToUnitFiltrationGraded, MonoidHom.ker_comp_of_injective _
    (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.toMonoidHom
    (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.injective]
  exact IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGraded
    G (Localization.AtPrime (basePrimeIdeal L)) i hϖ

/-! ### The embedding of the graded pieces -/

variable (i) in
/-- The **quotient map** `θ_i : G_i / G_{i+1} →* U(L,i) / U(L,i+1)`, induced by
`σ ↦ σ ϖ / ϖ` for a uniformizer `ϖ`. It is an embedding
(`TauCeti.ramificationGroupGradedToUnitFiltrationGraded_injective`). -/
def ramificationGroupGradedToUnitFiltrationGraded (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G 𝒪[L] (i : ℤ) →* UnitFiltrationGraded L i :=
  (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.toMonoidHom.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded G i hϖ)

@[simp]
theorem ramificationGroupGradedToUnitFiltrationGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupGradedToUnitFiltrationGraded, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_mk,
    unitFiltrationGradedEquivPrincipalUnitGraded_symm_mk]
  rfl

/-- **The quotient embeddings are injective.** -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ) :=
  (unitFiltrationGradedEquivPrincipalUnitGraded L i).symm.injective.comp
    (IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_injective
      G (Localization.AtPrime (basePrimeIdeal L)) i hϖ)

/-- The descended quotient map does not depend on the choice of uniformizer. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible {ϖ' : 𝒪[L]}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ' := by
  rw [ramificationGroupGradedToUnitFiltrationGraded, ramificationGroupGradedToUnitFiltrationGraded,
    IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_eq_of_irreducible
      G i hϖ hϖ']

/-! ### Positive-depth residue-field coordinates -/

variable (G L) in
/-- The positive-depth embedding of `G_{n+1}/G_{n+2}` into the additive residue field, in the
coordinate determined by a uniformizer `π`. -/
noncomputable def ramificationGroupGradedToResidueField (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Additive (RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) →+
      IsLocalRing.ResidueField 𝒪[L] :=
  IsDiscreteValuationRing.ramificationGroupGradedToResidueField G n hπ

@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π)
    (τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (QuotientGroup.mk τ)) =
      unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul (QuotientGroup.mk (uniformizerRatio (n + 1) hπ τ))) := by
  rw [ramificationGroupGradedToResidueField,
    IsDiscreteValuationRing.ramificationGroupGradedToResidueField_ofMul_mk,
    IsDiscreteValuationRing.ramificationGroupToResidueField_ofMul,
    ← unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_symm n π hπ,
    toMul_ofMul, unitFiltrationGradedEquivPrincipalUnitGraded_symm_mk]
  rfl

/-- The positive-depth ramification quotient embeds in the additive residue field. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ) :=
  IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective
    G (Localization.AtPrime (basePrimeIdeal L)) n hπ

/-- Compute a positive-depth residue coordinate from the displacement of a representative. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq
    (n : ℕ) (π : 𝒪[L]) (hπ : Irreducible π)
    (τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) (y : 𝒪[L])
    (hmove : (τ : G) • π - π = y * π ^ (n + 2)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (QuotientGroup.mk τ)) = residue 𝒪[L] y :=
  IsDiscreteValuationRing.ramificationGroupGradedToResidueField_of_smul_sub_eq n hπ τ y hmove

/-- Change the uniformizer used for a positive-depth ramification coordinate. -/
theorem ramificationGroupGradedToResidueField_change
    (n : ℕ) (π π' : 𝒪[L]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ (Additive.ofMul τ) =
      residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) ^ (n + 1) *
        ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
          (Additive.ofMul τ) :=
  IsDiscreteValuationRing.ramificationGroupGradedToResidueField_change n hπ hπ' τ

/-! ### The tame character -/

/-- The **tame character** `θ_0 : G_0 →* 𝓀[L]ˣ`: the depth-zero quotient homomorphism composed
with the identification of `U(L,0) / U(L,1)` with the multiplicative group of the residue
field. It carries `σ` to the residue of `σ ϖ / ϖ`. It kills `G_1`, hence factors through
`TauCeti.tameCharacterGraded`. -/
def tameCharacter (hϖ : Irreducible ϖ) : ramificationGroup G 𝒪[L] (0 : ℤ) →* 𝓀[L]ˣ :=
  IsDiscreteValuationRing.tameCharacter G hϖ

theorem coe_tameCharacter_of_val_eq_smul_div (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (0 : ℤ)) {y : 𝒪[L]}
    (hy : (y : L) = (σ : G) • (ϖ : L) / (ϖ : L)) :
    (tameCharacter hϖ σ : 𝓀[L]) = IsLocalRing.residue 𝒪[L] y := by
  have hϖne : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hmul : ϖ * y = (σ : G) • ϖ := Subtype.ext (by
    rw [Subring.coe_mul, coe_smul_integer, hy, mul_div_cancel₀ _ hϖne])
  exact IsDiscreteValuationRing.coe_tameCharacter_of_mul_eq hϖ hmul

/-- The tame character does not depend on the choice of uniformizer. -/
theorem tameCharacter_eq_of_irreducible {ϖ' : 𝒪[L]} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacter (G := G) hϖ = tameCharacter (G := G) hϖ' :=
  IsDiscreteValuationRing.tameCharacter_eq_of_irreducible G hϖ hϖ'

/-- The tame character read on the quotient `G_0 / G_1` it factors through. It is injective
(`TauCeti.tameCharacterGraded_injective`). -/
def tameCharacterGraded (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G 𝒪[L] (0 : ℤ) →* 𝓀[L]ˣ :=
  IsDiscreteValuationRing.tameCharacterGraded G hϖ

-- The `(0 : ℤ)` index of the depth-zero declarations is `simp`-normal, unlike the cast `(i : ℤ)`
-- of the general ones, so this application lemma can carry `@[simp]`.
@[simp]
theorem tameCharacterGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G 𝒪[L] (0 : ℤ)) :
    tameCharacterGraded hϖ (QuotientGroup.mk σ) = tameCharacter hϖ σ :=
  IsDiscreteValuationRing.tameCharacterGraded_mk hϖ σ

/-- The graded tame character does not depend on the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {ϖ' : 𝒪[L]} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacterGraded (G := G) hϖ = tameCharacterGraded (G := G) hϖ' :=
  IsDiscreteValuationRing.tameCharacterGraded_eq_of_irreducible G hϖ hϖ'

/-- **The tame character is injective on `G_0 / G_1`.** -/
theorem tameCharacterGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacterGraded (G := G) hϖ) :=
  IsDiscreteValuationRing.tameCharacterGraded_injective
    G (Localization.AtPrime (basePrimeIdeal L)) hϖ

/-- **The kernel of the tame character is the wild inertia group `G_1`**, viewed inside `G_0`. -/
@[simp]
theorem ker_tameCharacter (hϖ : Irreducible ϖ) :
    (tameCharacter (G := G) hϖ).ker =
      (ramificationGroup G 𝒪[L] 1).subgroupOf (ramificationGroup G 𝒪[L] 0) := by
  ext σ
  rw [MonoidHom.mem_ker, ← tameCharacterGraded_mk,
    map_eq_one_iff _ (tameCharacterGraded_injective hϖ), QuotientGroup.eq_one_iff, zero_add]

variable (G L) in
/-- **The tame quotient is cyclic**: `G_0 / G_1` embeds into the multiplicative group of the
residue field, which is cyclic because the residue field is finite. -/
theorem isCyclic_ramificationGroupGraded_zero :
    IsCyclic (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) := by
  obtain ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have : Finite (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) :=
    Finite.of_injective _ (tameCharacterGraded_injective hϖ)
  exact IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero
    G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L]

variable (G L) in
/-- The order of the tame quotient `G_0 / G_1` divides `q - 1`, for `q` the cardinality of the
residue field. -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) ∣ Nat.card 𝓀[L] - 1 := by
  obtain ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Nat.card_units]
  exact Subgroup.card_dvd_of_injective _ (tameCharacterGraded_injective hϖ)

/-! ### Wild inertia as the Sylow subgroup of inertia -/

variable (G) in
/-- The index of `G_1` in `G_0` is prime to the residue characteristic `p`. This is the
order-theoretic consequence of the tame-character embedding `G_0/G_1 → 𝓀[L]ˣ`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [CharP 𝓀[L] p] :
    ¬p ∣ ((ramificationGroup G 𝒪[L] 1).subgroupOf
      (ramificationGroup G 𝒪[L] 0)).index := by
  obtain ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have : Finite (RamificationGroupGraded G 𝒪[L] (0 : ℤ)) :=
    Finite.of_injective _ (tameCharacterGraded_injective hϖ)
  exact IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one
    G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] p

variable (G) in
/-- **Wild inertia is the Sylow `p`-subgroup of inertia.** For the residue characteristic `p`,
the first ramification group `G_1`, viewed as a subgroup of `G_0`, is a Sylow `p`-subgroup.

The two inputs are the positive-depth `p`-group theorem and the tame-character embedding, which
shows that the index `#(G_0/G_1)` divides `#𝓀[L] - 1` and is therefore prime to `p`. -/
noncomputable def ramificationGroupOneSylow (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    Sylow p (ramificationGroup G 𝒪[L] 0) :=
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  IsDiscreteValuationRing.ramificationGroupOneSylow
    G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] p

variable (G) in
/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    (ramificationGroupOneSylow (G := G) (L := L) p :
      Subgroup (ramificationGroup G 𝒪[L] 0)) =
      (ramificationGroup G 𝒪[L] 1).subgroupOf (ramificationGroup G 𝒪[L] 0) :=
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  IsDiscreteValuationRing.ramificationGroupOneSylow_coe
    G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] p

variable (G) in
/-- The wild inertia Sylow subgroup is normal in inertia. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    (ramificationGroupOneSylow (G := G) (L := L) p :
      Subgroup (ramificationGroup G 𝒪[L] 0)).Normal :=
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  IsDiscreteValuationRing.ramificationGroupOneSylow_normal
    G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] p

variable (G) in
/-- The wild inertia Sylow subgroup is the unique Sylow `p`-subgroup of inertia. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)]
    (Q : Sylow p (ramificationGroup G 𝒪[L] 0)) :
    Q = ramificationGroupOneSylow (G := G) (L := L) p :=
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[L] p⟩
  IsDiscreteValuationRing.eq_ramificationGroupOneSylow
    (Localization.AtPrime (basePrimeIdeal L)) Q

variable (G) in
/-- The order of wild inertia is the residue-characteristic part of the order of inertia:
`#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [CharP 𝓀[L] p]
    [FaithfulSMul G 𝒪[L]] [Finite (ramificationGroup G 𝒪[L] 0)] :
    Nat.card (ramificationGroup G 𝒪[L] 1) =
      p ^ (Nat.card (ramificationGroup G 𝒪[L] 0)).factorization p :=
  IsDiscreteValuationRing.natCard_ramificationGroup_one
    G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] p

variable (G) in
/-- **Wild inertia is trivial exactly in the tame case.** For the residue characteristic `p`, the
first ramification group `G_1` is trivial if and only if `p` does not divide `Nat.card G_0`, that
is, if and only if the inertia group `G_0` is finite of order prime to `p`: when `G_0` is infinite,
`Nat.card G_0 = 0`, and `G_1` is nontrivial because `G_0 / G_1` embeds in the finite group
`𝓀[L]ˣ`. When `G_0` is finite, `G_1` is its Sylow `p`-subgroup. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [CharP 𝓀[L] p] [FaithfulSMul G 𝒪[L]] :
    ramificationGroup G 𝒪[L] 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G 𝒪[L] 0) := by
  by_cases hfin : Finite (ramificationGroup G 𝒪[L] 0)
  · exact
      IsDiscreteValuationRing.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero
        G (Localization.AtPrime (basePrimeIdeal L)) 𝒪[L] p
  · -- if `G_0` is infinite, `G_1 ≠ ⊥`, since `G_0 / G_1` embeds in the finite group `𝓀[L]ˣ`
    have hinf := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    simp only [dvd_zero, not_true_eq_false, iff_false]
    intro h
    obtain ⟨_, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
    have hker := ker_tameCharacter (G := G) hϖ
    rw [h, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff] at hker
    exact hfin (Finite.of_injective _ hker)

end TauCeti
