/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.LocalRing.PrincipalUnitGroup
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient

/-!
# Positive graded pieces of the unit filtration

For a nonarchimedean local field `K`, multiplication becomes addition on each positive
successive quotient of the unit filtration.  More precisely, subtracting one gives a canonical
isomorphism

`U(K,n) / U(K,n+1) ≃ 𝓂[K]^n / 𝓂[K]^(n+1)`

for `n > 0`.  Since the maximal ideal of the discrete valuation ring `𝒪[K]` is principal,
each ideal quotient is a one-dimensional copy of the residue field.  Combining these facts
identifies every positive graded piece with the additive group of `𝓀[K]`, and shows that it
has `#𝓀[K]` elements.

## Main results

* `TauCeti.principalUnitGroupEquivUnitFiltration` and
  `TauCeti.principalUnitGroupGradedEquivUnitFiltrationGraded`: canonical identifications with
  the local-ring principal unit filtration `(𝓂[K] ^ i).principalUnitGroup` and its graded
  quotients `TauCeti.IsLocalRing.PrincipalUnitGroupGraded 𝒪[K] i`.
* `TauCeti.unitFiltrationGradedSuccEquivMaximalIdealGraded`: subtracting one identifies a
  positive unit-filtration quotient with the corresponding quotient of powers of the maximal
  ideal.
* `TauCeti.unitFiltrationGradedSuccEquivResidueField`: every positive graded piece is additively
  isomorphic to the residue field.
* `TauCeti.natCard_unitFiltrationGraded_succ` and
  `TauCeti.relIndex_unitFiltration_succ_succ`: the positive graded pieces and relative indices
  have cardinality `#𝓀[K]`.
* `TauCeti.unitFiltration_isFiniteRelIndex_zero`: every step of the unit filtration has finite
  index in `U(K,0) = 𝒪[K]ˣ`; precisely, `TauCeti.relIndex_unitFiltration_succ_zero`:
  `[U(K,0) : U(K,n+1)] = (#𝓀[K] - 1) * #𝓀[K] ^ n`, so that
  `TauCeti.pow_natCard_sub_one_mul_pow_mem_unitFiltration_succ`: every unit `x` has
  `x ^ ((#𝓀[K] - 1) * #𝓀[K] ^ n) ∈ U(K,n+1)`.
* `TauCeti.relIndex_unitFiltration_add_succ_succ` and
  `TauCeti.natCard_unitFiltration_succ_quotient_add_succ`: more generally,
  `U(K,m+1) / U(K,m+n+1)` has `#𝓀[K] ^ n` elements.
* `TauCeti.unitFiltration_le_unitFiltration_iff`: the steps of the unit filtration are distinct,
  except that `U(K,1) = U(K,0)` when `#𝓀[K] = 2`
  (`TauCeti.unitFiltration_one_eq_unitFiltration_zero_iff`).

The final identification reuses Mathlib's `Ideal.quotEquivPowQuotPowSucc`, the linear equivalence
between a quotient by a nonzero principal ideal and each successive quotient of its powers.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The `i`-th step of the unit filtration inside `Kˣ` is the image of
`(𝓂[K] ^ i).principalUnitGroup` from the local ring `𝒪[K]`. -/
theorem unitFiltration_eq_map_principalUnitGroup (i : ℕ) :
    unitFiltration K i =
      (𝓂[K] ^ i).principalUnitGroup.map (Units.map (Subring.subtype 𝒪[K]).toMonoidHom) := by
  ext x
  simp only [mem_unitFiltration_iff_exists, Subgroup.mem_map, Ideal.mem_principalUnitGroup,
    Units.ext_iff, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    Subring.coe_subtype]

variable (K) in
/-- Identifying the principal unit group `(𝓂[K] ^ i).principalUnitGroup` of `𝒪[K]` with
`unitFiltration K i` inside `Kˣ`. -/
def principalUnitGroupEquivUnitFiltration (i : ℕ) :
    (𝓂[K] ^ i).principalUnitGroup ≃* unitFiltration K i :=
  (Subgroup.equivMapOfInjective ((𝓂[K] ^ i).principalUnitGroup)
      (Units.map (Subring.subtype 𝒪[K]).toMonoidHom)
      (Units.map_injective Subtype.coe_injective)).trans
    (MulEquiv.subgroupCongr (unitFiltration_eq_map_principalUnitGroup i).symm)

/-- Identifying `(𝓂[K] ^ i).principalUnitGroup` with `unitFiltration K i` preserves the
underlying unit in `Kˣ`. -/
@[simp]
theorem coe_principalUnitGroupEquivUnitFiltration (i : ℕ) (u : (𝓂[K] ^ i).principalUnitGroup) :
    (principalUnitGroupEquivUnitFiltration K i u : Kˣ) =
      Units.map (Subring.subtype 𝒪[K]).toMonoidHom (u : 𝒪[K]ˣ) :=
  (rfl)

/-- Transporting `x ∈ unitFiltration K i` back to `(𝓂[K] ^ i).principalUnitGroup` preserves its
underlying value in `K`. -/
@[simp]
theorem coe_coe_principalUnitGroupEquivUnitFiltration_symm (i : ℕ) (x : unitFiltration K i) :
    ((((principalUnitGroupEquivUnitFiltration K i).symm x : 𝒪[K]ˣ) : 𝒪[K]) : K) =
      ((x : Kˣ) : K) := by
  have h := congrArg (fun z : unitFiltration K i ↦ ((z : Kˣ) : K))
    ((principalUnitGroupEquivUnitFiltration K i).apply_symm_apply x)
  simpa only [coe_principalUnitGroupEquivUnitFiltration, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Subring.coe_subtype] using h

variable (K) in
/-- Identifying the local-ring graded piece `IsLocalRing.PrincipalUnitGroupGraded 𝒪[K] i` with
`UnitFiltrationGraded K i`. -/
def principalUnitGroupGradedEquivUnitFiltrationGraded (i : ℕ) :
    IsLocalRing.PrincipalUnitGroupGraded 𝒪[K] i ≃* UnitFiltrationGraded K i :=
  QuotientGroup.congr
    ((𝓂[K] ^ (i + 1)).principalUnitGroup.subgroupOf (𝓂[K] ^ i).principalUnitGroup)
    ((unitFiltration K (i + 1)).subgroupOf (unitFiltration K i))
    (principalUnitGroupEquivUnitFiltration K i) (by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Ideal.mem_principalUnitGroup]
      refine ⟨fun ⟨u, hu, hux⟩ ↦ mem_unitFiltration_iff_exists.mpr
        ⟨(u : 𝒪[K]ˣ), hu, congrArg (fun z : Kˣ ↦ (z : K))
          (congrArg (fun z : unitFiltration K i ↦ (z : Kˣ)) hux)⟩, fun hx ↦ ?_⟩
      refine ⟨(principalUnitGroupEquivUnitFiltration K i).symm x, ?_,
        (principalUnitGroupEquivUnitFiltration K i).apply_symm_apply x⟩
      rw [mem_unitFiltration_iff_exists] at hx
      obtain ⟨w, hw, hwx⟩ := hx
      have hweq : ((principalUnitGroupEquivUnitFiltration K i).symm x : 𝒪[K]ˣ) = w := by
        apply Units.ext
        apply Subtype.ext
        simpa using (coe_coe_principalUnitGroupEquivUnitFiltration_symm i x).trans hwx.symm
      rwa [hweq])

/-- Evaluating `principalUnitGroupGradedEquivUnitFiltrationGraded` on the class of `u`. -/
@[simp]
theorem principalUnitGroupGradedEquivUnitFiltrationGraded_mk (i : ℕ)
    (u : (𝓂[K] ^ i).principalUnitGroup) :
    principalUnitGroupGradedEquivUnitFiltrationGraded K i (QuotientGroup.mk u) =
      QuotientGroup.mk (principalUnitGroupEquivUnitFiltration K i u) :=
  QuotientGroup.congr_mk _ _ _ _ u

/-- Evaluating the inverse of `principalUnitGroupGradedEquivUnitFiltrationGraded` on the class of
`x`. -/
@[simp]
theorem principalUnitGroupGradedEquivUnitFiltrationGraded_symm_mk (i : ℕ)
    (x : unitFiltration K i) :
    (principalUnitGroupGradedEquivUnitFiltrationGraded K i).symm (QuotientGroup.mk x) =
      QuotientGroup.mk ((principalUnitGroupEquivUnitFiltration K i).symm x) := by
  refine (principalUnitGroupGradedEquivUnitFiltrationGraded K i).injective ?_
  simp

/-- The `n`th graded piece of the maximal-ideal filtration of `𝒪[K]`, presented as
`𝓂[K]^n / 𝓂[K]^(n+1)`.  The denominator is written as `𝓂[K] • ⊤` on the subtype
`𝓂[K]^n`; `Submodule.mem_smul_top_iff` identifies it with `𝓂[K]^(n+1)`. -/
abbrev MaximalIdealGraded (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :=
  (𝓂[K] ^ n : Ideal 𝒪[K]) ⧸
    (𝓂[K] • ⊤ : Submodule 𝒪[K] (𝓂[K] ^ n : Ideal 𝒪[K]))

/-- The difference `u - 1` attached to `u ∈ U(K,n+1)`, as an element of `𝓂[K]^(n+1)`. -/
noncomputable def unitFiltrationDifference (n : ℕ)
    (x : unitFiltration K (n + 1)) : (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
  ⟨unitFiltrationToIntegerUnits (n + 1) x - 1, by
    -- `mem_unitFiltration_succ_congr` spells the inclusion `𝒪[K]ˣ →* Kˣ` through
    -- `RingHom.toMonoidHom`, which is not the simp-normal form of the coercion.
    apply (mem_unitFiltration_succ_congr n (unitFiltrationToIntegerUnits (n + 1) x)).mp
    rw [RingHom.toMonoidHom_eq_coe, unitsMap_subtype_unitFiltrationToIntegerUnits]
    exact x.prop⟩

-- Not a `simp` lemma: the ambient-field form `coe_coe_unitFiltrationDifference` below is the
-- `simp`-normal one, and both firing would take its left-hand side out of normal form.
private theorem coe_unitFiltrationDifference (n : ℕ) (x : unitFiltration K (n + 1)) :
    (unitFiltrationDifference n x : 𝒪[K]) =
      (unitFiltrationToIntegerUnits (n + 1) x : 𝒪[K]) - 1 :=
  rfl

/-- In the ambient field, `unitFiltrationDifference n u` is `u - 1`. -/
@[simp]
theorem coe_coe_unitFiltrationDifference (n : ℕ) (x : unitFiltration K (n + 1)) :
    (((unitFiltrationDifference n x : 𝒪[K]) : K)) = ((x : Kˣ) : K) - 1 := by
  rw [coe_unitFiltrationDifference]
  -- Expose the two subtype coercions before applying the ambient-field comparison lemma.
  change (((unitFiltrationToIntegerUnits (n + 1) x : 𝒪[K]) : K)) - 1 =
    ((x : Kˣ) : K) - 1
  rw [coe_unitFiltrationToIntegerUnits]

/-- Subtracting one identifies the positive unit-filtration quotient
`U(K,n+1) / U(K,n+2)` with `𝓂[K]^(n+1) / 𝓂[K]^(n+2)`, transported from
`TauCeti.IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded`. -/
noncomputable def unitFiltrationGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    UnitFiltrationGraded K (n + 1) ≃* Multiplicative (MaximalIdealGraded K (n + 1)) :=
  (principalUnitGroupGradedEquivUnitFiltrationGraded K (n + 1)).symm.trans
    (IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded 𝒪[K] n)

/-- On a class represented by `u ∈ U(K,n+1)`, the positive-depth graded equivalence is the
class of `u - 1` modulo `𝓂[K]^(n+2)`. -/
@[simp]
theorem unitFiltrationGradedSuccEquivMaximalIdealGraded_mk
    (n : ℕ) (x : unitFiltration K (n + 1)) :
    unitFiltrationGradedSuccEquivMaximalIdealGraded (K := K) n (QuotientGroup.mk x) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n x)) := by
  rw [unitFiltrationGradedSuccEquivMaximalIdealGraded, MulEquiv.trans_apply,
    principalUnitGroupGradedEquivUnitFiltrationGraded_symm_mk,
    IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded_mk]
  refine congrArg (fun z ↦ Multiplicative.ofAdd (Submodule.Quotient.mk z)) (Subtype.ext ?_)
  apply Subtype.ext
  change ((((principalUnitGroupEquivUnitFiltration K (n + 1)).symm x : 𝒪[K]ˣ) : 𝒪[K]) : K) - 1 =
    (((unitFiltrationDifference n x : 𝒪[K]) : K))
  rw [coe_coe_principalUnitGroupEquivUnitFiltration_symm, coe_coe_unitFiltrationDifference]

/-- Every positive graded piece `U(K,n+1) / U(K,n+2)`, read additively, is isomorphic to the
additive group of the residue field. -/
noncomputable def unitFiltrationGradedSuccEquivResidueField (n : ℕ) :
    Additive (UnitFiltrationGraded K (n + 1)) ≃+ 𝓀[K] :=
  (unitFiltrationGradedSuccEquivMaximalIdealGraded (K := K) n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative (MaximalIdealGraded K (n + 1))).trans <|
      (Ideal.quotEquivPowQuotPowSucc
        (I := 𝓂[K]) (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field 𝒪[K]) (n + 1)).toAddEquiv.symm

/-- On a class represented by `u ∈ U(K,n+1)`, the positive-depth residue-field equivalence is
the residue class attached to `u - 1` by Mathlib's principal-power-quotient equivalence. -/
@[simp]
theorem unitFiltrationGradedSuccEquivResidueField_ofMul_mk (n : ℕ)
    (x : unitFiltration K (n + 1)) :
    unitFiltrationGradedSuccEquivResidueField (K := K) n
        (Additive.ofMul (QuotientGroup.mk x)) =
      (Ideal.quotEquivPowQuotPowSucc
        (I := 𝓂[K]) (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field 𝒪[K]) (n + 1)).symm
        (Submodule.Quotient.mk (unitFiltrationDifference n x)) := by
  rw [unitFiltrationGradedSuccEquivResidueField]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    unitFiltrationGradedSuccEquivMaximalIdealGraded_mk]
  -- What remains only strips the `Additive`/`Multiplicative` tags of the intermediate
  -- equivalence and reads the linear equivalence additively; both are definitional.
  rfl

/-- The positive graded piece `U(K,n+1) / U(K,n+2)` is finite. -/
noncomputable instance finite_unitFiltrationGraded_succ (n : ℕ) :
    Finite (UnitFiltrationGraded K (n + 1)) :=
  Finite.of_equiv 𝓀[K]
    (unitFiltrationGradedSuccEquivResidueField (K := K) n).symm.toEquiv

/-- Every positive graded piece has the cardinality of the residue field. -/
theorem natCard_unitFiltrationGraded_succ (n : ℕ) :
    Nat.card (UnitFiltrationGraded K (n + 1)) = Nat.card 𝓀[K] :=
  Nat.card_congr (unitFiltrationGradedSuccEquivResidueField (K := K) n).toEquiv

/-- Every positive step has relative index equal to the cardinality of the residue field:
`[U(K,n+1) : U(K,n+2)] = #𝓀[K]`. -/
theorem relIndex_unitFiltration_succ_succ (n : ℕ) :
    (unitFiltration K (n + 2)).relIndex (unitFiltration K (n + 1)) = Nat.card 𝓀[K] := by
  rw [Subgroup.relIndex, Subgroup.index]
  simpa only [UnitFiltrationGraded] using natCard_unitFiltrationGraded_succ (K := K) n

/-- The index of `U(K,m+n+1)` in `U(K,m+1)` is `q ^ n`, where `q = #𝓀[K]`. -/
theorem relIndex_unitFiltration_add_succ_succ (m n : ℕ) :
    (unitFiltration K (m + n + 1)).relIndex (unitFiltration K (m + 1)) =
      (Nat.card 𝓀[K]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ]
      calc
        (unitFiltration K (m + n + 2)).relIndex (unitFiltration K (m + 1)) =
            (unitFiltration K (m + n + 2)).relIndex (unitFiltration K (m + n + 1)) *
              (unitFiltration K (m + n + 1)).relIndex (unitFiltration K (m + 1)) :=
          (Subgroup.relIndex_mul_relIndex _ _ _
            (unitFiltration_antitone (K := K) (by omega : m + n + 1 ≤ m + n + 2))
            (unitFiltration_antitone (K := K) (by omega : m + 1 ≤ m + n + 1))).symm
        _ = (Nat.card 𝓀[K]) ^ (n + 1) := by
          rw [relIndex_unitFiltration_succ_succ, ih, pow_succ']

/-- Every `U(K,m)` has finite relative index in each positive-depth subgroup `U(K,n+1)`: the
index is `1` when `m ≤ n + 1`, and a power of `#𝓀[K]` otherwise. -/
noncomputable instance unitFiltration_isFiniteRelIndex_succ (m n : ℕ) :
    (unitFiltration K m).IsFiniteRelIndex (unitFiltration K (n + 1)) := by
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  rcases le_or_gt m (n + 1) with h | h
  · rw [Subgroup.relIndex_eq_one.mpr (unitFiltration_antitone h)]
    exact one_ne_zero
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k + 1 := ⟨m - n - 1, by omega⟩
    rw [relIndex_unitFiltration_add_succ_succ]
    exact pow_ne_zero k Nat.card_pos.ne'

/-- Every `U(K,m)` has finite index in the unit group `U(K,0) = 𝒪[K]ˣ`. -/
noncomputable instance unitFiltration_isFiniteRelIndex_zero (m : ℕ) :
    (unitFiltration K m).IsFiniteRelIndex (unitFiltration K 0) := by
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Subgroup.relIndex_self]
    exact one_ne_zero
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (unitFiltration_antitone hm)
    (unitFiltration_antitone (Nat.zero_le 1)), relIndex_unitFiltration_one_zero]
  have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  exact mul_ne_zero Subgroup.relIndex_ne_zero (by omega)

/-- The index of `U(K,n+1)` in the unit group `U(K,0) = 𝒪[K]ˣ` is `(q - 1) * q ^ n`, where
`q = #𝓀[K]`. -/
theorem relIndex_unitFiltration_succ_zero (n : ℕ) :
    (unitFiltration K (n + 1)).relIndex (unitFiltration K 0) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  have h := relIndex_unitFiltration_add_succ_succ (K := K) 0 n
  rw [zero_add, zero_add] at h
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (unitFiltration_antitone (by omega : 1 ≤ n + 1))
    (unitFiltration_antitone (Nat.zero_le 1)), h, relIndex_unitFiltration_one_zero, mul_comm]

/-- **Powering a unit into a deep step.** For every unit `x ∈ U(K,0)` and every `n`, the power
`x ^ ((q - 1) * q ^ n)` lies in `U(K,n+1)`, where `q = #𝓀[K]`: the exponent is the index of
`U(K,n+1)` in `U(K,0)`. -/
theorem pow_natCard_sub_one_mul_pow_mem_unitFiltration_succ {x : Kˣ}
    (hx : x ∈ unitFiltration K 0) (n : ℕ) :
    x ^ ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n) ∈ unitFiltration K (n + 1) := by
  rw [← relIndex_unitFiltration_succ_zero]
  exact Subgroup.pow_relIndex_mem _ hx

/-- The positive-depth finite-level quotient `U(K,m+1) / U(K,m+n+1)` has `q ^ n` elements,
where `q = #𝓀[K]`. -/
theorem natCard_unitFiltration_succ_quotient_add_succ (m n : ℕ) :
    Nat.card (unitFiltration K (m + 1) ⧸
      (unitFiltration K (m + n + 1)).subgroupOf (unitFiltration K (m + 1))) =
        (Nat.card 𝓀[K]) ^ n := by
  rw [← Subgroup.index_eq_card]
  exact relIndex_unitFiltration_add_succ_succ m n

/-- The first two steps of the unit filtration coincide, `U(K,1) = U(K,0)`, exactly when the
residue field has two elements. -/
theorem unitFiltration_one_eq_unitFiltration_zero_iff :
    unitFiltration K 1 = unitFiltration K 0 ↔ Nat.card 𝓀[K] = 2 := by
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  rw [le_antisymm_iff, and_iff_right (unitFiltration_antitone (Nat.zero_le 1)),
    ← Subgroup.relIndex_eq_one, relIndex_unitFiltration_one_zero]
  omega

/-- **The steps of the unit filtration are distinct**, apart from the coincidence
`U(K,1) = U(K,0)` when the residue field has two elements
(`unitFiltration_one_eq_unitFiltration_zero_iff`): away from it, `U(K,j) ⊆ U(K,i)` exactly
when `i ≤ j`. -/
theorem unitFiltration_le_unitFiltration_iff {i j : ℕ} (h : i ≠ 1 ∨ Nat.card 𝓀[K] ≠ 2) :
    unitFiltration K j ≤ unitFiltration K i ↔ i ≤ j := by
  refine ⟨fun hji ↦ ?_, fun hij ↦ unitFiltration_antitone hij⟩
  by_contra! hlt
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  -- Otherwise `U(K,i-1) ⊆ U(K,j) ⊆ U(K,i)`, so the step from depth `i - 1` to `i` is trivial.
  obtain _ | _ | k := i
  · omega
  · have hstep : (unitFiltration K 1).relIndex (unitFiltration K 0) = 1 :=
      Subgroup.relIndex_eq_one.mpr ((unitFiltration_antitone (by omega)).trans hji)
    rw [relIndex_unitFiltration_one_zero] at hstep
    omega
  · have hstep : (unitFiltration K (k + 2)).relIndex (unitFiltration K (k + 1)) = 1 :=
      Subgroup.relIndex_eq_one.mpr ((unitFiltration_antitone (by omega)).trans hji)
    rw [relIndex_unitFiltration_succ_succ] at hstep
    omega

end TauCeti
