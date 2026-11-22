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

for `n > 0`, obtained by identifying `unitFiltration K i` with `(𝓂[K] ^ i).principalUnitGroup`
and transporting the local-ring isomorphism
`TauCeti.IsLocalRing.principalUnitGradedSuccEquivMaximalIdealGraded`.  Since the maximal ideal of
the discrete valuation ring `𝒪[K]` is principal, each ideal quotient is a one-dimensional copy of
the residue field.  Combining these facts identifies every positive graded piece with the additive
group of `𝓀[K]`, and shows that it has `#𝓀[K]` elements.

## Main definitions

* `TauCeti.unitFiltrationEquivPrincipalUnitGroup` and
  `TauCeti.unitFiltrationGradedEquivPrincipalUnitGraded`: identification of the unit filtration and
  its successive quotients with the principal-unit filtration of `𝒪[K]`.
* `TauCeti.unitFiltrationGradedSuccEquivMaximalIdealGraded`: subtracting one identifies a
  positive unit-filtration quotient with the corresponding quotient of powers of the maximal
  ideal.
* `TauCeti.unitFiltrationGradedSuccEquivResidueField`: every positive graded piece is additively
  isomorphic to the residue field.

## Main results

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

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti.IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

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

variable (K) in
/-- Identification of the unit-filtration step `U(K, i)` with the principal unit group
`(𝓂[K] ^ i).principalUnitGroup` of the integer ring `𝒪[K]`. -/
def unitFiltrationEquivPrincipalUnitGroup (i : ℕ) :
    unitFiltration K i ≃* (maximalIdeal 𝒪[K] ^ i).principalUnitGroup where
  toFun x := ⟨unitFiltrationToIntegerUnits i x, by
    rw [Ideal.mem_principalUnitGroup]
    obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.mp x.prop
    have heq : unitFiltrationToIntegerUnits i x = u :=
      Units.ext (Subtype.ext (by rw [coe_unitFiltrationToIntegerUnits, ← hux]))
    rwa [heq]⟩
  invFun u := ⟨Units.map (Subring.subtype 𝒪[K]).toMonoidHom (u : 𝒪[K]ˣ),
    mem_unitFiltration_iff_exists.mpr ⟨u, Ideal.mem_principalUnitGroup.mp u.prop, rfl⟩⟩
  left_inv x := Subtype.ext (unitsMap_subtype_unitFiltrationToIntegerUnits i x)
  right_inv u := Subtype.ext (Units.ext (Subtype.ext (coe_unitFiltrationToIntegerUnits i _)))
  map_mul' x y := Subtype.ext (map_mul (unitFiltrationToIntegerUnits i) x y)

/-- Reading a principal unit corresponding to `x ∈ U(K, i)` in `K` recovers `x`. -/
@[simp]
theorem coe_unitFiltrationEquivPrincipalUnitGroup (i : ℕ) (x : unitFiltration K i) :
    (((unitFiltrationEquivPrincipalUnitGroup K i x : 𝒪[K]ˣ) : 𝒪[K]) : K) = ((x : Kˣ) : K) :=
  coe_unitFiltrationToIntegerUnits i x

/-- Reading the element of `U(K, i)` corresponding to `u ∈ (𝓂[K] ^ i).principalUnitGroup` in `K`
recovers `u`. -/
@[simp]
theorem coe_unitFiltrationEquivPrincipalUnitGroup_symm (i : ℕ)
    (u : (maximalIdeal 𝒪[K] ^ i).principalUnitGroup) :
    (((unitFiltrationEquivPrincipalUnitGroup K i).symm u : Kˣ) : K) = ((u : 𝒪[K]ˣ) : K) := by
  simp [unitFiltrationEquivPrincipalUnitGroup]

variable (K) in
/-- Identification of the graded unit-filtration quotient `U(K, i) / U(K, i + 1)` with the
corresponding principal-unit graded quotient `PrincipalUnitGraded 𝒪[K] i`. -/
def unitFiltrationGradedEquivPrincipalUnitGraded (i : ℕ) :
    UnitFiltrationGraded K i ≃* PrincipalUnitGraded 𝒪[K] i :=
  QuotientGroup.congr _ _ (unitFiltrationEquivPrincipalUnitGroup K i) <| by
    ext u
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    refine ⟨?_, fun hu ↦ ?_⟩
    · rintro ⟨x, hx, rfl⟩
      rw [Ideal.mem_principalUnitGroup]
      obtain ⟨v, hv, hvx⟩ :=
        mem_unitFiltration_iff_exists.mp (hx : (x : Kˣ) ∈ unitFiltration K (i + 1))
      have hv_eq : ((unitFiltrationEquivPrincipalUnitGroup K i x : 𝒪[K]ˣ) : 𝒪[K]) = (v : 𝒪[K]) :=
        Subtype.ext (by rw [coe_unitFiltrationEquivPrincipalUnitGroup, ← hvx])
      change ((unitFiltrationEquivPrincipalUnitGroup K i x : 𝒪[K]ˣ) : 𝒪[K]) - 1 ∈ 𝓂[K] ^ (i + 1)
      rwa [hv_eq]
    · obtain ⟨x, hxu⟩ := (unitFiltrationEquivPrincipalUnitGroup K i).surjective u
      refine ⟨x, ?_, hxu⟩
      rw [mem_unitFiltration_iff_exists]
      refine ⟨(unitFiltrationEquivPrincipalUnitGroup K i x : 𝒪[K]ˣ), ?_,
        coe_unitFiltrationEquivPrincipalUnitGroup i x⟩
      rwa [hxu, ← Ideal.mem_principalUnitGroup]

/-- Evaluating `unitFiltrationGradedEquivPrincipalUnitGraded` on a coset transports the
representative along `unitFiltrationEquivPrincipalUnitGroup`. -/
@[simp]
theorem unitFiltrationGradedEquivPrincipalUnitGraded_mk (i : ℕ) (x : unitFiltration K i) :
    unitFiltrationGradedEquivPrincipalUnitGraded K i (QuotientGroup.mk x) =
      QuotientGroup.mk (unitFiltrationEquivPrincipalUnitGroup K i x) :=
  QuotientGroup.congr_mk ..

/-- Evaluating the inverse of `unitFiltrationGradedEquivPrincipalUnitGraded` on a coset transports
the representative backwards along `unitFiltrationEquivPrincipalUnitGroup`. -/
@[simp]
theorem unitFiltrationGradedEquivPrincipalUnitGraded_symm_mk (i : ℕ)
    (u : (maximalIdeal 𝒪[K] ^ i).principalUnitGroup) :
    (unitFiltrationGradedEquivPrincipalUnitGraded K i).symm (QuotientGroup.mk u) =
      QuotientGroup.mk ((unitFiltrationEquivPrincipalUnitGroup K i).symm u) := by
  rw [MulEquiv.symm_apply_eq, unitFiltrationGradedEquivPrincipalUnitGraded_mk,
    MulEquiv.apply_symm_apply]

/-- Subtracting one identifies the positive unit-filtration quotient
`U(K,n+1) / U(K,n+2)` with `𝓂[K]^(n+1) / 𝓂[K]^(n+2)`. -/
noncomputable def unitFiltrationGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    UnitFiltrationGraded K (n + 1) ≃* Multiplicative (MaximalIdealGraded K (n + 1)) :=
  (unitFiltrationGradedEquivPrincipalUnitGraded K (n + 1)).trans
    (principalUnitGradedSuccEquivMaximalIdealGraded 𝒪[K] n).toMultiplicativeRight

/-- On a class represented by `u ∈ U(K,n+1)`, the positive-depth graded equivalence is the
class of `u - 1` modulo `𝓂[K]^(n+2)`. -/
@[simp]
theorem unitFiltrationGradedSuccEquivMaximalIdealGraded_mk
    (n : ℕ) (x : unitFiltration K (n + 1)) :
    unitFiltrationGradedSuccEquivMaximalIdealGraded (K := K) n (QuotientGroup.mk x) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n x)) := by
  rw [unitFiltrationGradedSuccEquivMaximalIdealGraded, MulEquiv.trans_apply,
    unitFiltrationGradedEquivPrincipalUnitGraded_mk]
  change Multiplicative.ofAdd (principalUnitGradedSuccEquivMaximalIdealGraded 𝒪[K] n
      (Additive.ofMul (QuotientGroup.mk (unitFiltrationEquivPrincipalUnitGroup K (n + 1) x)))) =
    _
  rw [principalUnitGradedSuccEquivMaximalIdealGraded_ofMul_mk]
  exact congrArg (fun z : (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) ↦
    Multiplicative.ofAdd (Submodule.Quotient.mk z)) (Subtype.ext rfl)

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
