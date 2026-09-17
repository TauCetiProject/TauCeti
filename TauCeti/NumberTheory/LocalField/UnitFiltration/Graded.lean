/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
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

* `TauCeti.unitFiltrationGradedSuccEquivMaximalIdealGraded`: subtracting one identifies a
  positive unit-filtration quotient with the corresponding quotient of powers of the maximal
  ideal.
* `TauCeti.unitFiltrationGradedSuccEquivResidueField`: every positive graded piece is additively
  isomorphic to the residue field.
* `TauCeti.natCard_unitFiltrationGraded_succ` and
  `TauCeti.relIndex_unitFiltration_succ_succ`: the positive graded pieces and relative indices
  have cardinality `#𝓀[K]`.

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

/-- Subtracting one, modulo the next power of the maximal ideal, is a homomorphism from a
positive unit-filtration step to the multiplicative copy of the corresponding ideal quotient. -/
noncomputable def unitFiltrationToMaximalIdealGraded (n : ℕ) :
    unitFiltration K (n + 1) →* Multiplicative (MaximalIdealGraded K (n + 1)) where
  toFun x := Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n x))
  map_one' := by
    have hzero :
        (Submodule.Quotient.mk
          (unitFiltrationDifference (K := K) n (1 : unitFiltration K (n + 1))) :
          MaximalIdealGraded K (n + 1)) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      have hdiff :
          unitFiltrationDifference (K := K) n (1 : unitFiltration K (n + 1)) = 0 := by
        apply Subtype.ext
        rw [coe_unitFiltrationDifference (K := K), map_one]
        simp
      rw [hdiff]
      exact Submodule.zero_mem _
    rw [hzero, ofAdd_zero]
  map_mul' x y := by
    have hquot :
        (Submodule.Quotient.mk (unitFiltrationDifference n (x * y)) :
          MaximalIdealGraded K (n + 1)) =
          Submodule.Quotient.mk
            (unitFiltrationDifference n x + unitFiltrationDifference n y) := by
      rw [Submodule.Quotient.eq,
        Submodule.mem_smul_top_iff (I := 𝓂[K])
          (𝓂[K] ^ (n + 1) : Submodule 𝒪[K] 𝒪[K])]
      -- The quotient relation lives on the ideal subtype; read it in the integer ring so that
      -- the elementary identity `(xy - 1) - ((x - 1) + (y - 1)) = (x - 1)(y - 1)` is visible.
      change
        (unitFiltrationDifference n (x * y) : 𝒪[K]) -
            ((unitFiltrationDifference n x : 𝒪[K]) +
              (unitFiltrationDifference n y : 𝒪[K])) ∈
          𝓂[K] • (𝓂[K] ^ (n + 1) : Submodule 𝒪[K] 𝒪[K])
      rw [smul_eq_mul, coe_unitFiltrationDifference, coe_unitFiltrationDifference,
        coe_unitFiltrationDifference, map_mul]
      have hx := (unitFiltrationDifference n x).prop
      have hy := (unitFiltrationDifference n y).prop
      have hx' : (unitFiltrationToIntegerUnits (n + 1) x : 𝒪[K]) - 1 ∈
          𝓂[K] ^ (n + 1) := by
        simpa only [coe_unitFiltrationDifference] using hx
      have hy' : (unitFiltrationToIntegerUnits (n + 1) y : 𝒪[K]) - 1 ∈
          𝓂[K] ^ (n + 1) := by
        simpa only [coe_unitFiltrationDifference] using hy
      have hxy :
          ((unitFiltrationToIntegerUnits (n + 1) x : 𝒪[K]) - 1) *
              ((unitFiltrationToIntegerUnits (n + 1) y : 𝒪[K]) - 1) ∈ 𝓂[K] ^ (n + 2) := by
        have hn : n + 2 ≤ (n + 1) + (n + 1) := by omega
        apply Ideal.pow_le_pow_right hn
        simpa only [← pow_add] using Ideal.mul_mem_mul hx' hy'
      rw [pow_succ'] at hxy
      convert hxy using 1
      simp only [Units.val_mul]
      ring
    have hmul :=
      congrArg (fun z : MaximalIdealGraded K (n + 1) ↦ Multiplicative.ofAdd z) hquot
    rw [Submodule.Quotient.mk_add, ofAdd_add] at hmul
    exact hmul

/-- The value of `unitFiltrationToMaximalIdealGraded` is the class of `u - 1`. -/
@[simp]
theorem unitFiltrationToMaximalIdealGraded_apply (n : ℕ)
    (x : unitFiltration K (n + 1)) :
    unitFiltrationToMaximalIdealGraded n x =
      Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n x)) :=
  (rfl)

/-- The kernel of subtracting one modulo `𝓂[K]^(n+2)` is precisely `U(K,n+2)`. -/
theorem ker_unitFiltrationToMaximalIdealGraded (n : ℕ) :
    (unitFiltrationToMaximalIdealGraded (K := K) n).ker =
      (unitFiltration K (n + 2)).subgroupOf (unitFiltration K (n + 1)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [unitFiltrationToMaximalIdealGraded_apply, ofAdd_eq_one,
    Submodule.Quotient.mk_eq_zero]
  -- Stated through `RingHom.toMonoidHom`, the spelling used by `mem_unitFiltration_succ_congr`.
  have hxmap : Units.map (Subring.subtype 𝒪[K]).toMonoidHom
      (unitFiltrationToIntegerUnits (n + 1) x) = (x : Kˣ) :=
    unitsMap_subtype_unitFiltrationToIntegerUnits (n + 1) x
  constructor
  · intro h
    rw [← hxmap, mem_unitFiltration_succ_congr]
    have h' := (Submodule.mem_smul_top_iff 𝓂[K]
      (𝓂[K] ^ (n + 1) : Submodule 𝒪[K] 𝒪[K]) (unitFiltrationDifference n x)).mp h
    simpa only [coe_unitFiltrationDifference, smul_eq_mul, pow_succ'] using h'
  · intro h
    rw [← hxmap, mem_unitFiltration_succ_congr] at h
    apply (Submodule.mem_smul_top_iff 𝓂[K]
      (𝓂[K] ^ (n + 1) : Submodule 𝒪[K] 𝒪[K]) (unitFiltrationDifference n x)).mpr
    simpa only [coe_unitFiltrationDifference, smul_eq_mul, pow_succ'] using h

/-- Subtracting one modulo `𝓂[K]^(n+2)` maps `U(K,n+1)` onto the corresponding maximal-ideal
graded piece. -/
theorem unitFiltrationToMaximalIdealGraded_surjective (n : ℕ) :
    Function.Surjective (unitFiltrationToMaximalIdealGraded (K := K) n) := by
  intro z
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z.toAdd
  have ha : (a : 𝒪[K]) ∈ 𝓂[K] :=
    Ideal.pow_le_self (Nat.succ_ne_zero n) a.prop
  have hu : IsUnit (1 + (a : 𝒪[K])) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
        ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem ha))
  let u : 𝒪[K]ˣ := hu.unit
  have hu_spec : (u : 𝒪[K]) = 1 + (a : 𝒪[K]) := hu.unit_spec
  let x : unitFiltration K (n + 1) :=
    ⟨Units.map (Subring.subtype 𝒪[K]).toMonoidHom u,
      (mem_unitFiltration_succ_congr n u).mpr (by
        rw [hu_spec, add_sub_cancel_left]
        exact a.prop)⟩
  have hinter : unitFiltrationToIntegerUnits (n + 1) x = u := by
    apply Units.ext
    apply Subtype.ext
    simp only [coe_unitFiltrationToIntegerUnits, x, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Subring.coe_subtype]
  refine ⟨x, ?_⟩
  -- Strip the multiplicative type tag to compare the two representatives in the module quotient.
  change Submodule.Quotient.mk (unitFiltrationDifference n x) = Submodule.Quotient.mk a
  rw [Submodule.Quotient.eq]
  have hdiff : unitFiltrationDifference n x = a := by
    apply Subtype.ext
    simp only [coe_unitFiltrationDifference, hinter, hu_spec]
    ring
  rw [hdiff, sub_self]
  exact Submodule.zero_mem _

/-- Subtracting one identifies the positive unit-filtration quotient
`U(K,n+1) / U(K,n+2)` with `𝓂[K]^(n+1) / 𝓂[K]^(n+2)`. -/
noncomputable def unitFiltrationGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    UnitFiltrationGraded K (n + 1) ≃* Multiplicative (MaximalIdealGraded K (n + 1)) :=
  QuotientGroup.liftEquiv
    ((unitFiltration K (n + 2)).subgroupOf (unitFiltration K (n + 1)))
    (unitFiltrationToMaximalIdealGraded_surjective (K := K) n)
    (ker_unitFiltrationToMaximalIdealGraded (K := K) n).symm

/-- On a class represented by `u ∈ U(K,n+1)`, the positive-depth graded equivalence is the
class of `u - 1` modulo `𝓂[K]^(n+2)`. -/
@[simp]
theorem unitFiltrationGradedSuccEquivMaximalIdealGraded_mk
    (n : ℕ) (x : unitFiltration K (n + 1)) :
    unitFiltrationGradedSuccEquivMaximalIdealGraded (K := K) n (QuotientGroup.mk x) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n x)) := by
  rw [unitFiltrationGradedSuccEquivMaximalIdealGraded,
    QuotientGroup.liftEquiv_mk, unitFiltrationToMaximalIdealGraded_apply]

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
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply,
    MonoidHom.toAdditive_apply_apply, MulEquiv.coe_toMonoidHom, toMul_ofMul,
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

end TauCeti
