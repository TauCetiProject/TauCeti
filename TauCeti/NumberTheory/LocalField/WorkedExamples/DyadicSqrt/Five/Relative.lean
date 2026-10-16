/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.SquareClass
public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.StiefelWhitney
import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# The relative Stiefel–Whitney calculation on all dyadic unit classes

Every nonzero element of `ℚ₂(√5)` with even valuation has a unique square class represented by
`(-1)^c₀ (2 + √5)^c₁ (3 + 2√5)^c₂`, with `c : Fin 3 → ZMod 2`.
This file connects these exhaustive representatives with the twisted trace-form tables.
It computes both sides of the relative Stiefel–Whitney identities for every such element,
including every integer-ring unit, not just for a list of coefficients.

Write `κ = (-1) ∪ (-1) ≠ 0` over `ℚ₂`. In these coordinates the results are

* `cor(a) = c₁ (-1) + c₂ (5)`;
* `w₁(Tr_*⟨a⟩) = c₁ (-1) + (1 + c₂) (5)`;
* `w₂(Tr_*⟨a⟩) = (1 + c₀)(1 + c₁) κ`;
* `N^{Ev}(a) = (1 + (1 + c₀)(1 + c₁)) κ`.

The untwisted trace form has classes `(5)` and `κ`, and the cup of its first class
with `cor(a)` vanishes. Thus the displayed values evaluate the degree-one and degree-two
relative formulas. The omitted uniformizer coset has odd valuation and is not a unit class.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations
  galoisiennes réelles*, Invent. Math. 78 (1984), Lemme II.2.1 and Théorème 2.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2.
-/

public section

noncomputable section

namespace TauCeti.DyadicSqrtFive

open _root_.QuadraticMap ValuativeRel

private def signIndex (c : Fin 3 → ZMod 2) : Fin 2 :=
  ⟨(c 0).val, ZMod.val_lt _⟩

private def coefficientIndex (c : Fin 3 → ZMod 2) : Fin 4 :=
  ⟨(c 1).val + 2 * (c 2).val, by have := ZMod.val_lt (c 1); have := ZMod.val_lt (c 2); omega⟩

private theorem coe_rep (c : Fin 3 → ZMod 2) :
    (unitSquareClassRep c : DyadicSqrtFive) = (-1) ^ (signIndex c).val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] (coefficientIndex c) := by
  have cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases cases (c 0) with h0 | h0 <;> rcases cases (c 1) with h1 | h1 <;>
    rcases cases (c 2) with h2 | h2 <;>
    simp [unitSquareClassRep_def, Fin.prod_univ_three, signIndex, coefficientIndex,
      h0, h1, h2, ZMod.val_one] <;> ring_nf <;> simp [sqrtFive_sq] <;> ring

private theorem representative_values
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) (c : Fin 3 → ZMod 2)
    (hQ : (((unitSquareClassRep c : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    galoisCor ℚ_[2] DyadicSqrtFive σ 1 (kummerClass (unitSquareClassRep c)) =
        c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
          c 2 • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw1Class (formClass _ hQ) = c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
        (1 + c 2) • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw2Class (formClass _ hQ) = ((1 + c 0) * (1 + c 1)) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) ∧
      galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two (kummerClass (unitSquareClassRep c)) =
        (1 + (1 + c 0) * (1 + c 1)) •
          kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  have hc := galoisCor_kummerClass_table σ (signIndex c) (coefficientIndex c) _ (coe_rep c)
  have h1 := sw1Class_traceTransfer_table (signIndex c) (coefficientIndex c) _ (coe_rep c) hQ
  have h2 := sw2Class_traceTransfer_table (signIndex c) (coefficientIndex c) _ (coe_rep c) hQ
  have he := galoisEvens_kummerClass_table σ (signIndex c) (coefficientIndex c) _ (coe_rep c)
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  have cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases cases (c 0) with h0c | h0c <;> rcases cases (c 1) with h1c | h1c <;>
    rcases cases (c 2) with h2c | h2c <;>
    simpa [signIndex, coefficientIndex, h0c, h1c, h2c, ZMod.val_one, htwo] using
      And.intro hc (And.intro h1 (And.intro h2 he))

/-- **The complete unit-class calculation of the relative Stiefel–Whitney formula over
`ℚ₂(√5)`.** Every nonzero element of even valuation has unique binary square-class
coordinates in the basis `-1`, `2 + √5`, `3 + 2√5`. In those coordinates the corestriction,
the two classes of its twisted trace form, and the Evens norm have the displayed values.
These evaluate both sides of the relative identities, since the untwisted classes are `(5)` and
`κ = (-1) ∪ (-1)`, and the cross term vanishes. -/
theorem existsUnique_relative_traceTransfer_values_of_even
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) (a : DyadicSqrtFiveˣ)
    (ha : Even (normalizedValuation DyadicSqrtFive a).toAdd)
    (hQ : (((a : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    ∃! c : Fin 3 → ZMod 2,
      squareClass a = squareClass (unitSquareClassRep c) ∧
      galoisCor ℚ_[2] DyadicSqrtFive σ 1 (kummerClass a) =
        c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
          c 2 • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw1Class (formClass _ hQ) = c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
        (1 + c 2) • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw2Class (formClass _ hQ) = ((1 + c 0) * (1 + c 1)) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) ∧
      galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two (kummerClass a) =
        (1 + (1 + c 0) * (1 + c 1)) •
          kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  obtain ⟨c, hc, hunique⟩ := (existsUnique_unitSquareClassRep_iff_even a).mpr ha
  have hk : kummerClass a = kummerClass (unitSquareClassRep c) := by
    rw [← kummerSquareClassEquiv_squareClass, ← kummerSquareClassEquiv_squareClass, hc]
  have hrep : (((unitSquareClassRep c : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate :=
    (QuadraticMap.nondegenerate_traceTransfer_iff _).mpr
      (nondegenerate_smul_sq (unitSquareClassRep c).ne_zero)
  obtain ⟨hcor, hsw1, hsw2, hev⟩ := representative_values σ c hrep
  have hbase : ((sq (R := DyadicSqrtFive) (A := DyadicSqrtFive)).traceTransfer
      ℚ_[2]).Nondegenerate := QuadraticMap.sq.nondegenerate_traceTransfer_iff.mpr
        (by simpa using nondegenerate_smul_sq (one_ne_zero : (1 : DyadicSqrtFive) ≠ 0))
  have hw1 : sw1Class (formClass _ hQ) = sw1Class (formClass _ hrep) := by
    rw [sw1Class_formClass_traceTransfer_smul_sq σ a hQ hbase,
      sw1Class_formClass_traceTransfer_smul_sq σ (unitSquareClassRep c) hrep hbase, hk]
  have hw2 : sw2Class (formClass _ hQ) = sw2Class (formClass _ hrep) := by
    rw [sw2Class_formClass_traceTransfer_smul_sq σ finrank_eq_two a hQ hbase,
      sw2Class_formClass_traceTransfer_smul_sq σ finrank_eq_two (unitSquareClassRep c) hrep hbase,
      hk]
  refine ⟨c, ⟨hc, ?_, hw1.trans hsw1, hw2.trans hsw2, ?_⟩, fun d hd => hunique d hd.1⟩
  · rw [hk]
    exact hcor
  · rw [hk]
    exact hev

/-- Every integer-ring unit has the relative Stiefel–Whitney values given by
`existsUnique_relative_traceTransfer_values_of_even`, since its valuation is zero. -/
theorem existsUnique_relative_traceTransfer_values
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) (u : 𝒪[DyadicSqrtFive]ˣ)
    (hQ : (((Units.map (𝒪[DyadicSqrtFive].subtype :
      𝒪[DyadicSqrtFive] →* DyadicSqrtFive) u : DyadicSqrtFive) •
        sq (R := DyadicSqrtFive) (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    let a := Units.map (𝒪[DyadicSqrtFive].subtype : 𝒪[DyadicSqrtFive] →* DyadicSqrtFive) u
    ∃! c : Fin 3 → ZMod 2,
      squareClass a = squareClass (unitSquareClassRep c) ∧
      galoisCor ℚ_[2] DyadicSqrtFive σ 1 (kummerClass a) =
        c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
          c 2 • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw1Class (formClass _ hQ) = c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
        (1 + c 2) • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw2Class (formClass _ hQ) = ((1 + c 0) * (1 + c 1)) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) ∧
      galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two (kummerClass a) =
        (1 + (1 + c 0) * (1 + c 1)) •
          kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  exact existsUnique_relative_traceTransfer_values_of_even σ _
    (by simp [normalizedValuation_integerUnits]) hQ

end TauCeti.DyadicSqrtFive
