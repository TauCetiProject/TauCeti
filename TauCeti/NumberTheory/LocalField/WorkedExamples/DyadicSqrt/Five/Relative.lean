/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.SquareClass
public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.StiefelWhitney
import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.Kummer.Value
import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup

/-!
# The relative Stiefel–Whitney calculation on all square classes of `ℚ₂(√5)`

Every nonzero element of `ℚ₂(√5)` with even valuation has a unique square class represented by
`(-1)^c₀ (2 + √5)^c₁ (3 + 2√5)^c₂`, with `c : Fin 3 → ZMod 2`; one of odd valuation has a
unique square class represented by `2` times such a product.
This file connects these exhaustive representatives with the twisted trace-form tables.
It computes both sides of the relative Stiefel–Whitney identities for every nonzero element,
including every integer-ring unit, not just for a list of coefficients.

Write `κ = (-1) ∪ (-1) ≠ 0` over `ℚ₂`, and let `e ∈ ZMod 2` be the parity of the valuation of
`a`. In these coordinates the results are

* `cor(a) = c₁ (-1) + c₂ (5)`;
* `w₁(Tr_*⟨a⟩) = c₁ (-1) + (1 + c₂) (5)`;
* `w₂(Tr_*⟨a⟩) = ((1 + c₀)(1 + c₁) + e (1 + c₂)) κ`;
* `N^{Ev}(a) = (1 + (1 + c₀)(1 + c₁) + e (1 + c₂)) κ`.

The untwisted trace form has classes `(5)` and `κ`, and the cup of its first class
with `cor(a)` vanishes. Thus the displayed values evaluate the degree-one and degree-two
relative formulas. The uniformizer `2` of `ℚ₂` stays a uniformizer of the unramified extension
`ℚ₂(√5)`; the Evens norm of `(2 a)` differs from that of `(a)` by `(2) ∪ (-5 · N a)`
(`TauCeti.galoisEvens2_kummerClass_algebraMap_mul`), which accounts for the term `e (1 + c₂) κ`.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations
  galoisiennes réelles*, Invent. Math. 78 (1984), Lemme II.2.1 and Théorème 2.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2.
-/

public section

noncomputable section

namespace TauCeti.DyadicSqrtFive

open _root_.QuadraticMap _root_.ValuativeRel

private theorem zmod_two_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  decide +revert

private def signIndex (c : Fin 3 → ZMod 2) : Fin 2 :=
  ⟨(c 0).val, ZMod.val_lt _⟩

private def coefficientIndex (c : Fin 3 → ZMod 2) : Fin 4 :=
  ⟨(c 1).val + 2 * (c 2).val, by have := ZMod.val_lt (c 1); have := ZMod.val_lt (c 2); omega⟩

private theorem coe_rep (c : Fin 3 → ZMod 2) :
    (unitSquareClassRep c : DyadicSqrtFive) = (-1) ^ (signIndex c).val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] (coefficientIndex c) := by
  rcases zmod_two_cases (c 0) with h0 | h0 <;> rcases zmod_two_cases (c 1) with h1 | h1 <;>
    rcases zmod_two_cases (c 2) with h2 | h2 <;>
    simp [unitSquareClassRep_def, Fin.prod_univ_three, signIndex, coefficientIndex,
      h0, h1, h2, ZMod.val_one] <;> ring_nf <;> simp [sqrtFive_sq] <;> ring

private theorem nondegenerate_traceTransfer_sq :
    ((sq (R := DyadicSqrtFive) (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate :=
  QuadraticMap.sq.nondegenerate_traceTransfer_iff.mpr
    (by simpa using nondegenerate_smul_sq (one_ne_zero : (1 : DyadicSqrtFive) ≠ 0))

private theorem nondegenerate_traceTransfer_smul_sq (u : DyadicSqrtFiveˣ) :
    (((u : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate :=
  (QuadraticMap.nondegenerate_traceTransfer_iff _).mpr (nondegenerate_smul_sq u.ne_zero)

/-- If `(N) = c₁ (-1) + c₂ (5)`, then `(2) ∪ (-(5 · N)) = (1 + c₂) κ`, by the Steinberg relation
`(2) ∪ (-1) = 0` and `(2) ∪ (5) = κ`. -/
private theorem cup_two_neg_five_mul {N : ℚ_[2]ˣ} {c₁ c₂ : ZMod 2}
    (hN : kummerClass N = c₁ • kummerClass (-1 : ℚ_[2]ˣ) +
      c₂ • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
        (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
        (kummerClass (-(Units.mk0 (5 : ℚ_[2]) (by norm_num) * N))) =
      (1 + c₂) • kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  have h2m1 : (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero)) (kummerClass (-1)) = 0 :=
    cup_kummerClass_eq_zero_of_add_eq_one (by norm_num)
  rw [neg_eq_neg_one_mul, kummerClass_mul, kummerClass_mul, hN,
    kummerCup_squareClass_squareClass]
  rcases zmod_two_cases c₁ with h1 | h1 <;> rcases zmod_two_cases c₂ with h2 | h2 <;>
    simp [h1, h2, h2m1, cup_kummerClass_two_five_eq_neg_one_neg_one_padicTwo, add_smul]

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
  rcases zmod_two_cases (c 0) with h0c | h0c <;> rcases zmod_two_cases (c 1) with h1c | h1c <;>
    rcases zmod_two_cases (c 2) with h2c | h2c <;>
    simpa [signIndex, coefficientIndex, h0c, h1c, h2c, ZMod.val_one, htwo] using
      And.intro hc (And.intro h1 (And.intro h2 he))

/-- The values on the odd representatives `2 u`. Corestriction and the first class agree with
those of `u`, while the second class and the Evens norm change by `(2) ∪ (-(5 · N u)) = (1 + c₂) κ`.
-/
private theorem two_mul_representative_values
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) (c : Fin 3 → ZMod 2)
    (hQ : ((((Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * unitSquareClassRep c :
      DyadicSqrtFiveˣ) : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
        (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    galoisCor ℚ_[2] DyadicSqrtFive σ 1
        (kummerClass (Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * unitSquareClassRep c)) =
        c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
          c 2 • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw1Class (formClass _ hQ) = c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
        (1 + c 2) • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw2Class (formClass _ hQ) = ((1 + c 0) * (1 + c 1) + (1 + c 2)) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) ∧
      galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two
          (kummerClass (Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * unitSquareClassRep c)) =
        ((1 + c 0) * (1 + c 1) + c 2) •
          kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  have hrep := nondegenerate_traceTransfer_smul_sq (unitSquareClassRep c)
  obtain ⟨hcor, hsw1, hsw2, hev⟩ := representative_values σ c hrep
  set u := unitSquareClassRep c
  -- The factor `2` comes from the base field.
  have hk : kummerClass (Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * u) = kummerClass
      (Units.map (algebraMap ℚ_[2] DyadicSqrtFive : ℚ_[2] →* DyadicSqrtFive)
        (Units.mk0 2 two_ne_zero) * u) := by
    congr 2
    ext
    simp [map_ofNat]
  -- Corestriction does not see the factor `2`, whose norm `4` is a square.
  have hcor' : galoisCor ℚ_[2] DyadicSqrtFive σ 1
      (kummerClass (Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * u)) =
        galoisCor ℚ_[2] DyadicSqrtFive σ 1 (kummerClass u) := by
    have hsq : kummerClass (Algebra.normUnits ℚ_[2]
        (Units.map (algebraMap ℚ_[2] DyadicSqrtFive : ℚ_[2] →* DyadicSqrtFive)
          (Units.mk0 2 two_ne_zero))) = 0 :=
      (kummerClass_eq_zero_iff_square ℚ_[2]).2 (Subgroup.mem_square.2 ⟨Units.mk0 2 two_ne_zero, by
        ext
        simp [finrank_eq_two, _root_.sq]⟩)
    rw [hk, galoisCor_kummerClass, galoisCor_kummerClass, map_mul, kummerClass_mul, hsq,
      zero_add]
  -- The Evens norm changes by `(2) ∪ (-(5 · N u))`, and `(N u) = c₁ (-1) + c₂ (5)` is `cor(u)`.
  have hNu : kummerClass (Units.map (Algebra.norm ℚ_[2] : DyadicSqrtFive →* ℚ_[2]) u) =
      c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
        c 2 • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) := by
    rw [← hcor, galoisCor_kummerClass]
    congr 1
    exact Units.ext (by simp)
  have hev' : galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two
      (kummerClass (Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * u)) =
        galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two (kummerClass u) +
          (1 + c 2) • kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
    rw [hk, galoisEvens2_kummerClass_algebraMap_mul σ finrank_eq_two
      (Units.mk0 (5 : ℚ_[2]) (by norm_num)) sqrtFive_not_mem (by simp [map_ofNat]) _ u]
    rw [cup_two_neg_five_mul hNu]
  -- Both classes then follow from the relative formulas for `2 u` and for `u`.
  have hbase := nondegenerate_traceTransfer_sq
  refine ⟨hcor'.trans hcor, ?_, ?_, ?_⟩
  · rw [sw1Class_formClass_traceTransfer_smul_sq σ _ hQ hbase, hcor', ← hsw1,
      sw1Class_formClass_traceTransfer_smul_sq σ u hrep hbase]
  · rw [sw2Class_formClass_traceTransfer_smul_sq σ finrank_eq_two _ hQ hbase, hev', hcor',
      add_smul ((1 + c 0) * (1 + c 1)) (1 + c 2), ← hsw2,
      sw2Class_formClass_traceTransfer_smul_sq σ finrank_eq_two u hrep hbase]
    abel
  · rw [hev', hev, ← add_smul]
    congr 1
    have htwo : (1 + 1 : ZMod 2) = 0 := by decide
    linear_combination htwo

/-- The Kummer class and the Stiefel–Whitney classes of the twisted trace form depend only on
the square class of the coefficient. -/
private theorem relative_values_congr
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) {a b : DyadicSqrtFiveˣ}
    (hab : squareClass a = squareClass b)
    (ha : (((a : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate)
    (hb : (((b : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    kummerClass a = kummerClass b ∧ sw1Class (formClass _ ha) = sw1Class (formClass _ hb) ∧
      sw2Class (formClass _ ha) = sw2Class (formClass _ hb) := by
  have hk : kummerClass a = kummerClass b := by
    rw [← kummerSquareClassEquiv_squareClass, ← kummerSquareClassEquiv_squareClass, hab]
  have hbase := nondegenerate_traceTransfer_sq
  refine ⟨hk, ?_, ?_⟩
  · rw [sw1Class_formClass_traceTransfer_smul_sq σ a ha hbase,
      sw1Class_formClass_traceTransfer_smul_sq σ b hb hbase, hk]
  · rw [sw2Class_formClass_traceTransfer_smul_sq σ finrank_eq_two a ha hbase,
      sw2Class_formClass_traceTransfer_smul_sq σ finrank_eq_two b hb hbase, hk]

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
  have hrep := nondegenerate_traceTransfer_smul_sq (unitSquareClassRep c)
  obtain ⟨hk, hw1, hw2⟩ := relative_values_congr σ hc hQ hrep
  obtain ⟨hcor, hsw1, hsw2, hev⟩ := representative_values σ c hrep
  refine ⟨c, ⟨hc, ?_, hw1.trans hsw1, hw2.trans hsw2, ?_⟩, fun d hd => hunique d hd.1⟩
  · rw [hk]
    exact hcor
  · rw [hk]
    exact hev

/-- **The relative Stiefel–Whitney calculation on the uniformizer coset of `ℚ₂(√5)`.** Every
nonzero element of odd valuation is, modulo squares, `2` times the unit representative with
unique coordinates `c`. Corestriction and the first class of the twisted trace form agree with
those of that unit, while the second class and the Evens norm both change by `(1 + c₂) κ`,
where `κ = (-1) ∪ (-1)`. With `existsUnique_relative_traceTransfer_values_of_even`, this
evaluates both relative identities on all sixteen square classes of `ℚ₂(√5)`. -/
theorem existsUnique_relative_traceTransfer_values_of_odd
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]) (a : DyadicSqrtFiveˣ)
    (ha : Odd (normalizedValuation DyadicSqrtFive a).toAdd)
    (hQ : (((a : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    ∃! c : Fin 3 → ZMod 2,
      squareClass a = squareClass
        (Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * unitSquareClassRep c) ∧
      galoisCor ℚ_[2] DyadicSqrtFive σ 1 (kummerClass a) =
        c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
          c 2 • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw1Class (formClass _ hQ) = c 1 • kummerClass (-1 : ℚ_[2]ˣ) +
        (1 + c 2) • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) ∧
      sw2Class (formClass _ hQ) = ((1 + c 0) * (1 + c 1) + (1 + c 2)) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) ∧
      galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two (kummerClass a) =
        ((1 + c 0) * (1 + c 1) + c 2) •
          kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  obtain ⟨c, hc, hunique⟩ := (existsUnique_two_mul_unitSquareClassRep_iff_odd a).mpr ha
  have hrep := nondegenerate_traceTransfer_smul_sq
    (Units.mk0 (2 : DyadicSqrtFive) (by norm_num) * unitSquareClassRep c)
  obtain ⟨hk, hw1, hw2⟩ := relative_values_congr σ hc hQ hrep
  obtain ⟨hcor, hsw1, hsw2, hev⟩ := two_mul_representative_values σ c hrep
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
